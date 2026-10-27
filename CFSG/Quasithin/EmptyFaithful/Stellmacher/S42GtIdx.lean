module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S42Gt

open CosetGeom F53 S42B1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

theorem card_le_two_of_sq_eq_one {B : Subgroup (Equiv.Perm (Fin 3))}
    (hB : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hB x x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hB2
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm]
    simp [Nat.factorial]
  have hd : Nat.card B ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card B
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : n ≤ 1 := by omega
    have h3 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h4 : 2 ^ 2 ∣ Nat.card B := hn ▸ pow_dvd_pow 2 h2
  have := h4.trans hd
  omega

theorem relIndex_inf_Qv_le_two (hA : F53Amalgam H M S) (hv : vtype β = true) {K : Subgroup G}
    (hK : K ≤ stab β) (hKe : IsElemAbelian 2 K) : (K ⊓ Qv β).relIndex K ≤ 2 := by
  obtain ⟨ψ, -, hψ⟩ := exists_quotHom_true hA hv
  have hker : ψ.ker = (Qv β).subgroupOf (stab β) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hψ x
  rw [relIndex_inf_eq_card_map hker hK]
  apply card_le_two_of_sq_eq_one
  rintro _ ⟨a, ha, rfl⟩
  have ha2 : a * a = 1 :=
    Subtype.ext (by simpa [pow_two] using hKe.2 _ (Subgroup.mem_subgroupOf.mp ha))
  rw [← map_mul, ha2, map_one]

namespace Sit

theorem relIndex_Y_le_eight (hs : Sit H M S α a₂ a₃ β) (hb3 : 3 ≤ bMin H M) {α' : Geo H M}
    (hc : IsCritData α β α') (hv' : vtype α' = true) :
    (Zv α ⊓ Zv a₂).relIndex (Zv α) ≤ 8 := by
  have hA := hs.amalg
  have hbA : bAt α = bMin H M := hs.bα
  obtain ⟨γ₁, hγ₁adj, hγ₁d⟩ := exists_adj_dist_eq hA.amalgam.gen (α := β) (δ := α')
    (d := bMin H M - 2) (by have := hc.dist_eq'; omega)
  have hγ₁ : γ₁ ∈ nbrs α' := hγ₁adj
  obtain ⟨γ₂, γ₃, T⟩ := exists_tri hA hv' hγ₁
  have hz' : Zv α' ≤ centerOf (stab α') :=
    Zv_central_of_vtype_eq hA (hs.vβ.trans hv'.symm) hs.hz
  have hvγ₁ : vtype γ₁ = false := vtype_false_of_nbr hv' hγ₁
  have hsit : Sit H M S γ₁ γ₂ γ₃ α' :=
    ⟨hA, hs.h28, hs.b1, (show (graph (H ⊔ M) H M).Adj α' γ₁ from hγ₁).symm, hvγ₁,
      (bAt_eq_of_vtype_eq (hvγ₁.trans hs.vα.symm)).trans hbA, hz', T⟩
  have hvγ₂ : vtype γ₂ = false := hsit.vtype₂
  have hbγ₂ : bAt γ₂ = bMin H M := (bAt_eq_of_vtype_eq (hvγ₂.trans hs.vα.symm)).trans hbA
  have hdαβ : dist α β = 1 := dist_eq_one_iff_adj.mpr hs.adj
  have hdαγ₁ : dist α γ₁ ≤ dist α β + dist β γ₁ := dist_triangle hA.amalgam.gen α β γ₁
  have hZαQγ₁ : Zv α ≤ Qv γ₁ := Zv_le_Qv_of_dist_lt (by rw [hbA]; omega)
  have hZαα' : Zv α ≤ stab α' := Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hbA])
  obtain ⟨x, hxZ, hxQ⟩ := Set.not_subset.mp hc.not_le
  have hxα' : x ∈ stab α' := hZαα' hxZ
  have hxγ₁ : x ∈ stab γ₁ := pCoreOf_le 2 _ (hZαQγ₁ hxZ)
  have hxH : x ∈ H ⊔ M := stab_le α' hxα'
  obtain ⟨h2, -⟩ := T.swap hA (g := ⟨x, hxH⟩) hxα' (smul_eq_of_mem_stab hxγ₁) hxQ
  have hconj3 : conjSub x (Zv γ₂) = Zv γ₃ := by
    have := (Zv_smul (⟨x, hxH⟩ : ↥(H ⊔ M)) γ₂).symm
    rwa [h2] at this
  have hdγ₂α' : dist γ₂ α' = 1 := dist_eq_one_iff_adj.mpr
    (show (graph (H ⊔ M) H M).Adj α' γ₂ from T.hb).symm
  have hK : Zv γ₂ ≤ stab β := by
    refine Zv_le_stab_of_dist_le hA ?_
    have h1 := dist_triangle hA.amalgam.gen γ₂ α' β
    have h2 : dist α' β = dist β α' := dist_comm _ _
    have := hc.dist_eq'
    omega
  have hZγ₁Qβ : Zv γ₁ ≤ Qv β := by
    refine Zv_le_Qv_of_dist_lt ?_
    have h1 : dist γ₁ β = dist β γ₁ := dist_comm _ _
    rw [hsit.bα]
    omega
  have hQβα : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA hs.n₁
  have hY'γ₁ : Zv γ₂ ⊓ Zv γ₃ ≤ Zv γ₁ :=
    calc Zv γ₂ ⊓ Zv γ₃ = Zv γ₁ ⊓ Zv γ₂ := hsit.R_eq₂.symm
      _ ≤ Zv γ₁ := inf_le_left
  have hY'B : Zv γ₂ ⊓ Zv γ₃ ≤ Zv γ₂ ⊓ stab α :=
    le_inf inf_le_left (hY'γ₁.trans (hZγ₁Qβ.trans hQβα))
  have hBQ : (Zv γ₂ ⊓ stab α) ⊓ Qv α ≤ Zv γ₂ ⊓ Zv γ₃ := by
    intro y hy
    refine ⟨hy.1.1, ?_⟩
    have hxy : y * x = x * y :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hxZ).2 y hy.2
    have : x * y * x⁻¹ ∈ conjSub x (Zv γ₂) := conj_mem_conjSub_iff.mpr hy.1.1
    rw [hconj3, show x * y * x⁻¹ = y by rw [← hxy]; group] at this
    exact this
  have hKe : IsElemAbelian 2 (Zv γ₂ ⊓ stab α) :=
    F7.isElemAbelian_mono (isElemAbelian_Zv hA γ₂) inf_le_left
  have h4 : ((Zv γ₂ ⊓ stab α) ⊓ Qv α).relIndex (Zv γ₂ ⊓ stab α) ≤ 4 :=
    relIndex_le_four_of_elemAbelian (quot_stab_five hA hs.vα) inf_le_right hKe
  have h5 : (Zv γ₂ ⊓ Qv β).relIndex (Zv γ₂) ≤ 2 :=
    relIndex_inf_Qv_le_two hA hs.vβ hK (isElemAbelian_Zv hA γ₂)
  have hb1 : (Zv γ₂ ⊓ stab α).relIndex (Zv γ₂) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ hQβα)
      Subgroup.index_ne_zero_of_finite).trans h5
  have hb2 : (Zv γ₂ ⊓ Zv γ₃).relIndex (Zv γ₂ ⊓ stab α) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_left hBQ Subgroup.index_ne_zero_of_finite).trans h4
  have hmul := Subgroup.relIndex_mul_relIndex (Zv γ₂ ⊓ Zv γ₃) (Zv γ₂ ⊓ stab α) (Zv γ₂) hY'B
    inf_le_left
  have hbound : (Zv γ₂ ⊓ Zv γ₃).relIndex (Zv γ₂) ≤ 8 := by
    rw [← hmul]
    calc (Zv γ₂ ⊓ Zv γ₃).relIndex (Zv γ₂ ⊓ stab α) * (Zv γ₂ ⊓ stab α).relIndex (Zv γ₂)
        ≤ 4 * 2 := Nat.mul_le_mul hb2 hb1
      _ = 8 := by norm_num
  obtain ⟨g₁, hg₁⟩ := exists_smul_of_vtype_eq (hvγ₂.trans hs.vα.symm)
  have hg₁α' : g₁ • α' ∈ nbrs α := by
    rw [hg₁]
    exact (smul_mem_nbrs_iff g₁ (l := γ₂) (δ := α')).mpr (nbrs_symm T.hb)
  obtain ⟨h, hh, hhα'⟩ := stab_transitive_on_nbrs hg₁α' hs.n₀
  have hgγ₂ : (h * g₁) • γ₂ = α := by
    rw [mul_smul, ← hg₁]
    exact smul_eq_of_mem_stab hh
  have hgα' : (h * g₁) • α' = β := by rw [mul_smul]; exact hhα'
  have hγ₃nb : (h * g₁) • γ₃ ∈ nbrs β := by
    rw [← hgα']
    exact (smul_mem_nbrs_iff (h * g₁) (l := α') (δ := γ₃)).mpr T.hc
  have hne : α ≠ (h * g₁) • γ₃ := fun he =>
    T.hbc (MulAction.injective (h * g₁) (hgγ₂.trans he))
  have hYY : conjSub ((h * g₁ : ↥(H ⊔ M)) : G) (Zv γ₂ ⊓ Zv γ₃) = Zv α ⊓ Zv a₂ := by
    have e2 := (Zv_smul (h * g₁) γ₂).symm
    have e3 := (Zv_smul (h * g₁) γ₃).symm
    rw [conjSub_inf, e2, e3, hgγ₂]
    exact hs.inf_eq_R hs.n₁ hγ₃nb hne
  have hZZ : conjSub ((h * g₁ : ↥(H ⊔ M)) : G) (Zv γ₂) = Zv α := by
    have e2 := (Zv_smul (h * g₁) γ₂).symm
    rw [e2, hgγ₂]
  have hrel := Subgroup.relIndex_map_map_of_injective
    (f := (MulAut.conj ((h * g₁ : ↥(H ⊔ M)) : G)).toMonoidHom) (Zv γ₂ ⊓ Zv γ₃) (Zv γ₂)
    (MulAut.conj ((h * g₁ : ↥(H ⊔ M)) : G)).injective
  have hrel' : (conjSub ((h * g₁ : ↥(H ⊔ M)) : G) (Zv γ₂ ⊓ Zv γ₃)).relIndex
      (conjSub ((h * g₁ : ↥(H ⊔ M)) : G) (Zv γ₂)) = (Zv γ₂ ⊓ Zv γ₃).relIndex (Zv γ₂) := hrel
  rw [hYY, hZZ] at hrel'
  rw [hrel']
  exact hbound

end Sit

end F53.Stellmacher.S42Gt

end CFSG.Quasithin
