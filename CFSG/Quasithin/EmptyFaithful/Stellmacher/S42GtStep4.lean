module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtCop
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S42Gt

open CosetGeom F53 S42B1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

omit [Finite G] in
theorem elem_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

namespace Sit

theorem Zv_le_Qv_nbr (hs : Sit H M S α a₂ a₃ β) {μ : Geo H M} (hμ : μ ∈ nbrs β) :
    Zv μ ≤ Qv β := by
  refine Zv_le_Qv_of_dist_lt ?_
  have h1 : dist μ β = 1 := dist_eq_one_iff_adj.mpr
    (show (graph (H ⊔ M) H M).Adj β μ from hμ).symm
  have h2 := bMin_le_bAt (H := H) (M := M) μ
  have := hs.b1
  omega

theorem stab_le_sup (hs : Sit H M S α a₂ a₃ β) {K : Subgroup G} (h1 : Qv α ≤ K)
    (h2 : Qv a₂ ≤ K) : stab β ≤ K ⊔ Qv β := by
  have e1 : Qv α ⊔ Qv β = stab β ⊓ stab α := by rw [hs.sup_Qv, inf_comm]
  have e2 : Qv a₂ ⊔ Qv β = stab β ⊓ stab a₂ := by
    have := hs.swap₁₂.sup_Qv
    rwa [inf_comm] at this
  have := sup_edges_eq_stab hs.amalg hs.vβ hs.n₁ hs.tri.hb hs.tri.hab
  rw [← this, ← e1, ← e2]
  exact sup_le (sup_le_sup_right h1 _) (sup_le_sup_right h2 _)

theorem exists_mem_C (hs : Sit H M S α a₂ a₃ β) (hb3 : 3 ≤ bMin H M) :
    ∃ s ∈ stab α ⊓ stab β,
      s ∈ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) ∧ s ∉ Qv α := by
  by_contra hcon
  push Not at hcon
  have hA := hs.amalg
  have hQS : Qv β ≤ stab α ⊓ stab β := by
    have := Qv_le_inf hA hs.n₁
    rwa [inf_comm] at this
  have hQβst : Qv β ≤ stab β := pCoreOf_le 2 _
  have hQp : IsPGroup 2 (Qv β) := pCoreOf_isPGroup 2 (stab β)
  have hYZ₁ : ∀ y ∈ Zv α ⊓ Zv a₂, ∀ q ∈ Qv α, q * y = y * q := fun y hy q hq =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hy.1).2 q hq
  have hYZ₂ : ∀ y ∈ Zv α ⊓ Zv a₂, ∀ q ∈ Qv a₂, q * y = y * q := fun y hy q hq =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA a₂ hy.2).2 q hq
  have hCn : stab β ≤ Subgroup.normalizer
      ((stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) : Subgroup G) :
        Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (hs.R_normal.trans (normalizer_le_normalizer_centralizer _))
  have hNC : Qv α ⊓ Qv β = (stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G)) ⊓
      Qv β := by
    apply le_antisymm
    · intro x hx
      exact ⟨⟨hQβst hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (hYZ₁ y hy x hx.1).symm⟩, hx.2⟩
    · intro x hx
      exact ⟨hcon x ⟨(hQS hx.2).1, hx.1.1⟩ hx.1.2, hx.2⟩
  have hNn : stab β ≤ Subgroup.normalizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
    rw [hNC]
    exact le_normalizer_inf hCn (le_normalizer_pCoreOf 2 (stab β))
  have hNμ : ∀ μ ∈ nbrs β, Qv α ⊓ Qv β ≤ Qv μ := by
    intro μ hμ
    obtain ⟨g, hg, hgα⟩ := stab_transitive_on_nbrs hs.n₁ hμ
    have hQ := Qv_smul g α
    rw [hgα] at hQ
    rw [hQ]
    calc Qv α ⊓ Qv β = conjSub (g : G) (Qv α ⊓ Qv β) :=
          (conjSub_eq_of_mem_normalizer (hNn hg)).symm
      _ ≤ conjSub (g : G) (Qv α) := conjSub_mono _ inf_le_left
  have hVE := isElemAbelian_Vn hA hb3 β
  have hZV : ∀ μ ∈ nbrs β, Zv μ ≤ Vn β := fun μ hμ =>
    le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β) => Zv μ) μ hμ le_rfl
  have hVQ : Vn β ≤ Qv β := iSup₂_le fun μ hμ => hs.Zv_le_Qv_nbr hμ
  have hVn : ∀ g ∈ stab β, ∀ x ∈ Vn β, g * x * g⁻¹ ∈ Vn β := by
    intro g hg x hx
    have hc : conjSub g (Vn β) = Vn β := by
      have := Vn_smul (⟨g, stab_le β hg⟩ : ↥(H ⊔ M)) β
      rw [smul_eq_of_mem_stab hg] at this
      exact this.symm
    have := (conj_mem_conjSub_iff (g := g) (y := x) (C := Vn β)).mpr hx
    rwa [hc] at this
  have hVN : ∀ v ∈ Vn β, ∀ n ∈ Qv α ⊓ Qv β, n * v = v * n := by
    have : Vn β ≤ Subgroup.centralizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) :=
      iSup₂_le fun μ hμ z hz => Subgroup.mem_centralizer_iff.mpr fun n hn =>
        (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hz).2 n (hNμ μ hμ hn))
    intro v hv n hn
    exact Subgroup.mem_centralizer_iff.mp (this hv) n hn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d', hd'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stab β)) 3
    (three_dvd_card_stab hA hs.vβ)
  have hdst : (d' : G) ∈ stab β := d'.2
  have hdord : orderOf (d' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd'
  have hd3 : (d' : G) ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one _
  have hdcube : (d' : G) * d' * d' = 1 := by
    have : (d' : G) * d' * d' = (d' : G) ^ 3 := by rw [pow_succ, pow_two]
    rw [this, hd3]
  have hQαC : Qv α ≤ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) :=
    fun q hq => ⟨Qv_le_stab_of_mem_nbrs hA hs.n₀ hq,
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hYZ₁ y hy q hq).symm⟩
  have hQ₂C : Qv a₂ ≤ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G) :=
    fun q hq => ⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hs.tri.hb) hq,
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hYZ₂ y hy q hq).symm⟩
  have hCQ := hs.stab_le_sup hQαC hQ₂C
  have hdC := mem_of_odd_of_le_sup hCn hQβst hQp hCQ hdst (by decide) hd3
  have hcomm' : ∀ c ∈ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Zv a₂ : Subgroup G) : Set G),
      ∀ x ∈ Qv β, c * x * c⁻¹ * x⁻¹ ∈ Qv α ⊓ Qv β := by
    intro c hc x hx
    rw [hNC]
    refine ⟨?_, ?_⟩
    · have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc
        ((Subgroup.mem_normalizer_iff.mp (hCn (hQβst hx)) _).mp (Subgroup.inv_mem _ hc))
    · exact Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab β) hc.1) x).mp hx)
        (Subgroup.inv_mem _ hx)
  have hmove : ∃ v ∈ Vn β, (d' : G) * v * (d' : G)⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    have hdZ : (d' : G) ∈ Subgroup.centralizer (Zv α : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        calc h * (d' : G) = ((d' : G) * h * (d' : G)⁻¹) * d' := by rw [hall h (hZV _ hs.n₁ hh)]
          _ = d' * h := by group
    have hconj : conjSub (d' : G) (Zv α) = Zv α :=
      conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hdZ)
    have hdg : (d' : G) ∈ H ⊔ M := stab_le β hdst
    have hZs := Zv_smul (⟨d', hdg⟩ : ↥(H ⊔ M)) α
    rw [hconj] at hZs
    have hmem : (⟨d', hdg⟩ : ↥(H ⊔ M)) • α ∈ nbrs β := smul_mem_nbrs_of_mem_stab hdst hs.n₁
    have hT2 : IsPGroup 2 ((stab β ⊓ stab α : Subgroup G)) :=
      (sylow_stab_inf_left hA hs.n₁).2.1
    have hne : (⟨d', hdg⟩ : ↥(H ⊔ M)) • α ≠ α := by
      intro h
      have hdα : (d' : G) ∈ stab α := mem_stab_of_smul_eq h
      have h1 : (d' : G) = 1 :=
        eq_one_of_pow_odd_of_isPGroup hT2 ⟨hdst, hdα⟩ (by decide) hd3
      rw [h1, orderOf_one] at hdord
      omega
    rcases hs.tri.all _ hmem with h | h | h
    · exact hne h
    · rw [h] at hZs
      exact hs.not_Zv_le hZs.symm.le
    · rw [h] at hZs
      apply hs.not_Zv_le
      have h1 : Zv α ≤ Zv α ⊓ Zv a₃ := le_inf le_rfl hZs.symm.le
      rw [← hs.R_eq₁] at h1
      exact h1.trans inf_le_right
  have hE : ElemNorm (Vn β) (d' : G) :=
    ⟨fun x hx y hy => elem_comm hVE hx hy, fun x hx => by rw [← pow_two]; exact hVE.2 x hx,
      fun x hx => hVn d' hdst x hx, hdcube⟩
  have hUne : dCom _ (d' : G) hE ≠ ⊥ := fun hb => by
    obtain ⟨v, hv, hne⟩ := hmove
    exact hne ((dCom_eq_bot_iff hE).mp hb v hv)
  have hUQ : dCom _ (d' : G) hE ≤ Qv β := (dCom_le hE).trans hVQ
  have key : ∀ q ∈ Qv β, ∀ u ∈ dCom _ (d' : G) hE, q * u * q⁻¹ ∈ dCom _ (d' : G) hE := by
    intro q hq
    refine dCom_conj_of_commute hE (fun x hx => hVn q (hQβst hq) x hx) (fun x hx => ?_)
    have hn : (d' : G)⁻¹ * q * d' * q⁻¹ ∈ Qv α ⊓ Qv β := by
      have := hcomm' (d' : G)⁻¹ (Subgroup.inv_mem _ hdC) q hq
      simpa using this
    have hx' : q * x * q⁻¹ ∈ Vn β := hVn q (hQβst hq) x hx
    have hc := hVN _ hx' _ hn
    calc ((d' : G)⁻¹ * q * d') * x * ((d' : G)⁻¹ * q * d')⁻¹
        = ((d' : G)⁻¹ * q * d' * q⁻¹) * (q * x * q⁻¹) * ((d' : G)⁻¹ * q * d' * q⁻¹)⁻¹ := by
          group
      _ = q * x * q⁻¹ := by rw [hc]; group
  have hUn : Qv β ≤ Subgroup.normalizer ((dCom _ (d' : G) hE : Subgroup G) : Set G) := by
    intro q hq
    exact F53B3.O1.mem_normalizer_of_conj (key q hq)
      (fun x hx => by simpa using key q⁻¹ (Subgroup.inv_mem _ hq) x hx)
  obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (F53B3.O1.inf_centralizer_ne_bot_of_normalized hQp hUQ hUn hUne)
  obtain ⟨hfU, hfC⟩ := Subgroup.mem_inf.mp hf
  have hfV : f ∈ Vn β := dCom_le hE hfU
  have hfΩ : f ∈ quasithinOmegaOneCenter (Qv β) :=
    Subgroup.subset_closure ⟨⟨hUQ hfU, hfC⟩, by rw [pow_two]; exact hE.sq f hfV⟩
  have hfix := hs.centralizes_omega hdst hdcube f hfΩ
  exact hf1 (Subtype.ext (eq_one_of_fix hE hfU hfix))

end Sit

end F53.Stellmacher.S42Gt

end CFSG.Quasithin
