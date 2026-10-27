module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.EndgameE1
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenE

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Iv_smul (g : ↥(H ⊔ M)) (ν : Geo H M) : Iv (g • ν) = conjSub (g : G) (Iv ν) := by
  unfold Iv
  apply le_antisymm
  · rw [le_conjSub_iff]
    refine le_iInf₂ fun δ hδ => ?_
    rw [← le_conjSub_iff, ← Vn_smul]
    exact iInf₂_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • ν)) => Vn δ) (g • δ)
      ((smul_adj g).mpr hδ)
  · refine le_iInf₂ fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs ν := (smul_adj g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (iInf₂_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs ν) => Vn δ) δ' hδ')

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem card_Iv_eq {ν ν' : Geo H M} (hν : vtype ν = true) (hν' : vtype ν' = true) :
    Nat.card (Iv ν') = Nat.card (Iv ν) := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := ν) (δ' := ν') (by rw [hν, hν'])
  rw [Iv_smul, card_conjSub]

theorem le_Vn_of_normal {ν μ δ : Geo H M} (hμ : μ ∈ nbrs ν) (hδ : δ ∈ nbrs ν)
    {T : Subgroup G} (hT : stab ν ≤ Subgroup.normalizer (T : Set G)) (hTV : T ≤ Vn μ) :
    T ≤ Vn δ := by
  obtain ⟨g, hgs, hgμ⟩ := stab_transitive_on_nbrs hμ hδ
  intro r hr
  have h1 : (g : G)⁻¹ * r * (g : G) ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (hT (Subgroup.inv_mem _ hgs)) r).mp hr
    simpa using this
  have h2 : (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ ∈ conjSub (g : G) (Vn μ) :=
    mul_mem_conjSub (hTV h1)
  rw [← Vn_smul, hgμ] at h2
  simpa [mul_assoc] using h2

theorem stab_le_normalizer_RZ (h6 : Claim6Spec H M S) (P : CritPath α β α')
    (h7 : Wnn β ≤ stab P.γ) (hWα : ¬ Wnn β ≤ stab α') :
    stab P.γ ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv P.γ : Subgroup G) : Set G) := by
  have hb := C.hb5
  have hvγ := C.vtype_P_γ P
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hZα'γ : Zv α' ≤ Zv P.γ := C.Zv_le_Zv_of_mem_nbrs hvγ hα'
  set T := ⁅Vn β, Vn α'⁆ ⊔ Zv P.γ with hT
  have hET : stab α' ⊓ stab P.γ ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    have h1 := h6 C (mem_nbrs_comm hα') (C.Vn_beta_le_Qv_P_γ P) hg
    have h2 := stab_le_normalizer_Zv C.hA P.γ hg.2
    have h3 := mem_normalizer_sup' h1 h2
    have e : ⁅Vn β, Vn α'⁆ ⊔ Zv α' ⊔ Zv P.γ = T := by
      rw [hT, sup_assoc, sup_eq_right.mpr hZα'γ]
    rwa [e] at h3
  have hWT : Wnn β ≤ Subgroup.normalizer (T : Set G) := by
    intro w hw
    refine mem_normalizer_sup' ?_ (stab_le_normalizer_Zv C.hA P.γ (h7 hw))
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hw))
      r (C.R_le_Vn_beta hr)
  set E := stab P.γ ⊓ stab α' with hE
  have h3 := C.relIndex_edge_three hvγ hα'
  set J := Wnn β ⊔ E with hJ
  have hEJ : E ≤ J := le_sup_right
  have hJs : J ≤ stab P.γ := sup_le h7 inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hEJ hJs
  rw [h3] at hmul
  have hsJ : stab P.γ ≤ J := by
    by_contra hne
    have h1 : J.relIndex (stab P.γ) ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
    have h0 : E.relIndex J = 1 := by
      have hdvd : E.relIndex J ∣ 3 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso; rw [h] at hmul; omega
    exact hWα ((le_sup_left.trans (Subgroup.relIndex_eq_one.mp h0)).trans inf_le_right)
  refine hsJ.trans (sup_le hWT ?_)
  intro g hg
  exact hET ⟨hg.2, hg.1⟩

theorem lemmaK (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (P : CritPath α β α') (h7 : Wnn β ≤ stab P.γ) :
    ⁅Vn β, Vn α'⁆ ⊔ Zv α' = Iv P.γ ∧ Nat.card (⁅Vn β, Vn α'⁆ : Subgroup G) = 4 ∧
      Nat.card (Iv P.γ) = 8 := by
  have hb := C.hb5
  have hvγ := C.vtype_P_γ P
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hδγ : P.δ ∈ nbrs P.γ := mem_nbrs_comm (P.δ_adj (by omega))
  have hWα := (C.e1 h4 h5 P h7).1
  have hN := C.stab_le_normalizer_RZ h6 P h7 hWα
  have hTV : ⁅Vn β, Vn α'⁆ ⊔ Zv P.γ ≤ Vn α' :=
    sup_le C.R_le_Vn_alpha' (Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hα'))
  have hRδ : ⁅Vn β, Vn α'⁆ ≤ Vn P.δ :=
    le_sup_left.trans (C.le_Vn_of_normal hα' hδγ hN hTV)
  have hZα'γ : Zv α' ≤ Zv P.γ := C.Zv_le_Zv_of_mem_nbrs hvγ hα'
  have hZI : Zv P.γ ≤ Iv P.γ := le_iInf₂ fun _ hε => Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hε)
  have hle : ⁅Vn β, Vn α'⁆ ⊔ Zv α' ≤ Iv P.γ := by
    refine sup_le ?_ (hZα'γ.trans hZI)
    rw [← C.Iv_P_γ_eq P]
    exact le_inf hRδ C.R_le_Vn_alpha'
  have hRZ : ⁅Vn β, Vn α'⁆ ⊓ Zv α' = ⊥ := by
    obtain ⟨hzmem, hz1, hzonly⟩ := C.zgen_spec' C.vtype_alpha'
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases hzonly x hx.2 with h | h
    · exact h
    · exfalso
      apply (h5 C).1
      intro z hz
      rcases hzonly z hz with rfl | rfl
      · exact one_mem _
      · rw [← h]; exact C.R_le_Vn_beta hx.1
  have hcomm : Zv α' ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ : Subgroup G) : Set G) := by
    refine fun z hz => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact isElemAbelian_comm (isElemAbelian_Vn C.hA C.hb3 α') (C.R_le_Vn_alpha' hr)
      (Zv_le_Vn_self C.hA α' hz)
  have hcard : Nat.card (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G) =
      2 * Nat.card (⁅Vn β, Vn α'⁆ : Subgroup G) := by
    have h1 := F112W.relIndex_sup_eq_relIndex_inf (N := ⁅Vn β, Vn α'⁆) hcomm
    rw [hRZ, Subgroup.relIndex_bot_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := Zv α') (K := ⁅Vn β, Vn α'⁆ ⊔ Zv α')
    rw [inf_eq_left.mpr le_sup_right, C.card_Zv_false C.vtype_alpha', h1] at h2
    omega
  have h4R := C.four_le_card_R
  have h8 := hI8 C hvγ
  have hcle := Subgroup.card_le_of_le hle
  have heq : ⁅Vn β, Vn α'⁆ ⊔ Zv α' = Iv P.γ := by
    apply Subgroup.eq_of_le_of_card_ge hle
    omega
  refine ⟨heq, by omega, ?_⟩
  rw [← heq]
  omega

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
