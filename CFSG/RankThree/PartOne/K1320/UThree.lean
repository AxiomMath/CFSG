module

public import CFSG.RankThree.PartOne.K1320.Row5
public import CFSG.RankThree.PartOne.K1320.RankU6
public import CFSG.RankThree.PartTwo.CTU6.ExtCU

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem three_le_of_dvd_two_pow_sub_one {p f : ℕ} (h5 : 5 ≤ p) (hf1 : 1 ≤ f)
    (hpq : p ∣ 2 ^ f - 1) : 3 ≤ f := by
  by_contra hlt
  have hpos : 0 < 2 ^ f - 1 := by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega
  have hle := Nat.le_of_dvd hpos hpq
  have hf : f = 1 ∨ f = 2 := by omega
  rcases hf with rfl | rfl <;> omega

theorem isPerfect_sup_three {G : Type} [Group G] {H₁ H₂ H₃ : Subgroup G}
    (h₁ : Group.IsPerfect ↥H₁) (h₂ : Group.IsPerfect ↥H₂) (h₃ : Group.IsPerfect ↥H₃) :
    Group.IsPerfect ↥(H₁ ⊔ H₂ ⊔ H₃) := by
  have hc : ∀ H : Subgroup G, Group.IsPerfect ↥H → ⁅H, H⁆ = H := by
    intro H hH
    have h := hH.commutator_eq_top
    have h2 := congrArg (Subgroup.map H.subtype) h
    rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  set J := H₁ ⊔ H₂ ⊔ H₃ with hJ
  have hle : ∀ H : Subgroup G, Group.IsPerfect ↥H → H ≤ J → H ≤ ⁅J, J⁆ := by
    intro H hH hHJ
    calc H = ⁅H, H⁆ := (hc H hH).symm
      _ ≤ ⁅J, J⁆ := Subgroup.commutator_mono hHJ hHJ
  have hJle : J ≤ ⁅J, J⁆ :=
    sup_le (sup_le (hle H₁ h₁ (le_sup_left.trans le_sup_left))
      (hle H₂ h₂ (le_sup_right.trans le_sup_left))) (hle H₃ h₃ le_sup_right)
  have hJeq : ⁅J, J⁆ = J := le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)) hJle
  refine ⟨?_⟩
  refine Subgroup.map_injective J.subtype_injective ?_
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  simpa [Subgroup.map_top, Subgroup.range_subtype] using hJeq

theorem not_le_centralizer_swap {G : Type} [Group G] {p : ℕ} {E L : Subgroup G}
    {t₁ t₂ t₃ : MulAut E} {f₁ f₂ : ℕ} {K₁ K₂ : Subgroup G} (hd : RefFacts.ElemData p E)
    (hch : Chain3 p E L t₁ t₂ t₃) (h₁ : KFKt p E f₁ t₁ K₁) (h₂ : KFKt p E f₂ t₂ K₂) :
    ¬ (E ⊓ K₁ ≤ Subgroup.centralizer (K₂ : Set G)) := by
  intro h
  have hmov : autMovedInG E t₁ ≤ E ⊓ K₁ := le_inf (Subgroup.map_subtype_le _) h₁.2.2.2.2.1
  have hfix : autMovedInG E t₁ ≤ autFixedInG E t₂ := by
    have h1 : autMovedInG E t₁ ≤ E ⊓ Subgroup.centralizer (K₂ : Set G) :=
      le_inf (hmov.trans inf_le_left) (hmov.trans h)
    rwa [h₂.2.2.2.1] at h1
  have hord : orderOf (t₂ * t₁) = 4 :=
    (Sec1320.orderOf_mul_comm_reflections hch.mem₁.1 hch.mem₂.1).trans hch.ord₁₂
  exact Sec1320.moved_not_le_fixed hd hch.mem₂.1 hch.mem₁.1 hord
    ((Subgroup.map_le_map_iff_of_injective E.subtype_injective).1 hfix)

variable {G : Type} [Group G] [Finite G]

theorem kf1320UThreeAt_four
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two)
    (hDist : S13K.KFCommDistinct) (hdist : RowModelsDistinct)
    (hRow5 : Row5Data) : KF1320UThreeAt 4 := by
  intro G _ _ p A c L E f h hF hF13 hT hf1 hpf hmodel hEA _ hweyl t₁ t₂ t₃ hch K₂ hK₂ hmod2
  obtain ⟨eX⟩ := hweyl
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd_two_pow_sub_one hp5 hf1 hpf
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  obtain ⟨hcen, hpair⟩ := hRow5 G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  have hn8 : ¬ ∃ f' : ℕ, 1 ≤ f' ∧ p ∣ 2 ^ f' + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f' :=
    fun ⟨_, _, _, h4⟩ => not_row8_of_psu hdist (Or.inl rfl) hmodel h4
  obtain ⟨w, hw, hs₁, hs₁L, hs₂, hs₂L, hord⟩ := chain_conj_into_L hp hch
  obtain ⟨hdeg, hgen⟩ := hpair _ hs₁ hs₁L _ hs₂ hs₂L hord
  rcases hdeg with ⟨hA1, hA2⟩ | ⟨-, hA2⟩
  ·
    have hKA₁ : KFAt p E f t₁ := KFAt.of_conj hw hA1
    have hKA₂ : KFAt p E (2 * f) t₂ := KFAt.of_conj hw hA2
    obtain ⟨w₃, hw₃, ht₃⟩ := chain_t₃_conj hch
    have hKA₃ : KFAt p E (2 * f) t₃ := by rw [ht₃]; exact hKA₂.conj hw₃
    have hLmod : StatedClassicalModel ↥L .PSU 4 2 f :=
      statedClassicalModel_of_equiv
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot) hmodel
    have hcomm := chain_comm_clause hS h133 hDist h hF hF13 hT hEA hn8 hz hch hw hs₁ hs₁L
      hA1 hKA₃ hpf
    have hL3 := chain_pair_L3 hGA hS h133 h hF hF13 hT hEA hn8 hz hch hKA₂
      (PAIR22.pairLift_of_kfAt hKA₃)
    have hU4 := chain_sup_model hw hgen hLmod
    have hk₁ := kfKt_of_kfAt hKA₁
    have hk₂ := kfKt_of_kfAt hKA₂
    have hk₃ := kfKt_of_kfAt hKA₃
    obtain ⟨hI, hEI, htor⟩ := Sec1320.package hp hp5 h.E_elem hF13.irreducible hch hk₁ hk₂ hk₃
    have hdE : RefFacts.ElemData p E :=
      RefFacts.ElemData.of_isElementaryAbelian hp (by omega) h.E_elem
    have hstd := not_le_centralizer_swap hdE hch hk₁ hk₂
    have h₃I : kZero p E t₃ ≤ lieGenerated p E := by rw [hI]; exact le_sup_left.trans le_sup_left
    have h₂I : kZero p E t₂ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right.trans le_sup_left
    have h₁I : kZero p E t₁ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right
    have hCT := extCurtisTitsCThreeU_ambient CFSG.RankThree.PartTwo.CTU6.extCurtisTitsCThreeU
      (by omega : 2 ≤ f) hp hpf h.E_elem hEI h₃I h₂I h₁I hI.symm hKA₃.2.1 hKA₂.2.1 hKA₁.2.1
      (Sec1320.commuting_symm hcomm) hL3 hU4 htor hstd
    have hperf : Group.IsPerfect ↥(lieGenerated p E) := by
      rw [hI]
      exact isPerfect_sup_three (S13K.isQuasisimple_of_model_psl_two hKA₃.2.1).1
        (S13K.isQuasisimple_of_model_psl_two hKA₂.2.1).1
        (S13K.isQuasisimple_of_model_psl_two hKA₁.2.1).1
    exact false_of_psu_six hGA hperf hf3 hCT h.setup.2.2.2.2.1
  ·
    have hKA₂ : KFAt p E f t₂ := KFAt.of_conj hw hA2
    have hK2eq : K₂ = kZero p E t₂ := (kfKt_of_kfAt hKA₂).2.1 K₂ hK₂
    rw [hK2eq] at hmod2
    have := psl_two_degree_eq hKA₂.2.1 hmod2
    omega

theorem kf1320U_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two)
    (hDist : S13K.KFCommDistinct) (hdist : RowModelsDistinct) :
    KF1320U' :=
  kf1320U'_holds hGA hS h133 hDist hdist
    (kf1320UThreeAt_four hGA hS h133 hDist hdist (row5Data_holds hGA))

end CFSG.RankThree.PartOne.K1320
