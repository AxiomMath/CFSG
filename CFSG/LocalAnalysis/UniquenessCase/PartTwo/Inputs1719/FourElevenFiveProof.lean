module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenCommon
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenClosing
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenPGLTwo
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenYStep
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenYStepFive
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenOuterMember

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.FourEleven

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p : ℕ}

theorem FourElevenSetting.centralizer_le_five (h : FourElevenSetting Q L p) (hp : p = 5)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω)
    (hcard : ∀ A ∈ Ω, A ≤ T → 8 ≤ Nat.card A) {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    centralizer ({z} : Set Q) ≤ genEi 2 T Ω ⊔ T := by
  subst hp
  have hN : L.Normal := h.normal
  have hP : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨A₀, hA₀Ω, hA₀T⟩ := hΩ.exists_mem_le hT
  have hA₀ : IsElemAbelian 2 A₀ := hΩ.elemAbelian A₀ hA₀Ω
  have h8 : 8 ≤ Nat.card A₀ := hcard A₀ hA₀Ω hA₀T
  have h4 : Nat.card ↥(A₀ ⊓ L) ≤ 4 := card_inf_le_four h.prime h.ne_two h.isL3 hA₀
  have h2le : Nat.card A₀ ≤ 2 * Nat.card ↥(A₀ ⊓ L) :=
    card_le_two_mul_card_inf h.index_le_two A₀
  have hA₀card : Nat.card A₀ = 8 := by omega
  have h4eq : Nat.card ↥(A₀ ⊓ L) = 4 := by omega
  have hzA : z ∈ A₀ :=
    mem_of_commute_of_card_inf_eq_four h.prime h.ne_two h.isL3 hA₀ h4eq hzL hz2
      (fun a ha => hzT a (hA₀T ha))
  obtain ⟨Y, hY⟩ := exists_leviData h.prime le_rfl h.isL3 hzL hz2
  have hYL : Y ≤ L := by
    rw [hY.eq_commutator]
    exact (Subgroup.commutator_le_self (L ⊓ centralizer ({z} : Set Q))).trans inf_le_left
  have hYsl2 := hY.sl2
  have hout : ∀ b : Q, b ∉ L → orderOf b = 2 → ¬ Y ≤ centralizer ({b} : Set Q) := by
    intro b hbL hb2
    exact OuterData.not_le_centralizer (p := 5) (by norm_num)
      (outerData_of_lieModel h.prime le_rfl h.centralizer_eq_bot h.isL3 hbL hb2) hYL hYsl2
  have hAY : ¬ A₀ ≤ centralizer (Y : Set Q) :=
    LeviData.not_le_centralizer hY h.index_le_two hout hA₀ (by omega)
  have hzT' : T ≤ centralizer ({z} : Set Q) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hzT t ht).symm
  have hK : InCalEi 2 T A₀ (centralizer ({z} : Set Q)) :=
    LeviData.inCalEi_two_centralizer_five h.isL3 h.pCoreOf_two_top h.isPGroup_quotient hT hA₀T
      hA₀ hA₀card hzA hz2 hzT' hY hAY
  exact (le_genEi_of_inCalEi hA₀Ω hA₀T hK).trans le_sup_left

theorem FourElevenSetting.exists_conj_five (h : FourElevenSetting Q L p) (hp : p = 5)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω)
    (hcard : ∀ A ∈ Ω, A ≤ T → 8 ≤ Nat.card A) {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ c ∈ genEi 2 T Ω ⊔ T, c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
  subst hp
  have hN : L.Normal := h.normal
  have hP : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨A₀, hA₀Ω, hA₀T⟩ := hΩ.exists_mem_le hT
  have hA₀ : IsElemAbelian 2 A₀ := hΩ.elemAbelian A₀ hA₀Ω
  have h8 : 8 ≤ Nat.card A₀ := hcard A₀ hA₀Ω hA₀T
  have h4 : Nat.card ↥(A₀ ⊓ L) ≤ 4 := card_inf_le_four h.prime h.ne_two h.isL3 hA₀
  have h2le : Nat.card A₀ ≤ 2 * Nat.card ↥(A₀ ⊓ L) :=
    card_le_two_mul_card_inf h.index_le_two A₀
  have hA₀card : Nat.card A₀ = 8 := by omega
  have hA₀notL : ¬ A₀ ≤ L := by
    intro hle
    have hinf : A₀ ⊓ L = A₀ := inf_eq_left.mpr hle
    rw [hinf] at h4
    omega
  obtain ⟨b, hbA₀, hbL⟩ := Set.not_subset.mp hA₀notL
  have hb2 : orderOf b = 2 := by
    apply orderOf_eq_prime
    · exact hA₀.2 b hbA₀
    · intro hb1
      exact hbL (hb1 ▸ L.one_mem)
  obtain ⟨g, hA'Ω, hA'T, hSyl⟩ :=
    exists_conj_isSylowIn_centralizer hT hΩ hA₀Ω hA₀T hbA₀
  set A' := conjSubgroup A₀ g with hA'def
  have hcardA' : Nat.card A' = 8 := by
    rw [hA'def, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      hA₀card]
  have hA' : IsElemAbelian 2 A' := hΩ.elemAbelian A' hA'Ω
  have hA'le : Nat.card A' ≤ 2 * Nat.card ↥(A' ⊓ L) :=
    card_le_two_mul_card_inf h.index_le_two A'
  have hA'L : A' ⊓ L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA'le
    omega
  have hb'A' : g⁻¹ * b * g ∈ A' := by
    rw [hA'def, conjSubgroup]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hbA₀
  have hb'L : g⁻¹ * b * g ∉ L := by
    intro hmem
    exact hbL (by simpa [mul_assoc] using h.normal.conj_mem (g⁻¹ * b * g) hmem g)
  have hb'2 : orderOf (g⁻¹ * b * g) = 2 := by
    simpa using (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b).trans hb2
  have hb' : OuterData L 5 (g⁻¹ * b * g) :=
    outerData_of_lieModel h.prime le_rfl h.centralizer_eq_bot h.isL3 hb'L hb'2
  have hKb : centralizer ({g⁻¹ * b * g} : Set Q) ≤ genEi 2 T Ω := by
    apply le_genEi_of_inCalEi hA'Ω hA'T
    exact OuterData.inCalEi_two_centralizer_five h.isPGroup_quotient h.pCoreOf_two_top hT
      hA'T hA' hcardA' hb'A' hb'L hSyl hb' hA'L
  have hzC : z ∈ centralizer ({g⁻¹ * b * g} : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hzT (g⁻¹ * b * g) (hA'T hb'A')
  obtain ⟨c, hcH, hne, hcomm⟩ :=
    exists_commuting_conj_of_mulEquiv_pgl2 (p := 5) (by norm_num)
      (Classical.choice hb'.pgl2) ⟨hzL, hzC⟩ hz2
  exact ⟨c, Subgroup.mem_sup_left (hKb hcH.2), hne, hcomm⟩

theorem fourElevenFive_holds : FourElevenFive := by
  intro Q _ _ L p h hp T hT Ω hΩ hcard
  subst hp
  have hN : L.Normal := h.normal
  have hcard8 : ∀ A ∈ Ω, A ≤ T → 8 ≤ Nat.card A := by
    intro A hA hAT
    have := hcard A hA hAT
    norm_num at this
    exact this
  obtain ⟨z, hzL, hz2, hzT⟩ := h.exists_central_involution hT
  have hCen : centralizer ({z} : Set Q) ≤ genEi 2 T Ω ⊔ T :=
    FourElevenSetting.centralizer_le_five h rfl hT hΩ hcard8 hzL hz2 hzT
  obtain ⟨c, hcK, hne, hcomm⟩ :=
    FourElevenSetting.exists_conj_five h rfl hT hΩ hcard8 hzL hz2 hzT
  have hY : ⁅L ⊓ centralizer ({z} : Set Q), L ⊓ centralizer ({z} : Set Q)⁆ ≤
      genEi 2 T Ω ⊔ T :=
    (Subgroup.commutator_le_self (L ⊓ centralizer ({z} : Set Q))).trans
      (le_trans inf_le_right hCen)
  have hLK : L ≤ genEi 2 T Ω ⊔ T :=
    le_of_commutator_le_of_commuting_conj h.prime (by norm_num) h.isL3 hzL hz2 hY hcK hne
      hcomm
  exact h.eq_top_of_le hT hLK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
