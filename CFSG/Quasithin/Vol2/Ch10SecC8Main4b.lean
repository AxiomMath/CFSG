module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecC8Z

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

section Component

variable {K : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
  {D : L3Data (autOn K (Vi T L I K)) ⊤
    ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}

omit [Finite G] in
theorem card_Vi (hF : CompFacts T L I K D) : Nat.card ↥(Vi T L I K) = 16 := by
  have h := D.card_U
  rw [hF.2.2.2.2.2.2.2.1, Subgroup.card_top] at h
  exact h

omit [Finite G] in
theorem T1_le_normalizer_Vi (hF : CompFacts T L I K D) :
    T1 T L ≤ Subgroup.normalizer (Vi T L I K : Set G) := by
  obtain ⟨hKL0, hKN, hTK, hD, hact, -⟩ := hF
  refine le_normalizer_of_conj_mem fun s hs w hw => ?_
  obtain ⟨d, hd, hds⟩ := hact s hs
  rw [hds w hw]
  exact (Subgroup.mem_normalizer_iff.mp
    (SecA.le_normalizer_commutator hKN Subgroup.le_normalizer hd.2) w).mp hw

omit [Finite G] in
theorem autOn_T1_le (hF : CompFacts T L I K D) {s : G} (hs : s ∈ T1 T L)
    (hsN : s ∈ Subgroup.normalizer (Vi T L I K : Set G)) :
    ∃ γ, IsU γ ∧ (D.π γ : MulAut ↥(Vi T L I K)) = conjAct (Vi T L I K) ⟨s, hsN⟩ := by
  obtain ⟨hKL0, hKN, hTK, hD, hact, -⟩ := hF
  obtain ⟨d, hd, hds⟩ := hact s hs
  have hdN : d ∈ Subgroup.normalizer (Vi T L I K : Set G) :=
    SecA.le_normalizer_commutator hKN Subgroup.le_normalizer hd.2
  have he : conjAct (Vi T L I K) ⟨s, hsN⟩ = conjAct (Vi T L I K) ⟨d, hdN⟩ := by
    ext w
    exact hds w w.2
  obtain ⟨γ, hγ⟩ := D.π_surj ⟨conjAct (Vi T L I K) ⟨d, hdN⟩,
    SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hd.2, rfl⟩⟩
  refine ⟨γ, ?_, by rw [he, hγ]⟩
  rw [← mem_U3, ← hD, hγ]
  exact SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hd, rfl⟩

theorem le_card_autOn_mul (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2)
    (hF : CompFacts T L I K D) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    16 ≤ Nat.card (autOn A (Vi T L I K)) * Nat.card (fixV (autOn A (Vi T L I K))) := by
  have h16 := card_Vi hF
  have hAT1 : A ≤ T1 T L := (B6.le_thompsonJ hA).trans (h1012 G T L I hyp).2.1
  have hAN : A ≤ Subgroup.normalizer (Vi T L I K : Set G) := hAT1.trans (T1_le_normalizer_Vi hF)
  have hWV : Vi T L I K ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF.2.1
  have hWel : IsElemAbelian 2 (Vi T L I K) :=
    ⟨inferInstance, fun x hx => (SecA.isElemAbelian_fsuVM hyp).2 x (hWV hx)⟩
  have h1 := card_mul_le_of_isMaxElemAbelian hA hWel (hWV.trans (SecA.fsuVM_le_T hyp))
  rw [card_autOn_eq hAN, card_fixV_autOn_eq hAN]
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (Vi T L I K : Set G)) A
  rw [inf_comm] at h2
  rw [h16, ← h2] at h1
  have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (Vi T L I K : Set G)) := Nat.card_pos
  have h3 : Nat.card ↥(A ⊓ Subgroup.centralizer (Vi T L I K : Set G)) * 16 ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer (Vi T L I K : Set G)) *
        ((Subgroup.centralizer (Vi T L I K : Set G)).relIndex A *
          Nat.card ↥(Vi T L I K ⊓ Subgroup.centralizer (A : Set G))) := by
    calc Nat.card ↥(A ⊓ Subgroup.centralizer (Vi T L I K : Set G)) * 16 =
        16 * Nat.card ↥(A ⊓ Subgroup.centralizer (Vi T L I K : Set G)) := by ring
      _ ≤ _ := h1
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 hpos

theorem autOn_maxElemAbelian (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2)
    (hF : CompFacts T L I K D) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    (∀ b ∈ autOn A (Vi T L I K), b = 1) ∨
      ((∀ b ∈ autOn A (Vi T L I K), ∃ γ, IsEa γ ∧ (D.π γ : MulAut ↥(Vi T L I K)) = b) ∧
        ∀ γ, IsEa γ → (D.π γ : MulAut ↥(Vi T L I K)) ∈ autOn A (Vi T L I K)) := by
  have h16 := le_card_autOn_mul hyp h1012 hF hA
  have hAT1 : A ≤ T1 T L := (B6.le_thompsonJ hA).trans (h1012 G T L I hyp).2.1
  have hBU : ∀ b ∈ autOn A (Vi T L I K), ∃ γ, IsU γ ∧ (D.π γ : MulAut ↥(Vi T L I K)) = b := by
    intro b hb
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := SecB.mem_autOn_iff.mp hb
    exact autOn_T1_le hF (hAT1 haA) haN
  obtain ⟨hKL0, hKN, hTK, hD, hact, hsq, hfix, hZc, hFF, hE4⟩ := hF
  have hBG : autOn A (Vi T L I K) ≤ autOn K (Vi T L I K) := fun b hb => by
    obtain ⟨γ, -, hγ⟩ := hBU b hb
    rw [← hγ]
    exact (D.π γ).2
  have hBel := isElemAbelian2_autOn (W := Vi T L I K) hA.2.1
  by_cases hB : autOn A (Vi T L I K) = ⊥
  · left
    intro b hb
    rw [hB] at hb
    exact (Subgroup.mem_bot).mp hb
  · right
    exact offender_eq_ea D hFF hZc hE4 hBG hBU hBel hB h16

omit [Finite G] in
theorem card_secSub_e0 (hF : CompFacts T L I K D) : Nat.card ↥(secSub D e0) = 4 := by
  have : Finite ↥(Vi T L I K) := Nat.finite_of_card_ne_zero (by rw [card_Vi hF]; norm_num)
  obtain ⟨-, -, -, -, -, hsq, -, hZc, -⟩ := hF
  obtain ⟨w, hw⟩ := coordOf_surj D e0
  have hwZ : w ∉ (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K) := by
    rw [← coordOf_eq_zero_iff D, hw]
    decide
  have heq : secSub D e0 =
      (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K) ⊔ Subgroup.zpowers w := by
    apply le_antisymm
    · rintro x (h | h)
      · exact Subgroup.mem_sup_left ((coordOf_eq_zero_iff D x).mp h)
      · have hx : x * w⁻¹ ∈ (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
            (Vi T L I K) := by
          rw [← coordOf_eq_zero_iff D, coordOf_mul, coordOf_inv, h, hw]
          exact add_neg_cancel _
        have e : x = x * w⁻¹ * w := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    · refine sup_le (fun z hz => Or.inl ((coordOf_eq_zero_iff D z).mpr hz)) ?_
      exact Subgroup.zpowers_le.mpr (Or.inr hw)
  rw [heq, card_sup_zpowers hwZ (hsq w)
    (le_normalizer_of_comm (X := ⊤) (fun a _ b _ => mul_comm a b) le_top le_top), hZc]

end Component

section TwoComponents

variable {K K' : Subgroup G} [IsMulCommutative ↥(Vi T L I K)] [IsMulCommutative ↥(Vi T L I K')]
  {D : L3Data (autOn K (Vi T L I K)) ⊤
    ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}
  {D' : L3Data (autOn K' (Vi T L I K')) ⊤
    ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K'))}

theorem card_fsuVM_eq (hyp : Hyp10 G T L I) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hcap : Vi T L I K ⊓ Vi T L I K' ≤ fsuCVM T L I) :
    Nat.card ↥(fsuVM T L I) = 16 * Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
      (secSub D' e0).map (Vi T L I K').subtype) := by
  have hWV : Vi T L I K ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF.2.1
  have hW'V : Vi T L I K' ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF'.2.1
  have hUW : (secSub D e0).map (Vi T L I K).subtype ≤ Vi T L I K := Subgroup.map_subtype_le _
  have hU'W' : (secSub D' e0).map (Vi T L I K').subtype ≤ Vi T L I K' :=
    Subgroup.map_subtype_le _
  have hU4 : Nat.card ↥((secSub D e0).map (Vi T L I K).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Vi T L I K).subtype_injective, card_secSub_e0 hF]
  have hU'4 : Nat.card ↥((secSub D' e0).map (Vi T L I K').subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Vi T L I K').subtype_injective, card_secSub_e0 hF']
  have hinf : (secSub D e0).map (Vi T L I K).subtype ⊓ (secSub D' e0).map (Vi T L I K').subtype =
      Vi T L I K ⊓ Vi T L I K' := by
    apply le_antisymm (inf_le_inf hUW hU'W')
    rintro x ⟨hx, hx'⟩
    have hxC := hcap ⟨hx, hx'⟩
    refine ⟨⟨⟨x, hx⟩, Or.inl ?_, rfl⟩, ⟨⟨x, hx'⟩, Or.inl ?_, rfl⟩⟩
    · exact (coordOf_eq_zero_iff D _).mpr (Subgroup.mem_subgroupOf.mpr hxC.2)
    · exact (coordOf_eq_zero_iff D' _).mpr (Subgroup.mem_subgroupOf.mpr hxC.2)
  have e1 := card_sup_mul_card_inf (H := (secSub D e0).map (Vi T L I K).subtype)
    (K := (secSub D' e0).map (Vi T L I K').subtype)
    (le_normalizer_of_le_fsuVM hyp (hU'W'.trans hW'V) (hUW.trans hWV))
  have e2 := card_sup_mul_card_inf (H := Vi T L I K) (K := Vi T L I K')
    (le_normalizer_of_le_fsuVM hyp hW'V hWV)
  rw [hinf, hU4, hU'4] at e1
  rw [← hV, card_Vi hF, card_Vi hF'] at e2
  have hx : 0 < Nat.card ↥(Vi T L I K ⊓ Vi T L I K') := Nat.card_pos
  have h1 : Nat.card ↥(fsuVM T L I) * Nat.card ↥(Vi T L I K ⊓ Vi T L I K') =
      16 * Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
        (secSub D' e0).map (Vi T L I K').subtype) * Nat.card ↥(Vi T L I K ⊓ Vi T L I K') := by
    rw [e2, mul_assoc, e1]
  exact Nat.eq_of_mul_eq_mul_right hx h1

theorem coord_conj_eq_of_fix (hyp : Hyp10 G T L I) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hcap : Vi T L I K ⊓ Vi T L I K' ≤ fsuCVM T L I) {a : G}
    (ha : a ∈ T1 T L) {w w' : G} (hw : w ∈ Vi T L I K) (hw' : w' ∈ Vi T L I K')
    (hfix : a * (w * w') * a⁻¹ = w * w') :
    coordOf D ⟨a * w * a⁻¹, (Subgroup.mem_normalizer_iff.mp (T1_le_normalizer_Vi hF ha) w).mp hw⟩ =
      coordOf D ⟨w, hw⟩ := by
  have hWV : Vi T L I K ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF.2.1
  have hW'V : Vi T L I K' ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF'.2.1
  have hp := (Subgroup.mem_normalizer_iff.mp (T1_le_normalizer_Vi hF ha) w).mp hw
  have hq := (Subgroup.mem_normalizer_iff.mp (T1_le_normalizer_Vi hF' ha) w').mp hw'
  have hy1 : a * w * a⁻¹ * w⁻¹ ∈ Vi T L I K := Subgroup.mul_mem _ hp (Subgroup.inv_mem _ hw)
  have hy2 : a * w * a⁻¹ * w⁻¹ ∈ Vi T L I K' := by
    have e1 : a * (w * w') * a⁻¹ = (a * w * a⁻¹) * (a * w' * a⁻¹) := by group
    rw [e1] at hfix
    have e2 : a * w * a⁻¹ * w⁻¹ = w' * (a * w' * a⁻¹)⁻¹ := by
      have hc1 := fsuVM_comm hyp (hWV hw) (hW'V hw')
      have hc2 := fsuVM_comm hyp (hWV hp) (hW'V hq)
      calc a * w * a⁻¹ * w⁻¹ = (a * w * a⁻¹) * (a * w' * a⁻¹) * (a * w' * a⁻¹)⁻¹ * w⁻¹ := by
            group
        _ = (w * w') * (a * w' * a⁻¹)⁻¹ * w⁻¹ := by rw [hfix]
        _ = (w' * w) * (a * w' * a⁻¹)⁻¹ * w⁻¹ := by rw [hc1]
        _ = w' * (w * (a * w' * a⁻¹)⁻¹ * w⁻¹) := by group
        _ = w' * (a * w' * a⁻¹)⁻¹ := by
            rw [fsuVM_comm hyp (hWV hw) ((fsuVM T L I).inv_mem (hW'V hq))]
            group
    rw [e2]
    exact Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ hq)
  have hyC := hcap ⟨hy1, hy2⟩
  have h0 : coordOf D ⟨_, hy1⟩ = 0 :=
    (coordOf_eq_zero_iff D _).mpr (Subgroup.mem_subgroupOf.mpr hyC.2)
  have e : (⟨a * w * a⁻¹ * w⁻¹, hy1⟩ : ↥(Vi T L I K)) = ⟨_, hp⟩ * (⟨w, hw⟩)⁻¹ := rfl
  rw [e, coordOf_mul, coordOf_inv] at h0
  exact eq_of_add_neg_eq_zero h0

theorem fsuVM_inf_centralizer_le_sup (hyp : Hyp10 G T L I) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hcap : Vi T L I K ⊓ Vi T L I K' ≤ fsuCVM T L I) {A : Subgroup G} (hAT1 : A ≤ T1 T L)
    (hB : ∀ γ, IsEa γ → (D.π γ : MulAut ↥(Vi T L I K)) ∈ autOn A (Vi T L I K))
    (hB' : ∀ γ, IsEa γ → (D'.π γ : MulAut ↥(Vi T L I K')) ∈ autOn A (Vi T L I K')) :
    fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) ≤
      (secSub D e0).map (Vi T L I K).subtype ⊔ (secSub D' e0).map (Vi T L I K').subtype := by
  have hWV : Vi T L I K ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF.2.1
  have hW'V : Vi T L I K' ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hF'.2.1
  rintro v ⟨hv, hvc⟩
  have hv' : v ∈ (↑(Vi T L I K ⊔ Vi T L I K') : Set G) := by rw [← hV]; exact hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_le_fsuVM hyp hW'V hWV)] at hv'
  obtain ⟨w, hw, w', hw', hww⟩ := hv'
  have hww' : w * w' = v := hww
  have hfix : ∀ a ∈ A, a * (w * w') * a⁻¹ = w * w' := fun a ha => by
    rw [hww', Subgroup.mem_centralizer_iff.mp hvc a ha, mul_inv_cancel_right]
  have hwU : (⟨w, hw⟩ : ↥(Vi T L I K)) ∈ secSub D e0 := by
    refine fix_Ea _ fun γ hγ => ?_
    obtain ⟨⟨a, haN⟩, haA, haγ⟩ := SecB.mem_autOn_iff.mp (hB γ hγ)
    rw [← coordOf_π, ← haγ]
    exact coord_conj_eq_of_fix hyp hF hF' hcap (hAT1 haA) hw hw' (hfix a haA)
  have hw'U : (⟨w', hw'⟩ : ↥(Vi T L I K')) ∈ secSub D' e0 := by
    refine fix_Ea _ fun γ hγ => ?_
    obtain ⟨⟨a, haN⟩, haA, haγ⟩ := SecB.mem_autOn_iff.mp (hB' γ hγ)
    rw [← coordOf_π, ← haγ]
    have hcap' : Vi T L I K' ⊓ Vi T L I K ≤ fsuCVM T L I := by rw [inf_comm]; exact hcap
    have hfix' : a * (w' * w) * a⁻¹ = w' * w := by
      rw [fsuVM_comm hyp (hW'V hw') (hWV hw)]
      exact hfix a haA
    exact coord_conj_eq_of_fix hyp hF' hF hcap' (hAT1 haA) hw' hw hfix'
  rw [← hww']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, hwU, rfl⟩)
    (Subgroup.mem_sup_right ⟨_, hw'U, rfl⟩)

omit [Finite G] in
theorem card_autOn_eq_four {A : Subgroup G} (hB1 : ∀ b ∈ autOn A (Vi T L I K), ∃ γ, IsEa γ ∧
      (D.π γ : MulAut ↥(Vi T L I K)) = b)
    (hB2 : ∀ γ, IsEa γ → (D.π γ : MulAut ↥(Vi T L I K)) ∈ autOn A (Vi T L I K)) :
    Nat.card (autOn A (Vi T L I K)) = 4 := by
  have heq : autOn A (Vi T L I K) = (Ea.map D.π).map (autOn K (Vi T L I K)).subtype := by
    ext b
    constructor
    · intro hb
      obtain ⟨γ, hγ, rfl⟩ := hB1 b hb
      exact ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact hB2 γ hγ
  rw [heq, Subgroup.card_map_of_injective (autOn K (Vi T L I K)).subtype_injective,
    Subgroup.card_map_of_injective D.π_injective, Nat.card_eq_fintype_card, ← card_Ea]
  exact Fintype.card_subtype (· ∈ Ea)

theorem exists_realize_ea (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hcap : Vi T L I K ⊓ Vi T L I K' ≤ fsuCVM T L I) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAW : ¬ A ≤ Subgroup.centralizer (Vi T L I K : Set G))
    {γ : L3.Γ} (hγ : IsEa γ) :
    ∃ a ∈ A ⊓ Subgroup.centralizer (Vi T L I K' : Set G),
      ∃ haN : a ∈ Subgroup.normalizer (Vi T L I K : Set G),
        conjAct (Vi T L I K) ⟨a, haN⟩ = (D.π γ : MulAut ↥(Vi T L I K)) := by
  have hAT1 : A ≤ T1 T L := (B6.le_thompsonJ hA).trans (h1012 G T L I hyp).2.1
  have hAN : A ≤ Subgroup.normalizer (Vi T L I K : Set G) := hAT1.trans (T1_le_normalizer_Vi hF)
  have hAN' : A ≤ Subgroup.normalizer (Vi T L I K' : Set G) :=
    hAT1.trans (T1_le_normalizer_Vi hF')
  obtain ⟨hB1, hB2⟩ : (∀ b ∈ autOn A (Vi T L I K), ∃ γ, IsEa γ ∧
      (D.π γ : MulAut ↥(Vi T L I K)) = b) ∧
      ∀ γ, IsEa γ → (D.π γ : MulAut ↥(Vi T L I K)) ∈ autOn A (Vi T L I K) := by
    rcases autOn_maxElemAbelian hyp h1012 hF hA with h | h
    · exfalso
      apply hAW
      intro a ha
      have h1 := h _ (SecB.mem_autOn_iff.mpr ⟨⟨a, hAN ha⟩, ha, rfl⟩)
      exact A4.conjAct_eq_one_iff.mp h1
    · exact h
  suffices hmem : (D.π γ : MulAut ↥(Vi T L I K)) ∈
      autOn (A ⊓ Subgroup.centralizer (Vi T L I K' : Set G)) (Vi T L I K) by
    obtain ⟨⟨a, haN⟩, ha, hae⟩ := SecB.mem_autOn_iff.mp hmem
    exact ⟨a, ha, haN, hae⟩
  rcases autOn_maxElemAbelian hyp h1012 hF' hA with h' | ⟨hB1', hB2'⟩
  ·
    have hA2 : A ⊓ Subgroup.centralizer (Vi T L I K' : Set G) = A := by
      refine inf_eq_left.mpr fun a ha => ?_
      exact A4.conjAct_eq_one_iff.mp (h' _ (SecB.mem_autOn_iff.mpr ⟨⟨a, hAN' ha⟩, ha, rfl⟩))
    rw [hA2]
    exact hB2 γ hγ
  ·
    have hcard := card_autOn_eq_four hB1 hB2
    have hcard' := card_autOn_eq_four hB1' hB2'
    have hVel : IsElemAbelian 2 (fsuVM T L I) := SecA.isElemAbelian_fsuVM hyp
    have h1 := card_mul_le_of_isMaxElemAbelian hA hVel (SecA.fsuVM_le_T hyp)
    have hle := Subgroup.card_le_of_le
      (fsuVM_inf_centralizer_le_sup hyp hF hF' hV hcap hAT1 hB2 hB2')
    rw [card_fsuVM_eq hyp hF hF' hV hcap] at h1
    have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (fsuVM T L I : Set G)) A
    rw [inf_comm] at h2
    have hpos : 0 < Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
        (secSub D' e0).map (Vi T L I K').subtype) := Nat.card_pos
    have hpos' : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := Nat.card_pos
    have h16 : 16 ≤ (Subgroup.centralizer (fsuVM T L I : Set G)).relIndex A := by
      have h3 : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) *
          Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
            (secSub D' e0).map (Vi T L I K').subtype) ≤
          (Subgroup.centralizer (fsuVM T L I : Set G)).relIndex A *
            Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) *
            Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
              (secSub D' e0).map (Vi T L I K').subtype) := by
        calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) *
            Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
              (secSub D' e0).map (Vi T L I K').subtype) =
            16 * Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
              (secSub D' e0).map (Vi T L I K').subtype) *
              Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by ring
          _ ≤ Nat.card A * Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) := h1
          _ ≤ Nat.card A * Nat.card ↥((secSub D e0).map (Vi T L I K).subtype ⊔
              (secSub D' e0).map (Vi T L I K').subtype) := Nat.mul_le_mul_left _ hle
          _ = _ := by rw [← h2]
      have h4 := Nat.le_of_mul_le_mul_right h3 hpos
      exact Nat.le_of_mul_le_mul_left ((le_of_eq (mul_comm _ _)).trans
        (h4.trans (le_of_eq (mul_comm _ _)))) hpos'
    have hCV : Subgroup.centralizer (Vi T L I K : Set G) ⊓
        (A ⊓ Subgroup.centralizer (Vi T L I K' : Set G)) =
        A ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
      ext a
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [hV]
        exact ⟨h2, mem_centralizer_sup h1 h3⟩
      · rintro ⟨h2, h4⟩
        rw [hV] at h4
        exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) h4, h2,
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) h4⟩
    have hchain := Subgroup.relIndex_mul_relIndex
      (A ⊓ Subgroup.centralizer (fsuVM T L I : Set G))
      (A ⊓ Subgroup.centralizer (Vi T L I K' : Set G)) A
      (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (commutator_le_left_of_le_normalizer hF'.2.1)))) inf_le_left
    rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, ← card_autOn_eq hAN',
      hcard'] at hchain
    have hA2N : A ⊓ Subgroup.centralizer (Vi T L I K' : Set G) ≤
        Subgroup.normalizer (Vi T L I K : Set G) := inf_le_left.trans hAN
    have hc2 : 4 ≤ Nat.card (autOn (A ⊓ Subgroup.centralizer (Vi T L I K' : Set G))
        (Vi T L I K)) := by
      rw [card_autOn_eq hA2N, ← Subgroup.inf_relIndex_right, hCV]
      omega
    have hsub : autOn (A ⊓ Subgroup.centralizer (Vi T L I K' : Set G)) (Vi T L I K) ≤
        autOn A (Vi T L I K) := autOn_mono inf_le_left
    have heq := Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard]; exact hc2)
    rw [heq]
    exact hB2 γ hγ

end TwoComponents

omit [Finite G] in
theorem mul_inv_mem_Q {x y : G} (hx : x ∈ T) (hy : y ∈ T)
    (h : ∀ v ∈ fsuVM T L I, x * v * x⁻¹ = y * v * y⁻¹) :
    x * y⁻¹ ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
  refine ⟨T.mul_mem hx (T.inv_mem hy), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hv' : y⁻¹ * v * y ∈ fsuVM T L I := by
    have := (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_fsuVM T L I (T.inv_mem hy)) v).mp
      hv
    rwa [inv_inv] at this
  have h1 := h _ hv'
  have e1 : y * (y⁻¹ * v * y) * y⁻¹ = v := by group
  rw [e1] at h1
  calc v * (x * y⁻¹) = x * (y⁻¹ * v * y) * x⁻¹ * (x * y⁻¹) := by rw [h1]
    _ = x * y⁻¹ * v := by group

theorem exists_maxElemAbelian_not_le (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3210 : TmpL6_3_2_10_nine) (hne : cV1 T L I ≠ ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    (∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (fsuUL T L I : Set G)) ∧
      ∃ A, IsMaxElemAbelian T A ∧
        ¬ A ≤ Subgroup.centralizer
          ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, -, -, -⟩ := hdec t ht htn
  have hJ := not_thompsonJ_le_centralizer hyp h3210 (fsuCVM_ne_bot_of_cV1 hne)
  obtain ⟨A, hA, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    by_contra hcon
    exact hJ (iSup₂_le fun A hA => by
      by_contra h
      exact hcon ⟨A, hA, h⟩)
  have hW := mem_V2_iff (L := L) (I := I) ht
  have hmap : ∀ g ∈ T, IsMaxElemAbelian T (A.map (MulAut.conj g).toMonoidHom) := by
    intro g hg
    have hT : T.map (MulAut.conj g).toMonoidHom = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact T.mul_mem (T.mul_mem hg hy) (T.inv_mem hg)
      · intro hx
        refine ⟨g⁻¹ * x * g, T.mul_mem (T.mul_mem (T.inv_mem hg) hx) hg, ?_⟩
        change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
    have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g) (H := T) (A := A)).mpr hA
    rwa [hT] at this
  by_cases h1 : A ≤ Subgroup.centralizer (fsuUL T L I : Set G)
  ·
    have h2 : ¬ A ≤ Subgroup.centralizer
        ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
      intro h2
      apply hAV
      intro a ha
      rw [hVeq]
      exact mem_centralizer_sup (h1 ha) (h2 ha)
    refine ⟨⟨A.map (MulAut.conj t).toMonoidHom, hmap t ht, fun h => h2 fun a ha => ?_⟩,
      A, hA, h2⟩
    have h3 := h ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at h3 ⊢
    intro w hw
    have hw' := (hW w).mp hw
    have h4 := h3 _ hw'
    change t * w * t⁻¹ * (t * a * t⁻¹) = t * a * t⁻¹ * (t * w * t⁻¹) at h4
    have e1 : w * a = t⁻¹ * (t * w * t⁻¹ * (t * a * t⁻¹)) * t := by group
    have e2 : a * w = t⁻¹ * (t * a * t⁻¹ * (t * w * t⁻¹)) * t := by group
    rw [e1, e2, h4]
  · refine ⟨⟨A, hA, h1⟩, A.map (MulAut.conj t⁻¹).toMonoidHom, hmap t⁻¹ (T.inv_mem ht),
      fun h => h1 fun a ha => ?_⟩
    have h3 := h ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at h3 ⊢
    intro w hw
    have hw' : t⁻¹ * w * t ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
      rw [hW]
      have e : t * (t⁻¹ * w * t) * t⁻¹ = w := by group
      rw [e]
      exact hw
    have h4 := h3 _ hw'
    change t⁻¹ * w * t * (t⁻¹ * a * t⁻¹⁻¹) = t⁻¹ * a * t⁻¹⁻¹ * (t⁻¹ * w * t) at h4
    have e1 : w * a = t * (t⁻¹ * w * t * (t⁻¹ * a * t⁻¹⁻¹)) * t⁻¹ := by group
    have e2 : a * w = t * (t⁻¹ * a * t⁻¹⁻¹ * (t⁻¹ * w * t)) * t⁻¹ := by group
    rw [e1, e2, h4]

theorem R_le_thompsonJ_sup {K K' : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
    [IsMulCommutative ↥(Vi T L I K')]
    {D : L3Data (autOn K (Vi T L I K)) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}
    {D' : L3Data (autOn K' (Vi T L I K')) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K'))}
    (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hcap : Vi T L I K ⊓ Vi T L I K' ≤ fsuCVM T L I)
    (hW'K : Vi T L I K' ≤ Subgroup.centralizer (K : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAW : ¬ A ≤ Subgroup.centralizer (Vi T L I K : Set G)) {U R : Subgroup G}
    (hU : IsU10_2_8 T L I K U) (hR : IsR10_2_8 T L I K U R) :
    R ≤ thompsonJ T ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  intro r hr
  have hrT := hR.1 hr
  obtain ⟨hKL0, hKN, hTK, hD, hact, -⟩ := id hF
  obtain ⟨k, hk, hkr, γ, hγE, hkN, hkγ⟩ :=
    (mem_R_iff D hKN hKL0 hD hTK hact hV hW'K hU hR hrT).mp hr
  obtain ⟨a, ⟨haA, haW'⟩, haN, haγ⟩ := exists_realize_ea hyp h1012 hF hF' hV hcap hA hAW hγE
  have haT : a ∈ T := hA.1 haA
  have hagree : ∀ v ∈ fsuVM T L I, r * v * r⁻¹ = a * v * a⁻¹ := by
    intro v hv
    rw [hV] at hv
    refine mem_of_le_eqSet (fun x hx => ?_) (fun y hy => ?_) hv
    · rw [hkr x (commutator_le_left_of_le_normalizer hKN hx)]
      have h1 := congrArg (fun f : MulAut ↥(Vi T L I K) => ((f ⟨x, hx⟩ : ↥(Vi T L I K)) : G))
        (hkγ.trans haγ.symm)
      exact h1
    · rw [hkr y (commutator_le_left_of_le_normalizer hF'.2.1 hy),
        Subgroup.mem_centralizer_iff.mp (hW'K hy) k hk, mul_inv_cancel_right,
        ← Subgroup.mem_centralizer_iff.mp haW' y hy, mul_inv_cancel_right]
  have hq := mul_inv_mem_Q hrT haT hagree
  have e : r = r * a⁻¹ * a := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq)
    (Subgroup.mem_sup_left (B6.le_thompsonJ hA haA))

theorem maxElemAbelian_le_R_sup {K K' : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
    [IsMulCommutative ↥(Vi T L I K')]
    {D : L3Data (autOn K (Vi T L I K)) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}
    {D' : L3Data (autOn K' (Vi T L I K')) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K'))}
    (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2) (hF : CompFacts T L I K D)
    (hF' : CompFacts T L I K' D') (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hW'K : Vi T L I K' ≤ Subgroup.centralizer (K : Set G))
    (hWK' : Vi T L I K ≤ Subgroup.centralizer (K' : Set G))
    {U U' R R' : Subgroup G} (hU : IsU10_2_8 T L I K U) (hR : IsR10_2_8 T L I K U R)
    (hU' : IsU10_2_8 T L I K' U') (hR' : IsR10_2_8 T L I K' U' R')
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ R ⊔ R' ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  intro a haA
  have haT : a ∈ T := hA.1 haA
  have hAT1 : A ≤ T1 T L := (B6.le_thompsonJ hA).trans (h1012 G T L I hyp).2.1
  have key : ∀ {K₁ K₂ : Subgroup G} [IsMulCommutative ↥(Vi T L I K₁)]
      {D₁ : L3Data (autOn K₁ (Vi T L I K₁)) ⊤
        ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K₁))}
      (hF₁ : CompFacts T L I K₁ D₁) (hV₁ : fsuVM T L I = Vi T L I K₁ ⊔ Vi T L I K₂)
      (hW₂ : Vi T L I K₂ ≤ Subgroup.centralizer (K₁ : Set G)) {U₁ R₁ : Subgroup G}
      (hU₁ : IsU10_2_8 T L I K₁ U₁) (hR₁ : IsR10_2_8 T L I K₁ U₁ R₁),
      ∃ d ∈ R₁, d ∈ T ⊓ K₁ ∧ ∀ w ∈ Vi T L I K₁, a * w * a⁻¹ = d * w * d⁻¹ := by
    intro K₁ K₂ _ D₁ hF₁ hV₁ hW₂ U₁ R₁ hU₁ hR₁
    have haN := T1_le_normalizer_Vi hF₁ (hAT1 haA)
    obtain ⟨γ, hγE, hγa⟩ : ∃ γ, IsEa γ ∧
        (D₁.π γ : MulAut ↥(Vi T L I K₁)) = conjAct (Vi T L I K₁) ⟨a, haN⟩ := by
      have hmem : conjAct (Vi T L I K₁) ⟨a, haN⟩ ∈ autOn A (Vi T L I K₁) :=
        SecB.mem_autOn_iff.mpr ⟨⟨a, haN⟩, haA, rfl⟩
      rcases autOn_maxElemAbelian hyp h1012 hF₁ hA with h | ⟨h1, -⟩
      · exact ⟨1, isEa_one, by rw [map_one, Subgroup.coe_one, h _ hmem]⟩
      · exact h1 _ hmem
    obtain ⟨hKL0, hKN, hTK, hD, hact, -⟩ := id hF₁
    obtain ⟨⟨d, hdN⟩, hdTK, hdγ⟩ := SecB.mem_autOn_iff.mp ((hD γ).mpr (ea_le γ hγE).2)
    refine ⟨d, (mem_R_iff D₁ hKN hKL0 hD hTK hact hV₁ hW₂ hU₁ hR₁ hdTK.1).mpr
      ⟨d, hdTK.2, fun v _ => rfl, γ, hγE, hdN, hdγ⟩, hdTK, fun w hw => ?_⟩
    have h1 := congrArg (fun f : MulAut ↥(Vi T L I K₁) => ((f ⟨w, hw⟩ : ↥(Vi T L I K₁)) : G))
      (hdγ.trans hγa)
    exact h1.symm
  obtain ⟨d₁, hd₁R, hd₁, hd₁a⟩ := key hF hV hW'K hU hR
  have hV' : fsuVM T L I = Vi T L I K' ⊔ Vi T L I K := by rw [hV, sup_comm]
  obtain ⟨d₂, hd₂R, hd₂, hd₂a⟩ := key hF' hV' hWK' hU' hR'
  have hagree : ∀ v ∈ fsuVM T L I, a * v * a⁻¹ = (d₁ * d₂) * v * (d₁ * d₂)⁻¹ := by
    intro v hv
    rw [hV] at hv
    refine mem_of_le_eqSet (fun x hx => ?_) (fun y hy => ?_) hv
    · rw [hd₁a x hx]
      have hc : d₂ * x * d₂⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff.mp (hWK' hx) d₂ hd₂.2, mul_inv_cancel_right]
      calc d₁ * x * d₁⁻¹ = d₁ * (d₂ * x * d₂⁻¹) * d₁⁻¹ := by rw [hc]
        _ = (d₁ * d₂) * x * (d₁ * d₂)⁻¹ := by group
    · rw [hd₂a y hy]
      have hy' : d₂ * y * d₂⁻¹ ∈ Vi T L I K' :=
        (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator hF'.2.1
          Subgroup.le_normalizer hd₂.2) y).mp hy
      have hc : d₁ * (d₂ * y * d₂⁻¹) * d₁⁻¹ = d₂ * y * d₂⁻¹ := by
        rw [Subgroup.mem_centralizer_iff.mp (hW'K hy') d₁ hd₁.2, mul_inv_cancel_right]
      calc d₂ * y * d₂⁻¹ = d₁ * (d₂ * y * d₂⁻¹) * d₁⁻¹ := hc.symm
        _ = (d₁ * d₂) * y * (d₁ * d₂)⁻¹ := by group
  have hq := mul_inv_mem_Q haT (T.mul_mem hd₁.1 hd₂.1) hagree
  have e : a = a * (d₁ * d₂)⁻¹ * (d₁ * d₂) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd₁R))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd₂R)))

theorem R_sup_eq_thompsonJ_sup (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h484 : ASInputs.AS_B_4_8_four) (h3210 : TmpL6_3_2_10_nine)
    (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₁ U₂ R₁ R₂ : Subgroup G}
    (hU₁ : IsU10_2_8 T L I L U₁) (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂)
    (hR₁ : IsR10_2_8 T L I L U₁ R₁) (hR₂ : IsR10_2_8 T L I (CFSG.conjugate L t) U₂ R₂) :
    R₁ ⊔ R₂ ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) =
      thompsonJ T ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  have hV12 : fsuVM T L I = Vi T L I L ⊔ Vi T L I (CFSG.conjugate L t) := hVeq
  have hV21 : fsuVM T L I = Vi T L I (CFSG.conjugate L t) ⊔ Vi T L I L := by
    rw [hV12, sup_comm]
  have hcap12 : Vi T L I L ⊓ Vi T L I (CFSG.conjugate L t) ≤ fsuCVM T L I :=
    inf_V2_le_fsuCVM hyp h1011 ht htn
  have hcap21 : Vi T L I (CFSG.conjugate L t) ⊓ Vi T L I L ≤ fsuCVM T L I := by
    rw [inf_comm]
    exact hcap12
  obtain ⟨⟨A₁, hA₁, hA₁W⟩, ⟨A₂, hA₂, hA₂W⟩⟩ :=
    exists_maxElemAbelian_not_le hyp h1011 h3210 hne ht htn
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact R_le_thompsonJ_sup hyp h1012 hF1 hF2 hV12 hcap12 hV2 hA₁ hA₁W hU₁ hR₁
    · exact R_le_thompsonJ_sup hyp h1012 hF2 hF1 hV21 hcap21 hV1 hA₂ hA₂W hU₂ hR₂
  · refine sup_le (iSup₂_le fun A hA => ?_) le_sup_right
    exact maxElemAbelian_le_R_sup hyp h1012 hF1 hF2 hV12 hV2 hV1 hU₁ hR₁ hU₂ hR₂ hA

end CFSG.Quasithin.Vol2.Ch10.SecC
