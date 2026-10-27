module

public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes

public section

namespace CFSG.Quasithin.RonanF65

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6

theorem charTwo_of_isPGroup_generalizedFitting {D : Type*} [Group D] [Finite D] {H : Subgroup D}
    (h : IsPGroup 2 ↥(CFSG.generalizedFitting ↥H)) : CharTwo H := by
  have hn : (CFSG.generalizedFitting ↥H).Normal := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hle : CFSG.generalizedFitting ↥H ≤ Open.pCore 2 ↥H := le_pCore 2 hn h
  refine F6.charTwo_iff_centralizer_le.mpr fun x hx => hle ?_
  apply CFSG.centralizer_generalizedFitting_le
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  exact fun y hy => hx y (hle hy)

theorem not_isPGroup_generalizedFitting {D : Type*} [Group D] [Finite D] {H : Subgroup D}
    (h : ¬ CharTwo H) : ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H) :=
  fun hp => h (charTwo_of_isPGroup_generalizedFitting hp)

variable {D : Type*} [Group D] [Finite D] {H₁ H₂ : Subgroup D}

theorem charTwo_of_card_inf (h : IsGoldschmidtAmalgam H₁ H₂)
    (hT : 16 < Nat.card ↥(H₁ ⊓ H₂)) : CharTwo H₁ ∧ CharTwo H₂ := by
  have hG := h.toIsGoldschmidtTriple
  have h₁ := GoldAmN.card_inf_eq_two_mul_left hG
  have h₂ := GoldAmN.card_inf_eq_two_mul_right hG
  refine ⟨?_, ?_⟩
  · by_contra hnc
    obtain ⟨x, hx⟩ := GoldAmN.exists_centThree H₁ h.quotient₁ hnc
    have := GoldAmN.card_pCoreOf_left_le_eight (GoldAmN.amalgam_symm h) hx
    omega
  · by_contra hnc
    obtain ⟨x, hx⟩ := GoldAmN.exists_centThree H₂ h.quotient₂ hnc
    have := GoldAmN.card_pCoreOf_left_le_eight h hx
    omega

theorem charTwo_of_isGoldCaseVICat (h : IsGoldschmidtAmalgam H₁ H₂) (hc : IsGoldCaseVICat H₁ H₂) :
    CharTwo H₁ ∧ CharTwo H₂ := by
  have hG := h.toIsGoldschmidtTriple
  rcases hc with ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | hc | hc | hc | hc
  · exact ⟨charTwo_of_mulEquiv_perm_four e₁, charTwo_of_mulEquiv_perm_four e₂⟩
  · exact ⟨charTwo_of_mulEquiv_z2_perm_four e₁, charTwo_of_mulEquiv_z2_perm_four e₂⟩
  · refine charTwo_of_card_inf h ?_
    rw [hc.card_inf hG]
    norm_num
  · refine charTwo_of_card_inf h ?_
    rw [hc.card_inf hG]
    norm_num
  · refine charTwo_of_card_inf h ?_
    rw [hc.card_inf hG]
    norm_num
  · refine charTwo_of_card_inf h ?_
    rw [GoldAmN.card_inf_eq_two_mul_right hG, hc.2.2.2.2.2.2.2]
    norm_num

theorem charTwo_of_isGoldCaseVICat_or (h : IsGoldschmidtAmalgam H₁ H₂)
    (hc : IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁) : CharTwo H₁ ∧ CharTwo H₂ := by
  rcases hc with hc | hc
  · exact charTwo_of_isGoldCaseVICat h hc
  · exact (charTwo_of_isGoldCaseVICat (GoldAmN.amalgam_symm h) hc).symm

theorem not_isPGroup_of_isGoldCase_i_v
    (h : IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
      IsGoldCaseV H₁ H₂ ∨ IsGoldCaseI H₂ H₁ ∨ IsGoldCaseII H₂ H₁ ∨ IsGoldCaseIII H₂ H₁ ∨
      IsGoldCaseIV H₂ H₁ ∨ IsGoldCaseV H₂ H₁) :
    ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₁) ∨ ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₂) := by
  have key : ¬ CharTwo H₁ ∨ ¬ CharTwo H₂ := by
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact not_charTwo_of_isGoldCase_i_v (Or.inl h)
    · exact not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h))
    · exact not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h)))
    · exact not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact (not_charTwo_of_isGoldCase_i_v (Or.inl h)).symm
    · exact (not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h))).symm
    · exact (not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h)))).symm
    · exact (not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h))))).symm
    · exact (not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h))))).symm
  rcases key with h' | h'
  · exact Or.inl (not_isPGroup_generalizedFitting h')
  · exact Or.inr (not_isPGroup_generalizedFitting h')

theorem perm3_centralizer :
    ∀ c t : Equiv.Perm (Fin 3), t * t = 1 → t ≠ 1 → c * t = t * c → c = 1 ∨ c = t := by
  decide

theorem mem_inf_of_mem_normalizer {A B : Subgroup D} (h : IsGoldschmidtTriple A B) {x : D}
    (hxB : x ∈ B) (hxN : x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D)) :
    x ∈ A ⊓ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient₂
  set T : Subgroup D := A ⊓ B with hT
  set TB : Subgroup B := T.subgroupOf B with hTB
  set π : B →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 B)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ TB := by
    intro y hy
    have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 B) y) = 1 := hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 B) y = 1 := e.injective (h1.trans (map_one e).symm)
    have h3 : y ∈ CFSG.pCore 2 B := (QuotientGroup.eq_one_iff y).mp h2
    have h4 : (y : D) ∈ pCoreOf 2 B := (CFSG.Quasithin.F1.mem_pCore_iff_coe y).mp h3
    exact Subgroup.mem_subgroupOf.mpr (F6.pCoreOf_le_inf_right h h4)
  have hTBidx : TB.index = 3 := h.relIndex_inf_right
  set P : Subgroup (Equiv.Perm (Fin 3)) := TB.map π with hP
  have hPidx : P.index = 3 := by
    rw [hP, Subgroup.index_map_eq (f := π) (H := TB) hπs hker, hTBidx]
  have hPcard : Nat.card P = 2 := by
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card]; rfl
    have hm := Subgroup.card_mul_index (H := P)
    rw [hPidx, h6] at hm
    omega
  obtain ⟨u, v, huv, huniv⟩ := Nat.card_eq_two_iff.mp hPcard
  have hall : ∀ z : P, z = u ∨ z = v := by
    intro z
    have hz : z ∈ ({u, v} : Set P) := by rw [huniv]; exact Set.mem_univ z
    simpa using hz
  have hall' : ∀ c ∈ P, c = u.1 ∨ c = v.1 := fun c hc => by
    rcases hall ⟨c, hc⟩ with h' | h'
    · exact Or.inl (congrArg Subtype.val h')
    · exact Or.inr (congrArg Subtype.val h')
  obtain ⟨t, htP, ht1, hcases⟩ : ∃ t ∈ P, t ≠ 1 ∧ ∀ c ∈ P, c = 1 ∨ c = t := by
    by_cases hu1 : u.1 = 1
    · refine ⟨v.1, v.2, fun hv => huv (Subtype.ext (hu1.trans hv.symm)), fun c hc => ?_⟩
      rcases hall' c hc with h' | h'
      · exact Or.inl (h'.trans hu1)
      · exact Or.inr h'
    · refine ⟨u.1, u.2, hu1, fun c hc => ?_⟩
      have hv1 : v.1 = 1 := by
        rcases hall' 1 P.one_mem with h' | h'
        · exact absurd h'.symm hu1
        · exact h'.symm
      rcases hall' c hc with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans hv1)
  have htt : t * t = 1 := by
    rcases hcases (t * t) (P.mul_mem htP htP) with h' | h'
    · exact h'
    · exact absurd (mul_left_cancel (h'.trans (mul_one t).symm)) ht1
  obtain ⟨t₀, ht₀TB, ht₀⟩ := Subgroup.mem_map.mp htP
  set y : B := ⟨x, hxB⟩ with hy
  have hconj : π y * t * (π y)⁻¹ = t := by
    have hmem : y * t₀ * y⁻¹ ∈ TB := by
      rw [hTB, Subgroup.mem_subgroupOf]
      have h1 : (t₀ : D) ∈ T := Subgroup.mem_subgroupOf.mp ht₀TB
      have h2 := (Subgroup.mem_normalizer_iff.mp hxN (t₀ : D)).mp h1
      simpa [hy] using h2
    have hPmem : π (y * t₀ * y⁻¹) ∈ P := Subgroup.mem_map_of_mem π hmem
    have hPmem' : π (y * t₀ * y⁻¹) = π y * t * (π y)⁻¹ := by
      rw [map_mul, map_mul, map_inv, ht₀]
    rw [hPmem'] at hPmem
    rcases hcases _ hPmem with h' | h'
    · exfalso
      apply ht1
      calc t = (π y)⁻¹ * (π y * t * (π y)⁻¹) * π y := by group
        _ = 1 := by rw [h']; group
    · exact h'
  have hcomm : π y * t = t * π y := mul_inv_eq_iff_eq_mul.mp hconj
  have hPy : π y ∈ P := by
    rcases perm3_centralizer (π y) t htt ht1 hcomm with h' | h'
    · rw [h']; exact P.one_mem
    · rw [h']; exact htP
  obtain ⟨s, hsTB, hs⟩ := Subgroup.mem_map.mp hPy
  have hinv : s⁻¹ * y ∈ TB := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
  have hyTB : y ∈ TB := by
    have := TB.mul_mem hsTB hinv
    simpa using this
  exact Subgroup.mem_subgroupOf.mp hyTB

theorem borelOf_inf_eq {A B : Subgroup D} (h : IsGoldschmidtTriple A B) :
    borelOf B (A ⊓ B) = A ⊓ B := by
  have e : (A ⊓ B) ⊓ B = A ⊓ B := by rw [inf_assoc, inf_idem]
  apply le_antisymm
  · intro x hx
    unfold borelOf at hx
    rw [e] at hx
    exact mem_inf_of_mem_normalizer h hx.1 hx.2
  · intro x hx
    unfold borelOf
    rw [e]
    exact ⟨(Subgroup.mem_inf.mp hx).2, Subgroup.le_normalizer hx⟩

theorem hyp111At_of_charTwo {A B : Subgroup D} (h : IsGoldschmidtTriple A B) (hc : CharTwo A) :
    Hyp111At A B (A ⊓ B) where
  finite := inferInstance
  pgroup := h.isPGroup_inf
  normalizes := inf_le_left.trans Subgroup.le_normalizer
  sylow := by
    rw [inf_eq_left.mpr inf_le_left]
    refine ⟨inf_le_left, h.isPGroup_inf, ?_⟩
    show ¬ 2 ∣ (A ⊓ B).relIndex A
    rw [h.relIndex_inf_left]
    norm_num
  listed := Or.inl ⟨1, le_rfl, CFSG.Quasithin.isL2Quot_one_iff_perm3.2 h.quotient₁⟩
  borel_le := by
    rw [borelOf_inf_eq h]
    exact inf_le_left.trans Subgroup.le_normalizer
  charTwo := by
    have e : A ⊔ (A ⊓ B) ⊔ (A ⊓ B) = A :=
      le_antisymm (sup_le (sup_le le_rfl inf_le_left) inf_le_left) (le_sup_left.trans le_sup_left)
    rw [borelOf_inf_eq h, e]
    exact hc

theorem isWeakBNPair_of_charTwo {D : Type*} [Group D] [Finite D]
    {H₁ H₂ : Subgroup D} (h : IsGoldschmidtAmalgam H₁ H₂) (h₁ : CharTwo H₁) (h₂ : CharTwo H₂) :
    IsWeakBNPair H₁ H₂ := by
  have hG := h.toIsGoldschmidtTriple
  have hDd : pCoreOf 2 (H₁ ⊔ H₂ ⊔ (H₁ ⊓ H₂)) = ⊥ := by
    rw [sup_eq_left.mpr (inf_le_left.trans le_sup_left), hG.gen,
      CFSG.QuasithinUnique.B113Lie.pCoreOf_top_eq_pCore']
    exact h.pCore_eq_bot
  have hA₂ : Hyp111At H₂ H₁ (H₁ ⊓ H₂) := by
    have := hyp111At_of_charTwo hG.symm h₂
    rwa [inf_comm H₂ H₁] at this
  have hH : Hyp111 H₁ H₂ (H₁ ⊓ H₂) := ⟨hyp111At_of_charTwo hG h₁, hA₂, hDd⟩
  have hR : Hyp111R H₁ H₂ (H₁ ⊓ H₂) := Hyp111R.of_hyp111 rankOneListedFacts hH
  have hW := F1.isWeakBNPair hR
  have hb2 : borelOf H₂ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := borelOf_inf_eq hG
  have hb1 : borelOf H₁ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := by
    have := borelOf_inf_eq hG.symm
    rwa [inf_comm H₂ H₁] at this
  have hbig : bigB H₁ H₂ (H₁ ⊓ H₂) = H₁ ⊓ H₂ := by
    unfold bigB
    rw [hb1, hb2, sup_idem, sup_idem]
  rwa [hbig, sup_eq_left.mpr inf_le_left, sup_eq_left.mpr inf_le_right] at hW

end CFSG.Quasithin.RonanF65
