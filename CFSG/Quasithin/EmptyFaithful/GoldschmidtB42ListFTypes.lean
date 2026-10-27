module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFAux
public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.Quasithin.B42ListF

open CFSG.Assembly.LowTwoRank

variable {X Y : Type} [Group X] [Group Y]

theorem isPSL3_of_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSL 3 K)) : IsPSL 3 2 n X :=
  ⟨⟨Nat.prime_two, hn, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
    fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩, K, inferInstance, inferInstance, hK,
    ⟨e⟩⟩

theorem isPSL3_of_cover (hY : CFSG.IsQuasisimple Y)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (e : Y ≃* StatedSL 3 K) :
    IsPSL 3 2 n (X ⧸ Subgroup.center X) := by
  obtain ⟨eY⟩ := lred3_cq_stated hY (StatedSL 3 K)
    (lred3_simple_statedProj_sl (by norm_num) (Or.inl le_rfl)) e.symm.toMonoidHom
    e.symm.surjective
  exact isPSL3_of_equiv hn hK (cq.trans eY)

theorem isPSU33_of_cover
    (hY : CFSG.IsQuasisimple Y) (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : Y ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) :
    IsPSU 3 3 1 (X ⧸ Subgroup.center X) := by
  obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hK
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  have hP : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 3 (2 * 1)) 3 1
      hK9 3 le_rfl hne
  obtain ⟨eY⟩ := lred3_cq_simple hY hP (e.symm.toMonoidHom.comp eP.toMonoidHom)
    (e.symm.surjective.comp eP.surjective)
  exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance,
    inferInstance, hK9, ⟨cq.trans eY⟩⟩

theorem isAlt_of_cover (hY : CFSG.IsQuasisimple Y)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {m : ℕ} (hm : 5 ≤ m)
    (e : Y ≃* ↥(alternatingGroup (Fin m))) : IsAlt m (X ⧸ Subgroup.center X) := by
  obtain ⟨eY⟩ := lred3_cq_simple hY (CFSG.Quasithin.Vol2.Ch10.SecA.isSimpleGroup_alt hm)
    e.symm.toMonoidHom e.symm.surjective
  exact ⟨cq.trans eY⟩

theorem isPSL_two_of_cover (hcover : AsA36NoOddCover) [Finite X] (hX : CFSG.IsQuasisimple X)
    (hSQ : SQTKGroup X) (hO2 : CFSG.pCore 2 X = ⊥) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Y ≃* StatedSL n (ZMod 2)) : IsPSL n 2 1 X := by
  have hsurj : Function.Surjective (e.toMonoidHom.comp ρ) := e.surjective.comp hρ
  have hodd : ∀ x ∈ (e.toMonoidHom.comp ρ).ker, Odd (orderOf x) := by
    intro x hx
    have h1 : ρ x = 1 := by
      have : e (ρ x) = 1 := hx
      exact e.injective (by simpa using this)
    exact odd_orderOf_of_mem_center hO2 (hker h1)
  have hL : IsL345Type (StatedSL n (ZMod 2)) := by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
        ⟨MulEquiv.refl _⟩⟩)
    · exact Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
        ⟨MulEquiv.refl _⟩⟩)
  have hinj := hcover X (StatedSL n (ZMod 2)) hX hSQ (e.toMonoidHom.comp ρ) hsurj hodd hL
  exact R3c2.isPSL_two_of_statedSL (n := n) (by omega)
    (MulEquiv.ofBijective (e.toMonoidHom.comp ρ) ⟨hinj, hsurj⟩)

theorem list_of_b56
    (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley)
    [Finite X] [Finite Y] (hX : CFSG.IsQuasisimple X) (hSQ : SQTKGroup X)
    (hO2 : CFSG.pCore 2 X = ⊥) (hY : CFSG.IsQuasisimple Y) (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center X)
    (hl : B56QuasisimpleList Y) :
    (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n X) ∨
      (((∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n X) ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n X) ∨
          ∃ n : ℕ, 2 ≤ n ∧ IsG2 2 n X) ∨
        ∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (X ⧸ Subgroup.center X)) ∨
      (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) ∨
      (IsAlt 7 (X ⧸ Subgroup.center X) ∨ IsPSL 3 2 1 (X ⧸ Subgroup.center X) ∨
        IsAlt 6 (X ⧸ Subgroup.center X) ∨ IsPSU 3 3 1 (X ⧸ Subgroup.center X)) := by
  obtain ⟨cq⟩ := lred3_cq_of_quasisimple hX hY ρ hρ
  rcases hl with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | hA6 | hA7 | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | hS4 | hS5
  ·
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · exact Or.inl ⟨n, hn, isPSL2_of_cover hX hO2 hY cq hn hK e⟩
    · exfalso
      have hn' : n = 1 := by omega
      subst hn'
      have hK2 : Nat.card K = 2 := by simpa using hK
      refine SBc3.false_of_card_dvd_six hY ?_
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hK2]
      norm_num
  ·
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hK
    have h3 := isPSL3_of_cover hY cq hn1 hK e
    by_cases hn : 2 ≤ n
    · right; left; right; exact ⟨n, hn, h3⟩
    · have hn' : n = 1 := by omega
      subst hn'
      right; right; right; right; left; exact h3
  ·
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · right; left; left; right; left; exact ⟨n, hn, isPSp4_of_cover hX hO2 hY cq hn hK e⟩
    · exfalso
      have hn' : n = 1 := by omega
      subst hn'
      exact R3c2.not_isQuasisimple_statedSp_two (by simpa using hK) e hY
  ·
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hK
    by_cases hn : 2 ≤ n
    · right; left; left; right; right; exact ⟨n, hn, isG2_of_cover hG2 hX hO2 cq hn hK e⟩
    · exfalso
      have hn' : n = 1 := by omega
      subst hn'
      exact R3c2.not_isQuasisimple_quasithinG2_two (by simpa using hK) e hY
  ·
    right; right; right; right; right; left
    obtain ⟨e⟩ := hA6
    exact isAlt_of_cover hY cq (by norm_num) e
  ·
    right; right; right; left
    obtain ⟨e⟩ := hA7
    exact isAlt_of_cover hY cq (by norm_num) e
  ·
    right; right; right; right; right; left
    obtain ⟨f⟩ := hhat.2.2
    exact ⟨cq.trans f⟩
  ·
    right; right; right; right; right; right
    exact isPSU33_of_cover hY cq hK e
  ·
    right; right; left; left
    obtain ⟨e⟩ := hS4
    exact isPSL_two_of_cover hcover hX hSQ hO2 ρ hρ hker (Or.inl rfl) e
  ·
    right; right; left; right
    obtain ⟨e⟩ := hS5
    exact isPSL_two_of_cover hcover hX hSQ hO2 ρ hρ hker (Or.inr rfl) e

end CFSG.Quasithin.B42ListF
