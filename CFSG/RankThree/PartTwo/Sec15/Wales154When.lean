module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Read
public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
import CFSG.RankThree.PartTwo.Sec14.Ronan148KPoint
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec15.F153Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA10
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofProper

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem card_imgX {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (imgX X Y) = (CFSG.Open.pCoreOf 2 Y).relIndex X := by
  have hcore : CFSG.pCore 2 ↥Y = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y := by
    ext x
    rw [Sec18.mem_pCore_iff_mem_pCoreOf, Subgroup.mem_subgroupOf]
  rw [imgX, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hcore,
    Subgroup.relIndex_subgroupOf hXY]

theorem card_quot_dvd_card_imgX {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∣ Nat.card (imgX X Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := CFSG.Open.pCoreOf 2 Y with hD
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hXDP : D ⊓ X ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (Late.le_normalizer_inf (hXY.trans hYD) Subgroup.le_normalizer) (hD2.to_le inf_le_left)
  have h1 := Subgroup.relIndex_mul_card D X
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have hcP : Nat.card (CFSG.pCore 2 ↥X) = Nat.card P := by
    rw [hP, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  rw [hcP] at h2
  obtain ⟨k, hk⟩ : Nat.card (D ⊓ X : Subgroup G) ∣ Nat.card P := Subgroup.card_dvd_of_le hXDP
  rw [card_imgX hXY]
  have hpos : 0 < Nat.card (D ⊓ X : Subgroup G) := Nat.card_pos
  refine ⟨k, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
  calc D.relIndex X * Nat.card (D ⊓ X : Subgroup G) = Nat.card X := h1
    _ = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card P := h2
    _ = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * k * Nat.card (D ⊓ X : Subgroup G) := by
      rw [hk]; ring

theorem commutator_le_of_tripleA6 (hK : KS1543A6) {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {X Y R : Subgroup G} (hY : Y ∈ scriptY4 A LB)
    (h6 : Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)))
    (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X) (hX1 : X ≠ ⊥)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) : ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
  commutator_le_of_forall hXY hXR hRY hR2 fun P hP2 hPK =>
    hK _ hY.2.2.2 h6 (imgX X Y) (imgX_ne_bot hXY hXp hX1) (isPerfect_imgX hXY hXp) P hP2 hPK

theorem commutator_le_of_M22 (hK : KS154M22A7) {X Y R : Subgroup G}
    (hM : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X) (h35 : 35 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) : ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
  commutator_le_of_forall hXY hXR hRY hR2 fun P hP2 hPK =>
    hK _ hM (imgX X Y) (isPerfect_imgX hXY hXp) (h35.trans (card_quot_dvd_card_imgX hXY)) P hP2
      hPK

theorem commutator_le_of_U35 (hK : KS154U35A7) [Fact (Nat.Prime 5)] {X Y R : Subgroup G}
    (hU : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1))
    (hXY : X ≤ Y) (h7 : 7 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) : ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
  commutator_le_of_forall hXY hXR hRY hR2 fun P hP2 hPK =>
    hK inferInstance _ hU (imgX X Y) (h7.trans (card_quot_dvd_card_imgX hXY)) P hP2 hPK

section Reading


open F153 in
theorem type154_of_item148R
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY4 : Y ∈ scriptY4 A (lB A)) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
        IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON := by
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY4.2.2.2
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hnt : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hYΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hY4
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have key : ∀ {S : Type} [Group S], Proof1515.MultFree S →
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* S) → Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* S) :=
    fun hm hS => Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hY4 hS hm
  have hL3eps : ∀ {p f : ℕ} [Fact p.Prime], 1 ≤ f → p ≠ 3 →
      IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f := by
    intro p f hp hf hp3 hε
    have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun Z _ hZc hcop ⟨φ⟩ =>
        Proof1511Steps.eq_bot_of_isLThreeEpsAt _ Z hperf hZc hcop hf
          (IsLThreeEpsAt.of_mulEquiv φ.symm hε)
    exact ⟨p, f, hp, hf, hp3,
      IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq) hε⟩
  have hL3pi : ∀ {p e : ℕ} [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p e →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f := by
    intro p e hp he hiso
    obtain ⟨φ⟩ := key (Proof1515.multFree_of_isLThreePi ⟨p, e, hp, he, hiso⟩)
      (⟨MulEquiv.refl _⟩ : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y))
    exact ⟨p, e, hp, he, Sec14.Ronan148K.ne_three_of_isoLThreePi he hiso,
      Sec14.isLThreeEpsAt_of_isoLThreePi148 (Proof1515.isoLThreePi_congr φ.symm hiso)⟩
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ | ⟨⟨φ10⟩, -, -⟩ |
      ⟨c', L', n, m, hc', hL', hn, hm, hiso, -⟩
  ·
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e₀, hp, hf, he₀, hiso, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    ·
      rcases (hR.chosen136.2 c' hc' L' hL').1 with ⟨⟨φJ⟩⟩ | ⟨p, e₀, hp, he, hiso⟩ | ⟨⟨φ7⟩⟩ |
        ⟨⟨φM⟩⟩ | ⟨⟨φM⟩⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl (key Proof1515.multFree_J2 ⟨φ.trans φJ⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hL3pi he (Proof1515.isoLThreePi_congr φ.symm hiso))))))
      · exact Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_alternatingGroup_seven ⟨φ.trans φ7⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_M22 ⟨φ.trans φM⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_M12 ⟨φ.trans φM⟩)))))))
    ·
      exact Or.inr (Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩)))
    ·
      have hf' : 1 ≤ f * e₀ := Nat.mul_pos hf he₀
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hL3eps hf (Sec14.Ronan148K.ne_three_of_isoLThreePi hf' hiso) hε)))))
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 1080 := by
        rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6
      exact Or.inr (Or.inl
        (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6))
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 60 := by
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6
      exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans φ⟩
  ·
    rcases h3 with hON | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
    · have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun Z _ hZc hcop ⟨φ⟩ =>
          ks1515ONMult _ Z hperf hZc hcop (Proof1515.isTripleCover_congr φ.symm hON)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) hON))))))))
    · exact Or.inr (Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hL3eps (p := 7) (f := 1) le_rfl (by norm_num) (Or.inl ⟨φ⟩))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key Proof1515.multFree_alternatingGroup_ten ⟨φ10⟩))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hL3pi (p := 2) (by omega) hiso)))))

@[expose] noncomputable def Item154ProperWhen (T : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ Y →
      Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y → T (↥Y ⧸ CFSG.pCore 2 ↥Y) →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

theorem item154ProperR_of_when
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hA5 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 5)))
    (hA6 : Item154ProperWhen fun Q _ => Sec4.IsTripleCover Q (alternatingGroup (Fin 6)))
    (hA7 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 7)))
    (hJ2 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hL3 : Item154ProperWhen fun Q _ =>
      ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt Q p f)
    (hM22 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hM12 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hA10 : Item154ProperWhen fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 10)))
    (hON : Item154ProperWhen fun Q _ => Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON) :
    Item154ProperR := by
  intro G _ _ A c L hR Y hY X hX hXY hYX R hRm
  rcases type154_of_item148R h148 h134 h48 hR hY.1 with h | h | h | h | h | h | h | h | h
  · exact hA5 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hA6 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hA7 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hJ2 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hL3 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hM22 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hM12 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hA10 G A c L hR Y hY X hX hXY hYX h R hRm
  · exact hON G A c L hR Y hY X hX hXY hYX h R hRm

end Reading

theorem item154ProperWhen_tripleA6 (hK : KS1543A6) :
    Item154ProperWhen fun Q _ => Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX h6 R hRm
  refine Or.inl (commutator_le_of_tripleA6 hK hY.1 h6 hXY (isPerfect_of_mem_scriptY4 hX)
    (ne_bot_of_mem_scriptY4 hX) hRm.1 ((isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1)
    ((le_sup_right : X ≤ A ⊔ X).trans hRm.2.2))

end CFSG.RankThree.PartTwo.Sec15.Wales154
