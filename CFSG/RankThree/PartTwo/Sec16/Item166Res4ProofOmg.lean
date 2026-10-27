module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofCtr
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOrders
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTen
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof166Res4

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_comm_of_isQuasisimple {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

omit [Finite G] in
theorem map_conj_one_zpowers (c : G) :
    (Subgroup.zpowers c).map (MulAut.conj (1 : G)).toMonoidHom = Subgroup.zpowers c := by
  ext x
  simp

section Points

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem forall_conj_of_item1514 (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) :
    ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
      F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
  have hΩ : omegaA A = {Subgroup.zpowers c} ∨ TransOmegaThree A c := by
    rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨-, -, hΩ, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, -, hΩ, -⟩
    · exact Or.inl hΩ
    · exact Or.inr hT
    · exact Or.inl hΩ
  rcases hΩ with hΩ | hT
  · intro F hF
    rw [hΩ, Set.mem_singleton_iff] at hF
    exact ⟨1, Subgroup.one_mem _, by rw [hF, map_conj_one_zpowers]⟩
  · exact hT.2

theorem nonempty_thetaQuot_equiv_of_point (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  Proof1515.nonempty_thetaQuot_equiv_of_transOmega h.toSec14Std
    (three_dvd_card_of_mem_lA h.toSec15R h.zpowers_mem_omegaA h.mem_lA)
    (forall_conj_of_item1514 h h1514 hMeets) hc' hL'

theorem points_of_other (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) (hL : ¬ IsL3TwoPow L)
    (hJ2 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ¬ IsL3TwoPow L' ∧
      IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨e⟩ := nonempty_thetaQuot_equiv_of_point h h1514 hMeets hc' hL'
  refine ⟨fun ⟨n, hn, hiso⟩ => hL ⟨n, hn, Proof1515.isoLThreePi_congr e hiso⟩, ⟨fun φ => ?_⟩⟩
  exact hJ2.false (e.symm.trans φ)

theorem points_of_hj (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ¬ IsL3TwoPow L' := by
  obtain ⟨e⟩ := nonempty_thetaQuot_equiv_of_point h h1514 hMeets hc' hL'
  obtain ⟨φ⟩ := hJ2
  rintro ⟨n, -, hiso⟩
  exact KFacts.KS14.ks17J2NotList.1 2 n (Proof1515.isoLThreePi_congr (e.trans φ) hiso)

end Points

theorem isL3TwoPow_of_isLThreeEpsAt_two {A : Subgroup G} (hch : Chosen136 A) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') {k : ℕ}
    (hk : 1 ≤ k) (hε : IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 k) :
    IsL3TwoPow L' := by
  rcases (hch.2 c' hc' L' hL').1 with hφ | ⟨p, e, hp, he, hiso⟩ | hφ | hφ | hφ
  · obtain ⟨φ⟩ := hφ
    exact (KFacts.KS14.not_isLThreeEpsAt_j2 2 k (Sec15.IsLThreeEpsAt.of_mulEquiv φ hε)).elim
  · by_cases hp2 : p = 2
    · subst hp2
      exact ⟨e, he, hiso⟩
    · exact (not_isLThreeEpsAt_two_of_isoLThreePi hp2 he hiso hk hε).elim
  · obtain ⟨φ⟩ := hφ
    refine (Item148Rank.not_isLThreeEpsAt_of_card_2520 ?_ 2 k
      (Sec15.IsLThreeEpsAt.of_mulEquiv φ hε)).elim
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  · obtain ⟨φ⟩ := hφ
    exact (KFacts.KS14.not_isLThreeEpsAt_M22 2 k (Sec15.IsLThreeEpsAt.of_mulEquiv φ hε)).elim
  · obtain ⟨φ⟩ := hφ
    exact (KFacts.KS14.not_isLThreeEpsAt_M12 2 k (Sec15.IsLThreeEpsAt.of_mulEquiv φ hε)).elim

theorem pPrimeCore_eq_pCore_of_isSimpleGroup {A J : Subgroup G} (hJ : J ∈ scriptY4 A (lB A))
    (hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J)) : CFSG.pPrimeCore 3 ↥J = CFSG.pCore 2 ↥J :=
  pPrimeCore_three_eq_pCore_two
    (pPrimeCore_three_eq_bot_of_isSimpleGroup hs (Proof1515.three_dvd_card_of_mem_scriptY4 hJ))

section Read

variable {A : Subgroup G}

theorem false_of_isoLThreePi_two (h148 : Item148 A (lB A)) (hAab : IsMulCommutative A)
    (hch : Chosen136 A)
    (hpts : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      ¬ IsL3TwoPow L')
    {J : Subgroup G} (hJ : J ∈ scriptY4 A (lB A)) (hJΔ : J = deltaZero A (lB A) J)
    {m : ℕ} (hm : 1 ≤ m) (hiso : Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 m) : False := by
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := hJ.2.2.2
  have hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) :=
    Steps166.isSimpleGroup_of_isLThreePi hq ⟨2, m, inferInstance, hm, hiso⟩
  have hO := pPrimeCore_eq_pCore_of_isSimpleGroup hJ hs
  let e : ↥J ⧸ CFSG.pPrimeCore 3 ↥J ≃* ↥J ⧸ CFSG.pCore 2 ↥J :=
    QuotientGroup.quotientMulEquivOfEq hO
  have hK : Sec4.IsoLThreePi (↥J ⧸ CFSG.pPrimeCore 3 ↥J) 2 m :=
    Proof1515.isoLThreePi_congr e.symm hiso
  have hKq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pPrimeCore 3 ↥J) :=
    Proof1515.isQuasisimple_quot_pPrimeCore hJ
  have hKs : IsSimpleGroup (↥J ⧸ CFSG.pPrimeCore 3 ↥J) := by
    have := hs
    exact e.isSimpleGroup
  have hKnab := exists_ne_comm_of_isQuasisimple hKq
  rcases Proof1515.cases148_of_mem_scriptY4 h148 hAab hJ hJΔ with h2 | h3 | h4 | h5
  ·
    obtain ⟨c', hc', -, L', hL', hcase⟩ := h2
    rcases hcase with hφ | ⟨-, hφ⟩ | ⟨p, f, e', hp, hf, he', hisoL, hε⟩ | ⟨-, h6 | hφ⟩
    ·
      obtain ⟨φ⟩ := hφ
      exact hpts c' L' hc' hL' ⟨m, hm, Proof1515.isoLThreePi_congr φ hK⟩
    ·
      obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_a7_of_isoLThreePi_two hm hK).false φ
    ·
      obtain ⟨rfl, rfl⟩ := kf148FieldChar_holds _ m hm hKq.1 hK p f hf hε
      exact hpts c' L' hc' hL' ⟨f * e', Nat.mul_pos (by omega) (by omega), hisoL⟩
    ·
      exact not_isTripleCover_of_isSimpleGroup hKs hKnab h6
    ·
      obtain ⟨φ⟩ := hφ
      refine not_isoLThreePi_of_card_small (Or.inl ?_) 2 m hK
      rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
  ·
    obtain ⟨c', L', -, -, -, hON | hφ | ⟨h7, hφ⟩⟩ := h3
    · exact not_isTripleCover_of_isSimpleGroup hKs hKnab hON
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_a7_of_isoLThreePi_two hm hK).false φ
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_l37_of_isoLThreePi_two hm hK h7).false φ
  ·
    obtain ⟨hφ, -, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact (isEmpty_mulEquiv_a10_of_isoLThreePi_two hm hK).false φ
  ·
    obtain ⟨c', L', n, m', hc', hL', hn, hm', -, hε⟩ := h5
    exact hpts c' L' hc' hL'
      (isL3TwoPow_of_isLThreeEpsAt_two hch hc' hL' (Nat.mul_pos (by omega) (by omega)) hε)

theorem false_of_alt5 (h148 : Item148 A (lB A))
    (hAab : IsMulCommutative A) (hch : Chosen136 A)
    (hpts : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    {J : Subgroup G} (hJ : J ∈ scriptY4 A (lB A)) (hJΔ : J = deltaZero A (lB A) J)
    (φ5 : ↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) : False := by
  have hs : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) φ5
  have hO := pPrimeCore_eq_pCore_of_isSimpleGroup hJ hs
  have h60 : Nat.card (↥J ⧸ CFSG.pPrimeCore 3 ↥J) = 60 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans φ5).toEquiv,
      card_alternatingGroup_five]
  rcases Proof1515.cases148_of_mem_scriptY4 h148 hAab hJ hJΔ with h2 | h3 | h4 | h5
  ·
    obtain ⟨c', hc', -, L', hL', hcase⟩ := h2
    rcases hcase with hφ | ⟨-, hφ⟩ | ⟨p, f, e', hp, -, -, -, hε⟩ | ⟨hφJ, -⟩
    ·
      obtain ⟨φ⟩ := hφ
      refine not_mem_list136_of_card_small (Or.inl ?_) (hch.2 c' hc' L' hL').1
      rw [← Nat.card_congr φ.toEquiv, h60]
    ·
      obtain ⟨φ⟩ := hφ
      have h := Nat.card_congr φ.toEquiv
      rw [h60, card_alternatingGroup_seven] at h
      omega
    ·
      exact not_isLThreeEpsAt_of_card_small (Or.inl h60) p f hε
    ·
      obtain ⟨φJ⟩ := hφJ
      exact (hpts c' L' hc' hL').false φJ
  ·
    obtain ⟨c', L', hc', hL', hφJ, -⟩ := h3
    obtain ⟨φJ⟩ := hφJ
    exact (hpts c' L' hc' hL').false φJ
  ·
    obtain ⟨hφ, -, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    have h := Nat.card_congr φ.toEquiv
    rw [h60, card_alternatingGroup_ten] at h
    omega
  ·
    obtain ⟨-, -, n, -, -, -, -, -, hiso, -⟩ := h5
    exact not_isoLThreePi_of_card_small (Or.inl h60) 2 (3 * n) hiso

end Read

section Omg

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem omg155_of_other (h : Sec17Std G A c L Y₀)
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) (hL : ¬ IsL3TwoPow L)
    (hJ2 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {J : Subgroup G} (hJ : J ∈ scriptY0 A (lB A)) : omg155 A J := by
  have hJΔ : J = deltaZero A (lB A) J := rank3II_15_1_lB h.toSec14Std.isE27 hbot hJ.1
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  have hpts := fun c' L' hc' hL' => points_of_other h h1514 hMeets hL hJ2 (c' := c') (L' := L')
    hc' hL'
  refine Or.inl ⟨?_, ⟨fun φ => ?_⟩⟩
  · rintro ⟨m, hm, hiso⟩
    exact false_of_isoLThreePi_two h148 hAab h.chosen136
      (fun c' L' hc' hL' => (hpts c' L' hc' hL').1) hJ.1 hJΔ hm hiso
  · exact false_of_alt5 h148 hAab h.chosen136 (fun c' L' hc' hL' => (hpts c' L' hc' hL').2)
      hJ.1 hJΔ φ

theorem omg155_of_hj (h : Sec17Std G A c L Y₀) (h148 : Item148 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {J : Subgroup G} (hJ : J ∈ scriptY0 A (lB A))
    (h5 : IsEmpty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5))) : omg155 A J := by
  have hJΔ : J = deltaZero A (lB A) J := rank3II_15_1_lB h.toSec14Std.isE27 hbot hJ.1
  refine Or.inl ⟨?_, h5⟩
  rintro ⟨m, hm, hiso⟩
  exact false_of_isoLThreePi_two h148 h.isElemAbelian.1 h.chosen136
    (fun c' L' hc' hL' => points_of_hj h h1514 hMeets hJ2 hc' hL') hJ.1 hJΔ hm hiso

theorem omg166_of (h : Sec17Std G A c L Y₀)
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) (hL : ¬ IsL3TwoPow L)
    (hJ2 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Omg166 A Y₀ :=
  fun _ _ _ _ _ _ _ _ _ hJ0 _ => omg155_of_other h h148 hbot h1514 hMeets hL hJ2 hJ0

theorem omg166NotA5_of (h : Sec17Std G A c L Y₀) (h148 : Item148 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Omg166NotA5 A Y₀ :=
  fun _ _ _ _ _ _ _ _ _ hJ0 _ h5 => omg155_of_hj h h148 hbot h1514 hMeets hJ2 hJ0 h5

end Omg

end Proof166Res4

section Provers

open Proof166Res4

theorem step166OmgOther_of (h148 : Item148R)
    (hbot : Item145BotS17) (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Step166OmgOther :=
  fun G _ _ A c L Y₀ h hL hJ2 =>
    omg166_of h (h148 G A c L h.toSec15R) (hbot G A c L Y₀ h) (h1514 G A c L Y₀ h)
      (hMeets G A c L Y₀ h) hL hJ2

theorem step166OmgNotA5HJ_of (h148 : Item148R) (hbot : Item145BotS17) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : Step166OmgNotA5HJ :=
  fun G _ _ A c L Y₀ h hJ2 =>
    omg166NotA5_of h (h148 G A c L h.toSec15R) (hbot G A c L Y₀ h) (h1514 G A c L Y₀ h)
      (hMeets G A c L Y₀ h) hJ2

theorem step166OmgSzHJ_of (h148 : Item148R) (hbot : Item145BotS17) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hA5 : Step166OmegaA5HJ) : Step166OmgSzHJ :=
  fun G _ _ A c L Y₀ h hJ2 =>
    omg166Sz_of_a5 (step166OmgNotA5HJ_of h148 hbot h1514 hMeets G A c L Y₀ h hJ2)
      (hA5 G A c L Y₀ h hJ2)

end Provers

end CFSG.RankThree.PartTwo.Sec16
