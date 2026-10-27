module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofClaim
public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofJ2
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof17Res14

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem dichotomy_of_not_l3 (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hL3 : ¬ IsL3TwoPow L) (hMeets : Claim1715Meets) (hPrime : Claim1715Prime) :
    (omegaA A = {Subgroup.zpowers c} ∧ Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
            Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))) ∨
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
        Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) ∧
        WStarS4 A ∧ TransOmegaThree A c) := by
  rcases h1514 Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
    ⟨hY, -, hΩ, hprod, hM12⟩ | ⟨hA7, hW, hT, -⟩ | ⟨-, -, -, -, hno, -⟩
  ·
    have hYL : Y₀ ⊓ L = L := inf_eq_right.mpr h.le_y0
    rw [hYL] at hY
    refine Or.inl ⟨hΩ, hY, hprod, ?_⟩
    rcases (h.hypR.2.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with hJ | hL3' | hA7 | hM22 | hM
    · exact Or.inr (Or.inr (Or.inr hJ))
    · obtain ⟨p, e, hp, he, hiso⟩ := hL3'
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hL3 ⟨e, he, hiso⟩
      have hp3 : p ≠ 3 := by
        rintro rfl
        rcases hiso with ⟨hmod, -⟩ | ⟨hmod, -⟩ <;>
        · rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at hmod
          omega
      have hp3' : 3 < p := by
        have := hp.out.two_le
        omega
      have he1 : e = 1 := hPrime G A c L Y₀ h p e hp3' he hiso
      subst he1
      exact Or.inl ⟨p, hp, hp3', hiso⟩
    · exact Or.inr (Or.inl hA7)
    · exact Or.inr (Or.inr (Or.inl hM22))
    · exact absurd hM (not_nonempty_iff.mpr hM12)
  ·
    have hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) := by
      rcases h.a10_or_omega with h10 | hΩ
      · exact h10
      · exfalso
        have := hT.1
        rw [hΩ, Set.ncard_singleton] at this
        omega
    exact Or.inr ⟨hA7, hA10, hW, hT⟩
  ·
    exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

section Certified

theorem le_sup_cQuot_of_sec17Y1 (hL3 : Claim1720InnerL3) (hJ : KS1717J2Inner)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hPrime : Claim1715Prime) (h135 : Item135)
    (h142 : Concl142S14) (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h9 : CardInfNineS17) {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hnL3 : ¬ IsL3TwoPow L) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  have hs := h.toSec17Std
  have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  have hSM := hs.qStar_le S hSG
  have h142' := h142 G A c L hs.toSec14Std
  rcases dichotomy_of_not_l3 hs (h1514 G A c L Y₀ hs) hnL3 hMeets hPrime with
    ⟨hΩ, hY, -, htypes⟩ | ⟨⟨φL⟩, ⟨φ⟩, -, hT⟩
  · have h9' := h9 G A c L Y₀ hs
    have hLsurj := Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY
    have hAnorm := Proof17Res6.le_normalizer_of_inf hs h9'
    have hB9 := Proof17Res6.card_kimg_inf hs h9'
    rcases htypes with hL3' | hA7 | hM22 | hJ2
    · exact hL3 G A c L Y₀ Y₁ S p P h hΩ hL3'
    · obtain ⟨φL⟩ := hA7
      obtain ⟨φ, g, hP⟩ := Proof17Res6.exists_a7Pic h135 hs hY φL h9'
      exact Proof17Res6.le_sup_cQuot_of_a7 h hP h142' hSM
    · obtain ⟨φL⟩ := hM22
      have : Nontrivial ↥CFSG.Blueprint.NativeSporadic.M22 := by
        rw [← Finite.one_lt_card_iff_nontrivial, CFSG.Sporadic.Mathieu.card_M22]
        norm_num
      have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
        Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L hs.toSec13Data hs.hypS_or_hypT)
          ⟨φL⟩ Proof1515.multFree_M22
      obtain ⟨e⟩ := Proof17Res6.nonempty_quot_equiv_of_theta hs.le_y0 hY hθ φL
      obtain ⟨⟨-, hM22z⟩, -⟩ := Sec13.sporadicModels131
      exact Proof17Res6.le_sup_cQuot_of_inner h h142' hLsurj hAnorm hSM
        (Proof17Res6.center_eq_bot_of_equiv' e hM22z)
        (Proof17Res6.actQ_le_range_of h hSM fun Q hQ3 hQN =>
          KFacts.KP4.m22_aut_threePrime_le_range ⟨e⟩ hB9 hQ3 hQN)
    · obtain ⟨⟨f⟩, -⟩ := hs.j2_local hJ2
      obtain ⟨e₀⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hs.le_y0 hY
      set e := e₀.trans f with he
      obtain ⟨-, -, -, hJ2z⟩ := Sec13.sporadicModels131
      exact Proof17Res6.le_sup_cQuot_of_inner h h142' hLsurj hAnorm hSM
        (Proof17Res6.center_eq_bot_of_equiv' e hJ2z)
        (Proof17Res6.actQ_le_range_of h hSM fun Q hQ3 hQN =>
          hJ _ ⟨e⟩ _ hB9 Q hQ3 hQN)
  · obtain ⟨g, hP⟩ := Proof17Res4.exists_a10Pic hs φ φL hT.1
    exact Proof17Res4.le_sup_cQuot_of_a10 h hP h142' hSM

end Certified

omit [Finite G] in
theorem le_sup_cQuot_of_map_conj {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y₀ : Set G))
    (hS : S.map (MulAut.conj g).toMonoidHom ≤
      (S.map (MulAut.conj g).toMonoidHom ⊓ Y₀) ⊔ (S.map (MulAut.conj g).toMonoidHom ⊓ cQuot Y₀)) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  set f := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hgi : g⁻¹ ∈ Subgroup.normalizer (Y₀ : Set G) := inv_mem hg
  have hY : Y₀.map f = Y₀ := Late.map_conj_eq_of_mem_normalizer hgi
  have hC : (cQuot Y₀).map f = cQuot Y₀ :=
    Late.map_conj_eq_of_mem_normalizer (HeadProof.normalizer_le_normalizer_cQuot Y₀ hgi)
  have hSS : (S.map (MulAut.conj g).toMonoidHom).map f = S := by
    rw [hf, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have h1 := Subgroup.map_mono (f := f) hS
  rw [hSS, Subgroup.map_sup] at h1
  refine h1.trans (sup_le_sup ?_ ?_)
  · refine (Subgroup.map_inf_le _ _ _).trans ?_
    rw [hSS, hY]
  · refine (Subgroup.map_inf_le _ _ _).trans ?_
    rw [hSS, hC]

theorem exists_sec17Y1 (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h146 : Item146 A (lB A)) (h1411 : Item1411_1 A (lB A)) {Y S : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hYM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G))
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ (p : ℕ) (P : Subgroup G),
      Sec17Y1 G A c L Y₀ (Y.map (MulAut.conj w).toMonoidHom)
        (S.map (MulAut.conj w).toMonoidHom) p P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
    mem_qStar_top_of_item168 h h166 hbot h168 hY.prop.1 hYM
      (fun _ hN hYN => le_antisymm (hY.2 hN hYN) hYN) hS
  obtain ⟨T, hT⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) L (piOf 2)
  have hTG : T ∈ scriptQPi A (lB A) ⊤ (piOf 2) := ⟨⟨hT.prop.1.1, le_top⟩, hT.prop.2⟩
  obtain ⟨S₀, hTS₀, hS₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hTG
  obtain ⟨w, hw, hS₀w⟩ := h1411 S hSG S₀ hS₀
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hw.1
  have hwM : w ∈ M := h.normalizer_le hwA
  set S' := S.map (MulAut.conj w).toMonoidHom with hS'
  set Y' := Y.map (MulAut.conj w).toMonoidHom with hY'
  have hS'G : S' ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := hS₀w ▸ hS₀
  have hS'Q : S' ∈ scriptQ A (lB A) := hS'G.prop.1.1
  have hS'2 : IsPGroup 2 S' := (isPiSubgroup_piOf_iff Nat.prime_two S').mp hS'G.prop.2
  have hS'L : S' ⊓ L ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hS'Q inf_le_left
        (Late.le_normalizer_inf hS'Q.1.2.2 h.toSec13Data.le_normalizer), inf_le_right⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS'2.to_le inf_le_left)⟩
  have hTS' : T ≤ S' ⊓ L := le_inf (hS₀w ▸ hTS₀) hT.prop.1.2
  have hS'LT : S' ⊓ L = T := le_antisymm (hT.2 hS'L hTS') hTS'
  have hY'1 : Y' ∈ scriptY1Star A (lB A) := map_conj_mem_scriptY1Star hwA hY
  have hY'M : ¬ Y' ≤ M := by
    intro hle
    apply hYM
    intro y hy
    have h1 : w * y * w⁻¹ ∈ M := hle ⟨y, hy, rfl⟩
    have e : y = w⁻¹ * (w * y * w⁻¹) * w := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.inv_mem hwM) h1) hwM
  have hS'Y : S' ∈ scriptQPiStar A (lB A) Y' (piOf 2) := map_conj_mem_scriptQPiStar hwA hS
  obtain ⟨-, hY's⟩ := mem_scriptY1_of_not_le_M h h166 hbot hY'1.prop.1 hY'M
  have hY'3 : ¬ 3 ∣ Nat.card Y' := not_three_dvd_of_oPrimeResidualOf_eq_bot hY'1.prop.2
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := hY'1.prop.1.1.1.2
  have hY'Q : Y' ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y').mpr hY'3, hAY'⟩
    rwa [← hY'1.prop.1.2] at this
  obtain ⟨r, hr, hr2, hr3, R, hRY', hRr, hAR, hRM⟩ := exists_pGroup_not_le_M h hY'Q hY'M
  have hRQ : R ∈ scriptQPi A (lB A) Y' (piOf r) :=
    ⟨⟨mem_scriptQ_of_le hY'Q hRY' hAR, hRY'⟩, (isPiSubgroup_piOf_iff hr R).mpr hRr⟩
  obtain ⟨P, hRP, hP⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) Y' (piOf r))) hRQ
  have hPQ : P ∈ scriptQ A (lB A) := hP.prop.1.1
  have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPQ.1.2.1
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.toSec13Data.orderOf_eq, pow_one])
  have hcP : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (hPQ.1.2.2 hcA)
  have hPc : ¬ ⁅P, Subgroup.zpowers c⁆ ≤ M := by
    intro hle
    refine hRM (hRP.trans (le_of_commutator_le Nat.prime_three hc3 hP3 hcP hle ?_))
    refine inf_le_right.trans ((Subgroup.centralizer_le ?_).trans (centralizer_c_le_M h))
    exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)
  have hr3' : 3 < r := by
    have := hr.two_le
    omega
  refine ⟨w, hwA, r, P, ?_⟩
  exact
    { toSec17Std := h
      mem_y1Star := hY'1
      not_le_M := hY'M
      mem_qStar_two := hS'Y
      inf_L_mem_qStar_two := hS'LT ▸ hT
      y1_isSolvable := hY's
      p_prime := hr
      three_lt_p := hr3'
      mem_qStar_p := hP
      commutator_not_le_M := hPc }

end Proof17Res14

section Certified

open Proof17Res14 in
theorem claim174Inner_of_types (hL3 : Claim1720InnerL3) (hJ : KS1717J2Inner)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hPrime : Claim1715Prime) (h135 : Item135)
    (h142 : Concl142S14) (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h9 : CardInfNineS17) (h146 : Item146S14) (h1411 : Item1411_1S17) : Claim174Inner := by
  intro G _ _ A c L Y₀ h hnL3 _ _ _ _ _ _ Y hY hYM S hS
  obtain ⟨w, hwA, p, P, h'⟩ := exists_sec17Y1 h (h166 G A c L Y₀ h) (hbot G A c L Y₀ h)
    (h168 G A c L Y₀ h) (h146 G A c L h.toSec14Std) (h1411 G A c L Y₀ h) hY hYM hS
  exact le_sup_cQuot_of_map_conj (h.normalizer_le hwA)
    (le_sup_cQuot_of_sec17Y1 hL3 hJ h1514 hMeets hPrime h135 h142 h166 hbot h168 h9 h' hnL3)

end Certified

end CFSG.RankThree.PartTwo.Sec17
