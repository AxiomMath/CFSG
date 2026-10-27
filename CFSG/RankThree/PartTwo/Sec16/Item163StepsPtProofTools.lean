module

public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_lBar_of_sec15R
    {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hD := h.toSec13Data
  have hq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hZ := center_eq_bot_of_types hD.mem_thetaComponentsAt
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have : IsSimpleGroup ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem le_of_forall_cover
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c}) (h142 : Concl142 A (lB A))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A)) (h1411 : Item1411_1 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hcov : ∀ w ∈ Subgroup.normalizer (A : Set G), L.map (MulAut.conj w).toMonoidHom = L →
      L = (L ⊓ Y.map (MulAut.conj w).toMonoidHom) ⊔ CFSG.Open.pCoreOf 2 L) : L ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := CFSG.Open.pCoreOf 2 L with hO
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hOL : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLH : L ≤ H := hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := normalizer_zpowers_le_normalizer_L h h3L
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    hHL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hD.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) H (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨T₀, -, hT₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) hbot
  have hT₀2 : IsPGroup 2 T₀ := isPGroup_of_mem_scriptQPi Nat.prime_two hT₀.prop
  have hT₀H : T₀ ≤ H := hT₀.prop.1.2
  have hs2 : IsPGroup 2 ↥(T₀ ⊔ O) := IsPGroup.to_sup_of_normal_right' hT₀2 hO2 (hT₀H.trans hHO)
  have hs3 : ¬ 3 ∣ Nat.card ↥(T₀ ⊔ O) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hs2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hsH : T₀ ⊔ O ≤ H := sup_le hT₀H (hOL.trans hLH)
  have hsQ : T₀ ⊔ O ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA ⟨hsH,
      (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hs3,
      le_normalizer_sup hT₀.prop.1.1.1.2.2 hAO⟩, hsH⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hs2⟩
  have hOT : O ≤ T₀ := le_sup_right.trans (hT₀.2 hsQ le_sup_left)
  obtain ⟨S', hT₀S', hS'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) (a := T₀) ⟨⟨hT₀.prop.1.1, le_top⟩, hT₀.prop.2⟩
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h153 hobs hY
  obtain ⟨w, hw, rfl⟩ := h1411 S₀ hS₀ S' hS'
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  set Y' := Y.map (MulAut.conj w).toMonoidHom with hY'def
  have hT₀Y' : T₀ ≤ Subgroup.normalizer (Y' : Set G) := by
    refine hT₀S'.trans ?_
    rw [hY'def, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hS₀Y
  have hwc : w ∈ H := by
    have hcw := (map_conj_mem_omegaA_iff hwA).mpr h.zpowers_mem_omegaA
    rw [hΩ, Set.mem_singleton_iff] at hcw
    exact mem_normalizer_of_map_conj_eq hcw
  have hwL : L.map (MulAut.conj w).toMonoidHom = L := Late.map_conj_eq_of_mem_normalizer (hHL hwc)
  have hcovw : L = (L ⊓ Y') ⊔ O := hcov w hwA hwL
  have hLN : L ≤ Subgroup.normalizer (Y' : Set G) :=
    calc L = (L ⊓ Y') ⊔ O := hcovw
      _ ≤ Subgroup.normalizer (Y' : Set G) :=
        sup_le (inf_le_right.trans Subgroup.le_normalizer) (hOT.trans hT₀Y')
  have h3 : 3 ∣ Nat.card ↥(L ⊓ Y') := by
    have hdvd : Nat.card L ∣ Nat.card ↥(L ⊓ Y') * Nat.card O := by
      conv_lhs => rw [hcovw]
      exact card_sup_dvd_card_mul (inf_le_left.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    have hcop : Nat.Coprime 3 (Nat.card O) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (h3L.trans hdvd)
  have hLY' : L ≤ Y' := le_of_le_normalizer_of_theta
    (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt)
    (isSimpleGroup_lBar_of_sec15R h) hLN h3
  have hLw : L.map (MulAut.conj w⁻¹).toMonoidHom = L :=
    Late.map_conj_eq_of_mem_normalizer (inv_mem (hHL hwc))
  have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hLY'
  rwa [hLw, hY'def, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one] at this

theorem le_of_cover_of_omegaA_eq_singleton
    {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c})
    (h142 : Concl142 A (lB A)) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hcov : L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) : L ≤ Y := by
  refine le_of_forall_cover h hΩ h142 h153 hobs h1411 hY fun w _ hwL => ?_
  have h1 := congrArg (Subgroup.map (MulAut.conj w).toMonoidHom) hcov
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hwL,
    ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv, hwL, inf_comm] at h1
  exact h1

end CFSG.RankThree.PartTwo.Sec16
