module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec13.Item131a
import CFSG.RankThree.PartTwo.Sec15.Gagen1511Hessian
import CFSG.RankThree.PartTwo.Sec15.Gagen1511Setup
import CFSG.RankThree.PartTwo.Sec15.Gagen1511HJ
import CFSG.RankThree.PartTwo.Sec15.Gagen1511Point
import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec15.Item15Res6Proof159
import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1511Field :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY0 A (lB A)),
      letI := ker148_normal hY.1.1.2
      ¬ Case148Five A (lB A) Y

private theorem solvable_centralizer_of_mem_inf
    {G : Type} [Group G] [Finite G]
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (h131a : Item131a)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    ∀ d : ↥L, (d : G) ∈ A → d ≠ 1 →
      Group.IsSolvable ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  obtain ⟨hEe, hE9, htr⟩ :=
    Proof1511Point.hessian_of_prod h131a h he hiso hprod
  intro d hdA hd1
  have hdInf : (⟨d, d.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hdA, d.2⟩
  have hdE : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d ∈
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :=
    Subgroup.mem_map.mpr ⟨⟨d, d.2⟩, hdInf, rfl⟩
  have hP3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    have hx3 : ((x : ↥L) : G) ^ 3 = 1 :=
      h.isElemAbelian.2 ((x : ↥L) : G) (Subgroup.mem_subgroupOf.mp x.2).1
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx3))⟩
  have hdne : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d ≠ 1 := by
    intro h1
    have hinj := CFSG.RankThree.injOn_mk_of_isPGroup (G := ↥L) Nat.prime_three hP3
    have heq : (⟨d, d.2⟩ : ↥L) = 1 :=
      hinj hdInf (Subgroup.one_mem _) (by rw [map_one]; simpa using h1)
    exact hd1 (by simpa using heq)
  exact Proof1511Point.isSolvable_centralizer_of_hessian he hiso hEe hE9 htr hdE hdne

section Certificates


theorem step1511Point_of (h148 : Item148R) (h131a : Item131a) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hfield : Step1511Field) : Step1511Point := by
  intro G _ _ A c L h p e _ he hiso Y hY hmeet P hAP hP hprod hW hΩ
  have hD := h.toSec13Data
  have hAab : IsMulCommutative A := hD.isElemAbelian.1
  have h3L : 3 ∣ Nat.card L :=
    Proof1515.three_dvd_card_of_thetaQuot
      (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi he hiso)
  have hYΔ : Y = deltaZero A (lB A) Y :=
    Proof1515.eq_deltaZero_of_mem_scriptY4
      (forall_exists_isHyperplane_lB_eq_bot h134 h48 Sec4.Sporadic.rank3II_4_15) h hY.1
  obtain ⟨-, -, hAeq⟩ := Proof1511Point.facts_of_prod_of_isoLThreePi h he hiso hprod
  have hsolv := solvable_centralizer_of_mem_inf h h131a he hiso hprod
  haveI hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt).1
  obtain ⟨-, hq2ne⟩ := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
  have hq2 : 2 < p ^ e := by
    have hp2 : 2 ≤ p ^ e :=
      (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  letI := ker148_normal hY.1.1.2
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* ↥Y ⧸
      CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact nonempty_img148_equiv hY.1.1.2
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hY.1
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  rcases (h148 G A c L h Y hY.1.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY.1
    rw [← hYΔ] at h1
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1 y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rw [← hYΔ] at hdec
    obtain ⟨hc'A, hc'card, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'1 : c' ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'card
      omega
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c :=
      Proof1511Point.zpowers_eq_of_eq_sup_deltaZero h hAeq hsolv hY.1.1.2 hmeet hc'A hc'1 hdec
    rw [hcc] at hdec
    have hL'L : L' = L := Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
    subst L'
    refine ⟨hdec, ?_⟩
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p', f', e', hp', hf', he', hiso', hε⟩ | ⟨hJ, -⟩
    ·
      obtain ⟨φ⟩ := hφ
      refine Or.inl ⟨1, e, he, by simp, ?_⟩
      exact IsLThreeEpsAt.of_mulEquiv (φ.symm.trans e0)
        (isLThreeEpsAt_of_isoLThreePi hq2 hiso)
    ·
      obtain ⟨φ⟩ := hφ
      exact Or.inr ⟨e0.symm.trans φ⟩
    ·
      obtain ⟨hpp, hee⟩ := Sec14.Ronan148A.isoLThreePi_unique he (Nat.mul_pos hf' he')
        hiso hiso'
      subst p'
      refine Or.inl ⟨e', f', hf', ?_, IsLThreeEpsAt.of_mulEquiv e0 hε⟩
      rw [hee, Nat.mul_comm]
    ·
      obtain ⟨ψ⟩ := hJ
      exact (KFacts.KS14.ks17J2NotList.1 p e
        (Proof1515.isoLThreePi_congr ψ hiso)).elim
  ·
    obtain ⟨c₀, d, L₀, hc₀, hL₀, hJ, hdA, hd1, hd, -, -⟩ := h3
    exact (Proof1511Point.false_of_isThreeCentralIn h134 h48 h.toSec14Std he hiso
      hc₀ hL₀ hJ hdA hd1 hd).elim
  ·
    exact (Proof1511Point.not_wStarS4_of_le_normalizer h.isE27 h.mem_A h.ne_one hW
      h4.2.2).elim
  ·
    exact (hfield G A c L h Y hY h5).elim
  ·
    obtain ⟨φ⟩ := h6.1
    haveI : Nontrivial (alternatingGroup (Fin 5)) := Proof1515.nontrivial_alternatingGroup_five
    haveI : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := Proof1515.nontrivial_J2
    exact ((Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
      (H₁ := alternatingGroup (Fin 5)) (H₂ := CFSG.Blueprint.NativeSporadic.J2)
      hqX).false φ).elim
  ·
    exact (false_of_case148Seven hAab hY.1 hYΔ h7).elim

end Certificates

end CFSG.RankThree.PartTwo.Sec15
