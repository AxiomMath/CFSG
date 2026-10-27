module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1523Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Case148


theorem cases148Full_of_mem_scriptY4 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h148 : Item148 A LB) (hAab : IsMulCommutative A) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A LB) (hYΔ : Y = deltaZero A LB Y) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      Y = pPrimeCoreOf 3 Y ⊔
        deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ∧
      ∃ L' ∈ lA A c',
        Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
        ((Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
          Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7))) ∨
        (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p (f * e) ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f) ∨
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          (Sec4.IsTripleCover (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) (alternatingGroup (Fin 6)) ∨
            Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 5))))) ∨
    (∃ (c' d : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L' d ∧
      deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
        deltaZero A LB (Y ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      (Sec4.IsTripleCover (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) CFSG.Blueprint.NativeSporadic.ON ∨
        Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))) ∨
    (Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) ∧
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) ∧
      WStarS4 A) ∨
    (∃ (c' : G) (L' : Subgroup G) (n m : ℕ), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      1 ≤ n ∧ 1 ≤ m ∧ Sec4.IsoLThreePi (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) 2 (3 * n) ∧
      IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 (n * m)) := by
  let := ker148_normal hY.1.2
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hY
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact nonempty_img148_equiv hY.1.2
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  have := Proof1515.nontrivial_alternatingGroup_five
  have := Proof1515.nontrivial_J2
  rcases (h148 Y hY.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    apply hne
    rw [← hYΔ] at h1
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1 y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rw [← hYΔ] at hdec
    refine Or.inl ⟨c', hc', hdec, L', hL', ?_⟩
    rcases hcases with hφ | ⟨hL, hφ⟩ | ⟨p, f, e, hp, hf, he, hiso, hε⟩ | ⟨hJ, h6 | hφ⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inl ⟨e0.symm.trans φ⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨hL, ⟨e0.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, e, hp, hf, he, hiso, IsLThreeEpsAt.of_mulEquiv e0 hε⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hJ, Or.inl (Proof1515.isTripleCover_congr e0 h6)⟩))
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inr (Or.inr ⟨hJ, Or.inr ⟨e0.symm.trans φ⟩⟩))
  ·
    obtain ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec, h⟩ := h3
    rcases h with hON | hCP | hA6A5 | hφ | hφ | ⟨h7, hφ⟩
    · exact Or.inr (Or.inl ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec,
        Or.inl (Proof1515.isTripleCover_congr e0 hON)⟩)
    · exact (Proof1515.not_isCentralProductA6Covers_of_isQuasisimple hqX hCP).elim
    · exact (Proof1515.not_isA6CoverTimesA5_of_isQuasisimple hqX hA6A5).elim
    · obtain ⟨φ⟩ := hφ
      exact ((Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec,
        Or.inr (Or.inl ⟨e0.symm.trans φ⟩)⟩)
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec,
        Or.inr (Or.inr ⟨h7, ⟨e0.symm.trans φ⟩⟩)⟩)
  ·
    obtain ⟨hφ, hL7, hW⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact Or.inr (Or.inr (Or.inl ⟨⟨e0.symm.trans φ⟩, hL7, hW⟩))
  ·
    obtain ⟨c', -, L', n, m, hc', hL', hn, hm, hiso, -, -, -, hε, -⟩ := h5
    exact Or.inr (Or.inr (Or.inr ⟨c', L', n, m, hc', hL', hn, hm,
      Proof1515.isoLThreePi_congr e0 hiso, hε⟩))
  ·
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact ((Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    set X := img148 A Y (deltaZero A LB Y) with hX
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hC₁ : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    have hC₂ : img148 A Y J₁ ≤ Subgroup.centralizer (img148 A Y J₂ : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hN₁ : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
    have hN₂ : ((img148 A Y J₂).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
      rw [← hsup]
      exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    have hsup' : (img148 A Y J₁).subgroupOf X ⊔ (img148 A Y J₂).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
    have hinf' : (img148 A Y J₁).subgroupOf X ⊓ (img148 A Y J₂).subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J₁ ⊓ img148 A Y J₂ := ⟨hx.1, hx.2⟩
      rw [hinf] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases eq_bot_or_eq_bot_of_isQuasisimple hqX hN₁ hN₂ hsup' hinf' with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₂le)
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

end Case148

theorem not_meetsY4_of_lA (h134 : Item134) (h48 : Sec4.Item4_8) (h1514 : Item1514HJR)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hm : ¬ MeetsY4 A (lB A) L Y) {c' : G}
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    ¬ MeetsY4 A (lB A) L' Y := by
  intro hm'
  have h' := Sec16.sec15R_of_point h hc' hL'
  have hJ' := lA_j2_of_j2 h134 h48 h hJ hc' hL'
  obtain ⟨φJ'⟩ := hJ'
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  rcases h1514 G A c' L' h' ⟨φJ'⟩ Y hY hm' with ⟨-, -, hΩ, -, -⟩ | ⟨⟨φ7⟩, -⟩ |
      ⟨⟨_, ⟨φU⟩⟩, -⟩
  · have hc : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
    rw [hΩ] at hc
    have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
      rw [hJc]
      norm_num
    obtain ⟨φL⟩ := hJ
    have h3L : 3 ∣ Nat.card L := Proof1515.three_dvd_card_of_mulEquiv φL h3J
    have hLL : L' = L :=
      Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L (Set.mem_singleton_iff.mp hc).symm
        hL'
    exact hm (hLL ▸ hm')
  · have h1 := Nat.card_congr (φJ'.symm.trans φ7).toEquiv
    rw [hJc, card_alternatingGroup_seven] at h1
    norm_num at h1
  · exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1) (Or.inr ⟨by norm_num, ⟨φU⟩⟩)

theorem zpowers_not_mem_omegaA_of_j2 (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    Subgroup.zpowers d ∉ omegaA A := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hc1 := hD.ne_one
  have hcL : c ∉ L := (j2_point_facts hD hJ).1
  obtain ⟨hdL, S3, hdS, hSd⟩ := hdc
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hdZ : IsZCentral L d := by
    obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S3 hdS hSd
    exact ⟨_, hSy, hZ⟩
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hD.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S3, hdS, hSd⟩
  obtain ⟨K', hK', hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD.mem_lA.1 hJq
  have hcd : Subgroup.zpowers c ≠ Subgroup.zpowers d := fun heq =>
    hcL (Subgroup.zpowers_le.mpr hdL (heq ▸ Subgroup.mem_zpowers c))
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K' hK' hJK with
    ⟨-, -, hΩ⟩ | ⟨-, -, hWd, -, -, -, hcases⟩ | ⟨-, hWd, hΩ, -⟩
  · intro hdΩ
    rw [hΩ] at hdΩ
    exact hcd (Set.mem_singleton_iff.mp hdΩ).symm
  · have hPd : oThreeWPre A ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
      (Subgroup.map_subtype_le _).trans hWd
    rcases hcases with ⟨hΩ, -⟩ | ⟨I, -, -, -, a, -, had, hΩ, -, -⟩
    · rw [hΩ]
      exact Proof152ResW.not_mem_orbitIn hPd hcd
    · have had' : Subgroup.zpowers a ≠ Subgroup.zpowers d := fun heq =>
        had (heq ▸ Subgroup.mem_zpowers a)
      rw [hΩ]
      rintro (h1 | h2)
      · exact Proof152ResW.not_mem_orbitIn hPd hcd h1
      · exact Proof152ResW.not_mem_orbitIn hPd had' h2
  · rw [hΩ]
    exact Proof152ResW.not_mem_orbitIn hWd hcd

theorem isThreeCentralIn_of_onType
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L' d)
    (htype : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
      CFSG.Blueprint.NativeSporadic.ON) : IsThreeCentralIn L d := by
  have h' := Sec16.sec15R_of_point h hc' hL'
  have hJ' := lA_j2_of_j2 h134 h48 h hJ hc' hL'
  have hdΩ := zpowers_not_mem_omegaA_of_j2 h134 h48 h'.toSec14Std hJ' hdA hd1 hdc
  obtain ⟨hWd, -, hpts⟩ := Proof15Res11.onType_facts h134 h48 h' hJ' hdA hd1 hdc htype
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcd : c ∉ Subgroup.zpowers d := by
    intro hc
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hc
    have h3c : Nat.card (Subgroup.zpowers c) = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 c h.mem_A) h.toSec13Data.ne_one
    have h3d : Nat.card (Subgroup.zpowers d) = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
    have heq : Subgroup.zpowers c = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h3c, h3d])
    exact hdΩ (heq ▸ h.zpowers_mem_omegaA)
  obtain ⟨-, w, hw, hcw⟩ := hpts c h.mem_A hcd
  have hz : Subgroup.zpowers c = Subgroup.zpowers ((MulAut.conj w) c') := by
    rw [hcw, MonoidHom.map_zpowers]
    rfl
  have hLw : L'.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 c := by
    rw [Proof1515.thetaComponentsAt_eq_of_zpowers_eq hz]
    exact map_mem_thetaComponentsAt (MulAut.conj w) h'.mem_lA.1
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeJ2]
    norm_num
  obtain ⟨φJ'⟩ := hJ'
  have h3' : 3 ∣ Nat.card (L'.map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact Proof1515.three_dvd_card_of_mulEquiv φJ' h3J
  have hLeq : L'.map (MulAut.conj w).toMonoidHom = L :=
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLw h3'
  have hcent := Item148PtRes.isThreeCentralIn_map_conj hdc w
  rw [hLeq] at hcent
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hWd (inv_mem hw)
  have hmem : w⁻¹ * d * w ∈ Subgroup.zpowers d := by
    have := (Subgroup.mem_normalizer_iff.mp hwinv d).mp (Subgroup.mem_zpowers d)
    rwa [inv_inv] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Item148PtRes.isThreeCentralIn_of_mem_zpowers hcent
    (Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩)
  rw [conj_zpow, hk]
  group

theorem eq_inf_k_sup_of_dec {A : Subgroup G} {d : G} {Y : Subgroup G}
    (hY4 : Y ∈ scriptY4 A (lB A)) (hYΔ : Y = deltaZero A (lB A) Y)
    (hO : pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y)
    (hdec : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G))) :
    Y = (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y := by
  rw [← hYΔ, hO] at hdec
  set D := deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hD
  have hDY : D ≤ Y := (deltaZero_le _).trans inf_le_left
  have hDΔ : D ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
    (deltaZero_le_delta _).trans (delta_mono inf_le_right)
  have hcov : Y ≤ oPrimeResidualOf 3 D ⊔ CFSG.Open.pCoreOf 2 Y :=
    Proof1515Res.le_oRes3_sup hY4.2.1 hDY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y) (by rw [sup_comm]; exact hdec.le)
  have hDK : oPrimeResidualOf 3 D ≤ k1523 A d := oPrimeResidualOf_mono 3 hDΔ
  refine le_antisymm (hcov.trans (sup_le_sup_right (le_inf
    ((oPrimeResidualOf_le_self 3 D).trans hDY) hDK) _))
    (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))

end CFSG.RankThree.PartTwo.Sec15.Proof1523Res3
