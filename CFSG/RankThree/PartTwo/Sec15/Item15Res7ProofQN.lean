module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofConj
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadic
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsL

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res7

theorem eq_of_mem_thetaComponentsIn_of_hasFaithfulE9 {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {M : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    {Y₁ Y₂ : Subgroup G} (h₁ : Y₁ ∈ thetaComponentsIn M) (h₂ : Y₂ ∈ thetaComponentsIn M)
    (hE : HasFaithfulE9 Y₁) {E₂ : Subgroup G} (hE₂Y : E₂ ≤ Y₂)
    (hE₂ab : CFSG.Assembly.IsElemAbelian 3 E₂) (hE₂9 : Nat.card E₂ = 9) : Y₁ = Y₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨Y₁', hY₁', hYY₁⟩ := h₁
  obtain ⟨Y₂', hY₂', hYY₂⟩ := h₂
  change Y₁'.map M.subtype = Y₁ at hYY₁
  change Y₂'.map M.subtype = Y₂ at hYY₂
  have hY₁M : Y₁ ≤ M := hYY₁ ▸ Subgroup.map_subtype_le _
  have hY₂M : Y₂ ≤ M := hYY₂ ▸ Subgroup.map_subtype_le _
  have hne' : Y₁' ≠ Y₂' := by
    intro heq
    apply hne
    rw [← hYY₁, ← hYY₂, heq]
  have hcθ := commutator_le_of_mem_thetaComponents hY₁' hY₂' hne'
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥M).Normal := Subgroup.normal_of_characteristic _
  obtain ⟨E, hEY, hEab, hE9, hEc⟩ := hE
  have hab : ∀ {F : Subgroup G}, CFSG.Assembly.IsElemAbelian 3 F → F ≤ M →
      CFSG.Open.IsElemAbelian 3 (F.subgroupOf M) := by
    intro F hF hFM
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : ((a : ↥M) : G) ∈ F := Subgroup.mem_subgroupOf.mp a.2
      have hb : ((b : ↥M) : G) ∈ F := Subgroup.mem_subgroupOf.mp b.2
      have hab' : ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G) :=
        congrArg Subtype.val (hF.1.is_comm.comm (⟨_, ha⟩ : F) ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact hab'
    · exact Subtype.ext (hF.2 _ (Subgroup.mem_subgroupOf.mp hx))
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  set E₂' : Subgroup ↥M := E₂.subgroupOf M with hE₂'
  have hE₁Y : E₁ ≤ Y₁' := by
    intro x hx
    have hxY : (x : G) ∈ Y₁ := hEY (Subgroup.mem_subgroupOf.mp hx)
    rw [← hYY₁] at hxY
    obtain ⟨y, hy, hyx⟩ := hxY
    rwa [← Subtype.ext hyx]
  have hE₂Y' : E₂' ≤ Y₂' := by
    intro x hx
    have hxY : (x : G) ∈ Y₂ := hE₂Y (Subgroup.mem_subgroupOf.mp hx)
    rw [← hYY₂] at hxY
    obtain ⟨y, hy, hyx⟩ := hxY
    rwa [← Subtype.ext hyx]
  have hE₁card : Nat.card E₁ = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEY.trans hY₁M)).toEquiv
  have hE₂card : Nat.card E₂' = 9 := by
    rw [← hE₂9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE₂Y.trans hY₂M)).toEquiv
  have hc : ⁅E₁, E₂'⁆ ≤ aschbacherSolvableCore 3 ↥M :=
    (Subgroup.commutator_mono hE₁Y hE₂Y').trans hcθ
  have hd : ∀ x ∈ E₁, ∀ y ∈ E₂', x * y⁻¹ ∈ aschbacherSolvableCore 3 ↥M → x = 1 := by
    intro x hx y hy hxy
    have hxz : ∀ z ∈ Y₁', ⁅x, z⁆ ∈ aschbacherSolvableCore 3 ↥M := by
      intro z hz
      have hyz : ⁅z, y⁆ ∈ aschbacherSolvableCore 3 ↥M :=
        hcθ (Subgroup.commutator_mem_commutator hz (hE₂Y' hy))
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) x =
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) y := by
        have h1' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) (x * y⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hxy
        rwa [map_mul, map_inv, mul_inv_eq_one] at h1'
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅z, y⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hyz
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅x, z⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, h1]
        exact h2.symm
      exact (QuotientGroup.eq_one_iff _).mp h3
    have hxE : ((x : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hθN, hθs, hθ3'⟩ := map_aschbacherSolvableCore_facts M
    have hxG : ((x : ↥M) : G) ∈
        Late.sectionCentralizer E Y₁ ((aschbacherSolvableCore 3 ↥Y₁).map Y₁.subtype) := by
      refine ⟨hxE, fun z hz => ?_⟩
      rw [← hYY₁] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hxY : x ∈ Y₁' := hE₁Y hx
      have hmemY : ⁅x, z'⁆ ∈ Y₁' := by
        rw [commutatorElement_def]
        exact Y₁'.mul_mem (Y₁'.mul_mem (Y₁'.mul_mem hxY hz') (Y₁'.inv_mem hxY)) (Y₁'.inv_mem hz')
      have hmem : ((⁅x, z'⁆ : ↥M) : G) ∈
          (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y₁ :=
        ⟨Subgroup.mem_map_of_mem _ (hxz z' hz'), hYY₁ ▸ Subgroup.mem_map_of_mem _ hmemY⟩
      have := inf_le_map_aschbacherSolvableCore (hY₁M.trans hθN) hθs hθ3' hmem
      rwa [commutatorElement_def] at this
    exact Subtype.ext (hEc hxG)
  have h4 := four_le_pRank_of_commutator_le (aschbacherSolvableCore 3 ↥M) hθ3
    (hab hEab (hEY.trans hY₁M)) (hab hE₂ab (hE₂Y.trans hY₂M)) hE₁card hE₂card hc hd
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

omit [Finite G] in
theorem le_of_inf_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {Q P : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P ≤ Q) (hN : Q ⊓ Subgroup.normalizer (P : Set G) ≤ P) :
    Q ≤ P := by
  by_contra hne
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : ↥Q) ∈ P.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨x, hxN, hxP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  apply hxP
  rw [Subgroup.mem_subgroupOf]
  have hxNP : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyQ : y ∈ Q := hPQ hy
      have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyQ⟩).mp
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hy
      have hyQ : y ∈ Q := by
        have h1 : (x : G) * y * (x : G)⁻¹ ∈ Q := hPQ hy
        have h2 : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
        rw [h2]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem x.2) h1) x.2
      have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyQ⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hy)
      exact Subgroup.mem_subgroupOf.mp h1
  exact hN ⟨x.2, hxNP⟩

theorem mem_scriptQ_of_le_pPrimeCoreOf {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {d : G} (hdA : d ∈ A) {R : Subgroup G}
    (hR : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : R ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hD.isElemAbelian, fun B hB hAB => (hD.eq_of_le hB hAB).le⟩
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.card_dvd_of_le hR))
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR,
    fun B hB => ?_⟩
  by_cases hdB : d ∈ B
  · have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB)
    have hle : R ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
      refine (inf_le_inf_right _ hR).trans (le_pPrimeCoreOf inf_le_right ?_ ?_)
      · exact Late.le_normalizer_inf (hCB.trans (le_normalizer_pPrimeCoreOf 3 _))
          Subgroup.le_normalizer
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (coprime_card_pPrimeCoreOf 3 _)
    exact hle.trans (le_sup_left.trans le_sup_left)
  · have hAB := le_sup_zpowers_of_not_mem hA hB hdA hdB
    have hle : R ⊓ Subgroup.centralizer (B : Set G) ≤ R ⊓ Subgroup.centralizer (A : Set G) :=
      fun x hx => ⟨hx.1, mem_centralizer_of_le_sup hAB hx.2
        (pPrimeCoreOf_le 3 _ (hR hx.1))⟩
    exact hle.trans ((inf_centralizer_le_xA hAmax hR3).trans (le_sup_right.trans le_sup_left))

end Proof15Res7

open Proof15Res4 Proof15Res7

section Certificates


theorem Conf1515HJ.quot_pCore_two_equiv (h : Conf1515HJ A c L Y) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  have hR := h.sec15R
  have hLc := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (hR.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) h.j2
  have hYle : Y ≤ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
    rw [inf_comm]
    exact h.eq_Y.le
  obtain ⟨eY⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := Y) inf_le_right hYle
    (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  obtain ⟨eL⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := L) inf_le_left h.eq_L.le
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact ⟨(eY.symm.trans eL).trans eJ⟩

theorem Conf1515HJ.hasFaithfulE9 (h : Conf1515HJ A c L Y) :
    HasFaithfulE9 Y := by
  obtain ⟨e⟩ := h.quot_pCore_two_equiv
  obtain ⟨E, hE, h9⟩ := CFSG.QuasithinUnique.Id2519.exists_elemAbelian_nine_J2
  exact hasFaithfulE9_of_mulEquiv h.mem_scriptY0Star.prop.1.2.2.2 e
    (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
    ⟨E, hE, by rw [h9]; norm_num⟩

theorem Conf1515HJ.n155_le_normalizer (h : Conf1515HJ A c L Y)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) :
    n155 A Y ≤ Subgroup.normalizer (Y : Set G) := fun _ ht =>
  mem_normalizer_of_map_conj_eq_self (map_conj_eq_of_hasFaithfulE9 h.sec15R.toSec14Std h152
    h.mem_scriptY0Star h.hasFaithfulE9 (n155_mem_maximalTwoLocalsContaining h153
      h.mem_scriptY0Star) ht)

theorem Conf1515HJ.inf_theta_le_pCoreOf (h : Conf1515HJ A c L Y) :
    L ⊓ Y ⊓ inSubgroup (aschbacherSolvableCore 3) L ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := L ⊓ Y with hK
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hθ2 : IsPGroup 2 θL :=
    (Proof152Gen.isPGroup_theta_of_j2 h.sec15R.toSec14Std h.j2).map L.subtype
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  set T := (K ⊓ θL) ⊔ O with hT
  have hT2 : IsPGroup 2 T := (hθ2.to_le inf_le_right).to_sup_of_normal_right'
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (inf_le_left.trans hKO)
  have hTY : T ≤ Y := sup_le (inf_le_left.trans inf_le_right)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hKT : K ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sup (Late.le_normalizer_inf Subgroup.le_normalizer
      (inf_le_left.trans (Sec6.le_normalizer_theta L))) hKO
  have hOT : O ≤ Subgroup.normalizer (T : Set G) := le_sup_right.trans Subgroup.le_normalizer
  have hYle : Y ≤ K ⊔ O := by
    rw [hK, inf_comm]
    exact h.eq_Y.le
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTY
    (hYle.trans (sup_le hKT hOT)) hT2)

theorem Conf1515HJ.inf_pPrimeCoreOf_le (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdZ : IsZCentral L d) :
    Y ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  obtain ⟨hCq, -, -, -⟩ := Item148HJ.centralizer_facts h.j2 hz1 hzc
  obtain ⟨-, hZ3, -, -⟩ := KFacts.KS14.Native.j2_centralizer_quotient h.j2 hz1 hzc
  have hZC := KFacts.KS14.Native.j2_center_centralizer h.j2 hz1 hzc
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  set E := Y ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hE
  set O := CFSG.Open.pCoreOf 2 Y with hO
  set K := L ⊓ Y with hK
  set Z := zHJ L Y d with hZdef
  have hE3 : IsPiSubgroup (piCompl 3) E := by
    refine (isPiSubgroup_piCompl_iff Nat.prime_three E).mpr fun h3 => ?_
    have h3' : 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) :=
      h3.trans (Subgroup.card_dvd_of_le inf_le_right)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 _) h3'
  have hO3 : IsPiSubgroup (piCompl 3) O := by
    refine (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr fun h3 => ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hEN : E ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  set F := E ⊔ O with hF
  have hF3 : IsPiSubgroup (piCompl 3) F := isPiSubgroup_piCompl_sup hE3 hO3 hEN
  have hF3' : ¬ 3 ∣ Nat.card F := (isPiSubgroup_piCompl_iff Nat.prime_three F).mp hF3
  have hFY : F ≤ Y := sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hYle : Y ≤ K ⊔ O := by
    rw [hK, inf_comm]
    exact h.eq_Y.le
  set FK := F ⊓ K with hFK
  have hFle : F ≤ FK ⊔ O := by
    intro f hf
    obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup hKO (hYle (hFY hf))
    have hkF : k ∈ F := by
      have hk' : k = k * o * o⁻¹ := by group
      rw [hk']
      exact F.mul_mem hf (F.inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left ⟨hkF, hk⟩) (Subgroup.mem_sup_right ho)
  have hFKL : FK ≤ L := inf_le_right.trans inf_le_left
  have hOθ : O ⊓ L ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    refine (Proof15Res4.inf_le_pCoreOf_of_eq h.eq_L).trans ?_
    obtain ⟨-, -, -, -, -, -, hr⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.map_mono (hr 2 Nat.prime_two (by norm_num))
  set W := (FK.subgroupOf L).map π with hW
  have hWC : W ≤ C := by
    rintro _ ⟨k, hk, rfl⟩
    have hkFK : (k : G) ∈ FK := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨e, he, o, ho, heo⟩ := exists_mul_of_mem_sup hEN hkFK.1
    have hed : e * d = d * e :=
      Subgroup.mem_centralizer_singleton_iff.mp (pPrimeCoreOf_le 3 _ he.2)
    have hdO : d ∈ Subgroup.normalizer (O : Set G) := h.A_le_normalizer_pCoreOf hdA
    have hcomm : (k : G) * d * (k : G)⁻¹ * d⁻¹ ∈ O ⊓ L := by
      refine ⟨?_, L.mul_mem (L.mul_mem (L.mul_mem k.2 hdL) (L.inv_mem k.2)) (L.inv_mem hdL)⟩
      have h1 : o * d * o⁻¹ * d⁻¹ ∈ O := by
        have h2 : d * o⁻¹ * d⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hdO _).mp (inv_mem ho)
        rw [show o * d * o⁻¹ * d⁻¹ = o * (d * o⁻¹ * d⁻¹) by group]
        exact mul_mem ho h2
      have h3 : e * (o * d * o⁻¹ * d⁻¹) * e⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hEN he) _).mp h1
      have e1 : (k : G) * d * (k : G)⁻¹ * d⁻¹ = e * (o * d * o⁻¹ * d⁻¹) * e⁻¹ := by
        rw [heo]
        calc e * o * d * (e * o)⁻¹ * d⁻¹ = e * o * d * o⁻¹ * (e⁻¹ * d⁻¹) := by group
          _ = e * o * d * o⁻¹ * (d⁻¹ * e⁻¹) := by
              rw [show e⁻¹ * d⁻¹ = d⁻¹ * e⁻¹ by
                rw [← mul_inv_rev, ← mul_inv_rev, hed]]
          _ = e * (o * d * o⁻¹ * d⁻¹) * e⁻¹ := by group
      rw [e1]
      exact h3
    obtain ⟨t, ht, hte⟩ := hOθ hcomm
    have hkd : π (k * ⟨d, hdL⟩ * k⁻¹ * (⟨d, hdL⟩ : ↥L)⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have he' : k * ⟨d, hdL⟩ * k⁻¹ * (⟨d, hdL⟩ : ↥L)⁻¹ = t := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hte.symm)
      rw [he']
      exact ht
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hkd
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hkd
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    apply hF3'
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFKL).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hZY : Z ≤ Y := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_right)
  have hZL : Z ≤ L := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_left)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := (zHJ_le L Y d).trans inf_le_right
  have hZFK : Z ≤ Subgroup.normalizer (FK : Set G) := by
    have hZE : Z ≤ Subgroup.normalizer (E : Set G) :=
      Late.le_normalizer_inf (hZY.trans Subgroup.le_normalizer)
        (hZd.trans (le_normalizer_pPrimeCoreOf 3 _))
    exact Late.le_normalizer_inf
      (le_normalizer_sup hZE (hZY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)))
      (Late.le_normalizer_inf (hZL.trans Subgroup.le_normalizer)
        (hZY.trans Subgroup.le_normalizer))
  have hWn : C ≤ Subgroup.normalizer (W : Set (↥L ⧸ θ)) := by
    rw [← hmap]
    rintro _ ⟨z, hz, rfl⟩
    have hzN : (z : G) ∈ Subgroup.normalizer (FK : Set G) := hZFK (Subgroup.mem_subgroupOf.mp hz)
    have hz' : z ∈ Subgroup.normalizer ((FK.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp hzN (y : G)
    exact Subgroup.le_normalizer_map π ⟨z, hz', rfl⟩
  have hWbot : W = ⊥ := by
    have hWn' : (W.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hWn
    have hW3' : ¬ 3 ∣ Nat.card (W.subgroupOf C) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    have hcen : Nat.card (Subgroup.center ↥C) = 3 := by rw [hZC]; exact hZ3
    have hb := Item148HJ.eq_bot_of_normal_of_quasisimple hCq hcen hWn' hW3'
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hWC hx⟩ : ↥C) ∈ W.subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
    rw [hb, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hFKO : FK ≤ O := by
    intro k hk
    have h1 : π ⟨k, hFKL hk⟩ ∈ W := ⟨⟨k, hFKL hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hWbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h.inf_theta_le_pCoreOf ⟨hk.2, ⟨_, h1, rfl⟩⟩
  intro e he
  exact sup_le hFKO le_rfl (hFle (Subgroup.mem_sup_left he))

theorem Conf1515HJ.exists_maxP (h : Conf1515HJ A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d)
    (hodd : ¬ Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))) :
    ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧
      P ≤ Subgroup.normalizer (Y : Set G) ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ∧
      A ≤ Subgroup.normalizer (P : Set G) ∧ zHJ L Y d ≤ Subgroup.normalizer (P : Set G) ∧
      ∀ R : Subgroup G, IsPGroup 2 R →
        R ≤ Subgroup.normalizer (Y : Set G) ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) →
        A ≤ Subgroup.normalizer (R : Set G) → P ≤ R → R = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  set D := Subgroup.normalizer (Y : Set G) ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))
    with hDdef
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf (h.A_le_normalizer.trans Subgroup.le_normalizer)
      (hAd.trans (le_normalizer_pPrimeCoreOf 3 _))
  have hD3 : ¬ 3 ∣ Nat.card D := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨R₀, hR₀D, hR₀2, hAR₀, hR₀card⟩ :=
    Sec17.HeadProof.exists_invariant_sylow hA3 hD3 hAD Nat.prime_two
  have hR₀1 : R₀ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hR₀card
    have hf : (Nat.card D).factorization 2 = 0 := by
      by_contra hk
      have h2 : 2 ≤ 2 ^ (Nat.card D).factorization 2 := Nat.le_self_pow hk 2
      omega
    have h2 : 2 ∣ Nat.card D := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
    omega
  obtain ⟨P, hR₀P, hPmax⟩ := Finite.exists_le_maximal
    (p := fun R : Subgroup G => IsPGroup 2 R ∧ R ≤ D ∧ A ≤ Subgroup.normalizer (R : Set G))
    ⟨hR₀2, hR₀D, hAR₀⟩
  obtain ⟨hP2, hPD, hAP⟩ := hPmax.prop
  have hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ D →
      A ≤ Subgroup.normalizer (R : Set G) → P ≤ R → R = P :=
    fun R hR2 hRD hAR hPR => (hPmax.eq_of_ge ⟨hR2, hRD, hAR⟩ hPR)
  have hDO : D ≤ Subgroup.normalizer ((O ⊓ D : Subgroup G) : Set G) :=
    Late.le_normalizer_inf
      (inf_le_left.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      Subgroup.le_normalizer
  have hOD : O ⊓ D ≤ P := by
    have hT2 : IsPGroup 2 (P ⊔ (O ⊓ D) : Subgroup G) :=
      hP2.to_sup_of_normal_right' ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le
        inf_le_left) (hPD.trans hDO)
    have hAT : A ≤ Subgroup.normalizer ((P ⊔ (O ⊓ D) : Subgroup G) : Set G) :=
      le_normalizer_sup hAP (Late.le_normalizer_inf h.A_le_normalizer_pCoreOf hAD)
    have heq := hmax _ hT2 (sup_le hPD inf_le_right) hAT le_sup_left
    rw [← heq]
    exact le_sup_right
  set Z := zHJ L Y d with hZdef
  have hZY : Z ≤ Y := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := (zHJ_le L Y d).trans inf_le_right
  have hEO := h.inf_pPrimeCoreOf_le hdA hd1 hdZ
  have hZP : Z ≤ Subgroup.normalizer (P : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun z hz p hp => ?_
    have hpD := hPD hp
    have hzY := hZY hz
    have hc1 : z * p * z⁻¹ * p⁻¹ ∈ Y := by
      have h1 : p * z⁻¹ * p⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hpD.1 _).mp (inv_mem hzY)
      rw [show z * p * z⁻¹ * p⁻¹ = z * (p * z⁻¹ * p⁻¹) by group]
      exact mul_mem hzY h1
    have hc2 : z * p * z⁻¹ * p⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
      have h1 : z * p * z⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 _ (hZd hz)) p).mp hpD.2
      exact mul_mem h1 (inv_mem hpD.2)
    have hcO : z * p * z⁻¹ * p⁻¹ ∈ O := hEO ⟨hc1, hc2⟩
    have hcD : z * p * z⁻¹ * p⁻¹ ∈ D := ⟨Subgroup.le_normalizer hc1, hc2⟩
    have hcP : z * p * z⁻¹ * p⁻¹ ∈ P := hOD ⟨hcO, hcD⟩
    have he : z * p * z⁻¹ = z * p * z⁻¹ * p⁻¹ * p := by group
    rw [he]
    exact mul_mem hcP hp
  exact ⟨P, fun h0 => hR₀1 (le_bot_iff.mp (h0 ▸ hR₀P)), hP2, hPD, hAP, hZP, hmax⟩

theorem Conf1515HJ.delta_le_normalizer
    (h : Conf1515HJ A c L Y) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    (h155 : Item155w A (lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRQ : R ∈ scriptQ A (lB A))
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hZR : zHJ L Y d ≤ Subgroup.normalizer (R : Set G))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hRd : R ≤ Subgroup.centralizer ({d} : Set G)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (zHJ L Y d ⊔ R) : Subgroup G) : Set G)) :
    delta A (lB A) M ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  obtain ⟨eZ⟩ := h.zHJ_quot hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hCq : IsQuasisimple ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
    (Item148HJ.centralizer_facts h.j2 hz1 hzc).1
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ hmap
  set Y' := Z ⊔ R with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({d} : Set G) := sup_le hZd hRd
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAR
  have hY'R : Y' ≤ Subgroup.normalizer (R : Set G) := sup_le hZR Subgroup.le_normalizer
  have hRO' : R ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'R hR2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.sec15R.toTheoremFourHyp hd1 (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta hRQ le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRO'))⟩, le_antisymm hY'Δ (delta_le Y')⟩
  have hZ'Z : oPrimeResidualOf 3 Z = Z := by
    rw [hZdef, zHJ, Proof156Res4.oRes3_idem']
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZX' : Z ≤ X' := hZ'Z ▸ oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ R) := Proof155w.le_sup_inf_of_le hZR hZX' hX'Y'
  have hX'R : X' ≤ Subgroup.normalizer ((X' ⊓ R : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'R)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZX' hX'le (hZX'.trans hX'R) hX'R
    (hR2.to_le inf_le_right)
  set e := e₁.symm.trans eZ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZX'))
      (le_delta (mem_scriptQ_of_le hRQ inf_le_right
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAR)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZX'.trans le_sup_left) (hRO'.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hX'Y : X' ≤ Y :=
    Proof155R2.oPrimeResidualOf_le_of_le_sup hR2 hRY (sup_le_sup_right hZY R)
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨h.mem_scriptY0Star, hX'Y, sup_le (hZY.trans Subgroup.le_normalizer) hRY⟩
  have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
    rw [Nat.card_congr e.toEquiv, hC1080]
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
      not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
    have h60 := Nat.card_congr e5.toEquiv
    rw [hX'1080, card_alternatingGroup_five] at h60
    norm_num at h60
  exact ((h155 Y' hY'3 hX'4 hY'eq).2 Y hΓ hhyp M hM).trans (h.n155_le_normalizer h152 h153)

theorem Conf1515HJ.exists_Q
    (h : Conf1515HJ A c L Y)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) (h155 : Item155w A (lB A))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    (hodd : ¬ Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))) :
    ∃ Q ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) (piOf 2),
      Q ≠ ⊥ ∧ Q ≤ Subgroup.normalizer (Y : Set G) ∧
        zHJ L Y d ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sec15R.toSec14Std
  obtain ⟨P, hP1, hP2, hPD, hAP, hZP, hmax⟩ := h.exists_maxP hdA hd1 hdZ hodd
  set O3 := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hO3
  have hPQ : P ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le_pPrimeCoreOf hS hdA (hPD.trans inf_le_right) hAP
  have hPmem : P ∈ scriptQPi A (lB A) O3 (piOf 2) :=
    ⟨⟨hPQ, hPD.trans inf_le_right⟩, (isPiSubgroup_piOf_iff Nat.prime_two P).mpr hP2⟩
  obtain ⟨Q, hPQle, hQmax⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) O3 (piOf 2))) hPmem
  have hQmem := hQmax.prop
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mem_scriptQPi Nat.prime_two hQmem
  have hQQ : Q ∈ scriptQ A (lB A) := hQmem.1.1
  have hQO3 : Q ≤ O3 := hQmem.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hP1)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (zHJ L Y d ⊔ P) : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAP (sup_le hZP Subgroup.le_normalizer) hx)⟩
  have hΔ := h.delta_le_normalizer h152 h153 h155 hdA hd1 hdZ hP2 hP1 hPQ hAP hZP
    (hPD.trans inf_le_left) ((hPD.trans inf_le_right).trans (pPrimeCoreOf_le 3 _)) hMm
  set NQ := Q ⊓ Subgroup.normalizer (P : Set G) with hNQ
  have hANQ : A ≤ Subgroup.normalizer (NQ : Set G) :=
    Late.le_normalizer_inf hAQ (hAP.trans Subgroup.le_normalizer)
  have hNQQ : NQ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQQ inf_le_left hANQ
  have hNQY : NQ ≤ Subgroup.normalizer (Y : Set G) :=
    (le_delta hNQQ (inf_le_right.trans hle)).trans hΔ
  have hNQeq : NQ = P :=
    hmax NQ (hQ2.to_le inf_le_left) (le_inf hNQY (inf_le_left.trans hQO3)) hANQ
      (le_inf hPQle Subgroup.le_normalizer)
  have hQP : Q ≤ P := le_of_inf_normalizer_le hQ2 hPQle hNQeq.le
  have hQeq : Q = P := le_antisymm hQP hPQle
  refine ⟨Q, hQmax, ?_, ?_, ?_⟩
  · rw [hQeq]
    exact hP1
  · rw [hQeq]
    exact hPD.trans inf_le_left
  · rw [hQeq]
    exact hZP

theorem Conf1515HJ.normalizer_inf_le
    (h : Conf1515HJ A c L Y) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    (h155 : Item155w A (lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {Q : Subgroup G}
    (hQ : Q ∈ scriptQPiStar A (lB A) (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))
      (piOf 2))
    (hQ1 : Q ≠ ⊥) (hQY : Q ≤ Subgroup.normalizer (Y : Set G))
    (hZQ : zHJ L Y d ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sec15R.toSec14Std
  have hD := h.sec13Data
  have hY := h.mem_scriptY0Star
  have hQmem := hQ.prop
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mem_scriptQPi Nat.prime_two hQmem
  have hQQ : Q ∈ scriptQ A (lB A) := hQmem.1.1
  have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) := hQmem.1.2.trans (pPrimeCoreOf_le 3 _)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set Z := zHJ L Y d with hZdef
  have hZL : Z ≤ L := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_left)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ
      (h.map_zHJ hdA hd1 hdZ hdL)
  rintro g ⟨hgA, hgQ⟩
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hQ2 hQ1)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (Z ⊔ Q) : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (sup_le hAQ (sup_le hZQ Subgroup.le_normalizer) hx)⟩
  have hΔM := h.delta_le_normalizer h152 h153 h155 hdA hd1 hdZ hQ2 hQ1 hQQ hAQ hZQ hQY hQd hMm
  have hgM : g ∈ M := hle hgQ
  have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
    map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hΔg : (delta A (lB A) M).map (MulAut.conj g).toMonoidHom = delta A (lB A) M := by
    rw [Sec17.HeadProof.map_conj_delta hgA M, hMg]
  set Yg := Y.map (MulAut.conj g).toMonoidHom with hYg
  have hΔYg : delta A (lB A) M ≤ Subgroup.normalizer (Yg : Set G) := by
    intro x hx
    have hx' : x ∈ (delta A (lB A) M).map (MulAut.conj g).toMonoidHom := hΔg.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyN := hΔM hy
    refine mem_normalizer_of_map_conj_eq_self ?_
    rw [hYg, ← map_conj_mul, show (MulAut.conj g).toMonoidHom y * g = g * y by
      simp [MulAut.conj_apply], map_conj_mul, map_conj_eq_self_of_mem_normalizer hyN]
  have hZM : Z ≤ M := hZQ.trans hle
  have hZYg : Z ≤ Subgroup.normalizer (Yg : Set G) :=
    (hZΔ.trans (delta_mono hZM)).trans hΔYg
  have hQM : Q ≤ M := Subgroup.le_normalizer.trans hle
  have hQYg : Q ≤ Subgroup.normalizer (Yg : Set G) :=
    (le_delta hQQ hQM).trans hΔYg
  have hYg0 : Yg ∈ scriptY0Star A (lB A) := Sec16.map_conj_mem_scriptY0Star hgA hY
  have hAYg : A ≤ Subgroup.normalizer (Yg : Set G) := hYg0.prop.1.1.2
  have hNYg : n155 A Yg ∈ CFSG.maximalTwoLocalsContaining ((Yg ⊔ A : Subgroup G) : Set G) :=
    n155_mem_maximalTwoLocalsContaining h153 hYg0
  have hNle : Subgroup.normalizer (Yg : Set G) ≤ n155 A Yg := normalizer_le_n155w h153 hYg0
  have hNYgm : n155 A Yg ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (Z ⊔ Q) : Subgroup G) : Set G) :=
    ⟨hNYg.1, fun x hx => hNle (sup_le hAYg (sup_le hZYg hQYg) hx)⟩
  have hΔN := h.delta_le_normalizer h152 h153 h155 hdA hd1 hdZ hQ2 hQ1 hQQ hAQ hZQ hQY hQd
    hNYgm
  have hYgY : Yg ≤ Subgroup.normalizer (Y : Set G) :=
    (hYg0.prop.1.2.2.1.le.trans (delta_mono (Subgroup.le_normalizer.trans hNle))).trans hΔN
  have hMY : n155 A Y ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    n155_mem_maximalTwoLocalsContaining h153 hY
  have hYθ := mem_thetaComponentsIn_of_item152 hS h152 hY hMY
  obtain ⟨-, -, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining hS hMY
  have hYgle : Yg ≤ n155 A Y := hYgY.trans (normalizer_le_n155w h153 hY)
  obtain ⟨J, hJ, hYgJ, hJ0⟩ := h152 Yg hYg0.prop.1 (n155 A Y) hM2 hYgle hF
  have hJeq : Yg = J := hYg0.eq_of_le hJ0 hYgJ
  rw [← hJeq] at hJ
  obtain ⟨E, hEY, hEab, hE9, -⟩ := h.hasFaithfulE9
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤ Yg := Subgroup.map_mono hEY
  have heq := eq_of_mem_thetaComponentsIn_of_hasFaithfulE9 hS hMY.1 hYθ hJ h.hasFaithfulE9
    hEg (CFSG.SectionRank.isElemAbelian_map hEab _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9])
  exact mem_normalizer_of_map_conj_eq_self heq.symm

end Certificates

theorem step1515HJQN_of
    (h152 : Item152R) (h153 : Item153MainR) (h155 : Item155wR) :
    Step1515HJQN := by
  intro G _ _ A c L Y h d hdA hd1 hdZ hodd
  have hR := h.sec15R
  obtain ⟨Q, hQ, hQ1, hQY, hZQ⟩ := h.exists_Q (h152 G A c L hR) (h153 G A c L hR)
    (h155 G A c L hR) hdA hd1 hdZ hodd
  exact ⟨Q, hQ, fun g hg => h.normalizer_inf_le (h152 G A c L hR) (h153 G A c L hR)
    (h155 G A c L hR) hdA hd1 hdZ hQ hQ1 hQY hZQ hg.1⟩

end CFSG.RankThree.PartTwo.Sec15
