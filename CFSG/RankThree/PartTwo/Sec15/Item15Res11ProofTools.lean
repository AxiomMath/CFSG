module

import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTrans
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullCommutator
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof15Res11

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_le_of_le_sup {N Y R : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (N : Set G)) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hR : R ≤ N ⊔ Y) :
    ⁅R, Subgroup.zpowers c⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro r hr g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hr' : r ∈ (N : Set G) * (Y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N Y hYN]
    exact hR hr
  obtain ⟨n, hn, y, hy, rfl⟩ := hr'
  have hck : c ^ k ∈ Subgroup.normalizer (N : Set G) := Subgroup.zpow_mem _ hcN k
  have hyc : y * c ^ k = c ^ k * y := by
    have h1 : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hYc hy)
    exact (Commute.zpow_right h1 k).eq
  have e : ⁅n * y, c ^ k⁆ = n * (c ^ k * n⁻¹ * (c ^ k)⁻¹) := by
    rw [commutatorElement_def]
    calc n * y * c ^ k * (n * y)⁻¹ * (c ^ k)⁻¹ = n * (y * c ^ k) * y⁻¹ * n⁻¹ * (c ^ k)⁻¹ := by
          group
      _ = n * (c ^ k * y) * y⁻¹ * n⁻¹ * (c ^ k)⁻¹ := by rw [hyc]
      _ = n * (c ^ k * n⁻¹ * (c ^ k)⁻¹) := by group
  rw [e]
  exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp hck n⁻¹).mp (N.inv_mem hn))

omit [Finite G] in
theorem le_of_le_sup_of_le_centralizer {N Y R : Subgroup G} {c : G}
    (hRc : R = ⁅R, Subgroup.zpowers c⁆) (hcN : c ∈ Subgroup.normalizer (N : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hYc : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hR : R ≤ N ⊔ Y) : R ≤ N := by
  rw [hRc]
  exact commutator_zpowers_le_of_le_sup hcN hYN hYc hR

variable {A L : Subgroup G} {c : G}

theorem commutatorR_eq (h : Conf1515HJ A c L L) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ =
      ⁅⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆,
        Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Q := CFSG.Open.pCoreOf 2 N with hQdef
  have hZQ : Subgroup.zpowers c ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.mpr (hD.le_normalizer hD.mem_A)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [Nat.card_zpowers, hD.orderOf_eq, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact (CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.properHull_coprime_double_commutator
    Q (Subgroup.zpowers c) hZQ hcop).symm

theorem commutatorR_isPGroup (h : Conf1515HJ A c L L) :
    IsPGroup 2 (⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ :
        Subgroup G) ∧
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRQ := Proof15Res10.commutatorR_le h
  exact ⟨(CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hRQ,
    hRQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)⟩

theorem commutatorR_inf_eq_bot (h : Conf1515HJ A c L L) {d : G}
    (hodd : Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR2, hRN⟩ := commutatorR_isPGroup h
  set R : Subgroup G :=
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ with hRdef
  set M : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hMdef
  have h2 : IsPGroup 2 (R ⊓ M : Subgroup G) := hR2.to_le inf_le_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card (R ⊓ M : Subgroup G) ∣ Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓ M) :=
    Subgroup.card_dvd_of_le (inf_le_inf_right M hRN)
  rcases n with _ | n
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero])
  · exfalso
    have h2d : 2 ∣ Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓ M) :=
      (hn ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
    have := Nat.odd_iff.mp hodd
    omega

theorem omega_facts
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A ≠ {Subgroup.zpowers c}) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) :
    Subgroup.zpowers d ∉ omegaA A ∧
      ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c * b) ∈ omegaA A := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hc1 := hD.ne_one
  have hcL : c ∉ L := (j2_point_facts hD hJ).1
  obtain ⟨hdL, S3, hdS, hSd⟩ := Proof15Res4.isThreeCentralIn_of_isZCentral hdZ
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have hdc : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA hd1 hcA hcd
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hD.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S3, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD.mem_lA.1 hJq
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab', h9, -, hΩ'⟩ | ⟨-, hWd, hΩ', h12⟩
  · exact absurd h1 hΩ
  · have hΩ'' : (omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧
        (omegaA A).ncard = 3) ∨
        ∃ a ∈ A, a ∉ Subgroup.zpowers d ∧
          omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
            orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 := by
      rcases hΩ' with h3 | ⟨I, -, -, -, a', haAK, had', hΩe, h6, -⟩
      · exact Or.inl h3
      · exact Or.inr ⟨a', haAK.1, had', hΩe, h6⟩
    exact Proof152ResW.omegaA_facts_of_case2 hA hcA hc1 hdA hd1 hdc hWd hab' h9 hΩ''
  · exact Proof152ResW.omegaA_facts_of_case3 hA hcA hc1 hdA hd1 hdc hWd hΩ' h12

theorem theta_le_pPrimeCoreOf {C X : Subgroup G} (hXC : X ≤ C)
    (hnorm : C ≤ Subgroup.normalizer ((pPrimeCoreOf 3 C ⊔ X : Subgroup G) : Set G)) :
    inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := pPrimeCoreOf 3 C with hM
  set θ := inSubgroup (aschbacherSolvableCore 3) X with hθ
  set P := M ⊔ X with hP
  set S := θ ⊔ M with hS
  have hθX : θ ≤ X := Sec17.Proof171Steps.theta_le X
  have hXθ : X ≤ Subgroup.normalizer (θ : Set G) := Sec17.Proof171Steps.le_normalizer_theta X
  have hCM : C ≤ Subgroup.normalizer (M : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hθ3 : IsPiSubgroup (piCompl 3) θ := by
    refine (isPiSubgroup_piCompl_iff Nat.prime_three θ).mpr ?_
    rw [hθ, inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  have hM3 : IsPiSubgroup (piCompl 3) M :=
    (isPiSubgroup_piCompl_iff Nat.prime_three M).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
  have hS3 : IsPiSubgroup (piCompl 3) S :=
    isPiSubgroup_piCompl_sup hθ3 hM3 ((hθX.trans hXC).trans hCM)
  have hSP : S ≤ P := sup_le (hθX.trans le_sup_right) le_sup_left
  have hPS : P ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (le_sup_right.trans Subgroup.le_normalizer) (le_normalizer_sup hXθ (hXC.trans hCM))
  have hPC : P ≤ C := sup_le (pPrimeCoreOf_le 3 C) hXC
  have hSO : S ≤ pPrimeCoreOf 3 P :=
    le_pPrimeCoreOf hSP hPS ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three S).mp hS3))
  have hOM : pPrimeCoreOf 3 P ≤ M :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 P).trans hPC)
      (hnorm.trans (normalizer_le_normalizer_pPrimeCoreOf 3 P)) (coprime_card_pPrimeCoreOf 3 P)
  exact le_sup_left.trans (hSO.trans hOM)

theorem card_of_isTripleCover_a6 {Q : Type*} [Group Q] [Finite Q]
    (h : Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) : Nat.card Q = 1080 := by
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [card_of_isTripleCover h, hA6]

theorem residual_facts
    (h : Conf1515HJ A c L L)
    (hfree : ∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) :
    Group.IsPerfect ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ∧
      Sec4.IsTripleCover ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))
        (alternatingGroup (Fin 6)) ∧
      IsQuasisimple ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ∧
      Nat.card (Subgroup.center
        ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) = 3 ∧
      d ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) =
        oPrimeResidualOf 3 (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        delta A (lB A) (Subgroup.centralizer ({d} : Set G)) := by
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  set X₀ := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hX₀
  have hdL : d ∈ L := Proof15Res4.mem_of_isZCentral hdZ
  have hB := h.isHyperplane hdA hd1 hdL
  have hc := h.isLBConfig hdZ
  obtain ⟨-, -, hq, hZ3, -, htc, -⟩ := Item148HJ.resProj_facts hS hB hc
  have hinj : Function.Injective (Item148HJ.resProj L d) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro j hj
    have h1 := (Item148HJ.mem_ker_resProj j).mp hj
    have hjL : (j : G) ∈ L := Item148HJ.residual_le L d j.2
    have hjd : (j : G) ∈ Subgroup.centralizer ({d} : Set G) :=
      Item148HJ.residual_le_centralizer_singleton L d j.2
    have hjO : (j : G) ∈ CFSG.Open.pCoreOf 2 L := h.inf_theta_le_pCoreOf ⟨⟨hjL, hjL⟩, h1⟩
    have hj0 : (j : G) ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨hjO, hjd⟩
    rw [hfree d hdA hd1 hdZ, Subgroup.mem_bot] at hj0
    exact (Subgroup.mem_bot).mpr (Subtype.ext hj0)
  let e : ↥X₀ ≃* ↥(Item148HJ.resProj L d).range := MonoidHom.ofInjective hinj
  have hdX₀ : d ∈ X₀ := Item148HJ.inf_le_residual hS hB hc ⟨hdA, hdL⟩
  have hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G) := by
    have hAC : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := fun a ha =>
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hdA))
    exact (Late.le_normalizer_inf hD.le_normalizer hAC).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hX₀3 : X₀ = oPrimeResidualOf 3 X₀ :=
    Sec17.Proof171Steps.residual_eq_oPrimeResidualOf hS hB hc
  have hzX : zHJ L L d = X₀ := by
    rw [zHJ, inf_idem]
    exact hX₀3.symm
  have hmap : (X₀.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
    hzX ▸ h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL₂, S3, hdS, hSd⟩ := Proof15Res7.exists_sylow_of_isZCentral hdZ
  have hΔ := Proof15Res7.le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL ⟨S3, hdS, hSd⟩
    (Item148HJ.residual_le L d) hAX₀ hmap
  refine ⟨Item148HJ.residual_isPerfect L d, KFacts.KS14.isTripleCover_congr e.symm htc,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, hdX₀, hX₀3,
    hΔ.trans (delta_mono (Item148HJ.residual_le_centralizer_singleton L d))⟩
  rw [← hZ3, ← Subgroup.map_center_eq e]
  exact (Subgroup.card_map_of_injective (f := (e : ↥X₀ →* ↥(Item148HJ.resProj L d).range))
    e.injective).symm

theorem inf_pPrimeCoreOf_eq_bot {X₀ C : Subgroup G} (hX₀C : X₀ ≤ C)
    (hq : IsQuasisimple ↥X₀) (hZ3 : Nat.card (Subgroup.center ↥X₀) = 3) :
    X₀ ⊓ pPrimeCoreOf 3 C = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := pPrimeCoreOf 3 C with hM
  set V : Subgroup ↥X₀ := (X₀ ⊓ M).subgroupOf X₀ with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (Late.le_normalizer_inf Subgroup.le_normalizer (hX₀C.trans (le_normalizer_pPrimeCoreOf 3 C)))
  have hV3 : ¬ 3 ∣ Nat.card V := by
    rw [hV, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X₀ ⊓ M ≤ X₀)).toEquiv]
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
      (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hVb := Item148HJ.eq_bot_of_normal_of_quasisimple hq hZ3 hVn hV3
  rw [eq_bot_iff]
  intro x hx
  have hxV : (⟨x, hx.1⟩ : ↥X₀) ∈ V := Subgroup.mem_subgroupOf.mpr hx
  rw [hVb, Subgroup.mem_bot] at hxV
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxV)

end Proof15Res11

end CFSG.RankThree.PartTwo.Sec15
