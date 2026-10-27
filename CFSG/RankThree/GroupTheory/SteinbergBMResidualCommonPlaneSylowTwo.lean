module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralizedSylowTwo
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaMixedBalance
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_thetaT {p : ℕ} {B : Subgroup G} {g : G}
    (hg : ∀ b ∈ B, b ≠ 1 → g ∈ normalizer
      (inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)) : Set G)) :
    g ∈ normalizer (thetaT p B : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [thetaT, mem_iInf]
  exact ⟨fun hx b hb hb1 => (mem_normalizer_iff.mp (hg b hb hb1) x).mp (hx b hb hb1),
    fun hx b hb hb1 => (mem_normalizer_iff.mp (hg b hb hb1) x).mpr (hx b hb hb1)⟩

theorem thetaT_le_inSubgroup {p : ℕ} {B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    thetaT p B ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)) := by
  intro x hx
  simp only [thetaT, mem_iInf] at hx
  exact hx b hb hb1

theorem exists_isSylowOf_two_invariant_le [Finite G] {p : ℕ} (hp : p.Prime)
    {A X U : Subgroup G} (hA : IsPGroup p A) (hX : ¬ p ∣ Nat.card X)
    (hAX : A ≤ normalizer (X : Set G)) (hUX : U ≤ X) (hU2 : IsPGroup 2 U)
    (hAU : A ≤ normalizer (U : Set G)) :
    ∃ V : Subgroup G, ABGLocalTools.IsSylowOf 2 V X ∧ U ≤ V ∧ A ≤ normalizer (V : Set G) := by
  let : MulDistribMulAction A X := MulDistribMulAction.compHom X (Subgroup.inclusion hAX)
  have hsmul : ∀ (a : A) (x : X), ((a • x : X) : G) = a * x * (a : G)⁻¹ := fun _ _ => rfl
  have hcop : Nat.Coprime p (Nat.card X) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hX
  have hU2' : IsPGroup 2 (U.subgroupOf X) := hU2.of_equiv (subgroupOfEquivOfLe hUX).symm
  have hUinv : ∀ a : A, ∀ x ∈ U.subgroupOf X, a • x ∈ U.subgroupOf X := fun a x hx => by
    rw [mem_subgroupOf, hsmul]
    exact (mem_normalizer_iff.mp (hAU a.2) x).mp hx
  obtain ⟨P, hUP, hPinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p 2 hp
    Nat.prime_two hA hcop _ hU2' hUinv
  refine ⟨(P : Subgroup X).map X.subtype, ⟨P, rfl⟩, fun u hu => ⟨⟨u, hUX hu⟩, hUP hu, rfl⟩, ?_⟩
  refine le_normalizer_of_forall_conj_mem fun a ha g hg => ?_
  obtain ⟨x, hx, rfl⟩ := hg
  have heq : (⟨a, ha⟩ : A) • (P : Subgroup X) = (P : Subgroup X) := by
    rw [← Sylow.pointwise_smul_def, hPinv]
  refine ⟨(⟨a, ha⟩ : A) • x, ?_, hsmul _ _⟩
  rw [← heq]
  exact Subgroup.smul_mem_pointwise_smul x _ _ hx

theorem commutator_eq_bot_of_isSylowOf_two [Finite G] {p : ℕ} (hp : p.Prime)
    {A N T U : Subgroup G} (hA : IsPGroup p A) (hN : ¬ p ∣ Nat.card N)
    (hAN : A ≤ normalizer (N : Set G)) (hT : ABGLocalTools.IsSylowOf 2 T N) (hTA : ⁅T, A⁆ = ⊥)
    (hUN : U ≤ N) (hU2 : IsPGroup 2 U) (hAU : A ≤ normalizer (U : Set G)) : ⁅U, A⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hT
  let : MulDistribMulAction A N := MulDistribMulAction.compHom N (Subgroup.inclusion hAN)
  have hsmul : ∀ (a : A) (x : N), ((a • x : N) : G) = a * x * (a : G)⁻¹ := fun _ _ => rfl
  have hTc := commutator_eq_bot_iff_le_centralizer.mp hTA
  have hQfix : ∀ a : A, ∀ x ∈ (Q : Subgroup N), a • x = x := by
    intro a x hx
    apply Subtype.ext
    have hxT : (x : G) ∈ T := by
      rw [← hQ]
      exact mem_map_of_mem _ hx
    rw [hsmul, (mem_centralizer_iff.mp (hTc hxT) a a.2), mul_inv_cancel_right]
  have hU2' : IsPGroup 2 (U.subgroupOf N) := hU2.of_equiv (subgroupOfEquivOfLe hUN).symm
  have hUinv : ∀ a : A, ∀ x ∈ U.subgroupOf N, a • x ∈ U.subgroupOf N := fun a x hx => by
    rw [mem_subgroupOf, hsmul]
    exact (mem_normalizer_iff.mp (hAU a.2) x).mp hx
  have hfix := centralized_sylow_two_controls_invariant_two_subgroups hA hN Q hQfix
    (U.subgroupOf N) hU2' hUinv
  rw [commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [mem_centralizer_iff]
  intro a ha
  have h := congrArg Subtype.val (hfix ⟨a, ha⟩ ⟨u, hUN hu⟩ hu)
  rw [hsmul] at h
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h]

theorem le_inSubgroup_aschbacherSolvableCore_of_residual [Finite G] (hZ : center G = ⊥)
    {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hres : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ K : Subgroup G, D ≤ K → K ≠ ⊤ →
      ∀ t : K, (t : G) ∈ D → t ≠ 1 →
        CFSG.Quasithin.twoPrimeResidual
            (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set K)), D.subgroupOf K⁆ ⊔
              thetaT p (D.subgroupOf K)) ≤ aschbacherSolvableCore p K)
    {B : Subgroup G} (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hUA : U ≤ centralizer (A : Set G)) (hUB : U ≤ thetaT p B)
    {d : G} (hd : d ∈ A) (hd1 : d ≠ 1) :
    U ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({d} : Set G)) := by
  set K := centralizer ({d} : Set G) with hK
  have hKtop : K ≠ ⊤ := by
    intro h
    refine hd1 ((Subgroup.eq_bot_iff_forall _).mp hZ d (mem_center_iff.mpr fun g => ?_))
    have hg : g ∈ K := by
      rw [h]
      exact mem_top g
    exact mem_centralizer_singleton_iff.mp hg
  have hBK : B ≤ K := fun x hx => mem_centralizer_singleton_iff.mpr (hAcomm x (hBA hx) d hd)
  have hUK : U ≤ K := fun u hu =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hUA hu) d hd).symm
  have hB0 : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB
    have := hp.two_le
    nlinarith
  obtain ⟨⟨t, htB⟩, ht1⟩ := ne_bot_iff_exists_ne_one.mp hB0
  have ht1'' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht1' : (⟨t, hBK htB⟩ : K) ≠ 1 := fun h => ht1'' (congrArg Subtype.val h)
  have hUT : U.subgroupOf K ≤ thetaT p (B.subgroupOf K) := by
    intro x hx
    simp only [thetaT, mem_iInf]
    rintro ⟨b, hbK⟩ hb hb1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    rw [← mem_map_iff_mem K.subtype_injective, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      RankThreeEvenClassification.Helpers.thetaCoreOf_element_centralizer_subtype_map p hp K b hbK]
    refine RankThreeEvenClassification.Helpers.theta_element_centralizer_intersection_le p hp K b
      ⟨x.2, ?_⟩
    rw [← inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact thetaT_le_inSubgroup (B := B) (b := b) hb hb1' (hUB hx)
  have hU2' : IsPGroup 2 (U.subgroupOf K) := hU2.of_equiv (subgroupOfEquivOfLe hUK).symm
  have hUres : U.subgroupOf K ≤ aschbacherSolvableCore p K := by
    refine le_trans ?_ (hres B hBA hB K hBK hKtop ⟨t, hBK htB⟩ htB ht1')
    unfold CFSG.Quasithin.twoPrimeResidual
    exact le_iInf₂ fun N hN => SteinbergBY.le_of_isPGroup_two_of_odd_relIndex hU2'
      (hUT.trans le_sup_right) hN.1 hN.2.1 hN.2.2
  intro u hu
  exact mem_map_of_mem K.subtype (x := ⟨u, hUK hu⟩) (hUres hu)

theorem residual_common_plane_core_sylow_two [Finite G] (hZ : center G = ⊥) {p : ℕ}
    (hp : p.Prime) {A : Subgroup G} (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hres : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ K : Subgroup G, D ≤ K → K ≠ ⊤ →
      ∀ t : K, (t : G) ∈ D → t ≠ 1 →
        CFSG.Quasithin.twoPrimeResidual
            (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set K)), D.subgroupOf K⁆ ⊔
              thetaT p (D.subgroupOf K)) ≤ aschbacherSolvableCore p K)
    (hsyl : ∀ c ∈ A, c ≠ 1 → ∃ T : Subgroup G, ABGLocalTools.IsSylowOf 2 T
      (inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G))) ∧ ⁅T, A⁆ = ⊥) :
    (∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 →
      A ≤ normalizer (thetaT p D : Set G) ∧ Group.IsSolvable (thetaT p D) ∧
        thetaT p D ≤ centralizer (D : Set G) ∧
        centralizer (D : Set G) ≤ normalizer (thetaT p D : Set G) ∧
        ¬ p ∣ Nat.card (thetaT p D)) ∧
    (∀ c ∈ A, c ≠ 1 → ∀ U : Subgroup G,
      U ≤ inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G)) →
      IsPGroup 2 U → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = ⊥) ∧
    (∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ S : Subgroup G,
      ABGLocalTools.IsSylowOf 2 S (thetaT p B) → A ≤ normalizer (S : Set G) →
      ⁅S, A⁆ = ⊥ ∧ ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 →
        ABGLocalTools.IsSylowOf 2 S (thetaT p D)) := by
  have := hA
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hθsolv : ∀ H : Subgroup G, Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) H) :=
    fun H => by
      rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
      exact RankThreeEvenClassification.Helpers.thetaCoreOf_solvable p hp H
  have hθcop : ∀ H : Subgroup G, ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) H) :=
    fun H => by
      rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
      exact RankThreeEvenClassification.Helpers.thetaCoreOf_prime_complement p hp H
  have hθN : ∀ H : Subgroup G, H ≤ normalizer
      (inSubgroup (aschbacherSolvableCore p) H : Set G) := fun H =>
    le_normalizer.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p H)
  have hCN : ∀ c : G, centralizer ({c} : Set G) ≤ normalizer (zpowers c : Set G) := fun c => by
    rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact centralizer_le_normalizer _
  have hθCN : ∀ c : G, inSubgroup (aschbacherSolvableCore p) (centralizer ({c} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G)) := fun c => by
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    refine RankThreeEvenClassification.Helpers.thetaCoreOf_mono_of_normal p hp _ _ (hCN c) ?_
    refine (normal_subgroupOf_iff_le_normalizer (hCN c)).mpr ?_
    rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _
  have hAθ : ∀ c ∈ A, A ≤ normalizer
      (inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G)) : Set G) :=
    fun c hc x hx =>
      hθN _ (hCN c (mem_centralizer_singleton_iff.mpr (hAcomm x hx c hc)))
  have h2 : ∀ c ∈ A, c ≠ 1 → ∀ U : Subgroup G,
      U ≤ inSubgroup (aschbacherSolvableCore p) (normalizer (zpowers c : Set G)) →
      IsPGroup 2 U → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = ⊥ := by
    intro c hc hc1 U hU hU2 hAU
    obtain ⟨T, hT, hTA⟩ := hsyl c hc hc1
    exact commutator_eq_bot_of_isSylowOf_two hp hAp (hθcop _) (hAθ c hc) hT hTA hU hU2 hAU
  have h1 : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 →
      A ≤ normalizer (thetaT p D : Set G) ∧ Group.IsSolvable (thetaT p D) ∧
        thetaT p D ≤ centralizer (D : Set G) ∧
        centralizer (D : Set G) ≤ normalizer (thetaT p D : Set G) ∧
        ¬ p ∣ Nat.card (thetaT p D) := by
    intro D hDA hD
    have hD0 : D ≠ ⊥ := fun h => by
      rw [h, card_bot] at hD
      have := hp.two_le
      nlinarith
    obtain ⟨⟨d₀, hd₀⟩, hd₀1⟩ := ne_bot_iff_exists_ne_one.mp hD0
    have hd₀1' : d₀ ≠ 1 := fun h => hd₀1 (Subtype.ext h)
    have hle := thetaT_le_inSubgroup (p := p) hd₀ hd₀1'
    have hCD : centralizer (D : Set G) ≤ normalizer (thetaT p D : Set G) := fun g hg =>
      mem_normalizer_thetaT fun b hb _ => hθN _ (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hg b hb).symm)
    refine ⟨fun x hx => hCD (mem_centralizer_iff.mpr fun b hb => hAcomm b (hDA hb) x hx), ?_,
      SteinbergBY.thetaT_le_centralizer p D, hCD,
      fun h => hθcop _ (h.trans (card_dvd_of_le hle))⟩
    have := hθsolv (centralizer ({d₀} : Set G))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hcent : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ U : Subgroup G,
      U ≤ thetaT p D → IsPGroup 2 U → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = ⊥ := by
    intro D hDA hD U hUD hU2 hAU
    have hD0 : D ≠ ⊥ := fun h => by
      rw [h, card_bot] at hD
      have := hp.two_le
      nlinarith
    obtain ⟨⟨d₀, hd₀⟩, hd₀1⟩ := ne_bot_iff_exists_ne_one.mp hD0
    have hd₀1' : d₀ ≠ 1 := fun h => hd₀1 (Subtype.ext h)
    exact h2 d₀ (hDA hd₀) hd₀1' U
      ((hUD.trans (thetaT_le_inSubgroup hd₀ hd₀1')).trans (hθCN d₀)) hU2 hAU
  have htrans : ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ U : Subgroup G,
      IsPGroup 2 U → U ≤ centralizer (A : Set G) → U ≤ thetaT p B →
      ∀ D : Subgroup G, D ≤ A → U ≤ thetaT p D := by
    intro B hBA hB U hU2 hUA hUB D hDA x hx
    simp only [thetaT, mem_iInf]
    intro d hd hd1
    exact le_inSubgroup_aschbacherSolvableCore_of_residual hZ hp hAcomm hres hBA hB hU2 hUA hUB
      (hDA hd) hd1 hx
  refine ⟨h1, h2, fun B hBA hB S hS hAS => ?_⟩
  obtain ⟨Q, hQ⟩ := hS
  have hS2 : IsPGroup 2 S := hQ ▸ Q.isPGroup'.map _
  have hSB : S ≤ thetaT p B := hQ ▸ map_subtype_le _
  have hSA : ⁅S, A⁆ = ⊥ := hcent B hBA hB S hSB hS2 hAS
  have hSAc := commutator_eq_bot_iff_le_centralizer.mp hSA
  refine ⟨hSA, fun D hDA hD => ?_⟩
  obtain ⟨hAD, -, -, -, hDcop⟩ := h1 D hDA hD
  obtain ⟨V, ⟨P, hP⟩, hSV, hAV⟩ := exists_isSylowOf_two_invariant_le hp hAp hDcop hAD
    (htrans B hBA hB S hS2 hSAc hSB D hDA) hS2 hAS
  have hV2 : IsPGroup 2 V := hP ▸ P.isPGroup'.map _
  have hVD : V ≤ thetaT p D := hP ▸ map_subtype_le _
  have hVA := commutator_eq_bot_iff_le_centralizer.mp (hcent D hDA hD V hVD hV2 hAV)
  have hVB : V ≤ thetaT p B := htrans D hDA hD V hV2 hVA hVD B hBA
  have hQV : (Q : Subgroup (thetaT p B)) ≤ V.subgroupOf (thetaT p B) := fun x hx =>
    hSV (show (x : G) ∈ S from hQ ▸ mem_map_of_mem _ hx)
  have hVQ := Q.is_maximal' (hV2.of_equiv (subgroupOfEquivOfLe hVB).symm) hQV
  have hVS : V = S := by
    rw [← hQ, ← hVQ, map_subgroupOf_eq_of_le hVB]
  exact ⟨P, hP.trans hVS⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
