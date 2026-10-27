module

public import CFSG.Milestones.ASVolI.A1
public import CFSG.Quasithin.Background.A4Four
import CFSG.Quasithin.Background.A4Reduced

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.ASVolI.ChA
open scoped Pointwise

namespace ChA

section SignalizerVocabulary

variable {G : Type} [Group G]

@[expose] def IsTwoSignalizer (M X R : Subgroup G) : Prop :=
  R ≤ M ∧ IsPGroup 2 R ∧ X ≤ ChA.normalizerOf R

@[expose] def IsMaxTwoSignalizer (M X R : Subgroup G) : Prop :=
  IsTwoSignalizer M X R ∧ ∀ S : Subgroup G, IsTwoSignalizer M X S → R ≤ S → S = R

@[expose] def InClassX (Y : Subgroup G) : Prop :=
  Y ≠ ⊥ ∧ oResidual {2} Y = Y ∧ quasithinGenFitting Y = pCoreOf 2 Y

@[expose] def VYR (Y R : Subgroup G) : Subgroup G :=
  ⁅omegaOne 2 (centerOf R), Y⁆

@[expose] def VY (Y : Subgroup G) : Subgroup G :=
  VYR Y (pCoreOf 2 Y)

@[expose] def InClassXf (Y : Subgroup G) : Prop :=
  InClassX Y ∧ VY Y ≠ ⊥

end SignalizerVocabulary

end ChA

@[expose] def A_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X M : Subgroup G),
    oResidual {2} X = X → CFSG.Open.IsSubnormal X M →
    (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → (IsTwoSignalizer M X R ↔ ⁅X, R⁆ ≤ R)) ∧
    (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → (R : Set G) * (X : Set G) = (X : Set G) * (R : Set G) →
      oResidual {2} (X ⊔ R) = X ∧ (X.subgroupOf (X ⊔ R)).Normal) ∧
    (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → IsTwoSignalizer M X R → ⁅X, R⁆ ≤ pCoreOf 2 X) ∧
    (∀ S : Subgroup G, IsMaxTwoSignalizer M X S ↔
      IsSylowIn 2 S (CFSG.Quasithin.centralizerSection M X (pCoreOf 2 X))) ∧
    (∀ T : Subgroup G, IsSylowIn 2 T (M ⊓ ChA.normalizerOf X) →
      IsMaxTwoSignalizer M X (pCoreOf 2 (X ⊔ T))) ∧
    (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → IsMaxTwoSignalizer M X R →
      (Odd ((M ⊓ ChA.normalizerOf R).relIndex (ChA.normalizerOf R)) → R = pCoreOf 2 (ChA.normalizerOf R)) ∧
      (ChA.normalizerOf R ≤ M → IsMaxTwoSignalizer ⊤ X R)) ∧
    ((X.subgroupOf M).Normal → ∀ T : Subgroup G, IsSylowIn 2 T M →
      ∀ R : Subgroup G, R = pCoreOf 2 (X ⊔ T) → ChA.normalizerOf R ≤ M →
        IsSylowIn 2 R (CFSG.Quasithin.centralizerSection ⊤ X (pCoreOf 2 X)) ∧
        (∀ S : Subgroup G, IsSylowIn 2 S (CFSG.Quasithin.centralizerSection ⊤ X (pCoreOf 2 X)) →
          IsMaxTwoSignalizer ⊤ X S) ∧
        IsMaxTwoSignalizer ⊤ X R ∧ IsMaxTwoSignalizer M X R ∧
        IsSylowIn 2 R (CFSG.Quasithin.centralizerSection M X (pCoreOf 2 X)) ∧
        R = pCoreOf 2 (ChA.normalizerOf R) ∧
        IsSylowIn 2 R (CFSG.Quasithin.conjClosure R M))

section Bridge

variable {G : Type} [Group G]

private theorem a4_oResidual_two_eq_oTwoUpper [Finite G] (X : Subgroup G) :
    oResidual {2} X = CFSG.Quasithin.oTwoUpper X := by
  apply le_antisymm
  · refine iInf₂_le (CFSG.Quasithin.oTwoUpper X) ⟨CFSG.Quasithin.oTwoUpper_le X,
      Subgroup.normal_subgroupOf_of_le_normalizer (CFSG.Quasithin.le_normalizer_oTwoUpper X),
      fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := CFSG.Quasithin.exists_pow_mem_oTwoUpper X hx
    refine ⟨2 ^ k, by positivity, fun q hq hqk => ?_, hk⟩
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqk)
  · refine le_iInf₂ fun N hN => CFSG.Quasithin.oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨m, hm0, hmq, hxm⟩ := hN.2.2 x hx
    have hm : m = 2 ^ m.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hm0.ne' fun {d} hd hdm => hmq d hd hdm
    exact ⟨_, hm ▸ hxm⟩

private theorem a4_inClassX_iff [Finite G] (Y : Subgroup G) :
    InClassX Y ↔ CFSG.Quasithin.IsXClass Y := by
  unfold InClassX CFSG.Quasithin.IsXClass
  rw [a4_oResidual_two_eq_oTwoUpper, eq_comm (a := CFSG.Quasithin.oTwoUpper Y),
    CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff Y 2]
  rfl

private theorem a4_inClassXf_iff [Finite G] (Y : Subgroup G) :
    InClassXf Y ↔ CFSG.Quasithin.IsXf Y := by
  unfold InClassXf CFSG.Quasithin.IsXf
  rw [a4_inClassX_iff]
  rfl

private theorem a4_isMaxTwoSignalizer_iff {M X R : Subgroup G} :
    IsMaxTwoSignalizer M X R ↔ CFSG.Quasithin.IsMaxSignalizer M X R :=
  CFSG.Quasithin.isMaxSignalizer_iff.symm

private theorem a4_eq_oTwoUpper_of_oResidual [Finite G] {X : Subgroup G} (hX : oResidual {2} X
    = X) :
    X = CFSG.Quasithin.oTwoUpper X := by
  rw [← a4_oResidual_two_eq_oTwoUpper]
  exact hX.symm

private theorem a4_isTwoReduced_iff (M V : Subgroup G) :
    IsTwoReduced M V ↔ CFSG.Quasithin.IsTwoReducedIn M V := by
  constructor
  · rintro ⟨hVM, hVn, hel, h⟩
    have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp hVn
    refine ⟨hVM, hMV, hel, fun D hDM hMD hD => ?_⟩
    set K : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hK
    have hKM : M ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
      CFSG.Quasithin.A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
        (CFSG.Quasithin.A4.mem_normalizer_centralizer (hMV hg))
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := hDM.trans hKM
    have hN : K ⊔ D ≤ M := sup_le inf_le_left hDM
    have key := h (K ⊔ D) le_sup_left hN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hKM hg, hMD hg⟩) ?_
    · exact le_sup_right.trans (key.trans inf_le_right)
    · intro x hx
      have hx' : x ∈ (↑K : Set G) * (↑D : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K D hDK]
        exact hx
      obtain ⟨c, hc, d, hd, rfl⟩ := hx'
      obtain ⟨k, hk⟩ := hD d hd
      obtain ⟨c', hc', hcd⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq hc (hDK hd) (2 ^ k)
      refine ⟨k, ?_⟩
      rw [hcd]
      exact K.mul_mem hc' ⟨M.pow_mem (hDM hd) _, hk⟩
  · rintro ⟨hVM, hMV, hel, h⟩
    refine ⟨hVM, Subgroup.normal_subgroupOf_of_le_normalizer hMV, hel,
      fun N hKN hNM hNn hN => ?_⟩
    have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
    have := h N hNM hMN fun d hd => by
      obtain ⟨k, hk⟩ := hN d hd
      exact ⟨k, hk.2⟩
    exact le_inf hNM this

private theorem a4_twoReducedProduct_eq (M : Subgroup G) :
    twoReducedProduct M = CFSG.Quasithin.twoReducedJoin M := by
  unfold twoReducedProduct CFSG.Quasithin.twoReducedJoin
  rw [sSup_eq_iSup]
  simp only [Set.mem_setOf_eq, a4_isTwoReduced_iff]

end Bridge

section Transport

variable {K : Type*} [Group K] {Q : Type*} [Group Q]

private theorem a4_pCore_le_center_of_equiv {A : Subgroup K} (e : Q ≃* ↥A)
    (h : CFSG.Open.pCoreOf 2 A ≤ CFSG.Quasithin.centerOf A) :
    CFSG.pCore 2 Q ≤ Subgroup.center Q := by
  intro q hq
  have h1 : e q ∈ CFSG.pCore 2 ↥A := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact ⟨q, hq, rfl⟩
  have h2 : ((e q : ↥A) : K) ∈ CFSG.Open.pCoreOf 2 A := ⟨e q, h1, rfl⟩
  have h3 := (h h2).2
  rw [Subgroup.mem_center_iff]
  intro q'
  apply e.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp h3 (e q') (e q').2

private theorem a4_pCore_eq_bot_of_equiv {A : Subgroup K} (e : Q ≃* ↥A)
    (h : CFSG.Open.pCoreOf 2 A = ⊥) : CFSG.pCore 2 Q = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  have h1 : e q ∈ CFSG.pCore 2 ↥A := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact ⟨q, hq, rfl⟩
  have h2 : ((e q : ↥A) : K) ∈ CFSG.Open.pCoreOf 2 A := ⟨e q, h1, rfl⟩
  rw [h, Subgroup.mem_bot] at h2
  have h3 : e q = 1 := Subtype.ext h2
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h3, map_one])

end Transport

section AutOn

variable {G : Type} [Group G]

private theorem a4_exists_equiv_autOn (X V : Subgroup G) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    {Q : Type} [Group Q] (π : ↥X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = (centralizerOf V).subgroupOf X) :
    Nonempty (Q ≃* ↥(CFSG.Quasithin.autOn X V)) := by
  set act := CFSG.Quasithin.A4.actionOn V X hXV with hact
  have hrange : act.range = CFSG.Quasithin.autOn X V := by
    ext a
    rw [MonoidHom.mem_range, CFSG.Quasithin.A4.mem_autOn_iff hXV]
  have hkerA : act.ker = (centralizerOf V).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, CFSG.Quasithin.A4.actionOn_eq_one_iff hXV, Subgroup.mem_subgroupOf]
    rfl
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hker.trans hkerA.symm)).trans
      ((QuotientGroup.quotientKerEquivRange act).trans (MulEquiv.subgroupCongr hrange)))⟩

end AutOn

theorem as_A_4_2 : A_4_2 := by
  intro G _ _ X M hX hXM
  have hX' : X = CFSG.Quasithin.oTwoUpper X := a4_eq_oTwoUpper_of_oResidual hX
  have h4 : ∀ S : Subgroup G, IsMaxTwoSignalizer M X S ↔
      IsSylowIn 2 S (CFSG.Quasithin.centralizerSection M X (pCoreOf 2 X)) := fun S =>
    (a4_isMaxTwoSignalizer_iff).trans (CFSG.Quasithin.a4_2_4 hX' hXM S)
  refine ⟨fun R hRM hR => CFSG.Quasithin.a4_2_1 (X := X) (M := M) hRM hR, ?_,
    fun R _ _ hR => CFSG.Quasithin.a4_2_3 hX' hXM hR, h4,
    fun T hT => a4_isMaxTwoSignalizer_iff.mpr (CFSG.Quasithin.a4_2_5 hX' hXM hT), ?_, ?_⟩
  · intro R hRM hR hRX
    obtain ⟨h1, h2⟩ := CFSG.Quasithin.a4_2_2 hX' hXM hRM hR hRX
    exact ⟨by rw [a4_oResidual_two_eq_oTwoUpper]; exact h1.symm, h2⟩
  · intro R _ _ hR
    exact ⟨fun hodd => CFSG.Quasithin.a4_2_6_1 (a4_isMaxTwoSignalizer_iff.mp hR) hodd,
      fun hN => a4_isMaxTwoSignalizer_iff.mpr
        (CFSG.Quasithin.a4_2_6_2 (a4_isMaxTwoSignalizer_iff.mp hR) hN)⟩
  · intro hXN T hT R hR hNR
    obtain ⟨a, b, c, d, e, f⟩ :=
      CFSG.Quasithin.a4_2_7 hX' (CFSG.Quasithin.A4.subnormal_le hXM) hXN hT hR hNR
    exact ⟨a, fun S hS => a4_isMaxTwoSignalizer_iff.mpr (b S hS),
      a4_isMaxTwoSignalizer_iff.mpr (b R a), a4_isMaxTwoSignalizer_iff.mpr c, (d R).mp c, e, f⟩

@[expose] def A_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X M Y : Subgroup G),
    oResidual {2} X = X → CFSG.Open.IsSubnormal X M → Y ≤ M →
    Y = (X ⊓ Y) ⊔ pCoreOf 2 Y → X = (Y ⊓ X) ⊔ pCoreOf 2 X →
    ((∀ B : Subgroup G, IsTwoSignalizer M Y B →
        B ≤ CFSG.Quasithin.centralizerSection M X (pCoreOf 2 X)) ∧
      Y ≤ M ⊓ ChA.normalizerOf X) ∧
    (∀ B : Subgroup G, IsMaxTwoSignalizer M Y B → IsMaxTwoSignalizer M X B)

theorem as_A_4_3 : A_4_3 := by
  intro G _ _ X M Y hX hXM hYM hY hX2
  have hX' : X = CFSG.Quasithin.oTwoUpper X := a4_eq_oTwoUpper_of_oResidual hX
  have hYs : (Y : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (pCoreOf 2 Y : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (X ⊓ Y) (pCoreOf 2 Y)
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))]
    exact congrArg (fun S : Subgroup G => (S : Set G)) hY
  have hXs : (X : Set G) = ((Y ⊓ X : Subgroup G) : Set G) * (pCoreOf 2 X : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Y ⊓ X) (pCoreOf 2 X)
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))]
    exact congrArg (fun S : Subgroup G => (S : Set G)) hX2
  exact ⟨CFSG.Quasithin.a4_3_1 hX' hXM hYM hYs hXs, fun B hB =>
    a4_isMaxTwoSignalizer_iff.mpr (CFSG.Quasithin.a4_3_2 hX' hXM hYM hYs hXs
      (a4_isMaxTwoSignalizer_iff.mp hB))⟩

@[expose] def A_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K X : Subgroup G),
    pCoreOf 2 H ≤ X → X ≤ H ⊓ K → CFSG.Quasithin.A44Hyp H X →
    pCoreOf 2 H = pCoreOf 2 (H ⊓ K) ∧
    (IsMaxTwoLocalSubgroup H → CFSG.Quasithin.CKQ K (pCoreOf 2 (H ⊓ K)) ≤ H ⊓ K) ∧
    (IsMaxTwoLocalSubgroup H → IsMaxTwoLocalSubgroup K →
      (CFSG.Quasithin.O2Fstar ↥K).map K.subtype ≤ H → H = K)

theorem as_A_4_4 : A_4_4 := by
  intro G _ _ H K X h1 h2 h3
  exact ⟨(CFSG.Quasithin.a4_4_1 h1 h2 h3).symm, fun hH => CFSG.Quasithin.a4_4_2 h1 h2 h3 hH,
    fun hH hK hFK => CFSG.Quasithin.a4_4_3 h1 h2 h3 hH hK hFK⟩

@[expose] def A_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y R : Subgroup G), InClassX Y →
    IsTwoSignalizer (ChA.normalizerOf Y) Y R →
    VYR Y R ≤ Y ⊓ omegaOne 2 (centerOf R) ∧ VYR Y R = ⁅VYR Y R, Y⁆

theorem as_A_4_6 : A_4_6 := by
  intro G _ _ Y R hY hR
  exact ⟨CFSG.Quasithin.VYR_le_inf (Y := Y) (R := R) hR,
    CFSG.Quasithin.VYR_eq_commutator (Y := Y) (R := R) ((a4_inClassX_iff Y).mp hY).2.1 hR⟩

@[expose] def A_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), InClassX Y →
    IsTwoSignalizer (ChA.normalizerOf Y) Y (pCoreOf 2 Y)

theorem as_A_4_7 : A_4_7 := by
  intro G _ _ Y _
  exact CFSG.Quasithin.A4.isSignalizer_pCoreOf Y

@[expose] def A_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X M R S : Subgroup G),
    InClassX X → CFSG.Open.IsSubnormal X M → IsTwoSignalizer M X R → IsTwoSignalizer M X S →
    VYR X S ≤ R → R ≤ S → pCoreOf 2 X ≤ S →
    (pCoreOf 2 X ≤ centralizerOf (VY X) ∧ ⁅⁅R, X⁆, VY X⁆ = ⊥) ∧
    (∀ (Q : Type) (_ : Group Q) (π : ↥X →* Q), Function.Surjective π →
      π.ker = (centralizerOf (VY X)).subgroupOf X →
      (CFSG.Quasithin.NoncentralTwoChiefFactorsInO2 X → pCore 2 Q ≤ Subgroup.center Q) ∧
      (CFSG.Quasithin.TwoChiefFactorsInO2 X → pCore 2 Q = ⊥)) ∧
    VYR X S = ⁅VYR X R ⊓ centralizerOf S, X⁆ ∧
    VYR X S = ⁅VY X ⊓ centralizerOf S, X⁆ ∧
    (VYR X S ≠ ⊥ ↔ VY X ≠ ⊥)

theorem as_A_4_8 : A_4_8 := by
  intro G _ _ X M R S hX hXM hR hS hVR hRS hO
  have hX' : CFSG.Quasithin.IsXClass X := (a4_inClassX_iff X).mp hX
  have hh : CFSG.Quasithin.A48Hyp X M R S := ⟨hX', hXM, hR, hS, hVR, hRS, hO⟩
  refine ⟨⟨CFSG.Quasithin.A4.pCoreOf_le_centralizer_VY X, ?_⟩, ?_,
    CFSG.Quasithin.a4_8_3 hh, CFSG.Quasithin.a4_8_4 hh, CFSG.Quasithin.a4_8_5 hh⟩
  · have h1 : ⁅R, X⁆ ≤ Subgroup.centralizer (CFSG.Quasithin.VY X : Set G) :=
      (Subgroup.commutator_comm R X).le.trans
        ((CFSG.Quasithin.a4_2_3 hX'.2.1 hXM hR).trans
          (CFSG.Quasithin.A4.pCoreOf_le_centralizer_VY X))
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
  · intro Q _ π hπ hker
    obtain ⟨e⟩ := a4_exists_equiv_autOn X (VY X) (CFSG.Quasithin.A4.normalizer_VY X) π hπ hker
    exact ⟨fun hc => a4_pCore_le_center_of_equiv e (CFSG.Quasithin.a4_8_2_center hh hc),
      fun hc => a4_pCore_eq_bot_of_equiv e (CFSG.Quasithin.a4_8_2_bot hh hc)⟩

@[expose] def A_4_9 : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (X : Subgroup M), InClassX X → CFSG.Open.IsSubnormal X ⊤ →
    (⁅omegaOne 2 (centerOf (pCoreOf 2 (⊤ : Subgroup M))), X⁆ ≠ ⊥ ↔
      ⁅omegaOne 2 (centerOf (pCoreOf 2 X)), X⁆ ≠ ⊥)

theorem as_A_4_9 : A_4_9 := by
  intro M _ _ X hX hXM
  exact CFSG.Quasithin.a4_9 ((a4_inClassX_iff X).mp hX) hXM

@[expose] def A_4_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y T : Subgroup G),
    X ≤ Y → InClassX X → InClassX Y → T ≤ ChA.normalizerOf Y → IsSylowIn 2 T (Y ⊔ T) →
    pCoreOf 2 (Y ⊔ T) ≤ T ⊓ ChA.normalizerOf X →
    IsSylowIn 2 (T ⊓ ChA.normalizerOf X) (ChA.normalizerOf X ⊓ (Y ⊔ T)) →
    IsMaxTwoSignalizer (ChA.normalizerOf X ⊓ (Y ⊔ T)) X
        (CFSG.Quasithin.centralizerSection T X (pCoreOf 2 X)) ∧
    VYR X (CFSG.Quasithin.centralizerSection T X (pCoreOf 2 X)) ≤ VYR Y (pCoreOf 2 (Y ⊔ T)) ∧
    (InClassXf X → InClassXf Y)

theorem as_A_4_10 : A_4_10 := by
  intro G _ _ X Y T hXY hX hY hTn hT hO hS
  have hS' : IsSylowIn 2 (T ⊓ ChA.normalizerOf X) ((Y ⊔ T) ⊓ ChA.normalizerOf X) := by
    rw [inf_comm (Y ⊔ T) (ChA.normalizerOf X)]
    exact hS
  have h : CFSG.Quasithin.A410Hyp X Y T :=
    ⟨(a4_inClassX_iff X).mp hX, (a4_inClassX_iff Y).mp hY, hXY, hTn, hT, hO, hS'⟩
  refine ⟨?_, CFSG.Quasithin.a4_10_2 h, fun hf =>
    (a4_inClassXf_iff Y).mpr (CFSG.Quasithin.a4_10_3 h ((a4_inClassXf_iff X).mp hf))⟩
  have := CFSG.Quasithin.a4_10_1 h
  rw [inf_comm (Y ⊔ T) (Subgroup.normalizer (X : Set G))] at this
  exact a4_isMaxTwoSignalizer_iff.mpr this

@[expose] def A_4_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G),
    quasithinGenFitting M = pCoreOf 2 M → oResidual {2} X = X → CFSG.Open.IsSubnormal X M →
    CFSG.Quasithin.NoncentralTwoChiefFactorsInO2 X →
    (InClassXf X ↔ ∃ V : Subgroup G, IsTwoReduced M V ∧ ⁅V, X⁆ ≠ ⊥) ∧
    ((∃ V : Subgroup G, IsTwoReduced M V ∧ ⁅V, X⁆ ≠ ⊥) ↔ ⁅twoReducedProduct M, X⁆ ≠ ⊥)

theorem as_A_4_11 : A_4_11 := by
  intro G _ _ M X hFM hX hXM hchief
  have hFM' : CFSG.QuasithinUnique.CharTwo M :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff M 2).mp hFM
  have T := CFSG.Quasithin.a4_11 hFM' (a4_eq_oTwoUpper_of_oResidual hX) hXM hchief
  have e1 : (∃ V : Subgroup G, IsTwoReduced M V ∧ ⁅V, X⁆ ≠ ⊥) ↔
      ∃ V : Subgroup G, CFSG.Quasithin.IsTwoReducedIn M V ∧ ⁅V, X⁆ ≠ ⊥ := by
    simp only [a4_isTwoReduced_iff]
  refine ⟨?_, ?_⟩
  · rw [a4_inClassXf_iff, e1]
    exact T.out 1 2
  · rw [e1, a4_twoReducedProduct_eq]
    exact T.out 2 3

end CFSG.ASVolI
