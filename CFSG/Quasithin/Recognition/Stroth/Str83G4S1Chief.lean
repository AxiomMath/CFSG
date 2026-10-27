module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7
public import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem s1c_exists_fixed_of_fixed_coset {H U D2 L N : Subgroup G} (hUH : U ≤ H)
    (hD2H : D2 ≤ H) (hD2odd : Odd (Nat.card D2)) (hU2 : IsPGroup 2 U)
    (hstep : IsChiefStep H U L N) {x : G} (hxN : x ∈ N)
    (hxfix : ∀ d ∈ D2, d * x * d⁻¹ * x⁻¹ ∈ L) :
    ∃ y ∈ N, (∀ d ∈ D2, d * y * d⁻¹ = y) ∧ y⁻¹ * x ∈ L := by
  classical
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  let A : Type := ↥D2
  let G₁ : Type := ↥N
  haveI : Subgroup.Normalizes D2 N := ⟨hD2H.trans hHN⟩
  letI : MulDistribMulAction A G₁ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D2 N (hD2H.trans hHN)
  let Lsub : Subgroup G₁ := L.subgroupOf N
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : Lsub.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNL
  have hLinv : CFSG.IsInvariant A G₁ Lsub := by
    apply CFSG.SolvableHall.isInvariant_of_forall_smul_mem
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hHL (hD2H a.2)) (x : G)).mp hx
  have hLp : IsPGroup 2 ↥Lsub :=
    (hU2.to_le hstep.2.1.1).of_equiv (Subgroup.subgroupOfEquivOfLe hstep.2.2.1.le).symm
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥Lsub := hLp.isNilpotent
  haveI : Group.IsSolvable ↥Lsub := inferInstance
  obtain ⟨k, hk⟩ := hLp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card ↥Lsub) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Odd.coprime_two_right hD2odd)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    (A := A) (G := G₁) Lsub hLinv (inferInstance : Group.IsSolvable ↥Lsub) hcop
  have hmem : (QuotientGroup.mk (⟨x, hxN⟩ : G₁) : G₁ ⧸ Lsub) ∈
      fixedPointSubgroup A (G₁ ⧸ Lsub) := by
    rw [FixedPoints.mem_subgroup]
    intro a
    rw [MulAction.Quotient.smul_mk]
    have hmemL : ((a • (⟨x, hxN⟩ : G₁)) * (⟨x, hxN⟩ : G₁)⁻¹ : G₁) ∈ Lsub := by
      rw [Subgroup.mem_subgroupOf]
      change ((a : G) * x * (a : G)⁻¹) * x⁻¹ ∈ L
      exact hxfix a a.2
    have hq := (QuotientGroup.eq_one_iff _).mpr hmemL
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at hq
    exact hq
  rw [hlift] at hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(y : G), y.2, fun d hd => ?_, Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hyx)⟩
  have h := congrArg (fun z : G₁ => (z : G)) ((FixedPoints.mem_subgroup A G₁ y).mp hy ⟨d, hd⟩)
  rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h
  exact h

private theorem s1c_chiefStep_noncentral {H U R₀ D2 L N : Subgroup G} (hUH : U ≤ H)
    (hD2H : D2 ≤ H) (hD2odd : Odd (Nat.card D2)) (hU2 : IsPGroup 2 U)
    (hfix : ∀ y ∈ U, (∀ x ∈ D2, x * y * x⁻¹ * y⁻¹ ∈ R₀) → y ∈ R₀)
    (hstep : IsChiefStep H U L N) (hR0L : R₀ ≤ L) : ¬ IsCentralStep H L N := by
  intro hcent
  obtain ⟨x, hxN, hxL⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hstep.2.2.1)
  obtain ⟨y, hyN, hyfix, hyx⟩ := s1c_exists_fixed_of_fixed_coset hUH hD2H hD2odd hU2 hstep hxN
    fun d hd => hcent d (hD2H hd) x hxN
  have hyR : y ∈ R₀ := hfix y (hstep.1.1 hyN) fun d hd => by
    rw [hyfix d hd, mul_inv_cancel]
    exact R₀.one_mem
  refine hxL ?_
  have hx : x = y * (y⁻¹ * x) := by group
  rw [hx]
  exact L.mul_mem (hR0L hyR) hyx

private theorem s1c_between_eq_of_zero {H U R₀ : Subgroup G}
    (hnc : ∀ L N : Subgroup G, IsChiefStep H U L N → R₀ ≤ L → ¬ IsCentralStep H L N) :
    ∀ {N : Subgroup G} {n : ℕ}, F112W.IsChiefSeriesBetween H U R₀ N n → n = 0 → N = R₀ := by
  intro N n h
  induction h with
  | refl => intro _; rfl
  | central hstep hcent hs ih => intro _; exact (hnc _ _ hstep hs.le hcent).elim
  | noncentral hstep hnc' hs ih => intro hn; omega

private theorem s1c_exists_one_step {H U R₀ : Subgroup G}
    (hnc : ∀ L N : Subgroup G, IsChiefStep H U L N → R₀ ≤ L → ¬ IsCentralStep H L N)
    {N : Subgroup G} (hser : F112W.IsChiefSeriesBetween H U R₀ N 1) :
    IsChiefStep H U R₀ N ∧ ¬ IsCentralStep H R₀ N := by
  cases hser with
  | central hstep hcent hs => exact (hnc _ _ hstep hs.le hcent).elim
  | noncentral hstep hnc' hs =>
      have hL : _ = _ := s1c_between_eq_of_zero hnc hs rfl
      subst hL
      exact ⟨hstep, hnc'⟩

private theorem s1c_exists_two_steps {H U R₀ : Subgroup G}
    (hnc : ∀ L N : Subgroup G, IsChiefStep H U L N → R₀ ≤ L → ¬ IsCentralStep H L N)
    {N : Subgroup G} (hser : F112W.IsChiefSeriesBetween H U R₀ N 2) :
    ∃ L : Subgroup G, IsChiefStep H U R₀ L ∧ ¬ IsCentralStep H R₀ L ∧
      IsChiefStep H U L N ∧ ¬ IsCentralStep H L N := by
  cases hser with
  | central hstep hcent hs => exact (hnc _ _ hstep hs.le hcent).elim
  | noncentral hstep2 hnc2 hs1 =>
      obtain ⟨hstep1, hnc1⟩ := s1c_exists_one_step hnc hs1
      exact ⟨_, hstep1, hnc1, hstep2, hnc2⟩

private theorem s1c_count_le {H U R₀ : Subgroup G} {m c : ℕ} {t : G} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hU2 : IsPGroup 2 U) (hUH : U ≤ H) (htH : t ∈ H)
    (ht2 : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H)
    (hdisp : (centralizerMod R₀ U (Subgroup.zpowers t)).relIndex U ≤ (2 ^ m) ^ 2)
    (hser : F112W.IsChiefSeriesBetween H U R₀ U c) : c ≤ 2 := by
  have hpow : (2 ^ m) ^ c ≤ (centralizerMod R₀ U (Subgroup.zpowers t)).relIndex U :=
    pow_le_relIndex_centralizerMod_between hUH (Subgroup.zpowers_le.mpr htH)
      (fun _ _ _ hstep hnc =>
        l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm2 hL2 hU2 hUH hstep hnc htH ht2 htO)
      hser
  exact (Nat.pow_le_pow_iff_right (Nat.one_lt_two_pow (by omega))).mp (hpow.trans hdisp)

private theorem s1c_relIndex_mul_le {H U W L N A : Subgroup G} (hUH : U ≤ H) (hAH : A ≤ H)
    (hstep : IsChiefStep H U L N) (hWL : W ≤ L) :
    (centralizerMod W L A).relIndex L * (centralizerMod L N A).relIndex N ≤
      (centralizerMod W N A).relIndex N := by
  have hLN : L ≤ N := hstep.2.2.1.le
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hCD : centralizerMod W N A ≤ centralizerMod L N A := by
    rintro x ⟨hxN, hxNW, hx⟩
    exact ⟨hxN, (hstep.1.1.trans (hUH.trans hHL)) hxN, fun a ha => hWL (hx a ha)⟩
  have hLD : L ≤ centralizerMod L N A := by
    intro x hxL
    refine ⟨hLN hxL, Subgroup.le_normalizer hxL, fun a ha => ?_⟩
    have h1 : a * x⁻¹ * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hHL (hAH ha)) x⁻¹).mp (L.inv_mem hxL)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact L.mul_mem hxL h1
  have hCL : centralizerMod W N A ⊓ L = centralizerMod W L A := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨⟨-, hxNW, hx⟩, hxL⟩
      exact ⟨hxL, hxNW, hx⟩
    · intro x hx
      exact ⟨centralizerMod_mono_left A hLN hx, hx.1⟩
  have hmul : (centralizerMod W N A).relIndex (centralizerMod L N A) *
      (centralizerMod L N A).relIndex N = (centralizerMod W N A).relIndex N :=
    Subgroup.relIndex_mul_relIndex _ _ _ hCD (centralizerMod_le_left L N A)
  have h1 : (centralizerMod W L A).relIndex L ≤
      (centralizerMod W N A).relIndex (centralizerMod L N A) :=
    calc (centralizerMod W L A).relIndex L = (centralizerMod W N A).relIndex L := by
          rw [← hCL, Subgroup.inf_relIndex_right]
      _ ≤ (centralizerMod W N A).relIndex (centralizerMod L N A) :=
          Subgroup.relIndex_le_of_le_right hLD (D15Proof.relIndex_ne_zero _ _)
  calc (centralizerMod W L A).relIndex L * (centralizerMod L N A).relIndex N
      ≤ (centralizerMod W N A).relIndex (centralizerMod L N A) *
          (centralizerMod L N A).relIndex N := Nat.mul_le_mul_right _ h1
    _ = (centralizerMod W N A).relIndex N := hmul

private theorem s1c_single_commutator {H U R₀ : Subgroup G} (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hHR : H ≤ Subgroup.normalizer (R₀ : Set G))
    (hU2 : IsPGroup 2 U) (hR0U : R₀ ≤ U) (hne : R₀ ≠ U) (hstep : IsChiefStep H U R₀ U) :
    ⁅U, U⁆ ≤ R₀ := by
  have hch : ∀ J : Subgroup G, H ≤ Subgroup.normalizer (J : Set G) → R₀ ≤ J → J ≤ U →
      J = R₀ ∨ J = U := by
    intro J hJ hR0J hJU
    exact hstep.2.2.2 J ⟨hJU, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hJ hg) x).mp hx⟩ hR0J hJU
  exact CFSG.Quasithin.MS93.S52i.commutator_le_of_chief hUH hHR hHU hR0U hne hU2 hch

private theorem s1c_double_commutator {H U R₀ L : Subgroup G} {m : ℕ} {t : G} (hm2 : 2 ≤ m)
    (hmodd : Odd m) (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hU2 : IsPGroup 2 U) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (htH : t ∈ H) (ht2 : t * t ∈ pCoreOf 2 H)
    (htO : t ∉ pCoreOf 2 H)
    (hdisp : (centralizerMod R₀ U (Subgroup.zpowers t)).relIndex U ≤ (2 ^ m) ^ 2)
    (hstepL : IsChiefStep H U R₀ L) (hncL : ¬ IsCentralStep H R₀ L)
    (hstepU : IsChiefStep H U L U) (hncU : ¬ IsCentralStep H L U) : ⁅U, U⁆ ≤ R₀ := by
  classical
  have hkL := l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm2 hL2 hU2 hUH hstepL hncL htH
    ht2 htO
  have hkU := l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm2 hL2 hU2 hUH hstepU hncU htH
    ht2 htO
  have hmul := s1c_relIndex_mul_le (A := Subgroup.zpowers t) hUH (Subgroup.zpowers_le.mpr htH)
    hstepU hstepL.2.2.1.le
  obtain ⟨hrelL, hrelU⟩ : (centralizerMod R₀ L (Subgroup.zpowers t)).relIndex L = 2 ^ m ∧
      (centralizerMod L U (Subgroup.zpowers t)).relIndex U = 2 ^ m := by
    generalize (centralizerMod R₀ L (Subgroup.zpowers t)).relIndex L = x at *
    generalize (centralizerMod L U (Subgroup.zpowers t)).relIndex U = y at *
    generalize (centralizerMod R₀ U (Subgroup.zpowers t)).relIndex U = z at *
    have hq : 0 < 2 ^ m := by positivity
    constructor <;> nlinarith
  let hE_L := isElemAbelian_chiefMod hstepL hUH hU2
  let hE_U := isElemAbelian_chiefMod hstepU hUH hU2
  have hL2' := hL2
  obtain ⟨e₀⟩ := hL2
  let eSL : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 m))
  have hnatL := isNaturalModule_of_relIndex_eq hm2 hmodd hL2' hU2 hUH hstepL hncL hE_L eSL htH
    ht2 htO hrelL
  have hnatU := isNaturalModule_of_relIndex_eq hm2 hmodd hL2' hU2 hUH hstepU hncU hE_U eSL htH
    ht2 htO hrelU
  exact commutator_le_of_two_natural_chiefSteps hUH hHU hU2 hstepL hstepU hm2 eSL hE_L hE_U hnatL
    hnatU

private theorem s1c_commutator_le {H U R₀ D2 : Subgroup G} {m : ℕ} {t : G} (hm2 : 2 ≤ m)
    (hmodd : Odd m) (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hU2 : IsPGroup 2 U) (hR0U : R₀ ≤ U)
    (hHR : H ≤ Subgroup.normalizer (R₀ : Set G)) (hlt : R₀ < U) (hD2H : D2 ≤ H)
    (hD2odd : Odd (Nat.card D2))
    (hfix : ∀ y ∈ U, (∀ x ∈ D2, x * y * x⁻¹ * y⁻¹ ∈ R₀) → y ∈ R₀)
    (htH : t ∈ H) (ht2 : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H)
    (hdisp : (centralizerMod R₀ U (Subgroup.zpowers t)).relIndex U ≤ (2 ^ m) ^ 2) :
    ⁅U, U⁆ ≤ R₀ := by
  classical
  have hnormU : IsNormalIn H U U := F112W.isNormalIn_of_le_normalizer le_rfl hHU
  have hnormR : IsNormalIn H U R₀ := F112W.isNormalIn_of_le_normalizer hR0U hHR
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween hnormR U hnormU hR0U
  have hnc : ∀ L N : Subgroup G, IsChiefStep H U L N → R₀ ≤ L → ¬ IsCentralStep H L N :=
    fun L N hstep hRL => s1c_chiefStep_noncentral hUH hD2H hD2odd hU2 hfix hstep hRL
  have hc_le : c ≤ 2 := s1c_count_le hm2 hL2 hU2 hUH htH ht2 htO hdisp hser
  have hc_ne : c ≠ 0 := fun hc0 => hlt.ne (s1c_between_eq_of_zero hnc hser hc0).symm
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · obtain ⟨hstep, -⟩ := s1c_exists_one_step hnc hser
    exact s1c_single_commutator hUH hHU hHR hU2 hR0U hlt.ne hstep
  · obtain ⟨L, hstepL, hncL, hstepU, hncU⟩ := s1c_exists_two_steps hnc hser
    exact s1c_double_commutator hm2 hmodd hL2 hU2 hUH hHU htH ht2 htO hdisp hstepL hncL hstepU
      hncU

private theorem s1c_s_le_normalizer_q1 (L1 L2 S : Subgroup G) :
    S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
  ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S))

private theorem s1c_q2_le_normalizer_q1
    (hfr : Str83G4Frame L1 L2 S a) : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
  (str83G4_q2_le_s hfr).trans (s1c_s_le_normalizer_q1 L1 L2 S)

private theorem s1c_suzukiU_not_isMulCommutative
    {K : Type} [Field K] [Finite K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsMulCommutative (suzukiU a K) := by
  intro hcomm
  have hbot : commutator ↥(suzukiU a K) = ⊥ :=
    (commutator_eq_bot_iff (↥(suzukiU a K))).mpr hcomm
  have hz0 : suzukiSElt a K 0 (1 : K) ∈ suzukiZ0 a K :=
    (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩
  have hU : suzukiSElt a K 0 (1 : K) ∈ suzukiU a K :=
    suzukiZ0_le_suzukiU hz0
  have hmem : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) ∈
      (suzukiZ0 a K).subgroupOf (suzukiU a K) :=
    Subgroup.mem_subgroupOf.mpr hz0
  rw [← commutator_suzukiU hK ha, hbot] at hmem
  have h1 : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) = 1 :=
    Subgroup.mem_bot.mp hmem
  have hcoe : suzukiSElt a K 0 (1 : K) = suzukiSElt a K 0 (0 : K) := by
    simpa [suzukiSElt_zero_zero hK] using congrArg Subtype.val h1
  exact one_ne_zero ((suzukiSElt_inj.mp hcoe).2)

private theorem s1c_szSbar_equiv_quotient
    [(Q1 L1 L2 S).subgroupOf S |>.Normal] (hfr : Str83G4Frame L1 L2 S a) :
    Nonempty (szSbar L1 L2 S ≃* (↥S ⧸ (Q1 L1 L2 S).subgroupOf S)) := by
  classical
  let H1 : Subgroup G := L1 ⊔ S
  have hpCore : pCoreOf 2 H1 = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  let φ : ↥S →* szSbar L1 L2 S :=
    { toFun := fun s =>
        ⟨QuotientGroup.mk (Subgroup.inclusion (le_sup_right : S ≤ H1) s),
          Subgroup.mem_map_of_mem _
            (Subgroup.mem_subgroupOf.mpr s.2)⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (QuotientGroup.mk' (pCore 2 ↥H1))
      map_mul' := by
        intro x y
        apply Subtype.ext
        simpa [Subgroup.inclusion] using
          (QuotientGroup.mk_mul (pCore 2 ↥H1)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) x)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) y)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hker : φ.ker = (Q1 L1 L2 S).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hval : (φ s : oTwoQuot ↥H1) = 1 := congrArg Subtype.val h
      have h' : (Subgroup.inclusion (le_sup_right : S ≤ H1) s) ∈ pCore 2 ↥H1 :=
        (QuotientGroup.eq_one_iff _).mp hval
      rw [← CFSG.openPCoreOf_subgroupOf 2 H1] at h'
      have h'' : (s : G) ∈ pCoreOf 2 H1 := Subgroup.mem_subgroupOf.mp h'
      rwa [hpCore] at h''
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr (by
        rw [← CFSG.openPCoreOf_subgroupOf 2 H1, hpCore]
        exact Subgroup.mem_subgroupOf.mpr h)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

private theorem s1c_Q2R_equiv_SQ1
    [(Q1 L1 L2 S).subgroupOf S |>.Normal]
    [(Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal]
    (hfr : Str83G4Frame L1 L2 S a) (hQ : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S) :
    Nonempty ((↥(Q2 L1 L2 S) ⧸ (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S)) := by
  classical
  have hSNQ1 := s1c_s_le_normalizer_q1 L1 L2 S
  have hQ2NQ1 := s1c_q2_le_normalizer_q1 hfr
  have hsubEq : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) =
      (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NQ1
  have hQ2Q1NQ1 : Q2 L1 L2 S ⊔ Q1 L1 L2 S ≤
      Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    rw [sup_comm, hQ]
    exact hSNQ1
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2Q1NQ1
  let eY : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ≃* ↥S :=
    MulEquiv.subgroupCongr (by rw [sup_comm, hQ])
  let e3 : (↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ⧸
        (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    QuotientGroup.congr ((Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S))
      ((Q1 L1 L2 S).subgroupOf S) eY (by
        ext y
        constructor
        · rintro ⟨x, hx, hxy⟩
          have hxy' : (x : G) = (y : G) := congrArg Subtype.val hxy
          show (y : G) ∈ Q1 L1 L2 S
          rw [← hxy']
          exact Subgroup.mem_subgroupOf.mp hx
        · intro hy
          refine ⟨eY.symm y, ?_, eY.apply_symm_apply y⟩
          have hcoe : ((eY.symm y : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S)) : G) = (y : G) := rfl
          show (eY.symm y : G) ∈ Q1 L1 L2 S
          rw [hcoe]
          exact Subgroup.mem_subgroupOf.mp hy)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hsubEq.symm).trans
    ((QuotientGroup.quotientInfEquivProdNormalizerQuotient (Q2 L1 L2 S) (Q1 L1 L2 S)
      hQ2NQ1).trans e3)⟩

private theorem s1c_false_of_commutator_le
    (hfr : Str83G4Frame L1 L2 S a) (hQ : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hcomm : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S) : False := by
  classical
  have ha : 1 ≤ a := hfr.2.2.1
  have hSNQ1 := s1c_s_le_normalizer_q1 L1 L2 S
  have hQ2NQ1 := s1c_q2_le_normalizer_q1 hfr
  have hQ2NR : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S ⊓ Q2 L1 L2 S : Set G) :=
    Subgroup.le_normalizer_inf hQ2NQ1 (Subgroup.le_normalizer (H := Q2 L1 L2 S))
  haveI : (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NR
  haveI : (Q1 L1 L2 S).subgroupOf S |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSNQ1
  have hQcomm : IsMulCommutative
      (↥(Q2 L1 L2 S) ⧸ (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S)) := by
    refine (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q2 L1 L2 S))).mpr ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    exact hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
  obtain ⟨eQR⟩ := s1c_Q2R_equiv_SQ1 hfr hQ
  have hScomm : IsMulCommutative (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eQR hQcomm
  obtain ⟨eS⟩ := s1c_szSbar_equiv_quotient hfr
  have hszcomm : IsMulCommutative (szSbar L1 L2 S) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eS.symm hScomm
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  let eSU : szSbar L1 L2 S ≃* suzukiU a (GaloisField 2 (2 * a + 1)) :=
    (e.subgroupMap (szSbar L1 L2 S)).trans (MulEquiv.subgroupCongr he)
  have hUcomm : IsMulCommutative (suzukiU a (GaloisField 2 (2 * a + 1))) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eSU hszcomm
  exact s1c_suzukiU_not_isMulCommutative ha hK hUcomm

private theorem s1c_Q1_relIndex_S
    (hfr : Str83G4Frame L1 L2 S a) :
    (Q1 L1 L2 S).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
  have hQ1S := str83G4_q1_le_s hfr
  obtain ⟨hF, hB, ha, ⟨e⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨e⟩⟩)
  let Q : Subgroup G := Q1 L1 L2 S
  let P : Subgroup G := P1 L1 L2 S
  let S1 : Subgroup G := S ⊓ L1
  change Q.relIndex S = (2 ^ (2 * a + 1)) ^ 2
  have hS1P : S1 ≤ P := (inf_le_right : S ⊓ L1 ≤ L1).trans le_sup_left
  have hS1N : S1 ≤ Subgroup.normalizer (Q : Set G) :=
    hS1P.trans (le_normalizer_pCoreOf 2 P)
  have hsup : S1 ⊔ Q = S := hS1.symm
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    have h := CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
      (A := S1) (B := Q) hS1N
    rwa [hsup] at h
  rw [hrel]
  rw [← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L1 := by
    have h1 : Q ⊓ S1 = L1 ⊓ Q := by
      change Q ⊓ (S ⊓ L1) = L1 ⊓ Q
      rw [inf_comm Q (S ⊓ L1), inf_assoc,
        inf_eq_right.mpr (show L1 ⊓ Q ≤ S from inf_le_right.trans hQ1S)]
    rw [h1]
    exact str86_inf_p1_q1 (L1 := L1) (L2 := L2) (S := S) hF
  rw [hinf]
  exact relIndex_pCoreOf_sylow_sz ha e hF.1.h1.sylow

private theorem s1c_relIndex_Q2
    (hfr : Str83G4Frame L1 L2 S a) (hQ : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S) :
    (Q1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (Q2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [Subgroup.inf_relIndex_right]
  rw [← CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer (s1c_q2_le_normalizer_q1 hfr)]
  rw [sup_comm, hQ, s1c_Q1_relIndex_S hfr]

theorem str83G4_s1_false_of_r0
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {R₀ : Subgroup G}
    (hR0 : R₀ ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S)
    (hR0N : L2 ⊔ S ≤ Subgroup.normalizer (R₀ : Set G))
    (hfix : ∀ y ∈ Q2 L1 L2 S, (∀ x ∈ d.D2, x * y * x⁻¹ * y⁻¹ ∈ R₀) → y ∈ R₀)
    (hQ : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    {t : G} (htS : t ∈ S) (htQ : t ∉ Q2 L1 L2 S) (ht2 : t * t = 1)
    (hdisp : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤
      centralizerMod R₀ (Q2 L1 L2 S) (Subgroup.zpowers t)) :
    False := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr'
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : u3H L1 L2 S = L2 ⊔ S := (sup_eq_of_S_eq_right hS2).symm
  have hpc : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF
  have hU2 : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hHU : u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
    have h := le_normalizer_pCoreOf 2 (u3H L1 L2 S)
    rwa [hpc] at h
  have hindex := s1c_relIndex_Q2 hfr hQ
  have hlt : R₀ < Q2 L1 L2 S := by
    refine lt_of_le_of_ne (hR0.trans inf_le_right) ?_
    intro h
    have h1 : (Q1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (Q2 L1 L2 S) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact h ▸ hR0
    rw [hindex] at h1
    have hq : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    have hq2 : 1 < (2 ^ (2 * a + 1)) ^ 2 := one_lt_pow₀ hq (by norm_num)
    omega
  have hdisp' : (centralizerMod R₀ (Q2 L1 L2 S) (Subgroup.zpowers t)).relIndex (Q2 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← hindex]
    exact Subgroup.relIndex_le_of_le_left hdisp (D15Proof.relIndex_ne_zero _ _)
  have hD2H : d.D2 ≤ u3H L1 L2 S := by
    rw [hsup2]
    exact (d.hD2hall.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hHR : u3H L1 L2 S ≤ Subgroup.normalizer (R₀ : Set G) := by
    rw [hsup2]
    exact hR0N
  have htH : t ∈ u3H L1 L2 S := by
    rw [hsup2]
    exact (le_sup_right : S ≤ L2 ⊔ S) htS
  have ht2' : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [hpc, ht2]
    exact (Q2 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rw [hpc]
    exact htQ
  have hcomm : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ R₀ :=
    s1c_commutator_le (m := 2 * a + 1) (by omega) ⟨a, rfl⟩ (str86_isL2Quot_u3H hF hL2)
      (q2_le_u3H L1 L2 S) hHU hU2 (hR0.trans inf_le_right) hHR hlt hD2H d.hD2hall.2.1 hfix htH
      ht2' htO hdisp'
  exact s1c_false_of_commutator_le hfr hQ (hcomm.trans hR0)

end CFSG.Quasithin.Stroth

end
