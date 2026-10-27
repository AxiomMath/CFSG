module

public import CFSG.LocalAnalysis.StandardType.GGL45E67
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp
public import CFSG.LocalAnalysis.StandardType.GGL45E67Rank
public import CFSG.LocalAnalysis.StandardType.GGL45E67Inner
public import CFSG.LocalAnalysis.StandardType.GGL45E67Toral
public import CFSG.LocalAnalysis.StandardType.GGL45E67Torus
public import CFSG.LocalAnalysis.StandardType.GGL45E67TorusH
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcThreePart
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrameMap
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeAt
public import CFSG.LocalAnalysis.StandardType.GGL45E67FrameLang
public import CFSG.LocalAnalysis.StandardType.GGL45E67FrameExists
public import CFSG.LocalAnalysis.StandardType.GGL45E67FramePos
public import CFSG.LocalAnalysis.StandardType.GGL45E67FrameH
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGL45E67Center
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwF4
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.C14Exc
  CFSG.HardMathSupport.C14ExcBridgeE6 CFSG.HardMathSupport.C14ExcBridgeU
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped commutatorElement

private def E67Inner (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  ∃ (τ : Tag) (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2) (e : ℕ)
    (Q : ModGL τ (AlgebraicClosure K₀)) (ρ : R →* ModGL τ (AlgebraicClosure K₀)),
    (τ = .E6 ∨ τ = .E7) ∧ (τ = .E7 → lab.tag = .E7) ∧
    IsSteinbergEnd τ (AlgebraicClosure K₀) (2 ^ e)
      (frobTwistGL τ (AlgebraicClosure K₀) 2 e Q) ∧
    BridgeConclAt τ (AlgebraicClosure K₀) 3 I F e Q ρ ∧
    I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧ GGCenterPrime 3 R

private def E67FrameE6 :
    LargeEvenRawCont := fun R _ I F =>
  ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2) (n e : ℕ),
    Nat.card K₀ = 2 ^ n ∧ e * 3 = n ∧ 3 ∣ 2 ^ n - 1 ∧
    ∃ ε : R ≃* ↥(adjointGroup Tag.E6 K₀),
      BridgeConclAt Tag.E6 (AlgebraicClosure K₀) 3 I F e 1
        ((baseChangeGL (algebraMap K₀ (AlgebraicClosure K₀))).comp
          ((adjointGroup Tag.E6 K₀).subtype.comp ε.toMonoidHom)) ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (φ : L' →* R), Function.Surjective φ →
        φ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card φ.ker ∣ 3

private def E67FrameTwE6 :
    LargeEvenRawCont := fun R _ I F =>
  ∃ (n : ℕ) (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2) (σ : K₀ ≃+* K₀)
    (e : ℕ), 1 ≤ n ∧ Nat.card K₀ = (2 ^ n) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧ e * 3 = n ∧
    3 ∣ 2 ^ n + 1 ∧
    ∃ ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom),
      BridgeConclAt TwistTag.E6.tag (AlgebraicClosure K₀) 3 I F e
        (diagramMap TwistTag.E6 (AlgebraicClosure K₀))
        ((baseChangeGL (algebraMap K₀ (AlgebraicClosure K₀))).comp
          ((graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom).subtype.comp ε.toMonoidHom)) ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (φ : L' →* R), Function.Surjective φ →
        φ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card φ.ker ∣ 3

private def E67Case
    (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  (∃ f ∈ F, orderOf f = 3) → E67Inner lab R I F ∨ E67FrameE6 R I F ∨ E67FrameTwE6 R I F

private theorem e67_eq_inducedAut
    {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {α : MulAut K} {φ : MulAut R}
    (h : LargeEvenInduces θ (fun k k' => k' = α k) φ) : φ = ggInducedAut θ α := by
  exact ((ggL45_inducesIn_iff θ {φ} α).1 ⟨φ, rfl, h⟩).symm

private theorem e67_theta_rho
    {G R : Type} [Group G] [Group R] {H : Subgroup G} (ρ : R →* G)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ) (hρH : ∀ r, ρ r ∈ H)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : G)⁻¹) (r : R) :
    Θ ⟨ρ r, hρH r⟩ = MulAut.conj r := by
  ext r'
  refine hρinj ?_
  rw [hρΘ, MulAut.conj_apply]
  simp only [Subgroup.coe_mk, map_mul, map_inv]

private theorem e67_hfj
    {G R : Type} [Group G] [Group R] {H : Subgroup G} (ρ : R →* G)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : G)⁻¹) (F₀ : G →* G) {f : MulAut R} {j : ℕ}
    (hf : ∀ r, ρ (f r) = (endPowU F₀ j) (ρ r)) (h h' : H) (hh : (h' : G) = (⇑F₀)^[j] h) :
    f * Θ h * f⁻¹ = Θ h' := by
  ext r
  refine hρinj ?_
  calc ρ ((f * Θ h * f⁻¹) r)
      = endPowU F₀ j (ρ (Θ h (f⁻¹ r))) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, hf]
    _ = endPowU F₀ j (h * ρ (f⁻¹ r) * h⁻¹) := by rw [hρΘ, Subgroup.coe_inv]
    _ = endPowU F₀ j h * endPowU F₀ j (ρ (f⁻¹ r)) * (endPowU F₀ j h)⁻¹ := by
        simp only [map_mul, map_inv, Subgroup.coe_inv]
    _ = h' * ρ r * h'⁻¹ := by
        rw [← hf (f⁻¹ r), MulAut.apply_inv_self,
          CFSG.HardMathSupport.C14ExcBridgeTwF4.endPowU_apply_eq_iterate, ← hh]
        simp [Subgroup.coe_inv]
    _ = ρ (Θ h' r) := by rw [hρΘ]; simp [Subgroup.coe_inv]

private theorem e67_mem_H
    {G : Type} [Group G] (S : Subgroup G) (F : G →* G) (x : G) :
    x ∈ S ⊓ (endPowU F 3).eqLocus (MonoidHom.id G) ↔ x ∈ S ∧ (⇑F)^[3] x = x := by
  constructor
  · intro h
    rw [Subgroup.mem_inf] at h
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    change endPowU F 3 x = (MonoidHom.id G) x at h2
    rwa [CFSG.HardMathSupport.C14ExcBridgeTwF4.endPowU_apply_eq_iterate,
      MonoidHom.id_apply] at h2
  · rintro ⟨hS, hx⟩
    rw [Subgroup.mem_inf]
    refine ⟨hS, ?_⟩
    change endPowU F 3 x = (MonoidHom.id G) x
    rwa [CFSG.HardMathSupport.C14ExcBridgeTwF4.endPowU_apply_eq_iterate, MonoidHom.id_apply]

private theorem e67_center_hom
    {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) :
    Function.Surjective (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker =
        Subgroup.center K := by
  constructor
  · exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
      exact (QuotientGroup.eq_one_iff x).mp (θ.injective (by simpa using hx))
    · intro hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [show QuotientGroup.mk x = 1 from (QuotientGroup.eq_one_iff x).mpr hx, map_one]

private theorem e67_subsingleton_of_center_eq_top {K : Type} [Group K]
    (hcenter : Subgroup.center K = ⊤) (hK : commutator K = ⊤) : Subsingleton K := by
  have hKcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    have hx : x ∈ Subgroup.center K := by rw [hcenter]; trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcommbot : commutator K = ⊥ := by
    rw [commutator_def]
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (hKcomm x y).symm
  have htopbot : (⊤ : Subgroup K) = ⊥ := by
    rw [← hcommbot, hK]
  refine ⟨fun x y => ?_⟩
  have hx : x = 1 := by
    have hx' : x ∈ (⊥ : Subgroup K) := by rw [← htopbot]; trivial
    simpa using hx'
  have hy : y = 1 := by
    have hy' : y ∈ (⊥ : Subgroup K) := by rw [← htopbot]; trivial
    simpa using hy'
  rw [hx, hy]

private theorem e67_nonabelian
    {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E) : ∃ a b : R, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let π : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hker : π.ker = Subgroup.center K := (e67_center_hom θ).2
  have hle : commutator K ≤ Subgroup.center K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hmem : ⁅x, y⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h (π x) (π y)
    rw [hker] at hmem
    exact hmem
  have hcenter : Subgroup.center K = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = commutator K := hK.symm
      _ ≤ Subgroup.center K := hle
  haveI : Subsingleton K := e67_subsingleton_of_center_eq_top hcenter hK
  haveI : Subsingleton (MulAut K) :=
    ⟨fun φ ψ => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
  have hcardAut : Nat.card (MulAut K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  have hle1 : Nat.card E ≤ 1 := by
    calc Nat.card E ≤ Nat.card (MulAut K) := Subgroup.card_le_card_group E
      _ = 1 := hcardAut
  have h9 : 3 ^ 2 ≤ Nat.card E := hKG.2.2.2.1
  norm_num at h9

private theorem e67_isSteinbergEnd_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e : ℕ) :
    IsSteinbergEnd τ L (2 ^ e) (frobTwistGL τ L 2 e 1) := by
  refine ⟨iterateFrobenius L 2 e, fun c => iterateFrobenius_def 2 e c, 1, Or.inl rfl, fun g => ?_⟩
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]

private theorem e67_isSteinbergEnd_twE6
    {L : Type} [Field L] [CharP L 2] (e : ℕ) :
    IsSteinbergEnd TwistTag.E6.tag L (2 ^ e)
      (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) := by
  refine ⟨iterateFrobenius L 2 e, fun c => iterateFrobenius_def 2 e c,
    diagramMap TwistTag.E6 L, Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun g => ?_⟩
  rw [frobTwistGL_apply]

private theorem e67_pow_three_of_mem
    {G R : Type} [Group G] [Group R] {H : Subgroup G}
    (Θ : H →* MulAut R) (hΘ : Function.Injective Θ) {K : Type} [Group K]
    (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)} (hEab : IsElemAbelian 3 E)
    (x : G) {a : G}
    (ha : a ∈ (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
      (MulAut.conj x⁻¹).toMonoidHom) : a ^ 3 = 1 := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hb
  rw [Subgroup.mem_comap] at hh
  obtain ⟨e, he, hθ⟩ := Subgroup.mem_map.mp hh
  have he3 : e ^ 3 = 1 := hEab.2 e he
  have hh3 : h ^ 3 = 1 := by
    apply hΘ
    calc Θ (h ^ 3) = Θ h ^ 3 := map_pow Θ h 3
      _ = (ggInducedAut θ e) ^ 3 := by rw [← hθ]
      _ = ggInducedAut θ (e ^ 3) := (map_pow (ggInducedAut θ) e 3).symm
      _ = ggInducedAut θ 1 := by rw [he3]
      _ = Θ 1 := by rw [map_one, map_one]
  have hh3G : (h : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3, Subgroup.coe_one]
  change ((MulAut.conj x⁻¹).toMonoidHom (h : G)) ^ 3 = 1
  rw [← map_pow, hh3G, map_one]

private theorem e67_exponent
    {e : ℕ} (he : 1 ≤ e) :
    ∃ s : ℕ, 2 ≤ s ∧ 3 ^ s ∣ (2 ^ e) ^ 6 - 1 ∧ ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1 ∧
      ∃ c : ℤ, c * ((2 ^ e : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s] := by
  have hq0 : ¬ 3 ∣ 2 ^ e := by
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32
  have hNne : (2 ^ e) ^ 6 - 1 ≠ 0 := by
    have hge : 2 ≤ 2 ^ e := Nat.one_lt_two_pow (by omega)
    have hpow : 2 ^ 6 ≤ (2 ^ e) ^ 6 := Nat.pow_le_pow_left hge 6
    norm_num at hpow
    omega
  refine ⟨padicValNat 3 ((2 ^ e) ^ 6 - 1),
    two_le_of_not_three_pow_succ_dvd hq0 (pow_succ_padicValNat_not_dvd hNne),
    pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd hNne, ?_⟩
  have hcop : Nat.Coprime ((2 ^ e) ^ 2) (3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1)) := by
    have hqcop : Nat.Coprime (2 ^ e) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq0).symm
    exact hqcop.pow 2 (padicValNat 3 ((2 ^ e) ^ 6 - 1))
  refine ⟨(Nat.gcdA ((2 ^ e) ^ 2) (3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1)) : ℤ), ?_⟩
  set A : ℤ := (Nat.gcdA ((2 ^ e) ^ 2) (3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1)) : ℤ)
  set B : ℤ := (Nat.gcdB ((2 ^ e) ^ 2) (3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1)) : ℤ)
  set X : ℤ := ((2 ^ e : ℕ) : ℤ) ^ 2
  set M : ℤ := ((3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1) : ℕ) : ℤ)
  have h2 : A * X + M * B = 1 := by
    have hbezZ : X * A + M * B = 1 := by
      have hbez := Nat.gcd_eq_gcd_ab ((2 ^ e) ^ 2)
        (3 ^ padicValNat 3 ((2 ^ e) ^ 6 - 1))
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.cast_one] at hbez
      simp only [A, B, X, M]
      push_cast at hbez ⊢
      linarith
    linarith [hbezZ]
  rw [Int.modEq_iff_dvd]
  refine ⟨B, ?_⟩
  change 1 - A * X = M * B
  omega

private theorem e67_three_dvd_sub
    {q₀ : ℕ} (h : 3 ∣ q₀ ^ 3 - 1) : 3 ∣ q₀ - 1 := by
  have hx : q₀ ^ 3 % 3 = q₀ % 3 := by
    have h3 : q₀ % 3 = 0 ∨ q₀ % 3 = 1 ∨ q₀ % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases h3 with h3 | h3 | h3 <;> rw [h3]
  rcases Nat.eq_zero_or_pos q₀ with rfl | hq0
  · simp
  · have h2 : 3 ∣ q₀ ^ 3 - q₀ :=
      Nat.dvd_iff_mod_eq_zero.mpr (Nat.sub_mod_eq_zero_of_mod_eq hx)
    have hQ : q₀ ≤ q₀ ^ 3 := Nat.le_self_pow (by norm_num) q₀
    have hdec : q₀ ^ 3 - 1 = (q₀ ^ 3 - q₀) + (q₀ - 1) := by omega
    obtain ⟨c, hc⟩ := Nat.dvd_sub h h2
    refine ⟨c, ?_⟩
    rw [hdec, Nat.add_sub_cancel_left] at hc
    exact hc

private theorem e67_three_dvd_add
    {q₀ : ℕ} (h : 3 ∣ q₀ ^ 3 + 1) : 3 ∣ q₀ + 1 := by
  have hx : q₀ ^ 3 % 3 = q₀ % 3 := by
    have h3 : q₀ % 3 = 0 ∨ q₀ % 3 = 1 ∨ q₀ % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases h3 with h3 | h3 | h3 <;> rw [h3]
  have h2 : 3 ∣ q₀ ^ 3 - q₀ :=
    Nat.dvd_iff_mod_eq_zero.mpr (Nat.sub_mod_eq_zero_of_mod_eq hx)
  have hQ : q₀ ≤ q₀ ^ 3 := Nat.le_self_pow (by norm_num) q₀
  have hdec : q₀ ^ 3 + 1 = (q₀ ^ 3 - q₀) + (q₀ + 1) := by omega
  obtain ⟨c, hc⟩ := Nat.dvd_sub h h2
  refine ⟨c, ?_⟩
  rw [hdec, Nat.add_sub_cancel_left] at hc
  exact hc

private theorem e67_dvd_pow_three_sub
    {q₀ s : ℕ} (h3 : 3 ∣ q₀ ^ 3 - 1)
    (hs : 3 ^ s ∣ q₀ ^ 6 - 1) : 3 ^ s ∣ q₀ ^ 3 - 1 := by
  have hfac : (q₀ ^ 3 - 1) * (q₀ ^ 3 + 1) = q₀ ^ 6 - 1 := by
    rcases Nat.eq_zero_or_pos q₀ with rfl | hq0
    · simp
    · have h1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq0
      have h6 : 1 ≤ q₀ ^ 6 := Nat.one_le_pow _ _ hq0
      zify [h1, h6]
      ring
  have hnot : ¬ 3 ∣ q₀ ^ 3 + 1 := by
    rcases Nat.eq_zero_or_pos q₀ with rfl | hq0
    · norm_num
    · intro h
      have h1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq0
      have hd : 3 ∣ (q₀ ^ 3 + 1) - (q₀ ^ 3 - 1) := Nat.dvd_sub h h3
      have h2 : 3 ∣ 2 := by convert hd using 1; omega
      norm_num at h2
  have hcop : Nat.Coprime (3 ^ s) (q₀ ^ 3 + 1) :=
    (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three hnot).symm
  rw [← hfac] at hs
  exact hcop.dvd_of_dvd_mul_right hs

private theorem e67_dvd_pow_three_add
    {q₀ s : ℕ} (h3 : 3 ∣ q₀ ^ 3 + 1)
    (hs : 3 ^ s ∣ q₀ ^ 6 - 1) : 3 ^ s ∣ q₀ ^ 3 + 1 := by
  have hfac : (q₀ ^ 3 - 1) * (q₀ ^ 3 + 1) = q₀ ^ 6 - 1 := by
    rcases Nat.eq_zero_or_pos q₀ with rfl | hq0
    · simp
    · have h1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq0
      have h6 : 1 ≤ q₀ ^ 6 := Nat.one_le_pow _ _ hq0
      zify [h1, h6]
      ring
  have hnot : ¬ 3 ∣ q₀ ^ 3 - 1 := by
    rcases Nat.eq_zero_or_pos q₀ with rfl | hq0
    · norm_num at h3
    · intro h
      have h1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq0
      have hd : 3 ∣ (q₀ ^ 3 + 1) - (q₀ ^ 3 - 1) := Nat.dvd_sub h3 h
      have h2 : 3 ∣ 2 := by convert hd using 1; omega
      norm_num at h2
  have hcop : Nat.Coprime (3 ^ s) (q₀ ^ 3 - 1) :=
    (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three hnot).symm
  rw [← hfac] at hs
  exact hcop.dvd_of_dvd_mul_left hs

private theorem e67_setup
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    {H : Subgroup (ModGL τ L)} {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (ρ : R →* ModGL τ L) (Θ : H →* MulAut R)
    (hρinj : Function.Injective ρ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) = (endPowU F₀ j) (ρ r))
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K}
    {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E) :
    ∃ (f : MulAut R) (u : H) (j : ℕ), ¬ 3 ∣ j ∧ ggInducedAut θ ψ = Θ u * f * (Θ u)⁻¹ ∧
      (∀ h h' : H, (h' : ModGL τ L) = (⇑F₀)^[j] h → f * Θ h * f⁻¹ = Θ h') ∧
      ∀ e ∈ E, ggInducedAut θ e ∈ I := by
  obtain ⟨f, hf, u, hu, hfo, hind⟩ := hKG.2.1
  obtain ⟨j, hj, hfr⟩ := hFj f hf hfo
  obtain ⟨u', hu'⟩ := (hI u).1 hu
  refine ⟨f, u', j, hj, ?_, ?_, ?_⟩
  · subst u
    exact (e67_eq_inducedAut θ hind).symm
  · intro h h' hh
    exact e67_hfj ρ Θ hρinj hρΘ F₀ hfr h h' hh
  · intro e he
    exact (ggL45_inducesIn_iff θ I e).1 (hKG.2.2.2.2.2.1 e he)

private theorem e67_common
    (hB2 : GGL45E6NonToralThreeCent) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7)
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    {F₀ : ModGL τ (AlgebraicClosure K₀) →* ModGL τ (AlgebraicClosure K₀)} {e : ℕ}
    (he : 1 ≤ e) (hF₀ : IsSteinbergEnd τ (AlgebraicClosure K₀) (2 ^ e) F₀)
    {H : Subgroup (ModGL τ (AlgebraicClosure K₀))}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ (AlgebraicClosure K₀) ∧ (⇑F₀)^[3] x = x)
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)}
    (ρ : R →* ModGL τ (AlgebraicClosure K₀)) (Θ : H →* MulAut R)
    (hρinj : Function.Injective ρ) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ (AlgebraicClosure K₀))⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) = (endPowU F₀ j) (ρ r))
    (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hE4 : 3 ^ 4 ≤ Nat.card E) (hE7 : τ = .E7 → 3 ^ 6 ≤ Nat.card E) :
    ∃ (u : H) (w : WeylGroup τ) (g : ModGL τ (AlgebraicClosure K₀)),
      g ∈ adjointGroup τ (AlgebraicClosure K₀) ∧
      F₀ g = g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K₀) w ∧
      (∀ A : Subgroup (ModGL τ (AlgebraicClosure K₀)),
        A = (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL τ (AlgebraicClosure K₀)) * g)⁻¹).toMonoidHom →
        A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K₀) w) F₀ ∧
          rootsTrivialOn A = ∅ ∧
          adjointGroup τ (AlgebraicClosure K₀) ⊓
            Subgroup.centralizer (A : Set (ModGL τ (AlgebraicClosure K₀))) =
            torusGroup τ (AlgebraicClosure K₀)) ∧
      ∃ s : ℕ, 2 ≤ s ∧ 3 ^ s ∣ (2 ^ e) ^ 6 - 1 ∧
        ∃ (c : ℤ) (k : ℕ), ¬ 3 ∣ k ∧ c ≡ 1 + 3 ^ (s - 1) * k [ZMOD 3 ^ s] ∧
          GGL45HOne 3 I θ E (ggInducedAut θ ψ) s c ∧
          (∀ φ ∈ I, ∀ φ' ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
            (∀ x ∈ E, φ' * ggInducedAut θ x = ggInducedAut θ x * φ') → φ * φ' = φ' * φ) ∧
          ∃ a₁ a₂ : MulAut R, GGL45InCIp 3 I θ E a₁ ∧ GGL45InCIp 3 I θ E a₂ ∧
            ∀ m n : ℕ, (a₁ ^ 3 ^ (s - 1)) ^ m * (a₂ ^ 3 ^ (s - 1)) ^ n = 1 → 3 ∣ m ∧ 3 ∣ n := by
  obtain ⟨f, u, j, hj, hψ, hfj, hEI⟩ := e67_setup ρ Θ hρinj hI hρΘ hFj θ hKG
  have htoral := ggL45E67_isToralSubgroup hB2 hτ (fun x hx => ((hH x).1 hx).1)
    Θ hΘ hI hcyc θ hK hKG hE4 hE7
  obtain ⟨w, g, hg, hFg, hA⟩ := ggL45E67_frame_rootsTrivialOn_eq_empty hτ he hF₀ hH Θ hΘ hI
    hInv θ hK hKG.2.2.1 hE4 hEI hKG.2.2.2.2.2.2.1 hKG.2.2.2.2.2.2.2.1 htoral u hψ hj hfj
  obtain ⟨s, hs2, hs, hs', c₀, hc₀⟩ := e67_exponent he
  obtain ⟨hcomm, hH1, hpair⟩ := ggL45E67_frame_hOne hτ he hF₀ hH Θ hΘ hI θ hK
    hKG.2.2.1 (le_trans (by norm_num) hE4) hEI u hψ hfj hg hFg hA hs hs'
  have hq0 : ¬ 3 ∣ 2 ^ e := by
    intro h
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h2
  obtain ⟨k, hk, hc⟩ := exists_pow_modEq_one_add_three_pow_mul hq0 hs hs' hc₀ hj
  exact ⟨u, w, g, hg, hFg, hA, s, hs2, hs, c₀ ^ j, k, hk, hc, hH1 c₀ hc₀, hcomm, hpair⟩

private theorem e67_inner
    (hB2 : GGL45E6NonToralThreeCent) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7)
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {lab : LargeEvenLabel} {R : Type}
    [Group R] {I F : Set (MulAut R)} {e : ℕ} {Q : ModGL τ (AlgebraicClosure K₀)}
    {ρ : R →* ModGL τ (AlgebraicClosure K₀)}
    (hst : IsSteinbergEnd τ (AlgebraicClosure K₀) (2 ^ e)
      (frobTwistGL τ (AlgebraicClosure K₀) 2 e Q))
    (hbr : BridgeConclAt τ (AlgebraicClosure K₀) 3 I F e Q ρ)
    (hinn : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : GGCenterPrime 3 R) (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hE4 : 3 ^ 4 ≤ Nat.card E) (hE7 : τ = .E7 → 3 ^ 6 ≤ Nat.card E) :
    GGL45TorusH123 3 I θ ψ E := by
  obtain ⟨he, -, ⟨-, Θ, hρinj, hρH, hΘ, hI, hρΘ, hFj⟩, -, -⟩ := hbr
  let H : Subgroup (ModGL τ (AlgebraicClosure K₀)) :=
    adjointGroup τ (AlgebraicClosure K₀) ⊓
      (endPowU (frobTwistGL τ (AlgebraicClosure K₀) 2 e Q) 3).eqLocus
        (MonoidHom.id _)
  have hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ (AlgebraicClosure K₀) ∧
      (⇑(frobTwistGL τ (AlgebraicClosure K₀) 2 e Q))^[3] x = x := e67_mem_H _ _
  obtain ⟨u, w, g, hg, hFg, hA, s, hs2, hs, c, k, hk, hc, hH1, hcomm, hpair⟩ :=
    e67_common hB2 hτ he hst hH ρ Θ hρinj hΘ hI hρΘ hFj hInv hcyc θ hK hKG hE4 hE7
  have hInn : ∀ r : R, MulAut.conj r ∈ I := fun r =>
    (hI _).2 ⟨⟨ρ r, hρH r⟩, e67_theta_rho ρ Θ hρinj hρH hρΘ r⟩
  have hOut : ∀ u ∈ I, GGL45IsPElt 3 u → ∃ r : R, u = MulAut.conj r := by
    intro u hu _
    obtain ⟨r, hr⟩ := hinn hu
    exact ⟨r, hr.symm⟩
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    intro h3
    exact hZ K (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
      (e67_center_hom θ).1 (by rw [(e67_center_hom θ).2]) hK h3
  have hc' : c ≡ 1 + (3 : ℤ) ^ (s - 1) * k [ZMOD (3 : ℤ) ^ s] := by
    simpa using hc
  exact ggL45TorusH123_of_hOne_of_inner Nat.prime_three θ hK hKG.2.2.1
    hKG.2.2.2.2.2.2.1 hInn hOut hZ' hs2 hk hc' hcomm hH1 hpair


private theorem e67_frame_E6_mem
    {L : Type} [Field L] [CharP L 2] {e : ℕ}
    (h3 : 3 ∣ 2 ^ e - 1) {H : Subgroup (ModGL Tag.E6 L)}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup Tag.E6 L ∧ (⇑(frobTwistGL Tag.E6 L 2 e 1))^[3] x = x)
    {R : Type} [Group R] (Θ : H →* MulAut R) (hΘ : Function.Injective Θ) {K : Type} [Group K]
    (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)} (hEab : IsElemAbelian 3 E)
    (u : H) {w : WeylGroup Tag.E6} {g : ModGL Tag.E6 L} (hg : g ∈ adjointGroup Tag.E6 L)
    (hFg : frobTwistGL Tag.E6 L 2 e 1 g = g * canonicalRep (coxeterSystem Tag.E6) L w)
    (hAw : (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
        (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w) (frobTwistGL Tag.E6 L 2 e 1))
    (hC : adjointGroup Tag.E6 L ⊓ Subgroup.centralizer
        ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom : Set (ModGL Tag.E6 L)) =
        torusGroup Tag.E6 L) :
    (u : ModGL Tag.E6 L) * g ∈ H := by
  have hFA : ∀ a ∈ ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
      (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom),
      frobTwistGL Tag.E6 L 2 e 1 a =
        (canonicalRep (coxeterSystem Tag.E6) L (1 : WeylGroup Tag.E6))⁻¹ * a *
          canonicalRep (coxeterSystem Tag.E6) L 1 := by
    intro a ha
    have haT : a ∈ torusGroup Tag.E6 L := (mem_twistedTorusOf.1 (hAw ha)).1
    have ha3 : a ^ 3 = 1 :=
      e67_pow_three_of_mem Θ hΘ θ hEab ((u : ModGL Tag.E6 L) * g) ha
    rw [ggL45E67_frob_eq_self_of_pow_three_eq_one h3 haT ha3, canonicalRep_one]
    simp
  have hw1 : w = 1 := ggL45E67_weyl_eq_of_frame (m := 1) hFA hAw hC
  have hFg1 : frobTwistGL Tag.E6 L 2 e 1 g = g := by
    rw [hw1, canonicalRep_one, mul_one] at hFg
    exact hFg
  refine (hH _).2 ⟨?_, ?_⟩
  · exact Subgroup.mul_mem _ ((hH u.1).1 u.2).1 hg
  · rw [iterate_map_mul, ((hH u.1).1 u.2).2, Function.iterate_fixed hFg1 3]

private theorem e67_frame_twE6_lang
    {L : Type} [Field L] [CharP L 2] {e : ℕ}
    (h3 : 3 ∣ 2 ^ e + 1) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ (3 * e))
    {H : Subgroup (ModGL Tag.E6 L)}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup Tag.E6 L ∧
      (⇑(frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L)))^[3] x = x)
    {R : Type} [Group R] (Θ : H →* MulAut R) (hΘ : Function.Injective Θ) {K : Type} [Group K]
    (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)} (hEab : IsElemAbelian 3 E)
    (u : H) {w : WeylGroup Tag.E6} {g : ModGL Tag.E6 L} (hg : g ∈ adjointGroup Tag.E6 L)
    (hFg : frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L) g =
      g * canonicalRep (coxeterSystem Tag.E6) L w)
    (hAw : (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
        (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom ≤
      twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w)
        (frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L)))
    (hC : adjointGroup Tag.E6 L ⊓ Subgroup.centralizer
        ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom : Set (ModGL Tag.E6 L)) =
        torusGroup Tag.E6 L) :
    E6ThreeModel.IsLang Fr ((u : ModGL Tag.E6 L) * g) := by
  have hFA : ∀ a ∈ ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
      (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom),
      frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L) a =
        (canonicalRep (coxeterSystem Tag.E6) L twE6W0)⁻¹ * a *
          canonicalRep (coxeterSystem Tag.E6) L twE6W0 := by
    intro a ha
    have haT : a ∈ torusGroup Tag.E6 L := (mem_twistedTorusOf.1 (hAw ha)).1
    have ha3 : a ^ 3 = 1 :=
      e67_pow_three_of_mem Θ hΘ θ hEab ((u : ModGL Tag.E6 L) * g) ha
    simpa [TwistedDiag.n0] using
      ggL45E67_twFrob_eq_conj_of_pow_three_eq_one h3 haT ha3
  have hw : w = twE6W0 := ggL45E67_weyl_eq_of_frame (m := twE6W0) hFA hAw hC
  have hFg0 : frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L) g =
      g * TwistedDiag.n0 L := by
    rw [hw] at hFg
    simpa [TwistedDiag.n0] using hFg
  exact ggL45E67_isLang_of_frame Fr hFr hg hFg0
    ((hH u.1).1 u.2).1 ((hH u.1).1 u.2).2

private theorem e67_frame_finish
    {R : Type} [Group R] {I F : Set (MulAut R)} {lab : LargeEvenLabel}
    (D : E6ThreeModel.FrameData R) (hD : D.Good)
    (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)
    (hTI : ∀ t ∈ D.Tor, MulAut.conj t ∈ I)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    (hker : ∀ (L' : Type) [Group L'] [Finite L'] (φ : L' →* R), Function.Surjective φ →
      φ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card φ.ker ∣ 3)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) → ∀ t ∈ D.Tor, u t = t)
    (h3' : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      Nat.Coprime 3 (orderOf u) → ∃ t ∈ D.Tor, u = MulAut.conj t)
    (hCR : ∀ r : R, (∀ e ∈ E, ggInducedAut θ e r = r) → r ∈ D.Tor)
    {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ} (hk : ¬ 3 ∣ k)
    (hc : c ≡ 1 + 3 ^ (s - 1) * k [ZMOD 3 ^ s]) (hH1 : GGL45HOne 3 I θ E (ggInducedAut θ ψ) s c)
    (hH3 : ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    GGL45TorusH123 3 I θ ψ E := by
  have hZ : Nat.card (Subgroup.center K) ∣ 3 := by
    have h := hker K (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
      (e67_center_hom θ).1 (by rw [(e67_center_hom θ).2]) hK
    simpa [(e67_center_hom θ).2] using h
  exact ggL45TorusH123_of_hOne_of_frame D hD hI hTI θ hK hZ hKG.1 hKG.2.2.1
    hKG.2.2.2.2.2.1 hC h3' hCR hs hk hc hH1 hH3

private theorem e67_frame_E6
    (hB2 : GGL45E6NonToralThreeCent) {lab : LargeEvenLabel} {R : Type}
    [Group R] {I F : Set (MulAut R)} (hcase : E67FrameE6 R I F)
    (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hE4 : 3 ^ 4 ≤ Nat.card E) : GGL45TorusH123 3 I θ ψ E := by
  obtain ⟨K₀, hField, hFinite, hCharP, n, e, hK₀, hen, h3n, ε, hbr, hker⟩ := hcase
  let L := AlgebraicClosure K₀
  let F₀ : ModGL Tag.E6 L →* ModGL Tag.E6 L := frobTwistGL Tag.E6 L 2 e 1
  let H : Subgroup (ModGL Tag.E6 L) :=
    adjointGroup Tag.E6 L ⊓ (endPowU F₀ 3).eqLocus (MonoidHom.id _)
  let ρ : R →* ModGL Tag.E6 L :=
    (baseChangeGL (algebraMap K₀ L)).comp
      ((adjointGroup Tag.E6 K₀).subtype.comp ε.toMonoidHom)
  have hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup Tag.E6 L ∧ (⇑F₀)^[3] x = x := e67_mem_H _ _
  obtain ⟨he, -, ⟨-, Θ, hρinj, hρH, hΘ, hI, hρΘ, hFj⟩, -, -⟩ := hbr
  have hρΘ' : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL Tag.E6 L)⁻¹ := hρΘ
  obtain ⟨u, w, g, hg, hFg, hA, s, hs2, hs, c, k, hk, hc, hH1, hcomm, hpair⟩ :=
    e67_common (K₀ := K₀) hB2 (Or.inl rfl) he (e67_isSteinbergEnd_one e) hH ρ Θ hρinj hΘ hI hρΘ'
      hFj hInv hcyc θ hK hKG hE4 (fun h => absurd h (by decide))
  have hA' := hA ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
    (MulAut.conj ((u : ModGL Tag.E6 L) * g)⁻¹).toMonoidHom) rfl
  obtain ⟨hAw, -, hC⟩ := hA'
  have h3e : 3 ∣ 2 ^ e - 1 := by
    have h := h3n
    rw [show 2 ^ n = (2 ^ e) ^ 3 by rw [← hen, pow_mul]] at h
    exact e67_three_dvd_sub h
  have hx : (u : ModGL Tag.E6 L) * g ∈ H :=
    e67_frame_E6_mem h3e hH Θ hΘ θ hKG.2.2.1 u hg hFg hAw hC
  obtain ⟨D, hD, hTor, hpairD⟩ := ggL45E67_frame_exists_E6 hK₀ h3n ε Θ hρΘ' ⟨_, hx⟩
  obtain ⟨hIJ, hTI, hCD, h3', hCR⟩ :=
    ggL45E67_frame_pos (fun x hx => ((hH x).1 hx).1) ρ Θ hρinj hρH hΘ hI hρΘ' hInv θ
      ((hH _).1 hx).1 hC D hTor
  have h3e3 : 3 ∣ (2 ^ e) ^ 3 - 1 := by
    simpa [show 2 ^ n = (2 ^ e) ^ 3 by rw [← hen, pow_mul]] using h3n
  have h3s : 3 ^ s ∣ 2 ^ n - 1 := by
    have h := e67_dvd_pow_three_sub h3e3 hs
    rwa [show (2 ^ e) ^ 3 = 2 ^ n by rw [← hen, pow_mul]] at h
  exact e67_frame_finish D hD hIJ hTI θ hK hker hKG hCD h3' hCR hs2 hk hc hH1
    (hpairD s (by omega) h3s)

private theorem e67_frame_twE6
    (hB2 : GGL45E6NonToralThreeCent) {lab : LargeEvenLabel} {R : Type}
    [Group R] {I F : Set (MulAut R)} (hcase : E67FrameTwE6 R I F)
    (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hE4 : 3 ^ 4 ≤ Nat.card E) : GGL45TorusH123 3 I θ ψ E := by
  obtain ⟨n, K₀, hField, hFinite, hCharP, σ, e, hn, hK₀, hσ, hen, h3n, ε, hbr, hker⟩ := hcase
  let L := AlgebraicClosure K₀
  let F₀ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    frobTwistGL Tag.E6 L 2 e (diagramMap TwistTag.E6 L)
  let H : Subgroup (ModGL TwistTag.E6.tag L) :=
    adjointGroup Tag.E6 L ⊓ (endPowU F₀ 3).eqLocus (MonoidHom.id _)
  let ρ : R →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K₀ L)).comp
      ((graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom).subtype.comp ε.toMonoidHom)
  have hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup TwistTag.E6.tag L ∧ (⇑F₀)^[3] x = x := e67_mem_H _ _
  obtain ⟨he, -, ⟨-, Θ, hρinj, hρH, hΘ, hI, hρΘ, hFj⟩, -, -⟩ := hbr
  have hρΘ' : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL TwistTag.E6.tag L)⁻¹ := hρΘ
  obtain ⟨u, w, g, hg, hFg, hA, s, hs2, hs, c, k, hk, hc, hH1, hcomm, hpair⟩ :=
    e67_common (K₀ := K₀) hB2 (Or.inl rfl) he (e67_isSteinbergEnd_twE6 e) hH ρ Θ hρinj hΘ hI
      hρΘ' hFj hInv hcyc θ hK hKG hE4 (fun h => absurd h (by decide))
  have hA' := hA ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
    (MulAut.conj (u.1 * g)⁻¹).toMonoidHom) rfl
  obtain ⟨hAw, -, hC⟩ := hA'
  have h3n' : 3 ∣ (2 ^ e) ^ 3 + 1 := by
    simpa [show 2 ^ n = (2 ^ e) ^ 3 by rw [← hen, pow_mul]] using h3n
  have h3e : 3 ∣ 2 ^ e + 1 := e67_three_dvd_add h3n'
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ (3 * e) := by
    intro c
    rw [show Fr c = c ^ 2 ^ n from iterateFrobenius_def 2 n c]
    rw [show 2 ^ (3 * e) = 2 ^ n by rw [show 3 * e = n by omega]]
  have hx : E6ThreeModel.IsLang Fr (u.1 * g) :=
    e67_frame_twE6_lang h3e Fr hFr hH Θ hΘ θ hKG.2.2.1 u hg hFg hAw hC
  obtain ⟨D, hD, hTor, hpairD⟩ := ggL45E67_frame_exists_twE6 hK₀ σ hσ h3n Fr
    (fun c => iterateFrobenius_def 2 n c) ε hx
  obtain ⟨hIJ, hTI, hCD, h3', hCR⟩ :=
    ggL45E67_frame_pos (fun x hx => ((hH x).1 hx).1) ρ Θ hρinj hρH hΘ hI hρΘ' hInv θ
      (Subgroup.mul_mem _ ((hH u.1).1 u.2).1 hg) hC D hTor
  have h3s : 3 ^ s ∣ 2 ^ n + 1 := by
    have h := e67_dvd_pow_three_add h3n' hs
    rwa [show (2 ^ e) ^ 3 = 2 ^ n by rw [← hen, pow_mul]] at h
  exact e67_frame_finish D hD hIJ hTI θ hK hker hKG hCD h3' hCR hs2 hk hc hH1
    (hpairD s (by omega) h3s)

private theorem e67_inn_E6
    {K : Type} [Field K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (h3 : ¬ 3 ∣ 2 ^ n - 1) :
    LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false) ⊆
      Set.range (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))) := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, hK]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  exact chevIDImage_subset_inn_of_top (τ := .E6)
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj fun s =>
      ⟨(powCoprime hcop).symm s, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩)

private theorem e67_inn_twE6
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    TwE6Delta.RecipeI K n ⊆
      Set.range (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) := by
  exact chevIDImage_subset_inn (H := TwE6Delta.RecipeH K n) fun a ha =>
    CFSG.LocalAnalysis.GLTheoremA.K155X.diagHom_mem_twE6_of_not_three_dvd hn hK h3 ha

private theorem e67Case_E6
    {l n : ℕ} (hn : 1 ≤ n) :
    LargeEvenLabelAll ⟨.E6, l, n⟩ (E67Case ⟨.E6, l, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
  refine recipeChevalley_and (P := E67Case ⟨.E6, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro hf
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨e, hen, ε, hbr⟩ := bridge_chev_spec (τ := .E6) hn hK (AlgebraicClosure K)
    Nat.prime_three hf
  by_cases h3 : 3 ∣ 2 ^ n - 1
  · right; left
    refine ⟨K, inferInstance, inferInstance, inferInstance, n, e, hK, hen, h3, ε, hbr, ?_⟩
    intro L' _ _ φ hφ hker hperf
    exact TableBExc.E6Three.card_ker_dvd_three_e6 hn hK hφ hker hperf
  · left
    refine ⟨.E6, K, inferInstance, inferInstance, inferInstance, e, 1,
      (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        ((adjointGroup Tag.E6 K).subtype.comp ε.toMonoidHom),
      Or.inl rfl, fun h => absurd h (by decide), e67_isSteinbergEnd_one e, hbr,
      e67_inn_E6 hK h3, ?_⟩
    refine ggCenterPrime_recipe_E6_of_coprime (K := K) Nat.prime_three (by decide) ?_
    rw [hK]
    have hg : Nat.gcd 3 (2 ^ n - 1) = 1 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _
        (Nat.gcd_dvd_left 3 (2 ^ n - 1)) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_right 3 (2 ^ n - 1)) h3
    rw [hg]
    exact Nat.coprime_one_right 3

private theorem e67Case_twE6
    {l n : ℕ} (hn : 1 ≤ n) :
    LargeEvenLabelAll ⟨.twE6, l, n⟩ (E67Case ⟨.twE6, l, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  refine recipeTwisted_and (P := E67Case ⟨.twE6, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro hf
  have hK' : Nat.card K = 2 ^ (n * 2) := by rw [pow_mul]; exact hK
  haveI : CharP K 2 := charP_two_of_card hK'
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
  obtain ⟨e, hen, ε, hbr⟩ := bridge_twE6_chev_spec hn hK σ hσ (AlgebraicClosure K)
    Nat.prime_three (by decide) hf
  by_cases h3 : 3 ∣ 2 ^ n + 1
  · right; right
    refine ⟨n, K, inferInstance, inferInstance, inferInstance, σ, e, hn, hK, hσ, hen, h3,
      ε, hbr, ?_⟩
    intro L' _ _ φ hφ hker hperf
    have hn3 : 3 ≤ n := by
      have := hbr.1
      omega
    exact TwE6Delta.card_ker_dvd_three_q8 hn3 hK hφ hker hperf
  · left
    refine ⟨.E6, K, inferInstance, inferInstance, inferInstance, e,
      diagramMap TwistTag.E6 (AlgebraicClosure K),
      (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom),
      Or.inl rfl, fun h => absurd h (by decide), e67_isSteinbergEnd_twE6 e, hbr,
      e67_inn_twE6 hn hK h3, ?_⟩
    refine ggCenterPrime_twE6_of_coprime hn hK Nat.prime_three (by decide) ?_
    have hg : Nat.gcd 3 (2 ^ n + 1) = 1 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _
        (Nat.gcd_dvd_left 3 (2 ^ n + 1)) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_right 3 (2 ^ n + 1)) h3
    rw [hg]
    exact Nat.coprime_one_right 3

private theorem e67Case_E7
    {l n : ℕ} (hn : 1 ≤ n) :
    LargeEvenLabelAll ⟨.E7, l, n⟩ (E67Case ⟨.E7, l, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
  refine recipeChevalley_and (P := E67Case ⟨.E7, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro hf
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨e, hen, ε, hbr⟩ := bridge_chev_spec (τ := .E7) hn hK (AlgebraicClosure K)
    Nat.prime_three hf
  left
  refine ⟨.E7, K, inferInstance, inferInstance, inferInstance, e, 1,
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup Tag.E7 K).subtype.comp ε.toMonoidHom),
    Or.inr rfl, fun _ => rfl, e67_isSteinbergEnd_one e, hbr,
    TableBExc.idImage_subset_inn_E7 K, ?_⟩
  exact ExcSplitL.ggCenterPrime_recipe_E7 hn hK Nat.prime_three (by decide)

private theorem e67Case_all
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :
    LargeEvenLabelAll lab (E67Case lab) := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases htag with ht | ht | ht <;> dsimp only at ht <;> subst ht
  · exact e67Case_E6 hn
  · exact e67Case_twE6 hn
  · exact e67Case_E7 hn

private theorem e67Core_of_facts
    (hB2 : GGL45E6NonToralThreeCent) {lab : LargeEvenLabel}
    {R : Type} [Group R] {I F : Set (MulAut R)} (hsimp : GGL45NtSimp R I F)
    (hrank : GGL45E67Rank 3 lab R I F) (hinv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    (hcyc : GGRawPCyclic 3 R I F) (hcase : E67Case lab R I F) :
    GGL45E67Core 3 lab R I F := by
  intro K _ _ θ hK ψ E hKG
  have hnab := e67_nonabelian θ hK hKG
  obtain ⟨hE4, hE7⟩ := hrank K θ hK ψ E hKG
  have hcyc' := hcyc (hsimp hnab) hnab
  obtain ⟨f, hf, -, -, hfo, -⟩ := hKG.2.1
  rcases hcase ⟨f, hf, hfo⟩ with hin | hfr | hfr
  · obtain ⟨τ, K₀, _, _, _, e, Q, ρ, hτ, hlabτ, hst, hbr, hinn, hZ⟩ := hin
    exact e67_inner hB2 hτ hst hbr hinn hZ hinv hcyc' θ hK hKG hE4 fun h => hE7 (hlabτ h)
  · exact e67_frame_E6 hB2 hfr hinv hcyc' θ hK hKG hE4
  · exact e67_frame_twE6 hB2 hfr hinv hcyc' θ hK hKG hE4

theorem ggL45E67CoreOn_of_nonToralThree
    (hB2 : GGL45E6NonToralThreeCent) :
    GGL45NtOn GGL45FamE67 GGL45E67Core := by
  intro p hp hp2 lab hlab hkg hS
  obtain ⟨rfl, htag⟩ := hS
  have h1 := ggL45NtSimpOn_all GGL45FamE67 3 hp hp2 lab hlab hkg ⟨rfl, htag⟩
  have h2 := ggL45E67RankOn_holds 3 hp hp2 lab hlab hkg ⟨rfl, htag⟩
  have h3 := ggL45E67_pow_three_mem_inn 3 hp hp2 lab hlab hkg ⟨rfl, htag⟩
  have h4 := ggRawPCyclicOn_notD4Three_of_round5 ggRawPCyclicOn_rest5 3 hp hp2 lab hlab fun h => by
    rcases htag with h' | h' | h' <;> rw [h'] at h <;> exact absurd h.1 (by decide)
  have h5 := e67Case_all hlab htag
  exact (largeEvenLabelAll_and (largeEvenLabelAll_and (largeEvenLabelAll_and
    (largeEvenLabelAll_and h1 h2) h3) h4) h5).mono
      fun R _ I F h => e67Core_of_facts hB2 h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2

theorem ggL45TorusHKnownFormsOn_e67_of_nonToralThree
    (hB2 : GGL45E6NonToralThreeCent) :
    GGL45TorusHKnownFormsOn GGL45FamE67 :=
  ggL45TorusHKnownFormsOn_e67_of_core (ggL45E67CoreOn_of_nonToralThree hB2)

end CFSG.StandardType
