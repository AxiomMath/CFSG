module

public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof86
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84
import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofJCent
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOmega

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Item812Res7

section Tools

theorem conj_injective_of_center_trivial {M : Type*} [Group M]
    (hZ : Subgroup.center M = ⊥) : Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hmem : u ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj u g = g := by rw [hu]; rfl
    rw [MulAut.conj_apply] at h1
    calc g * u = u * g * u⁻¹ * u := by rw [h1]
      _ = u * g := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem exists_odd_pow_two_power {M N : Type*} [Group M] [Group N] [Finite M] (f : M →* N)
    (x : M) (hx : orderOf (f x) = 2) :
    ∃ k : ℕ, (∃ e : ℕ, (x ^ k) ^ 2 ^ e = 1) ∧ f (x ^ k) = f x := by
  obtain ⟨e, o, ho, hxo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨o, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hxo, pow_orderOf_eq_one]
  · have h2 : f x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    obtain ⟨j, rfl⟩ := ho
    rw [map_pow, pow_succ, pow_mul, h2, one_pow, one_mul]

theorem exists_pow_orderOf_eq_two {M : Type*} [Monoid M] {s : M} {e : ℕ} (hs : s ^ 2 ^ e = 1)
    (hs1 : s ≠ 1) : ∃ j : ℕ, orderOf (s ^ j) = 2 := by
  obtain ⟨f, hfe, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hf
    exact hs1 hf
  refine ⟨2 ^ (f - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hf]; exact Nat.pow_dvd_pow 2 (Nat.sub_le f 1)),
    hf, Nat.pow_div (Nat.sub_le f 1) (by norm_num), show f - (f - 1) = 1 by omega, pow_one]

theorem exists_shift_eq_conj {M : Type*} [Group M] {τ γ : MulAut M} {y w g : M}
    (hτ : τ = γ * MulAut.conj y) (hg : τ g = g) (hgw : g * w * g⁻¹ = y ∨ g * w * g⁻¹ = y⁻¹) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      τ * MulAut.conj w ^ ε = MulAut.conj g⁻¹ * γ * MulAut.conj g := by
  have hτg : τ * MulAut.conj g⁻¹ = MulAut.conj g⁻¹ * τ := by
    have h1 := KFacts.mul_mulAutConj_mul_inv τ g⁻¹
    rw [map_inv τ g, hg] at h1
    calc τ * MulAut.conj g⁻¹ = τ * MulAut.conj g⁻¹ * τ⁻¹ * τ := by
          rw [inv_mul_cancel_right]
      _ = MulAut.conj g⁻¹ * τ := by rw [h1]
  have key : τ * MulAut.conj (g⁻¹ * y⁻¹ * g) = MulAut.conj g⁻¹ * γ * MulAut.conj g := by
    have hγ : γ = τ * MulAut.conj y⁻¹ := by rw [hτ, map_inv, mul_inv_cancel_right]
    rw [hγ, map_mul, map_mul, ← mul_assoc, ← mul_assoc, hτg]
    simp only [mul_assoc]
  rcases hgw with h1 | h1
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hw : w⁻¹ = g⁻¹ * y⁻¹ * g := by rw [← h1]; group
    rw [zpow_neg_one, ← map_inv, hw]
    exact key
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hw : w = g⁻¹ * y⁻¹ * g := by rw [← h1]; group
    rw [zpow_one, hw]
    exact key

theorem apply_eq_of_commute_conj {M : Type*} [Group M]
    (hinj : Function.Injective (MulAut.conj : M →* MulAut M)) {τ : MulAut M} {w : M}
    (h : τ * MulAut.conj w = MulAut.conj w * τ) : τ w = w := by
  apply hinj
  rw [← KFacts.mul_mulAutConj_mul_inv τ w, h, mul_inv_cancel_right]

theorem exists_involution_of_two_element {M : Type*} [Group M] {τ : MulAut M} {w s : M} {e : ℕ}
    (hse : s ^ 2 ^ e = 1) (hs1 : s ≠ 1) (hτs : τ s = s) (hws : MulAut.conj w s = s) :
    ∃ v : M, v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v ∧ v * w = w * v := by
  have hsw : s * w = w * s := by
    rw [MulAut.conj_apply] at hws
    calc s * w = w * s * w⁻¹ * w := by rw [hws]
      _ = w * s := by group
  obtain ⟨j, hj⟩ := exists_pow_orderOf_eq_two hse hs1
  refine ⟨s ^ j, fun h1 => ?_, ?_, by rw [map_pow, hτs], (Commute.pow_left hsw j).eq⟩
  · rw [h1, orderOf_one] at hj
    exact absurd hj (by norm_num)
  · rw [← hj]
    exact pow_orderOf_eq_one _

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_of_imageModTheta_eq_top {L K : Subgroup G} (hKL : K ≤ L)
    (h : imageModTheta L K = ⊤) : L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  apply le_antisymm
  · intro x hx
    have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨x, hx⟩ : L) ∈
        imageModTheta L K := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkx
    have h1 : k⁻¹ * ⟨x, hx⟩ ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hkx
    have e : x = (k : G) * ((k⁻¹ * ⟨x, hx⟩ : L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
      (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)
  · exact sup_le hKL (Subgroup.map_subtype_le _)

theorem inducedAutHom_apply_of_commute {L : Subgroup G} {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {z : G} (hz : z ∈ Subgroup.normalizer (L : Set G))
    (u : L) (hzu : z * (u : G) = (u : G) * z) :
    inducedAutHom L e ⟨z, hz⟩ (e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) u)) =
      e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) u) := by
  rw [inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  congr 1
  rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  change z * (u : G) * z⁻¹ = u
  rw [hzu, mul_inv_cancel_right]

end Tools

end Item812Res7


namespace Item86ResProof

@[expose] def KF86D4ShiftConj : Prop :=
  ∀ (m : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ m) ^ 3 → (∀ c, σ c = c ^ 2 ^ m) →
    ∀ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y w t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Sec4.IsStdGraphFieldConj σ γ → γ y = y → orderOf y = 3 →
      ¬ Sec4.IsStdGraphFieldConj σ (γ * MulAut.conj y) →
      orderOf w = 3 → (γ * MulAut.conj y) w = w →
      t ≠ 1 → t ^ 2 = 1 → (γ * MulAut.conj y) t = t → t * w = w * t →
        ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, (γ * MulAut.conj y) g = g ∧
          (g * w * g⁻¹ = y ∨ g * w * g⁻¹ = y⁻¹)

end Item86ResProof

namespace Item812Res7

theorem isStdGraphFieldConj_conj {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hγ : Sec4.IsStdGraphFieldConj σ γ)
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Sec4.IsStdGraphFieldConj σ (α * γ * α⁻¹) := by
  obtain ⟨β, hβ⟩ := hγ
  refine ⟨α * β, ?_⟩
  rcases hβ with rfl | rfl
  · left
    group
  · right
    group

end Item812Res7


namespace Item812Res7

open Item86ResProof

variable {G : Type} [Group G] [Finite G]

theorem ne_one_of_partner {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X) (hcN : c ∈ Subgroup.normalizer (X : Set G)) :
    thetaQuotMulAut X (compAction X ⟨c, hcN⟩) ≠ 1 := by
  intro h1
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hbar : barCentralizer (Subgroup.zpowers c) X = ⊤ := by
    rw [Sec4.barCentralizer_zpowers_eq_autFix hcN, h1]
    exact eq_top_iff.mpr fun z _ => rfl
  have hqX := Sec6.isQuasisimple_of_mem_thetaComponentsAt hX
  have himg : imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))) = ⊤ := by
    rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hcN ⟨1, by rw [pow_one]; exact hc3⟩,
      hbar]
    exact inSubgroup_perfectResidual_of_isPerfect (Group.IsPerfect.top_iff.mpr hqX.1)
  set Kb := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hKb
  have hKbX : Kb ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hQ : IsQuasisimple (imageModTheta X Kb) :=
    LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr himg).trans Subgroup.topEquiv).symm hqX
  have hKbmem := Item87Proof.mem_thetaComponentsIn_residual hX
    (Item87Proof.isQuasisimple_quot_of_imageModTheta hKbX hQ)
  obtain ⟨hKe, -, hKe1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hKeL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ L :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hKeKb : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ Kb :=
    KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf hrel.2.2.2.1 (hKeL.trans hLc))
  have hKb' : Kb ∈ thetaComponentsIn (Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b}) := by
    rwa [inf_comm] at hKbmem
  have heq := Sec6.eq_of_mem_thetaComponentsIn_of_le hKe hKb'
    (Item87Proof.isPerfect_residual _) hKe1 le_rfl hKeKb
  apply hrel.2.2.2.2
  rw [heq]
  exact eq_sup_of_imageModTheta_eq_top hKbX himg

theorem exists_two_element_of_partner (hO : KF84OuterL2) (hR : KF84FieldReeStd)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n)
    {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G}
    (hrel : PairRel A c L b X) :
    ∃ u : X, a * (u : G) = (u : G) * a ∧ c * (u : G) = (u : G) * c ∧
      (∃ e : ℕ, u ^ 2 ^ e = 1) ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 X) u ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hLb⟩ := partner_data h hb hrel
  set Kd := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKd
  have hKdX : Kd ≤ X := by
    have h1 := hrel.2.2.2.1
    rwa [hLb] at h1
  have hKdL : Kd ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have h2 := two_dvd_card_barCentralizer_of hO hR h.toHyp81 (lt_card_of_sec8Std h) h.data83
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have haKd := mem_normalizer_residual_of_data83 h.toHyp81 h.data83
  have ht₀mem : (t₀ : Kd ⧸ aschbacherSolvableCore 3 Kd) ∈
      imageModTheta Kd (Kd ⊓ Subgroup.centralizer {a}) := by
    rw [KFacts.imageModTheta_centralizer_eq haKd ⟨1, by rw [pow_one]; exact ha3⟩]
    exact t₀.2
  obtain ⟨t, htC, htt₀⟩ := ht₀mem
  have ht₀2 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 Kd) t) = 2 := by
    rw [htt₀, Subgroup.orderOf_coe]
    exact ht₀
  obtain ⟨k, ⟨e, hke⟩, hkimg⟩ := exists_odd_pow_two_power _ t ht₀2
  have hta : (t : G) * a = a * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp htC).2
  have htc : (t : G) * c = c * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (hLc (hKdL t.2))
  refine ⟨⟨((t ^ k : Kd) : G), hKdX (t ^ k).2⟩, ?_, ?_, ⟨e, ?_⟩, ?_⟩
  · simp only [SubgroupClass.coe_pow]
    exact ((Commute.pow_left (show Commute (t : G) a from hta) k).eq).symm
  · simp only [SubgroupClass.coe_pow]
    exact ((Commute.pow_left (show Commute (t : G) c from htc) k).eq).symm
  · apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have h1 := congrArg (fun z : Kd => (z : G)) hke
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h1
  · intro h1
    have hθ : ((t ^ k : Kd) : G) ∈ ((aschbacherSolvableCore 3 X).map X.subtype : Subgroup G) :=
      ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    have hKdN : Kd ≤ Subgroup.normalizer
        (((aschbacherSolvableCore 3 X).map X.subtype : Subgroup G) : Set G) := fun z hz =>
      normalizer_le_normalizer_theta X (Subgroup.le_normalizer (hKdX hz))
    obtain ⟨u, hu, hue⟩ := Sec15.inf_le_map_aschbacherSolvableCore hKdN (isSolvable_theta X)
      (not_three_dvd_card_theta X) ⟨hθ, (t ^ k).2⟩
    have hut : u = t ^ k := Subtype.ext hue
    have h2' : QuotientGroup.mk' (aschbacherSolvableCore 3 Kd) (t ^ k) = 1 := by
      rw [← hut]
      exact (QuotientGroup.eq_one_iff _).mpr hu
    rw [hkimg] at h2'
    rw [h2', orderOf_one] at ht₀2
    exact absurd ht₀2 (by norm_num)

theorem exists_trialityD4_model {Y : Type} [Group Y] {m : ℕ} (hY : IsoTrialityD4 Y m) :
    1 ≤ m ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ m) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ m) ∧
        Nonempty (Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hm1 : 1 ≤ m := one_le_of_isoTrialityD4_or_isoGTwoEven (Or.inl hY)
  obtain ⟨q, hv, hq2, hqe, ⟨e₁⟩⟩ := hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (3 * m)) = (2 ^ m) ^ TwistTag.D4.order := by
    rw [GaloisField.card 2 (3 * m) (by omega), ← pow_mul, mul_comm]
    rfl
  obtain ⟨σ, hσ, -, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hm1
    (GaloisField 2 (3 * m)) hK
  have hKq : Nat.card (GaloisField 2 (3 * m)) = q.card ^ TwistTag.D4.order := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
    exact hK
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 _ hKq
    σ.toRingHom (fun x => by rw [TauCeti.PrimePower.card_def, hq2, hqe]; exact hσ x)
  have e₃ := CFSG.TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.D4)
    (σ := σ.toRingHom) Nat.prime_two hm1 hK hσ
  exact ⟨hm1, GaloisField 2 (3 * m), inferInstance, inferInstance, σ, hK, hσ,
    ⟨e₁.trans (e₂.symm.trans e₃)⟩⟩

theorem isStdGraphFieldConj_or_shift (hS : KF86D4ShiftConj) {m : ℕ} {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    {τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hτ3 : τ ^ 3 = 1)
    (hτin : ¬ IsInnerAut τ) {w v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hwo : orderOf w = 3) (hτw : τ w = w) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) (hτv : τ v = v)
    (hvw : v * w = w * v) :
    Sec4.IsStdGraphFieldConj σ τ ∨
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Sec4.IsStdGraphFieldConj σ (τ * MulAut.conj w ^ ε) := by
  rcases kF82D4OuterClasses_of_lang kF82D4LangCoset_holds m K σ hK hσ τ hτ3 hτin with
    hstd | ⟨γ, y, hγ, hγy, hy3, hτγ⟩
  · exact Or.inl hstd
  by_cases hstd : Sec4.IsStdGraphFieldConj σ τ
  · exact Or.inl hstd
  right
  rw [hτγ] at hstd hτw hτv
  obtain ⟨g, hg, hgw⟩ := hS m K σ hK hσ γ y w v hγ hγy hy3 hstd hwo hτw hv1 hv2 hτv hvw
  obtain ⟨ε, hε, hεeq⟩ := exists_shift_eq_conj hτγ (by rw [hτγ]; exact hg) hgw
  refine ⟨ε, hε, ?_⟩
  rw [hεeq, map_inv]
  have h1 := isStdGraphFieldConj_conj hγ (MulAut.conj g)⁻¹
  rwa [inv_inv] at h1

end Item812Res7

namespace Item86ResProof

theorem pair86D4_general (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hO : KF84OuterL2)
    (hR : KF84FieldReeStd) (hS : KF86D4ShiftConj) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n)
    {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G}
    (hrel : PairRel A c L b X) {m : ℕ}
    (hXm : IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) m) :
    IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) m ∨
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        IsoGTwoEven (barCentralizer (Subgroup.zpowers (a * c ^ ε)) X) m := by
  classical
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  obtain ⟨hkind, hckind⟩ := kinds_of_partner h418 hF h hb hrel
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  have hAel := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h3 : ∀ u ∈ A, u ^ 3 = 1 := hAel.2
  have hbA : b ∈ A := hbΓ.1
  have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz b hbA)
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3 b hbA)
      hbΓ.2.1 hA3 hAb X hX
  have haN : a ∈ Subgroup.normalizer (X : Set G) := hAN h.a_mem
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := hAN h.mem_A
  have hc3 : c ^ 3 = 1 := h3 c h.mem_A
  obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hXm
  have hinj := Item812Res7.conj_injective_of_center_trivial
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hτ3 : inducedAutHom X E ⟨a, haN⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one X E haN (h3 a h.a_mem)
  have haout : InducesOuterTheta a X := by
    rcases hkind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have hτin : ¬ IsInnerAut (inducedAutHom X E ⟨a, haN⟩) :=
    (not_isInnerAut_inducedAutHom_iff X E haN).mpr haout
  have hτcin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩) := by
    by_contra hnot
    have hcout : InducesOuterTheta c X := (not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hckind (Or.inr (KFacts.InducesStdKind.triality m hm1 _ hK σ hσ
      (KFacts.inducesKindTriality_graphField hm1 hK hσ X hc3 hcout E)))
  obtain ⟨w, hw⟩ := hτcin
  have hac' : (⟨a, haN⟩ : Subgroup.normalizer (X : Set G)) * ⟨c, hcN⟩ = ⟨c, hcN⟩ * ⟨a, haN⟩ :=
    Subtype.ext (hcomm a h.a_mem c h.mem_A)
  have hττc : inducedAutHom X E ⟨a, haN⟩ * MulAut.conj w =
      MulAut.conj w * inducedAutHom X E ⟨a, haN⟩ := by
    have h1 := congrArg (inducedAutHom X E) hac'
    rw [map_mul, map_mul, ← hw] at h1
    exact h1
  have hw3 : w ^ 3 = 1 := by
    apply hinj
    rw [map_pow MulAut.conj w 3, hw, map_one]
    exact inducedAutHom_pow_eq_one X E hcN hc3
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply Item812Res7.ne_one_of_partner h hb hrel hcN
    apply (MulAut.congr E).injective
    rw [map_one, ← inducedAutHom_apply, ← hw, map_one]
  obtain ⟨u, hua, huc, ⟨e, hue⟩, hu1⟩ := Item812Res7.exists_two_element_of_partner hO hR h hb hrel
  have hτs : inducedAutHom X E ⟨a, haN⟩ (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u)) =
      E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u) :=
    Item812Res7.inducedAutHom_apply_of_commute E haN u hua
  have hws : MulAut.conj w (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u)) =
      E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u) := by
    rw [hw]
    exact Item812Res7.inducedAutHom_apply_of_commute E hcN u huc
  have hse : (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u)) ^ 2 ^ e = 1 := by
    rw [← map_pow E, ← map_pow (QuotientGroup.mk' (aschbacherSolvableCore 3 X)), hue, map_one,
      map_one]
  have hs1 : E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u) ≠ 1 := by
    intro h1
    exact hu1 (E.injective (h1.trans (map_one E).symm))
  have hind : ∀ (ε : ℤ) (hεN : a * c ^ ε ∈ Subgroup.normalizer (X : Set G)),
      inducedAutHom X E ⟨a * c ^ ε, hεN⟩ = inducedAutHom X E ⟨a, haN⟩ * MulAut.conj w ^ ε := by
    intro ε hεN
    have h1 : (⟨a * c ^ ε, hεN⟩ : Subgroup.normalizer (X : Set G)) =
        ⟨a, haN⟩ * ⟨c, hcN⟩ ^ ε := Subtype.ext (by simp)
    have h2 := congrArg (inducedAutHom X E) h1
    rw [map_mul, map_zpow, ← hw] at h2
    exact h2
  have hclass : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (X : Set G)),
      Sec4.IsStdGraphFieldConj σ (inducedAutHom X E ⟨x, hx⟩) →
        IsoGTwoEven (barCentralizer (Subgroup.zpowers x) X) m := by
    rintro x hx ⟨β, hβ⟩
    exact isoGTwoEven_barCentralizer_of_conj_fieldActor hm1 hK hσ E hx β hβ
  generalize hτdef : inducedAutHom X E ⟨a, haN⟩ = τ at hτ3 hτin hττc hτs hind
  generalize E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) u) = s at hτs hws hse hs1
  obtain ⟨v, hv1, hv2, hτv, hvw⟩ := Item812Res7.exists_involution_of_two_element hse hs1 hτs hws
  rcases Item812Res7.isStdGraphFieldConj_or_shift hS hK hσ hτ3 hτin (orderOf_eq_prime hw3 hw1)
    (Item812Res7.apply_eq_of_commute_conj hinj hττc) hv1 hv2 hτv hvw with hstd | ⟨ε, hε, hstd⟩
  · left
    refine hclass a haN ?_
    rw [hτdef]
    exact hstd
  · right
    have hεN : a * c ^ ε ∈ Subgroup.normalizer (X : Set G) :=
      hAN (A.mul_mem h.a_mem (A.zpow_mem h.mem_A ε))
    refine ⟨ε, hε, hclass _ hεN ?_⟩
    rw [hind ε hεN]
    exact hstd

theorem pair86D4N_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hO : KF84OuterL2)
    (hR : KF84FieldReeStd) (hS : KF86D4ShiftConj) : Pair86D4N :=
  fun _ _ _ _ _ _ _ _ _ h _ _ _ hb hrel _ hXm =>
    pair86D4_general h45 h418 hO hR hS h hb hrel hXm

theorem pair86D4_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hO : KF84OuterL2)
    (hR : KF84FieldReeStd) (hS : KF86D4ShiftConj) : Pair86D4 :=
  fun _ _ _ _ _ _ _ _ _ h _ _ _ hb _ hrel hXn =>
    pair86D4_general h45 h418 hO hR hS h hb hrel hXn

end Item86ResProof

end CFSG.RankThree.PartTwo.Sec8
