module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3ProofInputs
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace Res413Cover

theorem mem_range_conj_of_pow_three {T : Type*} [Group T] (hout : ¬ 3 ∣ Nat.card (Outer T))
    {x : MulAut T} (hx : x ^ 3 = 1) : x ∈ (MulAut.conj : T →* MulAut T).range := by
  set y : Outer T := QuotientGroup.mk x with hy
  have h1 : orderOf y ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hy, ← QuotientGroup.mk_pow, hx]
    rfl
  have h2 : orderOf y ∣ Nat.card (Outer T) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h3 | h3
  · exact (QuotientGroup.eq_one_iff (N := inner T) x).mp (orderOf_eq_one_iff.mp h3)
  · rw [h3] at h2
    exact absurd h2 hout

theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx y']
  rw [hY, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_pow_three' {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ^ 3 = 1 := by
  rw [← map_pow, ← map_pow]
  have h : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  rw [h, map_one, map_one]

theorem center_pow_three_eq_one {L : Subgroup G}
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) :
    ∀ z : L, z ∈ Subgroup.center L → z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hzq : (z : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hz) y]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzq
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have h1 : orderOf (⟨z, hzq⟩ : aschbacherSolvableCore 3 L) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
  have h2 : orderOf (⟨z, hzq⟩ : aschbacherSolvableCore 3 L) ∣
      Nat.card (aschbacherSolvableCore 3 L) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h3 | h3
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
  · rw [h3] at h2
    exact absurd h2 hθ3

theorem false_of_noEnineAction (h45 : Item4_5) {L A E : Subgroup G} {c : G}
    (hyp : Hyp413 L A E c)
    (hout : ¬ 3 ∣ Nat.card (Outer (L ⧸ aschbacherSolvableCore 3 L)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : ∀ D T : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 D →
      9 ≤ Nat.card D → IsPGroup 2 T → D ≤ Subgroup.normalizer (T : Set _) →
      T ≤ Subgroup.centralizer (D : Set _)) : False := by
  obtain ⟨hG, hL, hT, hr⟩ := hyp
  have hT' := hT
  obtain ⟨hAmax, hAc, hc3, -, -, -⟩ := hT'
  have hA := hAmax.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hZL := odd_card_center_of_le_normalizer hG hA (by omega) hm hAN
  have hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := by
    intro a ha
    refine exists_inner_of_not_inducesOuterTheta hL.1 (hAN ha) ?_
    rintro ⟨ha', hout'⟩
    exact hout' (mem_range_conj_of_pow_three hout (thetaQuotMulAut_pow_three' ha' (hA.2 a ha)))
  have hZ3 := center_pow_three_eq_one hZ
  have hdec := exists_mem_inf_of_forall_inner hZ3 hAmax hAc hinner
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcL := zpowers_inf_eq_bot hZ3 hcAC.2 hc3'
  have h81 : 81 ≤ Nat.card (A ⊓ L : Subgroup G) := by
    have h1 := card_le_three_mul hA hcAC.1 hc3 hdec (le_refl A)
    rw [inf_of_le_right inf_le_left, hm] at h1
    have h2 : 3 ^ 5 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
    omega
  obtain ⟨D, T₁, hDB, hD9, hT₁L, hT₁2, hDN, hTD⟩ :=
    exists_two_subgroup_of_isTriple413 hG hL hT hdec hcL h81
  obtain ⟨D', T', hD', hD'9, hT', hD'T', hT'D'⟩ := exists_thetaQuot_of_two_subgroup hL.1 hZL
    (isElemAbelian_of_le hA (hDB.trans inf_le_left)) (hDB.trans inf_le_right) hD9 hT₁L hT₁2 hDN
    hTD
  exact hT'D' (hK D' T' hD' hD'9 hT' hD'T')

end Res413Cover

namespace Res413Cover

open Item434CharThree Res423Two

theorem le_centralizer_of_sl {e : ℕ} (he : e ≠ 0) {X : Type} [Group X] [Finite X]
    (θ : X ≃* SL(3, GaloisField 3 e)) {D T : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : 9 ≤ Nat.card D) (hT : IsPGroup 2 T) (hDT : D ≤ Subgroup.normalizer (T : Set X)) :
    T ≤ Subgroup.centralizer (D : Set X) := by
  have : Finite SL(3, GaloisField 3 e) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨g, a₀, b₀, -, hle⟩ := exists_map_le_lineSub he θ hD
  set φ := θ.trans (MulAut.conj g⁻¹) with hφ
  set D₁ := D.map φ.toMonoidHom with hD₁
  set T₂ := T.map φ.toMonoidHom with hT₂
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := isElemAbelian_map _ hD
  have hD₁9 : 3 ^ 2 ≤ Nat.card D₁ := by
    rw [hD₁, Subgroup.card_map_of_injective φ.injective]
    norm_num
    exact hD9
  have hT₂2 : IsPGroup 2 T₂ := hT.map _
  have hD₁T₂ : D₁ ≤ Subgroup.normalizer (T₂ : Set SL(3, GaloisField 3 e)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    have hdN := Subgroup.mem_normalizer_iff.mp (hDT hd) y'
    constructor
    · rintro ⟨t, ht, hty⟩
      have hty' : t = y' := φ.injective hty
      subst hty'
      exact ⟨d * t * d⁻¹, hdN.mp ht, by simp⟩
    · rintro ⟨t, ht, hty⟩
      have hty' : t = d * y' * d⁻¹ := by
        apply φ.injective
        simpa using hty
      rw [hty'] at ht
      exact ⟨y', hdN.mpr ht, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card T₂) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT₂2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have key : T₂ ≤ Subgroup.centralizer (D₁ : Set SL(3, GaloisField 3 e)) := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hD₁e hD₁9 hD₁T₂ hcop
      fun v hv hv1 => ?_
    rintro w ⟨hwT, hwv⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
    have hU := commutator_mem_heis (hle hv) hv1 hwv' (hle hr)
    have hW : r * w * r⁻¹ * w⁻¹ ∈ T₂ :=
      T₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hD₁T₂ hr) w).mp hwT) (T₂.inv_mem hwT)
    have h1 := eq_one_of_isPGroup_two hT₂2 hW (pow_three_eq_one_of_mem_heis hU)
    calc r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
      _ = w * r := by rw [h1, one_mul]
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h := Subgroup.mem_centralizer_iff.mp (key ⟨t, ht, rfl⟩) (φ d) ⟨d, hd, rfl⟩
  apply φ.injective
  simpa using h

theorem le_centralizer_of_su {e : ℕ} (he : e ≠ 0) {X : Type} [Group X] [Finite X]
    (θ : X ≃* SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) {D T : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : 9 ≤ Nat.card D) (hT : IsPGroup 2 T)
    (hDT : D ≤ Subgroup.normalizer (T : Set X)) : T ≤ Subgroup.centralizer (D : Set X) := by
  have : Finite (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) :=
    Finite.of_injective _ Subtype.val_injective
  obtain ⟨g, a₀, -, hle⟩ := exists_map_le_lineU he θ hD
  set φ := θ.trans (MulAut.conj g⁻¹) with hφ
  set D₁ := D.map φ.toMonoidHom with hD₁
  set T₂ := T.map φ.toMonoidHom with hT₂
  have hD₁e : CFSG.Assembly.IsElemAbelian 3 D₁ := isElemAbelian_map _ hD
  have hD₁9 : 3 ^ 2 ≤ Nat.card D₁ := by
    rw [hD₁, Subgroup.card_map_of_injective φ.injective]
    norm_num
    exact hD9
  have hT₂2 : IsPGroup 2 T₂ := hT.map _
  have hD₁T₂ : D₁ ≤ Subgroup.normalizer
      (T₂ : Set (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    have hdN := Subgroup.mem_normalizer_iff.mp (hDT hd) y'
    constructor
    · rintro ⟨t, ht, hty⟩
      have hty' : t = y' := φ.injective hty
      subst hty'
      exact ⟨d * t * d⁻¹, hdN.mp ht, by simp⟩
    · rintro ⟨t, ht, hty⟩
      have hty' : t = d * y' * d⁻¹ := by
        apply φ.injective
        simpa using hty
      rw [hty'] at ht
      exact ⟨y', hdN.mpr ht, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card T₂) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT₂2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have key : T₂ ≤ Subgroup.centralizer
      (D₁ : Set (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3)) := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hD₁e hD₁9 hD₁T₂ hcop
      fun v hv hv1 => ?_
    rintro w ⟨hwT, hwv⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hwv' : w * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwv
    have h3 := commutator_pow_three_heisU (hle hv).1 hv1 hwv' (hle hr).1
    have hW : r * w * r⁻¹ * w⁻¹ ∈ T₂ :=
      T₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hD₁T₂ hr) w).mp hwT) (T₂.inv_mem hwT)
    have h1 := eq_one_of_isPGroup_two hT₂2 hW h3
    calc r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
      _ = w * r := by rw [h1, one_mul]
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h := Subgroup.mem_centralizer_iff.mp (key ⟨t, ht, rfl⟩) (φ d) ⟨d, hd, rfl⟩
  apply φ.injective
  simpa using h

theorem center_SU_nine_eq_bot :
    Subgroup.center (SU (unitaryInvolution (GaloisField 3 (2 * 2)) 3 2) 3) = ⊥ := by
  have hF := card_galois_two_mul (e := 2) two_ne_zero
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine center_eq_bot_of_equiv (equivStatedSU hF 3) ?_
  rw [(isQuasisimple_statedSU_of_card hF le_rfl (by decide)).2]
  exact statedScalars_subgroupOf_statedSU_eq_bot _

end Res413Cover

open Res413Cover Item434CharThree in
theorem inputs413L3Nine_of (h45 : Item4_5) : Inputs413L3Nine := by
  intro G _ _ L A E c hyp h39
  rcases h39 with h | h
  ·
    obtain ⟨e₁⟩ := h
    set θ := e₁.trans (slEquivProjSL (GaloisField 3 2)).symm with hθ
    refine false_of_noEnineAction h45 hyp ?_ ?_ ?_
    · intro h3
      have h := card_outer_SL_three_dvd (e := 2) (by norm_num)
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv] at h
      have := h3.trans h
      omega
    · exact center_eq_bot_of_equiv θ (center_SL_three_eq_bot _)
    · intro D T hD hD9 hT hDT
      exact le_centralizer_of_sl two_ne_zero θ hD hD9 hT hDT
  ·
    obtain ⟨e₁⟩ := h
    set θ := e₁.trans (suEquivProjSU two_ne_zero).symm with hθ
    refine false_of_noEnineAction h45 hyp ?_ ?_ ?_
    · intro h3
      have h := card_outer_SU_three_dvd (e := 2) (by norm_num)
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv] at h
      have := h3.trans h
      omega
    · exact center_eq_bot_of_equiv θ center_SU_nine_eq_bot
    · intro D T hD hD9 hT hDT
      exact le_centralizer_of_su two_ne_zero θ hD hD9 hT hDT

section Closed

theorem inputs413L3Nine_holds
    : Inputs413L3Nine :=
  inputs413L3Nine_of rank3II_4_5

end Closed

end CFSG.RankThree.PartTwo.Sec4
