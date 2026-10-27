module

public import CFSG.RankThree.PartOne.N143X.RankHelpers
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.KF.D4Sylow
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.RankThree.PartOne.KE.FamilyArith
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.KF.G2Torus

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KFU

namespace CFSG.RankThree.PartOne.N143X

theorem charP_algebraicClosure_two {K : Type} [Field K] [Finite K] {g : ℕ}
    (hK : Nat.card K = 2 ^ g) : CharP (AlgebraicClosure K) 2 := by
  have : CharP K 2 := charP_two_of_card hK
  exact charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2

section Frame

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem card_le_sq_of_conj_into_fixedTuples
    (S : Subgroup (Fin TwistTag.D4.tag.rank → Lˣ))
    (hS : ∀ a ∈ S, ∀ b ∈ S, d4QCoord a = d4QCoord b → a = b)
    {p : ℕ} (hp : 0 < p) {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hE : ∀ x ∈ E, x ^ p = 1) (g0 : ModGL TwistTag.D4.tag L)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hc : ∀ y ∈ E, g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
      S.map (rootDiagUnitHom TwistTag.D4.tag L)) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have hex : ∀ y : E, ∃ a, a ∈ S ∧ rootDiagUnit TwistTag.D4.tag a =
      g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 := fun y => by
    obtain ⟨a, ha, h⟩ := hc y y.2
    exact ⟨a, ha, h⟩
  choose a haS hay using hex
  have hpow : ∀ y : E, a y ^ p = 1 := by
    intro y
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    have h1 : rootDiagUnit TwistTag.D4.tag (a y ^ p) =
        rootDiagUnit TwistTag.D4.tag (a y) ^ p :=
      map_pow (rootDiagUnitHom TwistTag.D4.tag L) (a y) p
    have h2 : (c * (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) ^ p = 1 := by
      rw [conj_pow, hE y y.2, mul_one, mul_inv_cancel]
    have h3 : (g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0) ^ p =
        g0⁻¹ * triEmb K σ L (c * y * c⁻¹) ^ p * g0 := by
      simpa using conj_pow (a := g0⁻¹) (b := triEmb K σ L (c * y * c⁻¹)) (i := p)
    rw [h1, hay y, rootDiagUnit_one, h3, ← map_pow (triEmb K σ L), h2, map_one, mul_one,
      inv_mul_cancel]
  let φ : E → (Fin 2 → Lˣ) := fun y => d4QCoord (a y)
  have hφ : Function.Injective φ := by
    intro y y' h
    have h1 : a y = a y' := hS _ (haS y) _ (haS y') h
    have h2 := hay y
    rw [h1, hay y'] at h2
    have h3 : triEmb K σ L (c * y * c⁻¹) = triEmb K σ L (c * y' * c⁻¹) :=
      (mul_left_cancel (mul_right_cancel h2)).symm
    have h4 := triEmb_injective h3
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h4))
  refine card_le_sq_of_injective_fun hp φ hφ fun y k => ?_
  have h := congrFun (congrArg d4QCoord (hpow y)) k
  rwa [map_pow, map_one] at h

theorem card_le_sq_of_qplus
    {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1)
    [IsAlgClosure K L] [CharP L ℓ] {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨g0, -, -, -, hconj⟩ := d4Q_frame hf K hK σ hσ hp hp3 hpq L
  have hP : IsPGroup p E := isPGroup_of_pow_eq_one hE
  obtain ⟨c, hc⟩ := hconj E hP
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hT := d4Q_twistedTorus (L := L) (iterateFrobenius L ℓ f)
  refine card_le_sq_of_conj_into_fixedTuples (fixedCharTuples d4QM (iterateFrobenius L ℓ f))
    (fun a ha b hb h => eq_of_d4QCoord_eq (fun c => iterateFrobenius_def ℓ f c) ha hb h)
    hp.pos hE g0 c fun y hy => ?_
  rw [← hT]
  exact hc y hy

theorem card_le_sq_of_threeSix
    {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    [IsAlgClosure K L] [CharP L ℓ] {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨n, hn, w, hnW, hw, g0, -, -, -, hconj⟩ := d4T36_frame hf K hK σ hσ hε hp hp3 hpd L
  have hP : IsPGroup p E := isPGroup_of_pow_eq_one hE
  obtain ⟨c, hc⟩ := hconj E hP
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) hn w hnW (d4T36M ε) hw
  refine card_le_sq_of_conj_into_fixedTuples (fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f))
    (fun a ha b hb h => eq_of_d4QCoord_eq_d4T36 hε (fun c => iterateFrobenius_def ℓ f c) ha hb h)
    hp.pos hE g0 c fun y hy => ?_
  rw [← hT]
  exact hc y hy

end Frame

theorem card_le_sq_of_split
    {p f : ℕ} {K : Type} [Field K] {σ : K →+* K} (h : D4Param p f K σ)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have := h.finite
  have : NeZero p := ⟨h.prime.ne_zero⟩
  obtain ⟨g, hg⟩ := exists_conj_into_Tp3 h E hE
  have hex : ∀ x : E, ∃ b, tp3M h b = g * (x : graphFixedRootGroup TwistTag.D4 K σ) * g⁻¹ :=
    fun x => MonoidHom.mem_range.1 (hg x x.2)
  choose φ hφ using hex
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : graphFixedRootGroup TwistTag.D4 K σ) * g⁻¹ =
        g * (y : graphFixedRootGroup TwistTag.D4 K σ) * g⁻¹ := by rw [← hφ x, ← hφ y, hxy]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hR : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
  calc Nat.card E ≤ Nat.card (Fin 2 → rootsOfUnity p K) := Nat.card_le_card_of_injective φ hφinj
    _ = Nat.card (rootsOfUnity p K) ^ 2 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hR 2

theorem false_of_pow_three_twelve
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  obtain ⟨T, -, -, hall⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers hℓ hf K hK σ hσ
  obtain ⟨-, hcyc, -⟩ := hall p hp hp3 hpd
  have hP : IsPGroup p E := isPGroup_of_pow_eq_one hE
  have : IsCyclic E := hcyc E hP
  exact false_of_pow_three_of_isCyclic hp hE hcard

theorem false_of_pow_three_triality
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  classical
  have hf : 1 ≤ f := hX.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hpT : p ∣ Nat.card X := by
    have : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨hrow, -, -⟩ := exact_E_type_and_triality_cross_prime_factor_exhaustion (ℓ := 2) (f := f)
    hp (by omega) (by omega) hX
  obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 f := hdvd
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hX.2
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  set E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := E.map e.toMonoidHom
    with hE'def
  have hE' : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (e y) ^ p = 1
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hcard]
  have hchar : CharP (AlgebraicClosure K) 2 :=
    charP_algebraicClosure_two (K := K) (g := f * 3) (by rw [hK', ← pow_mul])
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  ·
    have hpq : p ∣ 2 ^ f - 1 := by
      rw [cycloVal_one] at hd
      have h1 : (p : ℤ) ∣ ((2 ^ f - 1 : ℕ) : ℤ) := by rw [Nat.cast_sub hq1]; exact hd
      exact_mod_cast h1
    have hD : D4Param p f K σ.toRingHom := ⟨hp, by omega, hf, hK', fun c => hσ c, hpq⟩
    have := card_le_sq_of_split hD E' hE'
    omega
  ·
    rw [cycloVal_two] at hd
    have := card_le_sq_of_qplus (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ hp (by omega) hd hE'
    omega
  ·
    rw [cycloVal_three] at hd
    have := card_le_sq_of_threeSix (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ (ε := 1)
      (Or.inl rfl) hp (by omega) (by simpa using hd) hE'
    omega
  ·
    rw [cycloVal_six] at hd
    have := card_le_sq_of_threeSix (ℓ := 2) (L := AlgebraicClosure K) hf hK' hσ (ε := -1)
      (Or.inr rfl) hp (by omega) (by simpa [sub_eq_add_neg] using hd) hE'
    omega
  ·
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 := by
      have h24 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    exact false_of_pow_three_twelve Nat.prime_two hf hK' σ hσ hp (by omega) hpd hE' hcard'

end CFSG.RankThree.PartOne.N143X
