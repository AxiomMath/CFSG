module

public import CFSG.RankThree.PartTwo.Sec18.Item187F6Hyper

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise
open Polynomial

private noncomputable def Phi5 : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X ^ 2 + X + 1

private theorem Phi5_natDegree : Phi5.natDegree = 4 := by
  unfold Phi5; compute_degree!

private theorem Phi5_ne_zero : Phi5 ≠ 0 := by
  intro h; have := Phi5_natDegree; rw [h, natDegree_zero] at this; omega

private theorem monic_of_ne_zero_zmod2 (p : (ZMod 2)[X]) (hp0 : p ≠ 0) : p.Monic :=
  (show ∀ c : ZMod 2, c ≠ 0 → c = 1 from by decide) _ (leadingCoeff_ne_zero.mpr hp0)

private theorem Phi5_monic : Phi5.Monic := monic_of_ne_zero_zmod2 _ Phi5_ne_zero

private theorem two_eq_zero_alg (K : Type) [Ring K] [Algebra (ZMod 2) K] : (2 : K) = 0 := by
  rw [show (2 : K) = algebraMap (ZMod 2) K 2 from (map_ofNat _ 2).symm]
  rw [show (2 : ZMod 2) = 0 from rfl, map_zero]

private theorem root_five_of_aeval {L : Type} [Field L] [Algebra (ZMod 2) L] {r : L}
    (hr : aeval r Phi5 = 0) : r ^ 5 = 1 ∧ r ≠ 1 := by
  have hid : (r ^ 5 - 1 : L) = (r - 1) * aeval r Phi5 := by
    have h := congrArg (aeval r) (show (X ^ 5 - 1 : (ZMod 2)[X]) = (X - 1) * Phi5 by
      unfold Phi5; ring)
    simpa [map_sub, map_mul, map_pow, aeval_X, aeval_one] using h
  refine ⟨sub_eq_zero.mp (by rw [hid, hr, mul_zero]), fun h1 => ?_⟩
  rw [h1] at hr
  have h2 := two_eq_zero_alg L
  unfold Phi5 at hr
  simp only [map_add, map_pow, aeval_X, aeval_one] at hr
  have : (1 : L) = 0 := by linear_combination hr - (2 : L) * h2
  exact one_ne_zero this

private theorem natCard_adjoinRoot (p : (ZMod 2)[X]) (hp : Irreducible p) :
    Nat.card (AdjoinRoot p) = 2 ^ p.natDegree := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hfin : Module.Finite (ZMod 2) (AdjoinRoot p) :=
    (monic_of_ne_zero_zmod2 p hp0).finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    (AdjoinRoot.powerBasis hp0).finrank, AdjoinRoot.powerBasis_dim]

private theorem Phi5_irreducible : Irreducible Phi5 := by
  have hnu : ¬ IsUnit Phi5 := fun h => by
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [Phi5_natDegree] at this; norm_num at this
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnu Phi5_ne_zero
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpm : p.Monic := monic_of_ne_zero_zmod2 p hp0
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard := natCard_adjoinRoot p hp
  have hr : aeval (AdjoinRoot.root p) Phi5 = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact hpd
  obtain ⟨hr5, hr1⟩ := root_five_of_aeval hr
  have hr0 : AdjoinRoot.root p ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at hr5; exact zero_ne_one hr5
  haveI : Finite (AdjoinRoot p) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Fintype (AdjoinRoot p) := Fintype.ofFinite _
  have h1 := FiniteField.pow_card_sub_one_eq_one (AdjoinRoot.root p) hr0
  rw [← Nat.card_eq_fintype_card, hcard] at h1
  have hdiv : 5 ∣ 2 ^ p.natDegree - 1 := by
    have h5 : orderOf (AdjoinRoot.root p) = 5 := orderOf_eq_prime hr5 hr1
    exact h5 ▸ orderOf_dvd_of_pow_eq_one h1
  have hlo : 0 < p.natDegree := hp.natDegree_pos
  have hhi : p.natDegree ≤ Phi5.natDegree := natDegree_le_of_dvd hpd Phi5_ne_zero
  rw [Phi5_natDegree] at hhi
  have hpos : 1 ≤ 2 ^ p.natDegree := Nat.one_le_two_pow
  have hmod : 2 ^ p.natDegree % 5 = 1 := by omega
  have hn4 : p.natDegree = 4 := by
    rcases (by omega : p.natDegree = 1 ∨ p.natDegree = 2 ∨ p.natDegree = 3 ∨ p.natDegree = 4)
      with h | h | h | h
    · rw [h] at hmod; norm_num at hmod
    · rw [h] at hmod; norm_num at hmod
    · rw [h] at hmod; norm_num at hmod
    · exact h
  have heq : Phi5 = p := eq_of_monic_of_dvd_of_natDegree_le hpm Phi5_monic hpd
    (by rw [Phi5_natDegree, hn4])
  rw [heq]; exact hp

private theorem aeval_Phi5_apply {M : Type*} [Ring M] [Algebra (ZMod 2) M] (x : M) :
    aeval x Phi5 = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  simp [Phi5]

private theorem X_pow_five_sub_one_eq : (X ^ 5 - 1 : (ZMod 2)[X]) = (X - 1) * Phi5 := by
  unfold Phi5; ring

private theorem Phi5_sq_eq : Phi5 * Phi5 - Phi5 = (X ^ 5 - 1) * (X ^ 3 + X) := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := two_eq_zero_alg _
  unfold Phi5
  linear_combination (X ^ 7 + X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + X) * h2

private theorem commute_aeval_of {M : Type*} [Ring M] [Algebra (ZMod 2) M] {f T : M}
    (h : Commute f T) (p : (ZMod 2)[X]) : Commute f (aeval T p) := by
  have hT : T ∈ Subalgebra.centralizer (ZMod 2) ({f} : Set M) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact h
  have hle : Algebra.adjoin (ZMod 2) ({T} : Set M) ≤
      Subalgebra.centralizer (ZMod 2) ({f} : Set M) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hT)
  have hmem : aeval T p ∈ Algebra.adjoin (ZMod 2) ({T} : Set M) := by
    simp
  have hp := hle hmem
  rw [Subalgebra.mem_centralizer_iff] at hp
  exact hp f (Set.mem_singleton f)

private theorem add_self_zmod2 {A : Type} [AddCommGroup A] [Module (ZMod 2) A] (x : A) :
    x + x = 0 := by
  have h : (2 : ℕ) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]
  rwa [two_nsmul] at h

private theorem core_bound {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {G : Type} [Group G] (σ : G →* Module.End (ZMod 2) A) {z : G}
    (hzc : ∀ g : G, g * z = z * g) (hzcomm : z ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
    (hz5 : σ z ^ 5 = 1) (hz1 : σ z ≠ 1) :
    ∃ W : Submodule (ZMod 2) A, 2 ^ 20 ≤ Nat.card W ∧ ∀ w ∈ W, σ z w = w → w = 0 := by
  classical
  haveI : Fact (Irreducible Phi5) := ⟨Phi5_irreducible⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Module.End (ZMod 2) A, T = σ z := ⟨_, rfl⟩
  rw [← hTdef] at hz5 hz1
  obtain ⟨N, hNdef⟩ : ∃ N : Module.End (ZMod 2) A, N = aeval T Phi5 := ⟨_, rfl⟩
  have hNexp : N = T ^ 4 + T ^ 3 + T ^ 2 + T + 1 := by
    rw [hNdef, aeval_Phi5_apply]
  have h5 : aeval T (X ^ 5 - 1 : (ZMod 2)[X]) = 0 := by
    simp [map_sub, map_pow, aeval_X, aeval_one, hz5]
  have hTN : T * N = N := by
    have h := congrArg (aeval T) X_pow_five_sub_one_eq
    rw [h5, map_mul, map_sub, aeval_X, aeval_one, ← hNdef] at h
    have h' : (T - 1) * N = 0 := h.symm
    rw [sub_mul, one_mul, sub_eq_zero] at h'
    exact h'
  have hNN : N * N = N := by
    have h := congrArg (aeval T) Phi5_sq_eq
    rw [map_sub, map_mul, map_mul, h5, zero_mul, ← hNdef] at h
    exact sub_eq_zero.mp h
  have hσT : ∀ g : G, σ g * T = T * σ g := fun g => by
    rw [hTdef, ← map_mul, ← map_mul, hzc g]
  have hσN : ∀ g : G, σ g * N = N * σ g := fun g => by
    rw [hNdef]; exact commute_aeval_of (hσT g) Phi5
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) A, W = LinearMap.ker N := ⟨_, rfl⟩
  have hmemW : ∀ w, w ∈ W ↔ N w = 0 := fun w => by rw [hW, LinearMap.mem_ker]
  have hWG : ∀ g : G, ∀ w ∈ W, σ g w ∈ W := fun g w hw => by
    rw [hmemW] at hw ⊢
    have h := LinearMap.congr_fun (hσN g) w
    rw [Module.End.mul_apply, Module.End.mul_apply, hw, map_zero] at h
    exact h.symm
  let gW : G → Module.End (ZMod 2) W := fun g => (σ g).restrict (hWG g)
  have hgW : ∀ (g : G) (w : W), ((gW g w : W) : A) = σ g (w : A) := fun _ _ => rfl
  have hpowW : ∀ (g : G) (n : ℕ) (w : W), (((gW g) ^ n) w : A) = ((σ g) ^ n) (w : A) := by
    intro g n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hgW]
  have hcommW : ∀ g : G, Commute (gW g) (gW z) := fun g => by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have h := LinearMap.congr_fun (hσT g) (w : A)
    rw [hTdef, Module.End.mul_apply, Module.End.mul_apply] at h
    simpa only [Module.End.mul_apply, hgW] using h
  have hgWz : ∀ w : W, ((gW z) w : A) = σ z (w : A) := hgW z
  have hΦW : aeval (gW z) Phi5 = 0 := by
    rw [aeval_Phi5_apply]
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have hN0 : N (w : A) = 0 := (hmemW w).mp w.2
    rw [hNexp, hTdef] at hN0
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply,
      Submodule.coe_add, Submodule.coe_zero, hpowW, hgWz]
    simpa only [LinearMap.add_apply, Module.End.one_apply] using hN0
  obtain ⟨ι, hιmk⟩ : ∃ ι : AdjoinRoot Phi5 →+* Module.End (ZMod 2) W,
      ∀ q : (ZMod 2)[X], ι (AdjoinRoot.mk Phi5 q) = aeval (gW z) q := by
    refine ⟨Ideal.Quotient.lift (Ideal.span {Phi5})
      (aeval (gW z) : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) W).toRingHom ?_, fun q => ?_⟩
    · intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [map_mul, hΦW]
    · exact Ideal.Quotient.lift_mk _ _ _
  have hιroot : ι (AdjoinRoot.root Phi5) = gW z := by
    rw [AdjoinRoot.root, hιmk, aeval_X]
  letI : Module (AdjoinRoot Phi5) W := Module.compHom W ι
  have hsmul : ∀ (c : AdjoinRoot Phi5) (w : W), c • w = ι c w := fun _ _ => rfl
  have hcommι : ∀ (g : G) (c : AdjoinRoot Phi5), Commute (gW g) (ι c) := by
    intro g c
    induction c using AdjoinRoot.induction_on with
    | ih q => rw [hιmk]; exact commute_aeval_of (hcommW g) q
  let gK : G → (W →ₗ[AdjoinRoot Phi5] W) := fun g =>
    { toFun := gW g
      map_add' := fun x y => (gW g).map_add x y
      map_smul' := fun c w => by
        have h := LinearMap.congr_fun (hcommι g c).eq w
        simp only [Module.End.mul_apply] at h
        exact h }
  have hgK_coe : ∀ (g : G) (w : W), ((gK g w : W) : A) = σ g (w : A) := fun _ _ => rfl
  have hgK_one : gK 1 = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [hgK_coe, map_one, Module.End.one_apply]
  have hgK_mul : ∀ g h : G, gK (g * h) = gK g * gK h := by
    intro g h
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [hgK_coe, map_mul, Module.End.mul_apply]
  let χ : G →* Module.End (AdjoinRoot Phi5) W :=
    { toFun := gK
      map_one' := hgK_one
      map_mul' := hgK_mul }
  let D : G →* AdjoinRoot Phi5 :=
    (LinearMap.det : Module.End (AdjoinRoot Phi5) W →* AdjoinRoot Phi5).comp χ
  have hDinv : ∀ g : G, D g * D g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  let S : Subgroup G :=
    { carrier := {g | D g = 1}
      mul_mem' := fun {a b} ha hb => by
        show D (a * b) = 1
        have ha' : D a = 1 := ha
        have hb' : D b = 1 := hb
        rw [map_mul, ha', hb', mul_one]
      one_mem' := map_one D
      inv_mem' := fun {a} ha => by
        have ha' : D a = 1 := ha
        have h := hDinv a
        show D a⁻¹ = 1
        rw [ha', one_mul] at h
        exact h }
  have hcomm_le : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    show D ⁅g₁, g₂⁆ = 1
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    calc D g₁ * D g₂ * D g₁⁻¹ * D g₂⁻¹
        = (D g₁ * D g₁⁻¹) * (D g₂ * D g₂⁻¹) := by ring
      _ = 1 := by rw [hDinv, hDinv, mul_one]
  have hzD : LinearMap.det (gK z) = 1 := hcomm_le hzcomm
  have hzK : gK z = (AdjoinRoot.root Phi5) • LinearMap.id := by
    apply LinearMap.ext
    intro w
    rw [LinearMap.smul_apply, LinearMap.id_apply, hsmul, hιroot]
    rfl
  have hdet : LinearMap.det (gK z) = (AdjoinRoot.root Phi5) ^
      Module.finrank (AdjoinRoot Phi5) W := by
    rw [hzK, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hrootpow : (AdjoinRoot.root Phi5) ^ Module.finrank (AdjoinRoot Phi5) W = 1 := by
    rw [← hdet]; exact hzD
  have hroot5 := root_five_of_aeval (r := AdjoinRoot.root Phi5)
    (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  have hd5 : 5 ∣ Module.finrank (AdjoinRoot Phi5) W := by
    have h5' : orderOf (AdjoinRoot.root Phi5) = 5 := orderOf_eq_prime hroot5.1 hroot5.2
    exact h5' ▸ orderOf_dvd_of_pow_eq_one hrootpow
  obtain ⟨a, ha⟩ : ∃ a : A, T a ≠ a := by
    by_contra hcon
    push_neg at hcon
    exact hz1 (LinearMap.ext fun x => by rw [Module.End.one_apply]; exact hcon x)
  have hNNa : N (N a) = N a := by rw [← Module.End.mul_apply, hNN]
  have huW : a - N a ∈ W := by
    rw [hmemW, map_sub, hNNa, sub_self]
  have hune : a - N a ≠ 0 := by
    intro h0
    have h1 : a = N a := sub_eq_zero.mp h0
    have h2 : T (N a) = N a := by rw [← Module.End.mul_apply, hTN]
    exact ha ((congrArg T h1).trans (h2.trans h1.symm))
  haveI : Nontrivial W := ⟨⟨⟨a - N a, huW⟩, 0, fun h => hune (congrArg Subtype.val h)⟩⟩
  have hdpos : 0 < Module.finrank (AdjoinRoot Phi5) W := Module.finrank_pos
  have hd5ge : 5 ≤ Module.finrank (AdjoinRoot Phi5) W := Nat.le_of_dvd hdpos hd5
  haveI : Finite (AdjoinRoot Phi5) := by
    haveI : Module.Finite (ZMod 2) (AdjoinRoot Phi5) := Phi5_monic.finite_adjoinRoot
    exact Module.finite_of_finite (ZMod 2)
  haveI : Module.Finite (AdjoinRoot Phi5) W := Module.finite_iff_finite.mpr inferInstance
  have hcardK : Nat.card (AdjoinRoot Phi5) = 2 ^ 4 := by
    rw [natCard_adjoinRoot Phi5 Phi5_irreducible, Phi5_natDegree]
  have hcardW : Nat.card W = Nat.card (AdjoinRoot Phi5) ^ Module.finrank (AdjoinRoot Phi5) W :=
    Module.natCard_eq_pow_finrank
  refine ⟨W, ?_, ?_⟩
  · rw [hcardW, hcardK, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro w hw hfix
    have hfix' : T w = w := by rw [hTdef]; exact hfix
    have hTk : ∀ k : ℕ, (T ^ k) w = w := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hfix', ih]
    have hN0 : N w = 0 := (hmemW w).mp hw
    rw [hNexp] at hN0
    simp only [LinearMap.add_apply, Module.End.one_apply, hTk, hfix'] at hN0
    have h2 := add_self_zmod2 w
    calc w = (w + w + w + w + w) - (w + w) - (w + w) := by abel
      _ = 0 := by rw [hN0, h2]; simp

variable {V : Type} [Group V] [Finite V]

private theorem mem_Fix_iff {F : Subgroup (MulAut V)} {v : V} :
    v ∈ Fix F ↔ ∀ f ∈ F, f v = v :=
  ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
    fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩

private theorem exists_central_five {G : Type} [Group G] [Finite G] (hG : IsPGroup 5 G)
    (hnab : ∃ x y : G, x * y ≠ y * x) :
    ∃ z : G, orderOf z = 5 ∧ (∀ g : G, g * z = z * g) ∧
      z ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y, hxy⟩ := hnab
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := ⟨_, rfl⟩
  have hCne : C ≠ ⊥ := by
    intro h
    apply hxy
    have hmem : ⁅x, y⁆ ∈ C := by
      rw [hCdef]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hCn : C.Normal := by
    rw [hCdef]
    infer_instance
  haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G, K = C ⊓ Subgroup.center G := ⟨_, rfl⟩
  have hKne : K ≠ ⊥ := by
    rw [hKdef]
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hCne
  have hK5 : IsPGroup 5 K := hG.to_subgroup K
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hK5).mp inferInstance
  have hdvd : 5 ∣ Nat.card K := by
    rw [hcard]
    exact dvd_pow_self 5 (by omega)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 hdvd
  have hgK : (g : G) ∈ C ⊓ Subgroup.center G := by
    rw [← hKdef]
    exact g.2
  obtain ⟨hgC, hgZ⟩ := Subgroup.mem_inf.mp hgK
  refine ⟨(g : G), ?_, fun h => (Subgroup.mem_center_iff.mp hgZ) h, ?_⟩
  · rw [Subgroup.orderOf_coe, hg]
  · rw [← hCdef]
    exact hgC

private theorem two_pow_twenty_core (hV : ∀ v : V, v * v = 1) {F : Subgroup (MulAut V)}
    (hF : IsPGroup 5 F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) :
    2 ^ 20 ≤ (Fix F).index := by
  classical
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V ≃ V))
      (fun f g h => MulEquiv.ext fun v => congrArg (fun e : V ≃ V => e v) h)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hFnab
  obtain ⟨z, hzord, hzc, hzcomm⟩ := exists_central_five hF
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hV _)
    rw [mul_inv_rev, ha, hb] at hab
    exact hab.symm
  letI : AddCommGroup (Additive V) :=
    { (inferInstance : AddGroup (Additive V)) with
      add_comm := fun a b => congrArg Additive.ofMul (hcomm (Additive.toMul a) (Additive.toMul b)) }
  have h2 : ∀ a : Additive V, (2 : ℕ) • a = 0 := fun a => by
    rw [two_nsmul]
    exact hV (Additive.toMul a)
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  let act : MulAut V →* Module.End (ZMod 2) (Additive V) :=
    { toFun := fun f => AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive f).toAddMonoidHom
      map_one' := by ext a; rfl
      map_mul' := fun f g => by ext a; rfl }
  have hact : ∀ (f : MulAut V) (a : Additive V), act f a = Additive.ofMul (f (Additive.toMul a)) :=
    fun _ _ => rfl
  have hact_inj : ∀ f : MulAut V, act f = 1 → f = 1 := by
    intro f hf
    apply MulEquiv.ext
    intro v
    have h := LinearMap.congr_fun hf (Additive.ofMul v)
    rw [hact, Module.End.one_apply] at h
    exact Additive.ofMul.injective h
  have hz1 : act (z : MulAut V) ≠ 1 := by
    intro h
    have h' := hact_inj _ h
    have : z = 1 := Subtype.ext h'
    rw [this, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  let σ : F →* Module.End (ZMod 2) (Additive V) := act.comp F.subtype
  have hz5 : σ z ^ 5 = 1 := by
    rw [← map_pow]
    have : z ^ 5 = 1 := by
      rw [← hzord]
      exact pow_orderOf_eq_one z
    rw [this, map_one]
  obtain ⟨W, hW2, hWfix⟩ := core_bound σ hzc hzcomm hz5 hz1
  haveI : Finite (V ⧸ Fix F) := Quotient.finite _
  let φ : W → V ⧸ Fix F := fun w => QuotientGroup.mk (Additive.toMul (w : Additive V))
  have hinj : Function.Injective φ := by
    intro w₁ w₂ h
    have h' : (Additive.toMul (w₁ : Additive V))⁻¹ * Additive.toMul (w₂ : Additive V) ∈ Fix F :=
      QuotientGroup.eq.mp h
    have e : Additive.toMul ((w₂ : Additive V) - (w₁ : Additive V)) =
        (Additive.toMul (w₁ : Additive V))⁻¹ * Additive.toMul (w₂ : Additive V) :=
      (toMul_sub _ _).trans ((div_eq_mul_inv _ _).trans (hcomm _ _))
    have hfix : Additive.toMul ((w₂ : Additive V) - (w₁ : Additive V)) ∈ Fix F := by
      rw [e]
      exact h'
    have hzfix : act (z : MulAut V) ((w₂ : Additive V) - (w₁ : Additive V)) =
        (w₂ : Additive V) - (w₁ : Additive V) := by
      rw [hact]
      exact congrArg Additive.ofMul (mem_Fix_iff.mp hfix (z : MulAut V) z.2)
    have hz0 : (w₂ : Additive V) - (w₁ : Additive V) = 0 :=
      hWfix _ (W.sub_mem w₂.2 w₁.2) hzfix
    exact Subtype.ext (sub_eq_zero.mp hz0).symm
  have hcard : Nat.card W ≤ (Fix F).index := Nat.card_le_card_of_injective φ hinj
  exact le_trans hW2 hcard

private theorem comm_closure_of_comm {G : Type} [Group G] {T : Set G}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    ∀ x ∈ Subgroup.closure T, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have hC : Subgroup.closure T ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro t ht
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact hT h hh t ht
  intro x hx y hy
  have hx' : Subgroup.closure T ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.closure_le]
    intro t ht
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp (hC hx) t ht).symm
  exact Subgroup.mem_centralizer_iff.mp (hx' hy) x (Set.mem_singleton x)

private theorem isPGroup_of_le {G : Type} [Group G] {p : ℕ} {K F : Subgroup G}
    (hK : IsPGroup p K) (hle : F ≤ K) : IsPGroup p F := by
  intro g
  obtain ⟨k, hk⟩ := hK ⟨g.1, hle g.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

private theorem inv_on_of_abelian {K : Subgroup (MulAut V)} {T : Set (MulAut V)}
    (hT : Subgroup.closure T = K) (hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) {e : MulAut V}
    (hinv : ∀ y ∈ T, e * y * e⁻¹ = y⁻¹) : ∀ y ∈ K, e * y * e⁻¹ = y⁻¹ := by
  let H : Subgroup (MulAut V) :=
    { carrier := {y | y ∈ K ∧ e * y * e⁻¹ = y⁻¹}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨K.mul_mem ha.1 hb.1, ?_⟩
        calc e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha.2, hb.2]
          _ = (b * a)⁻¹ := (mul_inv_rev b a).symm
          _ = (a * b)⁻¹ := by rw [hab b hb.1 a ha.1]
      one_mem' := show (1 : MulAut V) ∈ K ∧ e * 1 * e⁻¹ = (1 : MulAut V)⁻¹ from
        ⟨K.one_mem, by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨K.inv_mem ha.1, ?_⟩
        calc e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [ha.2] }
  have hTH : T ⊆ (H : Set (MulAut V)) := fun y hy =>
    show y ∈ K ∧ e * y * e⁻¹ = y⁻¹ from
      ⟨by rw [← hT]; exact Subgroup.subset_closure hy, hinv y hy⟩
  have hKH : K ≤ H := by
    rw [← hT]
    exact (Subgroup.closure_le H).mpr hTH
  intro y hy
  exact (show y ∈ K ∧ e * y * e⁻¹ = y⁻¹ from hKH hy).2

private theorem sixteen_of_sq {x : ℕ} (h : 2 ^ 8 ≤ x ^ 2) : 16 ≤ x := by
  by_contra hx
  push_neg at hx
  have h1 : x ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact absurd (le_trans h h1) (by norm_num)

private theorem sixtyfour_of_sq {x : ℕ} (h : 2 ^ 12 ≤ x ^ 2) : 64 ≤ x := by
  by_contra hx
  push_neg at hx
  have h1 : x ^ 2 ≤ 63 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact absurd (le_trans h h1) (by norm_num)

private theorem sixtyfour_of_cube {x : ℕ} (h : 2 ^ 20 ≤ x ^ 3) : 64 ≤ x := by
  by_contra hx
  push_neg at hx
  have h1 : x ^ 3 ≤ 63 ^ 3 := Nat.pow_le_pow_left (by omega) 3
  exact absurd (le_trans h h1) (by norm_num)

private theorem two_pow_twenty_cube (hV : ∀ v : V, v * v = 1) {K : Subgroup (MulAut V)}
    (hK5 : IsPGroup 5 K) {T : Set (MulAut V)} (hT : Subgroup.closure T = K) {e : MulAut V}
    (he : e * e = 1) (hinv : ∀ y ∈ T, e * y * e⁻¹ = y⁻¹)
    (hnab : ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) :
    2 ^ 20 ≤ (Fix (Subgroup.zpowers e)).index ^ 3 := by
  have hsub : ∀ t ∈ T, t ∈ K := fun t ht => by
    rw [← hT]
    exact Subgroup.subset_closure ht
  obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ : ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ * t₂ ≠ t₂ * t₁ := by
    by_contra hcon
    apply hnab
    rw [← hT]
    refine comm_closure_of_comm (fun a ha b hb => ?_)
    by_contra hab
    exact hcon ⟨a, ha, b, hb, hab⟩
  have hodd : ∀ t ∈ K, Odd (orderOf t) := by
    intro t ht
    obtain ⟨k, hk⟩ := hK5 ⟨t, ht⟩
    have hk' : t ^ 5 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (Odd.pow (⟨2, by norm_num⟩ : Odd 5)) (orderOf_dvd_of_pow_eq_one hk')
  have hFle : Subgroup.closure ({t₁, t₂} : Set (MulAut V)) ≤ K := by
    rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact hsub _ ht₁
    · exact hsub _ ht₂
  have hF5 : IsPGroup 5 (Subgroup.closure ({t₁, t₂} : Set (MulAut V))) :=
    isPGroup_of_le hK5 hFle
  have hF1 : t₁ ∈ Subgroup.closure ({t₁, t₂} : Set (MulAut V)) :=
    Subgroup.subset_closure (Set.mem_insert t₁ {t₂})
  have hF2 : t₂ ∈ Subgroup.closure ({t₁, t₂} : Set (MulAut V)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem t₁ (Set.mem_singleton t₂))
  have h20 := two_pow_twenty_core hV hF5 ⟨t₁, hF1, t₂, hF2, hne⟩
  have hcube := index_fix_closure_le_cube he (hinv t₁ ht₁) (hinv t₂ ht₂)
    (hodd t₁ (hsub t₁ ht₁)) (hodd t₂ (hsub t₂ ht₂))
  exact le_trans h20 hcube

theorem sixteen_le_index_fix (hV : ∀ v : V, v * v = 1) {K : Subgroup (MulAut V)}
    (hK5 : IsPGroup 5 K) (hKnc : ¬ IsCyclic K) {e : MulAut V} (he : e * e = 1)
    (T : Set (MulAut V)) (hT : Subgroup.closure T = K) (hinv : ∀ y ∈ T, e * y * e⁻¹ = y⁻¹) :
    16 ≤ (Fix (Subgroup.zpowers e)).index := by
  by_cases hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x
  · exact sixteen_of_sq
      (abelian_case_sixteen hV hK5 hab hKnc he (inv_on_of_abelian hT hab hinv))
  · have h := sixtyfour_of_cube (two_pow_twenty_cube hV hK5 hT he hinv hab)
    omega

theorem sixtyfour_le_index_fix (hV : ∀ v : V, v * v = 1) {K D : Subgroup (MulAut V)}
    (hK5 : IsPGroup 5 K) (hKnc : ¬ IsCyclic K) {e : MulAut V} (he : e * e = 1)
    (T : Set (MulAut V)) (hT : Subgroup.closure T = K) (hinv : ∀ y ∈ T, e * y * e⁻¹ = y⁻¹)
    (hDK : D ≤ Subgroup.normalizer (K : Set (MulAut V))) (heD : e ∈ ⁅D, D⁆)
    (hD : ∀ D₀ : Subgroup (MulAut V), D₀ ≤ D → D₀.relIndex D ≤ 2 → D₀ = D) :
    64 ≤ (Fix (Subgroup.zpowers e)).index := by
  by_cases hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x
  · exact sixtyfour_of_sq (abelian_case_sixtyfour hV hK5 hab hKnc he
      (inv_on_of_abelian hT hab hinv) hDK heD hD)
  · exact sixtyfour_of_cube (two_pow_twenty_cube hV hK5 hT he hinv hab)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
