module

public import CFSG.RankThree.CentralCover.SteinbergBNReflectionNormalizers
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LieType.Chevalley.RankOneCentralImage

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2 CFSG.Assembly
  CFSG.Assembly.RankThreeEven

variable {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem torusGroup_le_adjointGroup : torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨⟨i, t⟩, rfl⟩; exact torusElt_mem_adjointGroup i t)

variable (τ) in
@[expose] def chevTorusExp (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin τ.rank → ZMod p) →* (Fin τ.rank → Kˣ) :=
  MonoidHom.pi fun i => (zmodPowHom ζ hζ).comp
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) i))

theorem chevTorusExp_apply (ζ : Kˣ) (hζ : ζ ^ p = 1) (a : Multiplicative (Fin τ.rank → ZMod p))
    (i : Fin τ.rank) :
    chevTorusExp τ ζ hζ a i = zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd a i)) := rfl

variable (τ) in
@[expose] noncomputable def chevTorus (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
  (Subgroup.inclusion torusGroup_le_adjointGroup).comp
    ((torusCoordHom τ K).comp (chevTorusExp τ ζ hζ))

theorem coe_chevTorus (ζ : Kˣ) (hζ : ζ ^ p = 1) (a : Multiplicative (Fin τ.rank → ZMod p)) :
    ((chevTorus τ ζ hζ a : adjointGroup τ K) : ModGL τ K) =
        (List.ofFn fun i => torusElt τ K i
        (zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd a i)))).prod :=
  rfl

theorem weylElt_conj_listProd_torusElt (i : Fin τ.rank) (t : Fin τ.rank → Kˣ) :
    weylElt τ K i 1 * (List.ofFn fun j => torusElt τ K j (t j)).prod * (weylElt τ K i 1)⁻¹ =
      (List.ofFn fun j => torusElt τ K j (t j)).prod *
        torusElt τ K i (∏ j, t j ^ (-τ.cartan j i)) := by
  have h1 : weylElt τ K i 1 * (List.ofFn fun j => torusElt τ K j (t j)).prod *
      (weylElt τ K i 1)⁻¹ = (List.ofFn fun j =>
        weylElt τ K i 1 * torusElt τ K j (t j) * (weylElt τ K i 1)⁻¹).prod := by
    rw [← MulAut.conj_apply, map_list_prod, List.map_ofFn]
    rfl
  rw [h1]
  simp_rw [weylElt_one_mul_torusElt_mul_inv]
  rw [list_prod_ofFn_mul _ _ fun j j' => torusElt_mul_comm _ _ _ _]
  congr 1
  have h2 := map_list_prod (torusEltHom τ K i) (List.ofFn fun j => t j ^ (-τ.cartan j i))
  rw [List.prod_ofFn] at h2
  rw [show torusElt τ K i (∏ j, t j ^ (-τ.cartan j i)) =
    torusEltHom τ K i (∏ j, t j ^ (-τ.cartan j i)) from rfl, h2, List.map_ofFn]
  rfl

variable (τ p) in
@[expose] def cartanFunctional (i : Fin τ.rank) : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ j, (τ.cartan j i : ZMod p) • LinearMap.proj j

omit [NeZero p] in
theorem cartanFunctional_apply (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) :
    cartanFunctional τ p i a = ∑ j, (τ.cartan j i : ZMod p) * a j := by
  simp [cartanFunctional, LinearMap.sum_apply]

omit [NeZero p] in
theorem cartanFunctional_single (i : Fin τ.rank) :
    cartanFunctional τ p i (Pi.single i 1) = 2 := by
  classical
  rw [cartanFunctional_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one, Tag.cartan_self]
    norm_num
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem chevTorusExp_smul_single (ζ : Kˣ) (hζ : ζ ^ p = 1) (i : Fin τ.rank) (x : ZMod p) :
    chevTorusExp τ ζ hζ (.ofAdd (x • Pi.single i 1)) =
      Pi.mulSingle i (zmodPowHom ζ hζ (.ofAdd x)) := by
  classical
  funext j
  rw [chevTorusExp_apply, toAdd_ofAdd, Pi.smul_apply]
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, smul_eq_mul, mul_one, Pi.mulSingle_eq_same]
  · rw [Pi.single_eq_of_ne hj, smul_zero, Pi.mulSingle_eq_of_ne hj, ofAdd_zero, map_one]

theorem weylElt_conj_chevTorus (ζ : Kˣ) (hζ : ζ ^ p = 1) (i : Fin τ.rank)
    (a : Fin τ.rank → ZMod p) :
    (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K) *
        chevTorus τ ζ hζ (.ofAdd a) *
        (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K)⁻¹ =
      chevTorus τ ζ hζ (.ofAdd (a - cartanFunctional τ p i a • Pi.single i 1)) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_chevTorus,
    weylElt_conj_listProd_torusElt, sub_eq_add_neg, ofAdd_add, map_mul, Subgroup.coe_mul,
    coe_chevTorus, ← neg_smul]
  congr 1
  change _ = (((chevTorus τ ζ hζ (.ofAdd (-cartanFunctional τ p i a • Pi.single i 1)) :
    adjointGroup τ K) : ModGL τ K))
  change _ = ((torusCoordHom τ K (chevTorusExp τ ζ hζ
    (.ofAdd (-cartanFunctional τ p i a • Pi.single i 1))) : torusGroup τ K) : ModGL τ K)
  rw [chevTorusExp_smul_single, coe_torusCoordHom_mulSingle]
  congr 1
  simp only [toAdd_ofAdd]
  rw [cartanFunctional_apply, ← Finset.sum_neg_distrib, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
  congr 2
  push_cast
  ring

omit [NeZero p] in
theorem eq_zero_of_cartan_sum_eq_zero {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : IsUnit ((A.det : ℤ) : ZMod p)) {a : Fin r → ZMod p}
    (h : ∀ j, ∑ i, (A i j : ZMod p) * a i = 0) : a = 0 := by
  set B : Matrix (Fin r) (Fin r) (ZMod p) := (A.map (Int.cast : ℤ → ZMod p)).transpose
  have hB : B.mulVec a = 0 := by
    funext j
    simp only [B, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
      Pi.zero_apply]
    exact h j
  have hdet : B.det = ((A.det : ℤ) : ZMod p) := by
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (Int.castRingHom (ZMod p)) A).symm
  have h1 : (B.adjugate * B).mulVec a = 0 := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, hdet] at h1
  have h2 : ((A.det : ℤ) : ZMod p) • a = 0 := by
    rw [← h1, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact (hA.smul_left_cancel).1 (h2.trans (smul_zero _).symm)

theorem chevTorus_injective {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p)) : Function.Injective (chevTorus τ ζ hζ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have ht : torusCoordHom τ K (chevTorusExp τ ζ hζ a) = 1 := by
    have := congrArg Subtype.val ha
    exact Subtype.ext this
  have hj : ∀ j, ∑ i, (τ.cartan i j : ZMod p) * Multiplicative.toAdd a i = 0 := by
    intro j
    have h := torusCoordHom_apply_rootVec_single (R := K) (chevTorusExp τ ζ hζ a) j
    rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
      rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h
    have h' := congrArg (fun v : RootModule τ K =>
      v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
    have h1 : ∏ i, chevTorusExp τ ζ hζ a i ^ τ.cartan i j = 1 := Units.ext (by
      rw [Units.val_one, ← h'])
    have h2 : zmodPowHom ζ hζ (.ofAdd (∑ i, (τ.cartan i j : ZMod p) * Multiplicative.toAdd a i))
        = 1 := by
      rw [← h1, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [chevTorusExp_apply, ← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
    have h3 := zmodPowHom_injective hζo hζ (h2.trans (map_one _).symm)
    exact Multiplicative.ofAdd.injective h3
  have h0 := eq_zero_of_cartan_sum_eq_zero τ.cartan hdet hj
  exact Multiplicative.toAdd.injective h0

theorem listProd_torusElt_conj_xUnit (i : Fin τ.rank) :
    ∀ l : List (ModGL τ K), (∀ g ∈ l, ∃ j t, g = torusElt τ K j t) → ∀ c : K,
      ∃ c' : K, l.prod * xUnit τ K i c * l.prod⁻¹ = xUnit τ K i c'
  | [], _, c => ⟨c, by simp⟩
  | g :: l, hl, c => by
    obtain ⟨c'', hc''⟩ := listProd_torusElt_conj_xUnit i l
      (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) c
    obtain ⟨j, t, rfl⟩ := hl g List.mem_cons_self
    refine ⟨((t ^ τ.cartan j i : Kˣ) : K) * c'', ?_⟩
    rw [List.prod_cons, mul_inv_rev, show torusElt τ K j t * l.prod * xUnit τ K i c *
      (l.prod⁻¹ * (torusElt τ K j t)⁻¹) = torusElt τ K j t * (l.prod * xUnit τ K i c * l.prod⁻¹) *
        (torusElt τ K j t)⁻¹ by group, hc'', (simple_torus_root_conjugation τ K j i t c'').1]

theorem chevalley_split_torus_witness {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    [Fintype K] (hp : p.Prime) (hp2 : p ≠ 2) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (i₀ j₀ : Fin τ.rank) (hodd : Odd (τ.cartan i₀ j₀)) (φ : Y →* adjointGroup τ K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    IsElemAbelian p (chevTorus τ ζ hζ).range ∧ Nat.card (chevTorus τ ζ hζ).range = p ^ τ.rank ∧
      (∀ x ∈ (chevTorus τ ζ hζ).range.comap φ, ∀ y ∈ (chevTorus τ ζ hζ).range.comap φ,
        x * y = y * x) ∧
      ∃ R : Subgroup G, R ≤ Y ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ A₀ : Subgroup G,
        A₀ ≤ Y ⊓ Subgroup.normalizer (R : Set G) ∧ IsElemAbelian p A₀ ∧
        Nat.card A₀ = p ^ τ.rank ∧ τ.rank ≤ localRank p G := by
  classical
  set e := chevTorus τ ζ hζ with he
  set D := e.range with hD
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have hDab : IsElemAbelian p D := ⟨⟨⟨fun x y => by
    obtain ⟨_, ⟨a, rfl⟩⟩ := x
    obtain ⟨_, ⟨b, rfl⟩⟩ := y
    exact Subtype.ext (((Commute.all a b).map e).eq)⟩⟩, hDp⟩
  have hcard : Nat.card D = p ^ τ.rank := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective (chevTorus_injective hζo hζ hdet)).toEquiv,
      card_multiplicative_fin_zmod]
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x :=
    reflection_comap_comm hφ hker hp hp2 e (cartanFunctional τ p)
      (fun i => cartanFunctional_single i)
      (fun i => ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩)
      (fun i v => weylElt_conj_chevTorus ζ hζ i v)
  obtain ⟨U, hU1, hU2, hDU⟩ : ∃ U : Subgroup (adjointGroup τ K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ d ∈ D, ∀ u ∈ U, d * u * d⁻¹ ∈ U := by
    by_cases hK2 : ringChar K = 2
    ·
      let xh : Multiplicative K →* adjointGroup τ K :=
        { toFun := fun c => ⟨xUnit τ K i₀ (Multiplicative.toAdd c), xUnit_mem_adjointGroup _ _⟩
          map_one' := Subtype.ext (xUnit_zero i₀)
          map_mul' := fun c c' => Subtype.ext (xUnit_add i₀ _ _) }
      have htwo : (2 : K) = 0 := by
        have h := ringChar.Nat.cast_ringChar (R := K)
        rwa [hK2, Nat.cast_ofNat] at h
      refine ⟨xh.range, fun h => ?_, ?_, ?_⟩
      · have h1 : xh (.ofAdd 1) ∈ xh.range := ⟨_, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        have h2 : xOp τ K i₀ 1 = xOp τ K i₀ 0 := by
          have h3 : xUnit τ K i₀ 1 = xUnit τ K i₀ 0 := by
            rw [xUnit_zero]
            exact congrArg Subtype.val h1
          exact congrArg Units.val h3
        exact one_ne_zero (xOp_injective i₀ h2)
      · rintro ⟨_, ⟨c, rfl⟩⟩
        refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
        simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        change (xUnit τ K i₀ (Multiplicative.toAdd c)) ^ 2 = 1
        rw [pow_two, ← xUnit_add, ← two_mul, htwo, zero_mul, xUnit_zero]
      · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
        obtain ⟨c', hc'⟩ := listProd_torusElt_conj_xUnit i₀
          (List.ofFn fun i => torusElt τ K i (zmodPowHom ζ hζ (.ofAdd (Multiplicative.toAdd a i))))
          (fun g hg => by
            obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
            exact ⟨i, _, rfl⟩) (Multiplicative.toAdd c)
        refine ⟨.ofAdd c', Subtype.ext ?_⟩
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_chevTorus]
        exact hc'.symm
    ·
      set z : adjointGroup τ K := ⟨torusElt τ K i₀ (-1), torusElt_mem_adjointGroup _ _⟩
      have hz2 : z ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, pow_two]
        change torusElt τ K i₀ (-1) * torusElt τ K i₀ (-1) = 1
        rw [← torusElt_mul, neg_one_mul, neg_neg, torusElt_one])
      have hz1 : z ≠ 1 := by
        intro h
        have h1 := torusElt_rootVec (R := K) i₀ (-1) (isRoot_single τ j₀)
        rw [show torusElt τ K i₀ (-1) = 1 from congrArg Subtype.val h, Units.val_one,
          Module.End.one_apply, sum_cartan_mul_pi_single, hodd.neg_one_zpow, Units.val_neg,
          Units.val_one, neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul K] at h1
        have h2 : (2 : K) = 0 := by
          by_contra h2
          have := (smul_eq_zero.1 h1).resolve_left h2
          rw [rootVec_eq_single_of_isRoot (isRoot_single τ j₀)] at this
          exact (Finsupp.single_ne_zero.2 one_ne_zero) this
        have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
        exact hK2 (ringChar.eq K 2)
      have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
      refine ⟨Subgroup.zpowers z, fun h => hz1 (Subgroup.zpowers_eq_bot.1 h),
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one]), ?_⟩
      rintro _ ⟨a, rfl⟩ u hu
      have hcz : e a * z = z * e a := by
        apply Subtype.ext
        exact mul_comm_of_mem_diagonalGroup
          (torusGroup_le_diagonalGroup (torusCoordHom τ K (chevTorusExp τ ζ hζ a)).2)
          (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup _ _))
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcz, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k
  obtain ⟨R, hRY, hR1, hR2, A₀, hA, hAab, hAcard, -, hrank⟩ :=
    central_cover_normalizer_witness Y hφ hker hp hp2 hDp hF hcard.ge hU1 hU2 hDU
  exact ⟨hDab, hcard, hF, R, hRY, hR1, hR2, A₀, hA, hAab, hAcard, hrank⟩

theorem mem_range_chevTorus_iff (ζ : Kˣ) (hζ : ζ ^ p = 1) (g : adjointGroup τ K) :
    g ∈ (chevTorus τ ζ hζ).range ↔ ∃ a : Fin τ.rank → ZMod p,
      (g : ModGL τ K) = (List.ofFn fun i => torusElt τ K i (ζ ^ (a i).val)).prod := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, coe_chevTorus ζ hζ a⟩
  · rintro ⟨a, ha⟩
    exact ⟨.ofAdd a, Subtype.ext ((coe_chevTorus ζ hζ _).trans ha.symm)⟩

omit [NeZero p] in
theorem isUnit_natCast_of_coprime {n : ℕ} (h : Nat.Coprime n p) :
    IsUnit (((n : ℤ) : ZMod p)) := by
  rw [Int.cast_natCast, ← ZMod.coe_unitOfCoprime n h]
  exact Units.isUnit _

end CFSG.RankThree.CentralCover
