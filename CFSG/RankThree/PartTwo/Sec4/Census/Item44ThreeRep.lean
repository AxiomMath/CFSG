module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped Matrix

@[expose] noncomputable def abelAut (G : Type*) [Group G] : MulAut G →* MulAut (Abelianization G)
    where
  toFun σ := MulEquiv.abelianizationCongr σ
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem abelAut_of (G : Type*) [Group G] (σ : MulAut G) (x : G) :
    abelAut G σ (Abelianization.of x) = Abelianization.of (σ x) :=
  rfl

@[expose] noncomputable def mulAutToEnd (A : Type*) [CommGroup A] [Module (ZMod 3) (Additive A)] :
    MulAut A →* Module.End (ZMod 3) (Additive A) where
  toFun σ := AddMonoidHom.toZModLinearMap 3 (MonoidHom.toAdditive σ.toMonoidHom)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

variable {X : Type*} [Group X] {D : Subgroup X} [Module (ZMod 3) (Additive (Abelianization D))]

@[expose] noncomputable def abEnd (h : CriticalAt 3 D) :
    X →* Module.End (ZMod 3) (Additive (Abelianization D)) :=
  (mulAutToEnd (Abelianization D)).comp ((abelAut D).comp h.conjD)

theorem abEnd_of (h : CriticalAt 3 D) (y : X) (x : D) :
    abEnd h y (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (h.conjD y x)) :=
  rfl

theorem abEnd_eq_one_iff (h : CriticalAt 3 D) (y : X) :
    abEnd h y = 1 ↔ ∀ x : D, Abelianization.of (h.conjD y x) = Abelianization.of x := by
  constructor
  · intro hy x
    have := congrArg (fun f : Module.End (ZMod 3) (Additive (Abelianization D)) =>
      f (Additive.ofMul (Abelianization.of x))) hy
    simp only [abEnd_of, Module.End.one_apply] at this
    exact Additive.ofMul.injective this
  · intro hy
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H x =>
      change abEnd h y (Additive.ofMul (Abelianization.of x)) = Additive.ofMul (Abelianization.of x)
      rw [abEnd_of, hy x]

theorem abEnd_eq_neg_one_iff (h : CriticalAt 3 D) (y : X) :
    abEnd h y = -1 ↔
      ∀ x : D, Abelianization.of (h.conjD y x) = (Abelianization.of x)⁻¹ := by
  constructor
  · intro hy x
    have := congrArg (fun f : Module.End (ZMod 3) (Additive (Abelianization D)) =>
      f (Additive.ofMul (Abelianization.of x))) hy
    simp only [abEnd_of, LinearMap.neg_apply, Module.End.one_apply] at this
    exact Additive.ofMul.injective (this.trans (ofMul_inv _).symm)
  · intro hy
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H x =>
      change abEnd h y (Additive.ofMul (Abelianization.of x)) =
        -Additive.ofMul (Abelianization.of x)
      rw [abEnd_of, hy x, ofMul_inv]

theorem abEnd_eq_one_of_mem (h : CriticalAt 3 D) {y : X} (hy : y ∈ D) : abEnd h y = 1 := by
  rw [abEnd_eq_one_iff]
  intro x
  have : h.conjD y x = ⟨y, hy⟩ * x * (⟨y, hy⟩ : D)⁻¹ := Subtype.ext (by
    rw [h.conjD_apply]
    rfl)
  rw [this, map_mul, map_mul, map_inv, mul_comm, inv_mul_cancel_left]

theorem mem_frattiniKer_of_abEnd_eq_one [Finite X] [hq : Fact (Nat.Prime 3)] (h : CriticalAt 3 D)
    {y : X} (hy : abEnd h y = 1) : y ∈ h.frattiniKer := by
  have hD : IsPGroup 3 D := pCore_isPGroup.to_le h.le
  have : Fact (IsPGroup 3 D) := ⟨hD⟩
  have hle : commutator D ≤ frattini D := commutator_le_frattini_of_isPGroup (R := D) (p := 3)
  rw [CriticalAt.mem_frattiniKer_iff, CriticalAt.frattiniAct, MonoidHom.comp_apply,
    ← MonoidHom.mem_ker, mem_quotientAutomorphism_kernel]
  intro x
  have h1 := (abEnd_eq_one_iff h y).mp hy x
  rw [← Abelianization.mk_eq_of, ← Abelianization.mk_eq_of] at h1
  have h2 : (h.conjD y x)⁻¹ * x ∈ commutator D := by
    have := (QuotientGroup.eq (s := commutator D)).mp (by exact h1.symm)
    rwa [show (h.conjD y x)⁻¹ * x = ((x : D)⁻¹ * h.conjD y x)⁻¹ by group, inv_mem_iff]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact hle h2

omit [Module (ZMod 3) (Additive (Abelianization D))] in
theorem exists_pow_eq_one_of_mem_frattiniKer [Finite X] [hq : Fact (Nat.Prime 3)]
    (h : CriticalAt 3 D) (hC : Subgroup.centralizer (pCore 3 X : Set X) ≤ pCore 3 X) {y : X}
    (hy : y ∈ h.frattiniKer) : ∃ k : ℕ, y ^ 3 ^ k = 1 := by
  obtain ⟨a, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3
    (by norm_num)
  set y' := y ^ 3 ^ a with hy'
  have hy'm : orderOf y' = m := by
    rw [hy', orderOf_pow' y (pow_ne_zero a (by norm_num)), hn,
      Nat.gcd_eq_right (Dvd.intro m rfl), Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)]
  have hcop : Nat.Coprime (orderOf y') 3 := by
    rw [hy'm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3 |>.symm
  have hy'K : y' ∈ h.frattiniKer := Subgroup.pow_mem _ hy _
  have hcen : y' ∈ Subgroup.centralizer (pCore 3 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := h.centralizes_of_mem_frattiniKer hy'K hcop x hx
    calc x * y' = y' * x * y'⁻¹ * y' := by rw [this]
      _ = y' * x := by group
  obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 X)) ⟨y', hC hcen⟩
  have hk' : y' ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf y' ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y' = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hcop)
    dvd_rfl h1
  exact ⟨a, orderOf_eq_one_iff.mp h2⟩

omit [Module (ZMod 3) (Additive (Abelianization D))] in
theorem frattiniKer_le_pCore [Finite X] [hq : Fact (Nat.Prime 3)] (h : CriticalAt 3 D)
    (hC : Subgroup.centralizer (pCore 3 X : Set X) ≤ pCore 3 X) : h.frattiniKer ≤ pCore 3 X := by
  have : h.frattiniKer.Normal := h.frattiniKer_normal
  refine le_sSup ⟨this, fun y => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_frattiniKer h hC y.2
  exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩

@[expose] noncomputable def abMat (h : CriticalAt 3 D) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D))) : X →* GL ι (ZMod 3) :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp (abEnd h).toHomUnits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem abMat_coe (h : CriticalAt 3 D) (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D)))
    (y : X) : (abMat h b y : Matrix ι ι (ZMod 3)) = LinearMap.toMatrix b b (abEnd h y) :=
  rfl

theorem abMat_eq_one_iff (h : CriticalAt 3 D)
    (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D))) (y : X) :
    abMat h b y = 1 ↔ abEnd h y = 1 := by
  constructor
  · intro hy
    have h1 := congrArg Units.val hy
    rw [abMat_coe, Units.val_one] at h1
    apply (LinearMap.toMatrix b b).injective
    rw [h1, ← LinearMap.toMatrix_id b]
    rfl
  · intro hy
    apply Units.ext
    rw [abMat_coe, hy, Units.val_one]
    exact LinearMap.toMatrix_id b

theorem abMat_eq_neg_one_iff (h : CriticalAt 3 D)
    (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D))) (y : X) :
    abMat h b y = -1 ↔ abEnd h y = -1 := by
  have hneg : LinearMap.toMatrix b b (-1 : Module.End (ZMod 3) (Additive (Abelianization D))) =
      -1 := by
    rw [map_neg]
    congr 1
    exact LinearMap.toMatrix_id b
  constructor
  · intro hy
    have h1 := congrArg Units.val hy
    rw [abMat_coe, Units.val_neg, Units.val_one] at h1
    exact (LinearMap.toMatrix b b).injective (h1.trans hneg.symm)
  · intro hy
    apply Units.ext
    rw [abMat_coe, hy, Units.val_neg, Units.val_one]
    exact hneg

theorem abMat_mulVec (h : CriticalAt 3 D)
    (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D))) (y : X)
    (v : Additive (Abelianization D)) :
    (abMat h b y : Matrix ι ι (ZMod 3)) *ᵥ b.equivFun v = b.equivFun (abEnd h y v) := by
  rw [abMat_coe, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

end CFSG.RankThree.PartTwo.Sec4.Census
