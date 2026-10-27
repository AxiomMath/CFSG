module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseAGBase
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2


public section

namespace CFSG.Quasithin.H13.L827X.LBCaseAGK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs CFSG.Quasithin.H13.L827X.LBCaseAGBase
open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_conjXEquiv_eq_of_iff {X : Subgroup G} {A : Subgroup ↥X} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G))
    (h : ∀ x : ↥X, conjXEquiv X hg x ∈ A ↔ x ∈ A) :
    A.map (conjXEquiv X hg).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mpr hy
  · intro hx
    refine ⟨(conjXEquiv X hg).symm x, ?_, MulEquiv.apply_symm_apply _ _⟩
    have h1 := h ((conjXEquiv X hg).symm x)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.mp hx

@[expose] noncomputable def actQuot {X : Subgroup G} (A : Subgroup ↥X) [A.Normal] {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hA : A.map (conjXEquiv X hg).toMonoidHom = A) : MulAut (↥X ⧸ A) :=
  QuotientGroup.congr A A (conjXEquiv X hg) hA

theorem actQuot_mk {X : Subgroup G} (A : Subgroup ↥X) [A.Normal] {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hA : A.map (conjXEquiv X hg).toMonoidHom = A) (x : ↥X) :
    actQuot A hg hA (x : ↥X ⧸ A) = ((conjXEquiv X hg x : ↥X) : ↥X ⧸ A) :=
  QuotientGroup.congr_mk _ _ _ _ x

@[expose] noncomputable def actHom {X K : Subgroup G} (hK : K ≤ Subgroup.normalizer (X : Set G))
    (A : Subgroup ↥X) [A.Normal]
    (hA : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (X : Set G),
      A.map (conjXEquiv X hg).toMonoidHom = A) :
    ↥K →* MulAut (↥X ⧸ A) where
  toFun s := actQuot A (hK s.2) (hA s (hK s.2))
  map_one' := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [actQuot_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    group
  map_mul' s t := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, actQuot_mk, actQuot_mk, actQuot_mk]
    congr 1
    apply Subtype.ext
    show (s : G) * (t : G) * (x : G) * ((s : G) * (t : G))⁻¹ = (s : G) * ((t : G) * (x : G) * (t : G)⁻¹) * (s : G)⁻¹
    group

theorem mul_comm_quot_Yof (X : Subgroup G) (a b : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) :
    a * b = b * a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [h]
  have hle : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ Yof ((pCoreOf 2 X).subgroupOf X) := le_sup_left
  exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

instance XiQuot.commGroup (X : Subgroup G) :
    CommGroup (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) :=
  { (inferInstance : Group (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) with
    mul_comm := fun a b => mul_comm_quot_Yof X a b }

end CFSG.Quasithin.H13.L827X.LBCaseAGK


namespace CFSG.Quasithin.H13.L827X.LBCaseAGK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs CFSG.Quasithin.H13.L827X.LBCaseAGBase
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pow_three_quot_eq_one (X : Subgroup G) (hpow : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    (q : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) : q ^ 3 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hle : (pCoreOf 2 X).subgroupOf X ≤ Yof ((pCoreOf 2 X).subgroupOf X) := le_sup_right
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply hle
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  exact hpow _ x.2

instance XiQuot.module (X : Subgroup G) [hf : Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)] :
    Module (ZMod 3) (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) :=
  AddCommGroup.zmodModule (fun x => by
    have h := pow_three_quot_eq_one X hf.out (Additive.toMul x)
    exact congrArg Additive.ofMul h)

@[expose] noncomputable def addEquivToZModLinear {n : ℕ} {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    [Module (ZMod n) M] [Module (ZMod n) M₂] (e : M ≃+ M₂) : M ≃ₗ[ZMod n] M₂ where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' := fun c x => ZMod.map_smul e c x
  left_inv := e.left_inv
  right_inv := e.right_inv

theorem Yof_conj_iff (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) :
    conjXEquiv X hg x ∈ Yof ((pCoreOf 2 X).subgroupOf X) ↔ x ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
  rw [mem_Yof_iff, mem_Yof_iff, conjXEquiv_coe]
  constructor
  · intro h
    have h' := conj_mem_XiY (Subgroup.inv_mem _ hg) h
    have e : g⁻¹ * (g * (x : G) * g⁻¹) * g⁻¹⁻¹ = (x : G) := by group
    rwa [e] at h'
  · intro h
    exact conj_mem_XiY hg h

theorem N_conj_iff (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) :
    conjXEquiv X hg x ∈ (pCoreOf 2 X).subgroupOf X ↔ x ∈ (pCoreOf 2 X).subgroupOf X := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjXEquiv_coe]
  constructor
  · intro h
    have h' := conj_mem_pCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hg) h
    have e : g⁻¹ * (g * (x : G) * g⁻¹) * g⁻¹⁻¹ = (x : G) := by group
    rwa [e] at h'
  · intro h
    exact conj_mem_pCoreOf_of_mem_normalizer hg h


theorem quot_eq_iff_mul_inv_mem {H : Type} [Group H] (N : Subgroup H) [N.Normal] {a b : H} :
    (a : H ⧸ N) = (b : H ⧸ N) ↔ a * b⁻¹ ∈ N := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    have e : a * b⁻¹ = b * (a⁻¹ * b)⁻¹ * b⁻¹ := by group
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem h) _
  · intro h
    have e : a⁻¹ * b = b⁻¹ * (a * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem h) _

theorem Yof_map_conj (X : Subgroup G) : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (X : Set G),
    (Yof ((pCoreOf 2 X).subgroupOf X)).map (conjXEquiv X hg).toMonoidHom =
      Yof ((pCoreOf 2 X).subgroupOf X) :=
  fun g hg => map_conjXEquiv_eq_of_iff hg (fun x => Yof_conj_iff X hg x)

theorem N_map_conj (X : Subgroup G) : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (X : Set G),
    ((pCoreOf 2 X).subgroupOf X).map (conjXEquiv X hg).toMonoidHom =
      (pCoreOf 2 X).subgroupOf X :=
  fun g hg => map_conjXEquiv_eq_of_iff hg (fun x => N_conj_iff X hg x)

@[expose] noncomputable def linHom {X K : Subgroup G} (hK : K ≤ Subgroup.normalizer (X : Set G))
    [Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)] :
    ↥K →* (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) ≃ₗ[ZMod 3]
      Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) where
  toFun s := addEquivToZModLinear (MulEquiv.toAdditive
    ((actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X)) s))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    show Additive.ofMul ((actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X) 1) (Additive.toMul x)) = x
    rw [map_one, MulAut.one_apply]
    rfl
  map_mul' s t := by
    apply LinearEquiv.ext
    intro x
    show Additive.ofMul ((actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X) (s * t))
        (Additive.toMul x)) =
      Additive.ofMul ((actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X) s)
        ((actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X) t) (Additive.toMul x)))
    rw [map_mul, MulAut.mul_apply]


theorem linHom_apply_ofMul {X K : Subgroup G} (hK : K ≤ Subgroup.normalizer (X : Set G))
    [Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)] (s : ↥K)
    (q : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) :
    linHom hK s (Additive.ofMul q) =
      Additive.ofMul (actHom hK (Yof ((pCoreOf 2 X).subgroupOf X)) (Yof_map_conj X) s q) :=
  rfl

theorem pow_apply_mk_of_apply {X : Subgroup G} (A : Subgroup ↥X) [A.Normal] {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (f : MulAut (↥X ⧸ A))
    (hf : ∀ y : ↥X, f (y : ↥X ⧸ A) = ((conjXEquiv X hg y : ↥X) : ↥X ⧸ A)) (n : ℕ) (x : ↥X) :
    (f ^ n) (x : ↥X ⧸ A) = ((((conjXEquiv X hg) ^ n) x : ↥X) : ↥X ⧸ A) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MulAut.one_apply, MulAut.one_apply]
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hf, pow_succ', MulAut.mul_apply]

theorem actN_pow_three_eq_one {X K : Subgroup G} [Finite G]
    (hKN : K ≤ Subgroup.normalizer (X : Set G))
    [hf : Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)]
    (hS : IsXiShape 3 ((pCoreOf 2 X).subgroupOf X)) (s : ↥K)
    (hs : linHom hKN s = 1) :
    (actHom hKN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X) s) ^ 3 = 1 := by
  have hgN : (s : G) ∈ Subgroup.normalizer (X : Set G) := hKN s.2
  have hα : ∀ x : ↥X, conjXEquiv X hgN x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
    intro x
    have h2 : Additive.ofMul (actHom hKN _ (Yof_map_conj X) s (x : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)))
        = Additive.ofMul (x : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) := by
      rw [← linHom_apply_ofMul, hs]
      rfl
    have h3 : ((conjXEquiv X hgN x : ↥X) : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) =
        (x : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) := by
      have h4 := Additive.toMul.injective h2
      exact h4
    exact (quot_eq_iff_mul_inv_mem _).mp h3
  have hαN : ∀ x : ↥X, conjXEquiv X hgN x ∈ (pCoreOf 2 X).subgroupOf X ↔
      x ∈ (pCoreOf 2 X).subgroupOf X := fun x => N_conj_iff X hgN x
  have hf : ∀ y : ↥X, (actHom hKN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X) s)
      (y : ↥X ⧸ (pCoreOf 2 X).subgroupOf X)
      = ((conjXEquiv X hgN y : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) :=
    fun y => actQuot_mk _ (hKN s.2) (N_map_conj X _ (hKN s.2)) y
  apply MulEquiv.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.one_apply, pow_apply_mk_of_apply _ hgN _ hf 3 x]
  have key := pow_fix_mod hS (α := conjXEquiv X hgN) hαN hα x
  exact (quot_eq_iff_mul_inv_mem _).mpr key


theorem isSolvable_of_trivial_action {X K : Subgroup G} [Finite G]
    (hKN : K ≤ Subgroup.normalizer (X : Set G))
    [Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)]
    (hS : IsXiShape 3 ((pCoreOf 2 X).subgroupOf X))
    (hK5 : ∀ K' : Subgroup G, K' ≤ K → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K')
    (hall : ∀ s : ↥K, linHom hKN s = 1) : Group.IsSolvable ↥K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let actN := actHom hKN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X)
  haveI : Finite (MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X)) :=
    Finite.of_injective (fun f : MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X) =>
      (f : (↥X ⧸ (pCoreOf 2 X).subgroupOf X) → (↥X ⧸ (pCoreOf 2 X).subgroupOf X)))
      (fun f g h => MulEquiv.ext (fun x => congrFun h x))
  have hRP : IsPGroup 3 ↥actN.range := by
    show ∀ g : ↥actN.range, ∃ k : ℕ, g ^ 3 ^ k = 1
    intro g
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp g.2
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hs]
    exact actN_pow_three_eq_one hKN hS s (hall s)
  haveI : Group.IsNilpotent ↥actN.range := IsPGroup.isNilpotent hRP
  haveI : Group.IsSolvable ↥actN.range := inferInstance
  have hKer : Group.IsSolvable ↥actN.ker := by
    have hK'K : actN.ker.map K.subtype ≤ K := Subgroup.map_subtype_le _
    have hcomm : ⁅actN.ker.map K.subtype, X⁆ ≤ pCoreOf 2 X := by
      rw [Subgroup.commutator_le]
      intro k hk x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
      have hs1 : actN s = 1 := hs
      have h1 : ((conjXEquiv X (hKN s.2) ⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) =
          ((⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) := by
        have h2 := congrArg (fun f : MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X) =>
          f ((⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X)) hs1
        rw [MulAut.one_apply] at h2
        exact h2
      have h3 := (quot_eq_iff_mul_inv_mem _).mp h1
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : ((conjXEquiv X (hKN s.2) ⟨x, hx⟩ * (⟨x, hx⟩ : ↥X)⁻¹ : ↥X) : G) =
          (s : G) * x * (s : G)⁻¹ * x⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjXEquiv_coe]
      rw [h4] at h3
      show ⁅(s : G), x⁆ ∈ pCoreOf 2 X
      rw [commutatorElement_def]
      exact h3
    have hK' : Group.IsSolvable ↥(actN.ker.map K.subtype) := hK5 _ hK'K hcomm
    haveI := hK'
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective actN.ker K.subtype K.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective actN.ker K.subtype K.subtype_injective).injective
  have hmap : actN.rangeRestrict.ker ≤ actN.ker.subtype.range := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  exact Group.isSolvable_of_ker_le_range actN.ker.subtype actN.rangeRestrict hmap

theorem not_three_of_cComponent {X K : Subgroup G} [Finite G]
    (hKperf : ⁅K, K⁆ = K) (hKne : K ≠ ⊥)
    (hNKX : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hK5 : ∀ K' : Subgroup G, K' ≤ K → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K')
    (hpow : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    (hidx : (pCoreOf 2 X).relIndex X = 3 ^ 3) (hnc : ¬ ⁅X, X⁆ ≤ pCoreOf 2 X) : False := by
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNKX
  haveI : Fact (∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) := ⟨hpow⟩
  have hnc' : ¬ ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ (pCoreOf 2 X).subgroupOf X :=
    fun h => hnc ((commutator_top_le_subgroupOf_iff X).mp h)
  have hN3 : ((pCoreOf 2 X).subgroupOf X).index = 3 ^ 3 := hidx
  have hMidx : (Yof ((pCoreOf 2 X).subgroupOf X)).index = 3 ^ 2 :=
    (index_Yof_of_index_cube hN3 hnc').1
  have hS : IsXiShape 3 ((pCoreOf 2 X).subgroupOf X) := Or.inr ⟨hN3, hnc'⟩
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨s₀, hs₀⟩ : ∃ s : ↥K, linHom hKN s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isSolvable ↥K (isSolvable_of_trivial_action hKN hS hK5 hcon)
  haveI : Group.IsPerfect (linHom hKN).range := Group.IsPerfect.range (linHom hKN)
  haveI : Nontrivial (linHom hKN).range := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    apply hs₀
    have hmem : linHom hKN s₀ ∈ (linHom hKN).range := ⟨s₀, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hns : ¬ Group.IsSolvable (linHom hKN).range := Group.IsPerfect.not_isSolvable _
  haveI : Module.Finite (ZMod 3) (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) :=
    inferInstance
  have hE : Module.finrank (ZMod 3) (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3)
      (V := Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)))
    have hcard : Nat.card (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) = 3 ^ 2 := hMidx
    rw [hcard, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (by norm_num) h1).symm
  exact CFSG.Quasithin.H13.L827X.SL2Orb.not_perfect_nonsolvable_three hE (linHom hKN).range hns

end CFSG.Quasithin.H13.L827X.LBCaseAGK

end
