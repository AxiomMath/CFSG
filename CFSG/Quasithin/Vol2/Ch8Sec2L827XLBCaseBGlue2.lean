module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseAGBase

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseBGlue2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs CFSG.Quasithin.H13.L827X.LBCaseAGBase
open scoped commutatorElement

variable {G : Type} [Group G]

theorem index_Yof_of_relIndex_glue2 [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hidx : (pCoreOf 2 X).relIndex X = p ^ 2 ∨
      ((pCoreOf 2 X).relIndex X = p ^ 3 ∧ ¬ ⁅X, X⁆ ≤ pCoreOf 2 X)) :
    (Yof ((pCoreOf 2 X).subgroupOf X)).index = p ^ 2 ∧
      IsXiShape p ((pCoreOf 2 X).subgroupOf X) := by
  rcases hidx with h2 | ⟨h3, hnc⟩
  · have hN : ((pCoreOf 2 X).subgroupOf X).index = p ^ 2 := h2
    exact ⟨by rw [Yof_eq_of_index_sq hN, hN], Or.inl hN⟩
  · have hN : ((pCoreOf 2 X).subgroupOf X).index = p ^ 3 := h3
    have hnc' : ¬ ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ (pCoreOf 2 X).subgroupOf X :=
      fun hh => hnc ((commutator_top_le_subgroupOf_iff X).mp hh)
    exact ⟨(index_Yof_of_index_cube hN hnc').1, Or.inr ⟨hN, hnc'⟩⟩

theorem pow_mem_Yof_glue2 {X : Subgroup G} {p : ℕ}
    (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) (x : ↥X) :
    x ^ p ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
  have h : x ^ p ∈ (pCoreOf 2 X).subgroupOf X := by
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
    exact hpow x x.2
  have hle : (pCoreOf 2 X).subgroupOf X ≤ Yof ((pCoreOf 2 X).subgroupOf X) := by
    unfold Yof
    exact le_sup_right
  exact hle h

@[instance_reducible] private noncomputable def glueCgOfComm {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

@[instance_reducible] private noncomputable def glueZModOfExp (p : ℕ) [NeZero p] {A : Type*}
    [Group A] (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ p = 1) :
    letI := glueCgOfComm hc
    Module (ZMod p) (Additive A) :=
  letI := glueCgOfComm hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp _

theorem exists_quot_glue2 [Finite G] {X : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hYidx : (Yof ((pCoreOf 2 X).subgroupOf X)).index = p ^ 2)
    (hexp : ∀ x : ↥X, x ^ p ∈ Yof ((pCoreOf 2 X).subgroupOf X)) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module (ZMod p) E), Finite E ∧
      Module.finrank (ZMod p) E = 2 ∧ ∃ q : X → E,
        (∀ x y : X, q (x * y) = q x + q y) ∧ Function.Surjective q ∧
        (∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hcomm : IsMulCommutative (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (show Nat.card (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) = p ^ 2 from hYidx)
  have hc : ∀ a b : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X), a * b = b * a :=
    fun a b => hcomm.is_comm.comm a b
  have hp1 : ∀ a : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X), a ^ p = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hexp x
  let _ := glueCgOfComm hc
  let _ := glueZModOfExp p hc hp1
  have hcard : Nat.card (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) = p ^ 2 := by
    rw [← hYidx]
    exact (Nat.card_congr Additive.ofMul).symm
  have hfin : Finite (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) :=
    Finite.of_equiv _ Additive.ofMul
  haveI : Module.Finite (ZMod p) (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p)
      (Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X))) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)))
    rw [Nat.card_zmod, hcard] at h
    exact Nat.pow_right_injective hp.out.two_le h.symm
  refine ⟨Additive (↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)), inferInstance, inferInstance,
    hfin, hfr, fun x => Additive.ofMul (QuotientGroup.mk (x : ↥X)), ?_, ?_, ?_⟩
  · intro x y
    show Additive.ofMul (QuotientGroup.mk (x * y : ↥X)) =
      Additive.ofMul (QuotientGroup.mk x) + Additive.ofMul (QuotientGroup.mk y)
    rw [QuotientGroup.mk_mul]
    rfl
  · intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul e)
    exact ⟨x, by show Additive.ofMul (QuotientGroup.mk x) = e; rw [hx]; rfl⟩
  · intro x y
    show Additive.ofMul (QuotientGroup.mk x : ↥X ⧸ Yof ((pCoreOf 2 X).subgroupOf X)) =
      Additive.ofMul (QuotientGroup.mk y) ↔ _
    rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, mem_Yof_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]

section Conj

variable {X : Subgroup G} {E : Type} [AddCommGroup E] {q : X → E}

@[expose] noncomputable def liftGlue2 (hq : Function.Surjective q) (e : E) : X :=
  Function.surjInv hq e

theorem q_liftGlue2 (hq : Function.Surjective q) (e : E) : q (liftGlue2 hq e) = e :=
  Function.surjInv_eq hq e

@[expose] noncomputable def conjFunGlue2 (hq : Function.Surjective q) {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e : E) : E :=
  q (conjXEquiv X hγ (liftGlue2 hq e))

theorem conjFunGlue2_q (hq : Function.Surjective q)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (x : X) :
    conjFunGlue2 hq hγ (q x) = q (conjXEquiv X hγ x) := by
  unfold conjFunGlue2
  apply (hker _ _).mpr
  have hmem : (liftGlue2 hq (q x) : G)⁻¹ * (x : G) ∈ XiY X :=
    (hker _ _).mp (q_liftGlue2 hq (q x))
  have hconj := conj_mem_XiY hγ hmem
  have e : ((conjXEquiv X hγ (liftGlue2 hq (q x)) : X) : G)⁻¹ * ((conjXEquiv X hγ x : X) : G)
      = γ * ((liftGlue2 hq (q x) : G)⁻¹ * (x : G)) * γ⁻¹ := by
    rw [conjXEquiv_coe, conjXEquiv_coe]
    group
  rw [e]
  exact hconj

theorem conjFunGlue2_add (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e₁ e₂ : E) :
    conjFunGlue2 hq hγ (e₁ + e₂) = conjFunGlue2 hq hγ e₁ + conjFunGlue2 hq hγ e₂ := by
  obtain ⟨a, rfl⟩ := hq e₁
  obtain ⟨b, rfl⟩ := hq e₂
  rw [← hq_add]
  simp only [conjFunGlue2_q hq hker hγ]
  rw [← hq_add, map_mul]

@[expose] noncomputable def conjAddGlue2 (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) : E →+ E where
  toFun := conjFunGlue2 hq hγ
  map_zero' := by
    have h := conjFunGlue2_add hq hq_add hker hγ 0 0
    simpa using h
  map_add' := conjFunGlue2_add hq hq_add hker hγ

theorem conjFunGlue2_inv (hq : Function.Surjective q)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e : E) :
    conjFunGlue2 hq hγ (conjFunGlue2 hq (Subgroup.inv_mem _ hγ) e) = e := by
  obtain ⟨x, rfl⟩ := hq e
  rw [conjFunGlue2_q hq hker, conjFunGlue2_q hq hker]
  congr 1
  apply Subtype.ext
  rw [conjXEquiv_coe, conjXEquiv_coe]
  group

theorem conjFunGlue2_inv' (hq : Function.Surjective q)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e : E) :
    conjFunGlue2 hq (Subgroup.inv_mem _ hγ) (conjFunGlue2 hq hγ e) = e := by
  obtain ⟨x, rfl⟩ := hq e
  rw [conjFunGlue2_q hq hker, conjFunGlue2_q hq hker]
  congr 1
  apply Subtype.ext
  rw [conjXEquiv_coe, conjXEquiv_coe]
  group

@[expose] noncomputable def conjLEGlue2 (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) : E ≃ₗ[ZMod p] E :=
  LinearEquiv.ofLinear ((conjAddGlue2 hq hq_add hker hγ).toZModLinearMap p)
    ((conjAddGlue2 hq hq_add hker (Subgroup.inv_mem _ hγ)).toZModLinearMap p)
    (LinearMap.ext fun e => conjFunGlue2_inv hq hker hγ e)
    (LinearMap.ext fun e => conjFunGlue2_inv' hq hker hγ e)

theorem conjLEGlue2_apply (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e : E) :
    conjLEGlue2 p hq hq_add hker hγ e = conjFunGlue2 hq hγ e := by
  rw [conjLEGlue2, LinearEquiv.ofLinear_apply, AddMonoidHom.coe_toZModLinearMap,
    conjAddGlue2]
  rfl

theorem conjLEGlue2_one (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (h1 : γ = 1) :
    conjLEGlue2 p hq hq_add hker hγ = 1 := by
  subst h1
  apply LinearEquiv.ext
  intro e
  obtain ⟨x, rfl⟩ := hq e
  rw [conjLEGlue2_apply, conjFunGlue2_q hq hker, LinearEquiv.coe_one, id]
  congr 1
  apply Subtype.ext
  simp [conjXEquiv_coe]

theorem conjLEGlue2_mul (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ δ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G))
    (hδ : δ ∈ Subgroup.normalizer (X : Set G)) (hγδ : γ * δ ∈ Subgroup.normalizer (X : Set G)) :
    conjLEGlue2 p hq hq_add hker hγδ = conjLEGlue2 p hq hq_add hker hγ *
      conjLEGlue2 p hq hq_add hker hδ := by
  apply LinearEquiv.ext
  intro e
  obtain ⟨x, rfl⟩ := hq e
  rw [LinearEquiv.mul_apply]
  simp only [conjLEGlue2_apply, conjFunGlue2_q hq hker]
  congr 1
  apply Subtype.ext
  simp only [conjXEquiv_coe]
  group

@[expose] noncomputable def conjHomGlue2 (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X) :
    Subgroup.normalizer (X : Set G) →* (E ≃ₗ[ZMod p] E) where
  toFun γ := conjLEGlue2 p hq hq_add hker γ.2
  map_one' := conjLEGlue2_one p hq hq_add hker (1 : ↥(Subgroup.normalizer (X : Set G))).2 rfl
  map_mul' γ δ := conjLEGlue2_mul p hq hq_add hker γ.2 δ.2 (γ * δ).2

theorem conjHomGlue2_apply (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {γ : G} (hγ : γ ∈ Subgroup.normalizer (X : Set G)) (e : E) :
    conjHomGlue2 p hq hq_add hker ⟨γ, hγ⟩ e = conjFunGlue2 hq hγ e :=
  conjLEGlue2_apply p hq hq_add hker hγ e

@[expose] noncomputable def sigmaGlue2 (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ Subgroup.normalizer (X : Set G)) : K₀ →* (E ≃ₗ[ZMod p] E) :=
  (conjHomGlue2 p hq hq_add hker).comp (Subgroup.inclusion hK₀)

theorem sigmaGlue2_apply_q (p : ℕ) [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ Subgroup.normalizer (X : Set G)) (γ : K₀) (x : X) :
    sigmaGlue2 p hq hq_add hker hK₀ γ (q x) = q (conjXEquiv X (hK₀ γ.2) x) := by
  have h : Subgroup.inclusion hK₀ γ = ⟨(γ : G), hK₀ γ.2⟩ :=
    Subtype.ext (Subgroup.coe_inclusion hK₀ γ)
  rw [sigmaGlue2, MonoidHom.comp_apply, h, conjHomGlue2_apply, conjFunGlue2_q hq hker]

end Conj

theorem conjClosure_commutator_glue2 {K T : Subgroup G} (hKperf : ⁅K, K⁆ = K) :
    ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ =
      CFSG.Quasithin.conjClosure K T := by
  have hKK₀ : K ≤ CFSG.Quasithin.conjClosure K T := CFSG.Quasithin.le_conjClosure K T
  have hK_le : K ≤ ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ := by
    calc K = ⁅K, K⁆ := hKperf.symm
      _ ≤ ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ :=
        Subgroup.commutator_mono hKK₀ hKK₀
  have hconj : ∀ t ∈ T, ∀ z ∈ K,
      t * z * t⁻¹ ∈ ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ := by
    intro t ht z hz
    have hN : t ∈ Subgroup.normalizer ((CFSG.Quasithin.conjClosure K T : Subgroup G) : Set G) :=
      CFSG.Quasithin.le_normalizer_conjClosure K T ht
    have hmap := commutator_map_conj_le hN
    exact hmap (Subgroup.mem_map_of_mem _ (hK_le hz))
  have hle : CFSG.Quasithin.conjClosure K T ≤
      ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ :=
    CFSG.Quasithin.conjClosure_le hconj
  refine le_antisymm ?_ hle
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

end CFSG.Quasithin.H13.L827X.LBCaseBGlue2

end
