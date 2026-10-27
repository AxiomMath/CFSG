module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Determinant

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.SingerQuotient

section LinearRep

variable (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V] {Q H : Type*} [Group Q]
  [Group H]

@[expose] def zmodLinearEquiv (f : V ≃+ V) : V ≃ₗ[ZMod n] V :=
  f.toLinearEquiv fun c x => (f.toAddMonoidHom.toZModLinearMap n).map_smul c x

@[expose] def linearRep (φ : Q ≃* Multiplicative V) (σ : H →* MulAut Q) :
    H →* (V ≃ₗ[ZMod n] V) where
  toFun h := zmodLinearEquiv n (AddEquiv.toMultiplicative.symm ((φ.symm.trans (σ h)).trans φ))
  map_one' := LinearEquiv.ext fun v => by
    change (φ (σ 1 (φ.symm (Multiplicative.ofAdd v)))).toAdd = v
    rw [map_one, MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_mul' g h := LinearEquiv.ext fun v => by
    change (φ (σ (g * h) (φ.symm (Multiplicative.ofAdd v)))).toAdd =
      (φ (σ g (φ.symm (Multiplicative.ofAdd
        (φ (σ h (φ.symm (Multiplicative.ofAdd v)))).toAdd)))).toAdd
    rw [map_mul, MulAut.mul_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

variable {n}

theorem linearRep_apply (φ : Q ≃* Multiplicative V) (σ : H →* MulAut Q) (h : H) (v : V) :
    linearRep n φ σ h v = (φ (σ h (φ.symm (Multiplicative.ofAdd v)))).toAdd :=
  rfl

theorem linearRep_apply_toAdd (φ : Q ≃* Multiplicative V) (σ : H →* MulAut Q) (h : H) (x : Q) :
    linearRep n φ σ h (φ x).toAdd = (φ (σ h x)).toAdd := by
  rw [linearRep_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem ker_linearRep (φ : Q ≃* Multiplicative V) (σ : H →* MulAut Q) :
    (linearRep n φ σ).ker = σ.ker := by
  ext h
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h1
    refine MulEquiv.ext fun x => φ.injective (Multiplicative.toAdd.injective ?_)
    have hx := LinearEquiv.congr_fun h1 (φ x).toAdd
    rw [linearRep_apply_toAdd] at hx
    exact hx
  · intro h1
    refine LinearEquiv.ext fun v => ?_
    rw [linearRep_apply, h1, MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl

end LinearRep

theorem card_units_zmod_four : Nat.card (ZMod 4)ˣ = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

theorem exists_index_two_of_inv {A H : Type*} [Group A] [Group H] {e : ℕ} (he : Odd e)
    (ψ : A ≃* Multiplicative (Fin e → ZMod 4)) (σ : H →* MulAut A) {u : H}
    (hu : ∀ a, σ u a = a⁻¹) : ∃ K : Subgroup H, K.index = 2 := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  let δ : H →* (ZMod 4)ˣ := LinearEquiv.det.comp (linearRep 4 ψ σ)
  have hneg : ((linearRep 4 ψ σ u : (Fin e → ZMod 4) ≃ₗ[ZMod 4] (Fin e → ZMod 4)) :
      (Fin e → ZMod 4) →ₗ[ZMod 4] (Fin e → ZMod 4)) = (-1 : ZMod 4) • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.coe_coe, linearRep_apply, hu, map_inv, MulEquiv.apply_symm_apply,
      LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul, toAdd_inv, toAdd_ofAdd]
  have hδu : δ u ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : (ZMod 4)ˣ => (x : ZMod 4)) h1
    simp only [δ, MonoidHom.comp_apply, LinearEquiv.coe_det, hneg, LinearMap.det_smul,
      LinearMap.det_id, Module.finrank_fin_fun, he.neg_one_pow, mul_one, Units.val_one] at h2
    exact absurd h2 (by decide)
  have hcard : Nat.card δ.range = 2 := by
    have hdvd : Nat.card δ.range ∣ 2 := card_units_zmod_four ▸ Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have hmem : δ u ∈ δ.range := ⟨u, rfl⟩
      rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hmem
      exact absurd hmem hδu
    · exact h2
  exact ⟨δ.ker, by rw [Subgroup.index_ker, hcard]⟩

theorem card_linearEquiv_le {k F : Type*} [Semiring k] [Field F] [Module k F] [Finite F] :
    Finite (F ≃ₗ[k] F) ∧ Nat.card (F ≃ₗ[k] F) ≤ (Nat.card F - 1).factorial := by
  let f : (F ≃ₗ[k] F) → Equiv.Perm {x : F // x ≠ 0} := fun g =>
    g.toEquiv.subtypeEquiv fun x => g.map_ne_zero_iff.symm
  have hf : Function.Injective f := by
    intro g g' hgg'
    refine LinearEquiv.ext fun x => ?_
    by_cases hx : x = 0
    · rw [hx, map_zero, map_zero]
    · exact congrArg Subtype.val (Equiv.congr_fun hgg' ⟨x, hx⟩)
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (F ≃ₗ[k] F) ≤ Nat.card (Equiv.Perm {x : F // x ≠ 0}) :=
        Nat.card_le_card_of_injective f hf
    _ = (Nat.card F - 1).factorial := by
        rw [Nat.card_perm, ← Nat.card_congr (unitsEquivNeZero (G₀ := F)), Nat.card_units]

theorem card_eq_mul_card_map_rightHom {N K : Type*} [Group N] [Group K] {φ : K →* MulAut N}
    (R : Subgroup (N ⋊[φ] K)) (hR : (SemidirectProduct.inl : N →* N ⋊[φ] K).range ≤ R) :
    Nat.card R = Nat.card N * Nat.card (R.map SemidirectProduct.rightHom) := by
  have h := Subgroup.card_ker_mul_card_range (SemidirectProduct.rightHom.comp R.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.comap_ker,
    ← SemidirectProduct.range_inl_eq_ker_rightHom] at h
  rw [← h]
  congr 1
  change Nat.card ((SemidirectProduct.inl : N →* N ⋊[φ] K).range.subgroupOf R) = Nat.card N
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv,
    Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv.symm]

theorem pCore_range_eq_bot {p : ℕ} {H L : Type*} [Group H] [Group L] (ρ : H →* L)
    (hker : ρ.ker = CFSG.pCore p H) : CFSG.pCore p ρ.range = ⊥ := by
  let P := CFSG.pCore p ρ.range
  have hN : (P.comap ρ.rangeRestrict).Normal := CFSG.pCore_normal.comap _
  have hNp : IsPGroup p (P.comap ρ.rangeRestrict) :=
    IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup ρ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, hker]; exact CFSG.pCore_isPGroup)
  have hle : P.comap ρ.rangeRestrict ≤ CFSG.pCore p H :=
    le_sSup (show _ ∈ {K : Subgroup H | K.Normal ∧ IsPGroup p K} from ⟨hN, hNp⟩)
  change P = ⊥
  rw [← Subgroup.map_comap_eq_self_of_surjective ρ.rangeRestrict_surjective P,
    Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict, hker]
  exact hle

theorem card_sup_mul_card_inf {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have hrel := Subgroup.relIndex_mul_card A B
  have hrel' := Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_left] at hrel'
  have : (A.subgroupOf (B ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
  have : (A.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hB
  have hidx : A.relIndex B = A.relIndex (A ⊔ B) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index, sup_comm]
    exact Nat.card_congr e.toEquiv
  rw [← hrel', ← hrel, hidx, inf_comm]
  ring

section Conj

variable {G : Type*} [Group G]

@[expose] def conjHom {H Q : Subgroup G} (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    H →* MulAut Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem conjHom_apply_coe {H Q : Subgroup G} (hN : H ≤ Subgroup.normalizer (Q : Set G)) (h : H)
    (x : Q) : ((conjHom hN h x : Q) : G) = h * x * (h : G)⁻¹ :=
  rfl

theorem ker_conjHom {H Q : Subgroup G} (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    (conjHom hN).ker = (Subgroup.centralizer (Q : Set G)).subgroupOf H := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 y hy
    have hy' := congrArg (fun f : MulAut Q => ((f ⟨y, hy⟩ : Q) : G)) h1
    simp only [conjHom_apply_coe, MulAut.one_apply] at hy'
    rw [mul_inv_eq_iff_eq_mul] at hy'
    exact hy'.symm
  · intro h1
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [conjHom_apply_coe, MulAut.one_apply, ← h1 y y.2, mul_inv_cancel_right]

theorem even_of_inv {H A : Subgroup G} (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hno : ∀ K : Subgroup H, K.index ≠ 2) {u : G} (huH : u ∈ H)
    (huinv : ∀ a ∈ A, u * a * u⁻¹ = a⁻¹) {e : ℕ} (ψ : A ≃* Multiplicative (Fin e → ZMod 4)) :
    Even e := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hHN : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  obtain ⟨K, hK⟩ := exists_index_two_of_inv hodd ψ (conjHom hHN) (u := ⟨u, huH⟩)
    fun a => Subtype.ext (huinv a a.2)
  exact hno K hK

theorem two_core_eq_sup [Finite G] {A J M : Subgroup G} {u : G} (hu2 : orderOf u = 2)
    (hJu : (J : Set G) = {1, u}) (hAJ : A ⊓ J = ⊥) (hAM : A ≤ M) (hJM : J ≤ M)
    (hrel : (A ⊔ J).relIndex M = 1) (hJA : J ≤ Subgroup.normalizer (A : Set G)) :
    J = Subgroup.zpowers u ∧ Nat.card J = 2 ∧ M = A ⊔ J ∧ Nat.card M = 2 * Nat.card A := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hJcard : Nat.card J = 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hJu, Set.ncard_pair hu1.symm]
  have huJ : u ∈ J := by
    have hu : u ∈ (J : Set G) := by
      rw [hJu]
      exact Set.mem_insert_of_mem _ rfl
    exact hu
  have hJz : J = Subgroup.zpowers u := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huJ) ?_
    rw [Nat.card_zpowers, hu2, hJcard]
  have hMeq : M = A ⊔ J := le_antisymm (Subgroup.relIndex_eq_one.mp hrel) (sup_le hAM hJM)
  refine ⟨hJz, hJcard, hMeq, ?_⟩
  have hprod := card_sup_mul_card_inf hJA
  rw [hAJ, Subgroup.card_bot, mul_one, hJcard] at hprod
  rw [hMeq, hprod, mul_comm]

end Conj

end CFSG.ShultStronglyClosedTI.FinalChain.SingerQuotient
