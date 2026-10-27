module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

section L8213A

@[expose] noncomputable def mulAutQuotCenter82 (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun α := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) α
    (J4.center_map_mulEquiv' α)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem mulAutQuotCenter82_mk {K : Type*} [Group K] (α : MulAut K) (x : K) :
    mulAutQuotCenter82 K α (x : K ⧸ Subgroup.center K) = ((α x : K) : K ⧸ Subgroup.center K) :=
  rfl

theorem injective_mulAutQuotCenter_82 {K : Type*} [Group K] (hK : commutator K = ⊤) :
    Function.Injective (mulAutQuotCenter82 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  have hZ : ∀ x : K, α x * x⁻¹ ∈ Subgroup.center K := by
    intro x
    have h1 := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ (x : K ⧸ Subgroup.center K))
      hα
    simp only [mulAutQuotCenter82_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have h2 : x⁻¹ * α x ∈ Subgroup.center K := by
      have := (Subgroup.center K).inv_mem h1
      simpa using this
    have h3 := (Subgroup.normal_of_characteristic (Subgroup.center K)).conj_mem _ h2 x
    simpa [mul_assoc] using h3
  let f : K →* ↥(Subgroup.center K) :=
    { toFun := fun x => ⟨α x * x⁻¹, hZ x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul]
        have hc : ∀ g : K, g * (α y * y⁻¹) = (α y * y⁻¹) * g := fun g =>
          Subgroup.mem_center_iff.mp (hZ y) g
        calc α x * α y * (x * y)⁻¹ = (α x * (α y * y⁻¹)) * x⁻¹ := by group
          _ = ((α y * y⁻¹) * α x) * x⁻¹ := by rw [hc]
          _ = (α y * y⁻¹) * (α x * x⁻¹) := by group
          _ = (α x * x⁻¹) * (α y * y⁻¹) := by rw [hc] }
  have hf : f.ker = ⊤ := by
    rw [eq_top_iff, ← hK]
    have : IsMulCommutative ↥(Subgroup.center K) := inferInstance
    refine Abelianization.commutator_subset_ker f
  ext x
  have h1 : f x = 1 := (MonoidHom.mem_ker).mp (hf ▸ Subgroup.mem_top x)
  have h2 := congrArg Subtype.val h1
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h2
  simpa [mul_inv_eq_one] using h2

theorem card_mulAut_le_quotCenter_82 {K : Type*} [Group K] [Finite K] (hK : commutator K = ⊤) :
    Nat.card (MulAut K) ≤ Nat.card (MulAut (K ⧸ Subgroup.center K)) := by
  have : Finite (MulAut (K ⧸ Subgroup.center K)) := finite_mulAut_82
  exact Nat.card_le_card_of_injective _ (injective_mulAutQuotCenter_82 hK)

theorem card_le_centralizer_mul_mulAut_82 {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    [K.Normal] :
    Nat.card X ≤ Nat.card ↥(Subgroup.centralizer (K : Set X)) * Nat.card (MulAut ↥K) := by
  have : Finite (MulAut ↥K) := finite_mulAut_82
  have happ : ∀ (x : X) (k : ↥K), ((MulAut.conjNormal (H := K) x k : ↥K) : X) = x * k * x⁻¹ :=
    fun x k => MulAut.conjNormal_apply x k
  have hker : (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set X) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) h
      simp only [happ, MulAut.one_apply] at h2
      calc k * x = x * k * x⁻¹ * x := by rw [h2]
        _ = x * k := by group
    · intro h
      ext k
      rw [happ, MulAut.one_apply, ← h k k.2]
      group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAut.conjNormal (H := K)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker] at h1
  rw [h1, mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

end L8213A

end CFSG.Quasithin.H13
