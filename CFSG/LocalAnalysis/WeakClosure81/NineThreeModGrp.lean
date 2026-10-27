module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nineThree_exists_rep {W W₀ L : Subgroup G} (hW : IsElemAbelian 2 W) (hW₀ : W₀ ≤ W)
    (hLW : L ≤ normalizer (W : Set G)) (hLW₀ : L ≤ normalizer (W₀ : Set G)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M)
      (ρ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) M) (π : Additive ↥W →+ M),
      Function.Surjective π ∧ (∀ w : ↥W, π (Additive.ofMul w) = 0 ↔ (w : G) ∈ W₀) ∧
      ∀ (l : ↥L) (w w' : ↥W), (w' : G) = l * w * l⁻¹ →
        π (Additive.ofMul w') = (ρ l : M →ₗ[ZMod 2] M) (π (Additive.ofMul w)) := by
  classical
  letI : CommGroup ↥W := @IsMulCommutative.instCommGroup _ _ hW.1
  let N : Subgroup ↥W := W₀.subgroupOf W
  haveI : N.Normal := Subgroup.normal_of_comm N
  let conjAut : ↥L → (↥W ≃* ↥W) := fun l =>
    { toFun := fun a =>
        ⟨(l : G) * a * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLW l.2) a).mp a.2⟩
      invFun := fun a => ⟨(l : G)⁻¹ * a * (l : G), by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLW (L.inv_mem l.2)) a).mp a.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hN : ∀ (l : ↥L) (a : ↥W), conjAut l a ∈ N ↔ a ∈ N := by
    intro l a
    show (l : G) * a * (l : G)⁻¹ ∈ W₀ ↔ (a : G) ∈ W₀
    exact (Subgroup.mem_normalizer_iff.mp (hLW₀ l.2) a).symm
  have hsq : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW.2 w w.2)
  have h2 : ∀ x : Additive (↥W ⧸ N), 2 • x = 0 := by
    intro x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) := by rw [hw]; rfl
    rw [hx]
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    simp only [toMul_ofMul, toMul_zero]
    rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]
  letI : Module (ZMod 2) (Additive (↥W ⧸ N)) := AddCommGroup.zmodModule h2
  let eQ : ↥L → ((↥W ⧸ N) ≃* (↥W ⧸ N)) := fun l =>
    QuotientGroup.congr N N (conjAut l) (by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact (hN l b).2 hb
      · intro ha
        refine ⟨(conjAut l).symm a, ?_, by simp⟩
        show (conjAut l).symm a ∈ N
        rw [← hN l ((conjAut l).symm a), MulEquiv.apply_symm_apply]
        exact ha)
  have hrep : ∀ v : Additive (↥W ⧸ N), ∃ w : ↥W, v = Additive.ofMul (QuotientGroup.mk w) := by
    intro v
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨w, by rw [hw]; rfl⟩
  have hconj1 : ∀ w : ↥W, conjAut 1 w = w := fun w =>
    Subtype.ext (by show ((1 : ↥L) : G) * w * ((1 : ↥L) : G)⁻¹ = w; simp)
  have hconjmul : ∀ (a b : ↥L) (w : ↥W), conjAut (a * b) w = conjAut a (conjAut b w) :=
    fun a b w => Subtype.ext (by
      show ((a * b : ↥L) : G) * w * ((a * b : ↥L) : G)⁻¹ =
        (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹
      simp [mul_assoc])
  let eM : ↥L → (Additive (↥W ⧸ N) ≃ₗ[ZMod 2] Additive (↥W ⧸ N)) := fun l =>
    AddEquiv.toLinearEquiv (MulEquiv.toAdditive (eQ l))
      (fun c v => ZMod.map_smul (MulEquiv.toAdditive (eQ l)) c v)
  have heM : ∀ (l : ↥L) (w : ↥W), eM l (Additive.ofMul (QuotientGroup.mk w)) =
      Additive.ofMul (QuotientGroup.mk (conjAut l w)) := fun l w => rfl
  let ρ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (↥W ⧸ N)) :=
    { toFun := fun l => LinearMap.GeneralLinearGroup.ofLinearEquiv (eM l)
      map_one' := Units.ext (LinearMap.ext fun v => by
        obtain ⟨w, rfl⟩ := hrep v
        show eM 1 (Additive.ofMul (QuotientGroup.mk w)) = Additive.ofMul (QuotientGroup.mk w)
        rw [heM, hconj1])
      map_mul' := fun a b => Units.ext (LinearMap.ext fun v => by
        obtain ⟨w, rfl⟩ := hrep v
        show eM (a * b) (Additive.ofMul (QuotientGroup.mk w)) =
          eM a (eM b (Additive.ofMul (QuotientGroup.mk w)))
        rw [heM, heM, heM, hconjmul]) }
  refine ⟨Additive (↥W ⧸ N), inferInstance, inferInstance, ρ,
    MonoidHom.toAdditive (QuotientGroup.mk' N), ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, rfl⟩ := hrep v
    exact ⟨Additive.ofMul w, rfl⟩
  · intro w
    show Additive.ofMul (QuotientGroup.mk w : ↥W ⧸ N) = 0 ↔ _
    rw [← ofMul_one, Additive.ofMul.injective.eq_iff, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  · intro l w w' hw'
    have : w' = conjAut l w := Subtype.ext hw'
    show Additive.ofMul (QuotientGroup.mk w' : ↥W ⧸ N) = eM l (Additive.ofMul (QuotientGroup.mk w))
    rw [heM, this]

end CFSG.LocalAnalysis.WeakClosure81
