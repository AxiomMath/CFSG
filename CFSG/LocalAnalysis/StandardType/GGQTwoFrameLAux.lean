module

public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

theorem qTwoFrameLP_rawDatumLegacy_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [LargeEvenRawDatumLegacy] at h <;> try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem qTwoFrameLP_centerQuotAut_eq_one {H : Type*} [Group H]
    (hH : commutator H = ⊤) {α : MulAut H} (hα : centerQuotAut H α = 1) : α = 1 := by
  have hz : ∀ y : H, α y * y⁻¹ ∈ Subgroup.center H := by
    intro y
    have h1 := congrArg
      (fun φ : MulAut (H ⧸ Subgroup.center H) => φ (y : H ⧸ Subgroup.center H)) hα
    simp only [centerQuotAut_mk, MulAut.one_apply] at h1
    have h2 : y⁻¹ * α y ∈ Subgroup.center H := by
      have := inv_mem (QuotientGroup.eq.mp h1)
      simpa [mul_inv_rev] using this
    have h3 : α y * y⁻¹ = y⁻¹ * α y := by
      have := (Subgroup.mem_center_iff.mp h2) y
      calc α y * y⁻¹ = (y * (y⁻¹ * α y)) * y⁻¹ := by group
        _ = ((y⁻¹ * α y) * y) * y⁻¹ := by rw [this]
        _ = y⁻¹ * α y := by group
    rw [h3]
    exact h2
  let f : H →* H :=
    { toFun := fun y => α y * y⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h := (Subgroup.mem_center_iff.mp (hz b)) a⁻¹
        simp only [map_mul, mul_inv_rev]
        calc α a * α b * (b⁻¹ * a⁻¹) = α a * ((α b * b⁻¹) * a⁻¹) := by group
          _ = α a * (a⁻¹ * (α b * b⁻¹)) := by rw [h]
          _ = α a * a⁻¹ * (α b * b⁻¹) := by group }
  have hker : commutator H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz b)) (f a)
  ext y
  have h1 : f y = 1 := hker (by rw [hH]; exact Subgroup.mem_top _)
  exact mul_inv_eq_one.mp h1

theorem qTwoFrameLP_centerQuotAut_injective {H : Type*} [Group H]
    (hH : commutator H = ⊤) : Function.Injective (centerQuotAut H) := by
  intro f g hfg
  have h : f * g⁻¹ = 1 := by
    apply qTwoFrameLP_centerQuotAut_eq_one hH
    rw [map_mul, hfg, map_inv, mul_inv_cancel]
  exact mul_inv_eq_one.mp h

theorem qTwoFrameLP_isElemAbelian_top {H : Type*} [Group H] {p : ℕ} {E : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (⊤ : Subgroup E) := by
  rw [CFSG.Open.isElemAbelian_iff_isElementaryAbelian] at hE ⊢
  exact CFSG.IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv.symm hE

theorem qTwoFrameLP_ggIsDiagMat_of_isDiag {n : ℕ} {K : Type} [Field K]
    {g : GL (Fin n) K} (h : (g : Matrix (Fin n) (Fin n) K).IsDiag) : ggIsDiagMat g := by
  refine ⟨fun i => (g : Matrix (Fin n) (Fin n) K) i i, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal]
  · have hzero : (Matrix.diagonal (fun i => (g : Matrix (Fin n) (Fin n) K) i i)) i j = 0 := by
      simp [Matrix.diagonal, hij]
    rw [hzero]
    exact h hij

theorem qTwoFrameLP_map_le_of_central_twoPower {L : Type*} [Group L]
    {Δ : Subgroup L} (hΔc : Δ ≤ Subgroup.center L) (hΔ2 : IsPGroup 2 Δ)
    (hΔmax : ∀ z ∈ Subgroup.center L, (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ Δ)
    (f : MulAut L) : Δ.map f.toMonoidHom ≤ Δ := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine hΔmax (f x) ?_ ?_
  · rw [← Subgroup.map_center_eq f]
    exact ⟨x, hΔc hx, rfl⟩
  · obtain ⟨k, hk⟩ := hΔ2 ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← map_pow, hk', map_one]

theorem qTwoFrameLP_characteristic_of_central_twoPower {L : Type*} [Group L] [Finite L]
    {Δ : Subgroup L} (hΔc : Δ ≤ Subgroup.center L) (hΔ2 : IsPGroup 2 Δ)
    (hΔmax : ∀ z ∈ Subgroup.center L, (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ Δ) :
    Δ.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro f
  apply le_antisymm (qTwoFrameLP_map_le_of_central_twoPower hΔc hΔ2 hΔmax f)
  have h := qTwoFrameLP_map_le_of_central_twoPower hΔc hΔ2 hΔmax f.symm
  intro x hx
  have hx' : f.symm x ∈ Δ := h ⟨x, hx, rfl⟩
  exact ⟨f.symm x, hx', by simp⟩

@[expose] noncomputable def qTwoFrameLP_centerQuotAutOfCharacteristic {G : Type*} [Group G]
    (Δ : Subgroup G) [Δ.Normal] (hΔ : Δ.Characteristic) : MulAut G →* MulAut (G ⧸ Δ) where
  toFun f := QuotientGroup.congr Δ Δ f (Subgroup.characteristic_iff_map_eq.mp hΔ f)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' f g := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem qTwoFrameLP_centerQuotAutOfCharacteristic_mk {G : Type*} [Group G]
    (Δ : Subgroup G) [Δ.Normal] (hΔ : Δ.Characteristic) (f : MulAut G) (l : G) :
    qTwoFrameLP_centerQuotAutOfCharacteristic Δ hΔ f (QuotientGroup.mk l : G ⧸ Δ) =
      QuotientGroup.mk (f l) :=
  rfl

theorem qTwoFrameLP_eq_of_mul_inv_mem_center {G H : Type*} [Group G] [Group H]
    (hperf : commutator G = ⊤) (A B : G →* H)
    (h : ∀ x, A x * (B x)⁻¹ ∈ Subgroup.center H) : A = B := by
  let φ : G →* H :=
    { toFun := fun x => A x * (B x)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hz : (A y * (B y)⁻¹) * (B x)⁻¹ = (B x)⁻¹ * (A y * (B y)⁻¹) :=
          ((Subgroup.mem_center_iff.mp (h y)) (B x)⁻¹).symm
        calc A (x * y) * (B (x * y))⁻¹
            = A x * A y * ((B y)⁻¹ * (B x)⁻¹) := by rw [map_mul, map_mul, mul_inv_rev]
          _ = A x * ((A y * (B y)⁻¹) * (B x)⁻¹) := by group
          _ = A x * ((B x)⁻¹ * (A y * (B y)⁻¹)) := by rw [hz]
          _ = A x * (B x)⁻¹ * (A y * (B y)⁻¹) := by group }
  have hφ : ∀ x, φ x ∈ Subgroup.center H := h
  have hker : commutator G ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp (hφ x)) (φ y)).symm
  ext x
  have h1 : φ x = 1 := hker (by rw [hperf]; exact Subgroup.mem_top x)
  exact mul_inv_eq_one.mp h1

end CFSG.StandardType.QTwo

end
