module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.GroupTheory.Coset.Card

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

section Stabilizer

variable {G : Type*} [Group G] (H : Subgroup G)

@[expose] def autStabilizer : Subgroup (MulAut G) where
  carrier := {γ | H.map (γ : G →* G) = H}
  mul_mem' {γ δ} (hγ : H.map (γ : G →* G) = H) (hδ : H.map (δ : G →* G) = H) := by
    change H.map ((δ.trans γ : G ≃* G) : G →* G) = H
    rw [MulEquiv.toMonoidHom_trans, ← Subgroup.map_map, hδ, hγ]
  one_mem' := Subgroup.map_id H
  inv_mem' {γ} (hγ : H.map (γ : G →* G) = H) := (Subgroup.map_symm_eq_iff_map_eq H).2 hγ

@[expose] def autStabilizerRestrict : autStabilizer H →* MulAut H where
  toFun γ := (MulEquiv.subgroupMap (γ : MulAut G) H).trans (MulEquiv.subgroupCongr γ.2)
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem coe_autStabilizerRestrict_apply (γ : autStabilizer H) (x : H) :
    ((autStabilizerRestrict H γ x : H) : G) = (γ : MulAut G) x :=
  rfl

variable {H} in
theorem apply_mem_of_mem_autStabilizer {γ : MulAut G} (hγ : γ ∈ autStabilizer H) {x : G}
    (hx : x ∈ H) : γ x ∈ H := by
  rw [← (hγ : H.map (γ : G →* G) = H)]
  exact Subgroup.mem_map_of_mem _ hx

end Stabilizer

section Semilinear

variable {K Q : Type*} [Field K] [Group Q] (e : Multiplicative K ≃* Q)

@[expose] def semilinearAddAut (c : Kˣ) (σ : K ≃+* K) : K ≃+ K where
  toFun x := c * σ x
  invFun x := σ.symm (↑c⁻¹ * x)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [mul_add]

@[expose] def coordSemilinearAut (c : Kˣ) (σ : K ≃+* K) : MulAut Q :=
  (e.symm.trans (AddEquiv.toMultiplicative (semilinearAddAut c σ))).trans e

theorem coordSemilinearAut_apply (c : Kˣ) (σ : K ≃+* K) (b : K) :
    coordSemilinearAut e c σ (e (.ofAdd b)) = e (.ofAdd (c * σ b)) := by
  simp [coordSemilinearAut, semilinearAddAut]

@[expose] def coordSemilinearGroup : Subgroup (MulAut Q) where
  carrier := {ψ | ∃ (c : Kˣ) (σ : K ≃+* K), ∀ b : K, ψ (e (.ofAdd b)) = e (.ofAdd (c * σ b))}
  mul_mem' := by
    rintro ψ ψ' ⟨c, σ, h⟩ ⟨c', σ', h'⟩
    refine ⟨c * Units.map σ.toMonoidHom c', σ'.trans σ, fun b => ?_⟩
    rw [MulAut.mul_apply, h', h]
    simp [mul_assoc]
  one_mem' := ⟨1, RingEquiv.refl K, fun b => by simp⟩
  inv_mem' := by
    rintro ψ ⟨c, σ, h⟩
    refine ⟨Units.map σ.symm.toMonoidHom c⁻¹, σ.symm, fun b => ?_⟩
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, h]
    simp

theorem coe_coordSemilinearGroup :
    (coordSemilinearGroup e : Set (MulAut Q)) =
      Set.range fun p : Kˣ × (K ≃+* K) => coordSemilinearAut e p.1 p.2 := by
  ext ψ
  constructor
  · rintro ⟨c, σ, h⟩
    refine ⟨(c, σ), MulEquiv.ext fun x => ?_⟩
    obtain ⟨b, rfl⟩ := e.surjective x
    exact (coordSemilinearAut_apply e c σ b.toAdd).trans (h b.toAdd).symm
  · rintro ⟨⟨c, σ⟩, rfl⟩
    exact ⟨c, σ, coordSemilinearAut_apply e c σ⟩

theorem coordSemilinearAut_injective :
    Function.Injective fun p : Kˣ × (K ≃+* K) => coordSemilinearAut e p.1 p.2 := by
  rintro ⟨c, σ⟩ ⟨c', σ'⟩ h
  have hb : ∀ b : K, (c : K) * σ b = c' * σ' b := fun b => by
    have := congrArg (fun ψ : MulAut Q => ψ (e (.ofAdd b))) h
    simpa only [coordSemilinearAut_apply, EmbeddingLike.apply_eq_iff_eq] using this
  have hc : c = c' := Units.ext (by simpa using hb 1)
  subst hc
  exact Prod.ext rfl (RingEquiv.ext fun b => mul_left_cancel₀ c.ne_zero (hb b))

theorem card_coordSemilinearGroup :
    Nat.card (coordSemilinearGroup e) = Nat.card Kˣ * Nat.card (K ≃+* K) := by
  rw [← SetLike.coe_sort_coe, coe_coordSemilinearGroup,
    Nat.card_range_of_injective (coordSemilinearAut_injective e), Nat.card_prod]

theorem card_dvd_of_forall_coordSemilinear {H : Subgroup (MulAut Q)}
    (hH : ∀ ψ ∈ H, ∃ (c : Kˣ) (σ : K ≃+* K), ∀ b : K, ψ (e (.ofAdd b)) = e (.ofAdd (c * σ b))) :
    Nat.card H ∣ Nat.card Kˣ * Nat.card (K ≃+* K) :=
  card_coordSemilinearGroup e ▸ Subgroup.card_dvd_of_le hH

end Semilinear

end CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
