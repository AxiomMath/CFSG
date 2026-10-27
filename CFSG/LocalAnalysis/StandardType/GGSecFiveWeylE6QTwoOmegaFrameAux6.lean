module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux4
public import CFSG.GroupTheory.TwoReflections
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def a5A : Fin 5 → ZMod 3 := Pi.single 2 1 + Pi.single 3 1

@[expose] def a5B : Fin 5 → ZMod 3 := Pi.single 3 1 + Pi.single 4 1

@[expose] def a5C : Fin 5 → ZMod 3 := Pi.single 0 1 - Pi.single 1 1

@[expose] def a5D : Fin 5 → ZMod 3 :=
  Pi.single 0 1 - Pi.single 1 1 + Pi.single 2 1 - Pi.single 3 1 + Pi.single 4 1

@[expose] def a5RhoL (x : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := stdRefl a5A (stdRefl a5B x)

@[expose] def a5SigmaL (x : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := stdRefl a5C (stdRefl a5D x)

theorem a5RhoL_cube : ∀ x : Fin 5 → ZMod 3, a5RhoL (a5RhoL (a5RhoL x)) = x := by
  decide +kernel

theorem a5SigmaL_cube : ∀ x : Fin 5 → ZMod 3, a5SigmaL (a5SigmaL (a5SigmaL x)) = x := by
  decide +kernel

theorem a5RhoL_comm : ∀ x : Fin 5 → ZMod 3, a5RhoL (a5SigmaL x) = a5SigmaL (a5RhoL x) := by
  decide +kernel

theorem a5RhoL_fix : a5RhoL a5C = a5C := by decide

theorem a5SigmaL_move : a5SigmaL a5C ≠ a5C := by decide

theorem a5SigmaL2_move : a5SigmaL (a5SigmaL a5C) ≠ a5C := by decide

theorem a5RhoL_ne : a5RhoL (Pi.single 2 1) ≠ Pi.single 2 1 := by decide

theorem nine_dvd_card_closure_rootRefl
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y : V} (hy : B y y = 2) :
    9 ∣ Nat.card (Subgroup.closure {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2, B u y = 0 ∧
      r = rootRefl (B := B) u hu}) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (V ≃ₗ[ZMod 3] V) :=
    Fintype.ofInjective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e1 e2 h => by
        ext x
        exact congrFun h x)
  obtain ⟨f, hf, hfy⟩ := exists_frame_add_eq_of_root (B := B) hP hV hB hα hy
  let Gen : Set (V ≃ₗ[ZMod 3] V) := {r : V ≃ₗ[ZMod 3] V |
    ∃ u : V, ∃ hu : B u u = 2, B u y = 0 ∧ r = rootRefl (B := B) u hu}
  let a : V := f 2 + f 3
  let b : V := f 3 + f 4
  let c : V := f 0 - f 1
  let d : V := f 0 - f 1 + f 2 - f 3 + f 4
  have ha : B a a = 2 := by
    show B (f 2 + f 3) (f 2 + f 3) = 2
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have hay : B a y = 0 := by
    show B (f 2 + f 3) y = 0
    rw [← hfy]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have hb : B b b = 2 := by
    show B (f 3 + f 4) (f 3 + f 4) = 2
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have hby : B b y = 0 := by
    show B (f 3 + f 4) y = 0
    rw [← hfy]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have hc : B c c = 2 := by
    show B (f 0 - f 1) (f 0 - f 1) = 2
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  have hcy : B c y = 0 := by
    show B (f 0 - f 1) y = 0
    rw [← hfy]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_right, hf]
    decide
  have hd : B d d = 2 := by
    show B (f 0 - f 1 + f 2 - f 3 + f 4) (f 0 - f 1 + f 2 - f 3 + f 4) = 2
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  have hdy : B d y = 0 := by
    show B (f 0 - f 1 + f 2 - f 3 + f 4) y = 0
    rw [← hfy]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  let ρ : V ≃ₗ[ZMod 3] V := rootRefl (B := B) a ha * rootRefl (B := B) b hb
  let σ : V ≃ₗ[ZMod 3] V := rootRefl (B := B) c hc * rootRefl (B := B) d hd
  have haH : rootRefl (B := B) a ha ∈ Subgroup.closure Gen :=
    Subgroup.subset_closure ⟨a, ha, hay, rfl⟩
  have hbH : rootRefl (B := B) b hb ∈ Subgroup.closure Gen :=
    Subgroup.subset_closure ⟨b, hb, hby, rfl⟩
  have hcH : rootRefl (B := B) c hc ∈ Subgroup.closure Gen :=
    Subgroup.subset_closure ⟨c, hc, hcy, rfl⟩
  have hdH : rootRefl (B := B) d hd ∈ Subgroup.closure Gen :=
    Subgroup.subset_closure ⟨d, hd, hdy, rfl⟩
  have hρH : ρ ∈ Subgroup.closure Gen := Subgroup.mul_mem _ haH hbH
  have hσH : σ ∈ Subgroup.closure Gen := Subgroup.mul_mem _ hcH hdH
  have hca : frameCoord hV hf a = a5A := by
    show frameCoord hV hf (f 2 + f 3) = a5A
    simp only [map_add, frameCoord_frame hV hf]
    rfl
  have hcb : frameCoord hV hf b = a5B := by
    show frameCoord hV hf (f 3 + f 4) = a5B
    simp only [map_add, frameCoord_frame hV hf]
    rfl
  have hcc : frameCoord hV hf c = a5C := by
    show frameCoord hV hf (f 0 - f 1) = a5C
    rw [map_sub, frameCoord_frame hV hf 0, frameCoord_frame hV hf 1]
    rfl
  have hcd : frameCoord hV hf d = a5D := by
    show frameCoord hV hf (f 0 - f 1 + f 2 - f 3 + f 4) = a5D
    rw [map_add, map_sub, map_add, map_sub,
      frameCoord_frame hV hf 0, frameCoord_frame hV hf 1,
      frameCoord_frame hV hf 2, frameCoord_frame hV hf 3,
      frameCoord_frame hV hf 4]
    rfl
  have hρcoord : ∀ u : V, frameCoord hV hf (ρ u) = a5RhoL (frameCoord hV hf u) := by
    intro u
    show frameCoord hV hf ((rootRefl (B := B) a ha * rootRefl (B := B) b hb) u) =
      a5RhoL (frameCoord hV hf u)
    rw [LinearEquiv.mul_apply, frameCoord_rootRefl hV hf ha,
      frameCoord_rootRefl hV hf hb, hca, hcb]
    rfl
  have hσcoord : ∀ u : V, frameCoord hV hf (σ u) = a5SigmaL (frameCoord hV hf u) := by
    intro u
    show frameCoord hV hf ((rootRefl (B := B) c hc * rootRefl (B := B) d hd) u) =
      a5SigmaL (frameCoord hV hf u)
    rw [LinearEquiv.mul_apply, frameCoord_rootRefl hV hf hc,
      frameCoord_rootRefl hV hf hd, hcc, hcd]
    rfl
  have hinj := (frameCoord hV hf).injective
  have hρcube : ρ ^ 3 = 1 := by
    rw [pow_three']
    apply LinearEquiv.ext
    intro u
    apply hinj
    show frameCoord hV hf (ρ (ρ (ρ u))) = frameCoord hV hf ((1 : V ≃ₗ[ZMod 3] V) u)
    rw [hρcoord, hρcoord, hρcoord]
    exact a5RhoL_cube (frameCoord hV hf u)
  have hρne : ρ ≠ 1 := by
    intro hone
    have h2 : ρ (f 2) = f 2 := by rw [hone]; rfl
    have h3 := congrArg (frameCoord hV hf) h2
    rw [hρcoord, frameCoord_frame hV hf 2] at h3
    exact a5RhoL_ne h3
  have hσcube : σ ^ 3 = 1 := by
    rw [pow_three']
    apply LinearEquiv.ext
    intro u
    apply hinj
    show frameCoord hV hf (σ (σ (σ u))) = frameCoord hV hf ((1 : V ≃ₗ[ZMod 3] V) u)
    rw [hσcoord, hσcoord, hσcoord]
    exact a5SigmaL_cube (frameCoord hV hf u)
  have hσne : σ ≠ 1 := by
    intro hone
    have h2 : σ c = c := by rw [hone]; rfl
    have h3 := congrArg (frameCoord hV hf) h2
    rw [hσcoord, hcc] at h3
    exact a5SigmaL_move h3
  have hρ3 : orderOf ρ = 3 := orderOf_eq_prime hρcube hρne
  have hσ3 : orderOf σ = 3 := orderOf_eq_prime hσcube hσne
  have hcomm : Commute ρ σ := by
    apply LinearEquiv.ext
    intro u
    apply hinj
    show frameCoord hV hf (ρ (σ u)) = frameCoord hV hf (σ (ρ u))
    simp only [hρcoord, hσcoord]
    exact a5RhoL_comm (frameCoord hV hf u)
  have hρc : ρ c = c := by
    apply hinj
    rw [hρcoord, hcc]
    exact a5RhoL_fix
  have hσc : σ c ≠ c := by
    intro h2
    have h3 := congrArg (frameCoord hV hf) h2
    rw [hσcoord, hcc] at h3
    exact a5SigmaL_move h3
  have hσ2c : (σ ^ 2) c ≠ c := by
    intro h2
    have h3 := congrArg (frameCoord hV hf) h2
    rw [pow_two, LinearEquiv.mul_apply, hσcoord, hσcoord, hcc] at h3
    exact a5SigmaL2_move h3
  have hρstab : ρ ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) c := by
    rw [MulAction.mem_stabilizer_iff]
    exact hρc
  have hstab : Subgroup.zpowers ρ ≤ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) c :=
    Subgroup.zpowers_le.mpr hρstab
  have hinf : Subgroup.zpowers ρ ⊓ Subgroup.zpowers σ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxρ, hxσ⟩ := hx
    rw [mem_zpowers_iff_mem_range_orderOf, hσ3] at hxσ
    simp only [Finset.mem_image, Finset.mem_range] at hxσ
    obtain ⟨k, hk, rfl⟩ := hxσ
    interval_cases k
    · exact pow_zero σ
    · exact absurd (by simpa using (MulAction.mem_stabilizer_iff.mp (hstab hxρ))) hσc
    · exact absurd (by simpa using (MulAction.mem_stabilizer_iff.mp (hstab hxρ))) hσ2c
  have hcard : Nat.card ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) = 9 := by
    have h := (@CFSG.GroupTheory.card_zpowers_sup_zpowers (V ≃ₗ[ZMod 3] V) _ _
      ρ σ 3 hcomm hρ3 hσ3 hinf).1
    simpa using h
  have hle : Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ ≤ Subgroup.closure Gen :=
    sup_le (Subgroup.zpowers_le.mpr hρH) (Subgroup.zpowers_le.mpr hσH)
  have hdvd : 9 ∣ Nat.card (Subgroup.closure Gen) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcard] at h
  simpa [Gen] using hdvd

end CFSG.StandardType.E6QTwo

end
