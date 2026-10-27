module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL
import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNsNorm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKAlign
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeEndNode
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs

public section

namespace CFSG.StandardType

open Matrix Polynomial CoordSL Multiplicative

private theorem ggSecFiveBPermQTwoK_center_eq_bot {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (m : ℕ) : Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_bot).mpr (TwoThree.eq_one_of_mem_scalars hF hx)

private theorem ggSecFiveBPermQTwoK_frameHom_eq {G : Type} [Group G] {F : Type} [Field F]
    {g : F[X]} [Fact (Irreducible g)] {m s r p : ℕ} [NeZero p]
    (κ : SpecialLinearGroup (Fin m) F →* G) (A₀ : SpecialLinearGroup (Fin m) F)
    (ε : Fin m ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (t : Multiplicative (Fin s → ZMod p)) :
    frameHom κ A₀ ε hC hCp t = κ (A₀ * SlNsRootGen.torusSL ε hC hCp t * A₀⁻¹) := by
  rw [← ofAdd_toAdd t, frameHom_apply, SlNsRootGen.torusSL_apply]

theorem ggSecFiveBPermQTwoK_signedPerm_of_mem_automizer {G : Type} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {g : F[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic 3 F) {m s r : ℕ}
    {Bs K : Subgroup G} {κ : SpecialLinearGroup (Fin m) F →* G} (hκ : Function.Injective κ)
    (hκK : κ.range = K) (ε : Fin m ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (A₀ : SpecialLinearGroup (Fin m) F) (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1)
    (T : ↥Bs →* Multiplicative (Fin s → ZMod 3)) (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) (x : SpecialLinearGroup (Fin m) F), (b : G) * κ x * (b : G)⁻¹ =
      frameHom κ A₀ ε hC hCp (T b) * κ x * (frameHom κ A₀ ε hC hCp (T b))⁻¹)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K Bs) :
    ∃ (π : Equiv.Perm (Fin s)) (σ : Fin s → ZMod 3), (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ (b : ↥Bs) (i : Fin s), toAdd (T (φ b)) (π i) = σ i * toAdd (T b) i := by
  classical
  obtain ⟨y, hyK, -, hy⟩ := mem_ggAutomizer_iff.mp hφ
  rw [← hκK] at hyK
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hyK
  let τ := SlNsRootGen.torusSL (p := 3) ε hC hCp
  let t : ↥Bs → Multiplicative (Fin s → ZMod 3) := fun b => T b
  have hZ := ggSecFiveBPermQTwoK_center_eq_bot hF m
  have hkey : ∀ b : ↥Bs, u * (A₀ * τ (t b) * A₀⁻¹) * u⁻¹ = A₀ * τ (t (φ b)) * A₀⁻¹ := by
    intro b
    refine mulAut_conj_injective hZ (MulEquiv.ext fun x => hκ ?_)
    simp only [MulAut.conj_apply]
    have hb := hT b (u⁻¹ * x * u)
    have hφb := hT (φ b) x
    rw [ggSecFiveBPermQTwoK_frameHom_eq] at hb hφb
    rw [hy b] at hφb
    simp only [map_mul, map_inv] at hb hφb ⊢
    have hb' : κ (A₀ * τ (t b) * A₀⁻¹) * (κ u⁻¹ * κ x * κ u) * (κ (A₀ * τ (t b) * A₀⁻¹))⁻¹ =
        (b : G) * (κ u⁻¹ * κ x * κ u) * (b : G)⁻¹ := by
      simp only [map_mul, map_inv]
      exact hb.symm
    calc κ u * (κ A₀ * κ (τ (t b)) * (κ A₀)⁻¹) * (κ u)⁻¹ * κ x *
          (κ u * (κ A₀ * κ (τ (t b)) * (κ A₀)⁻¹) * (κ u)⁻¹)⁻¹
        = κ u * (κ (A₀ * τ (t b) * A₀⁻¹) * (κ u⁻¹ * κ x * κ u) *
            (κ (A₀ * τ (t b) * A₀⁻¹))⁻¹) * (κ u)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = κ u * ((b : G) * (κ u⁻¹ * κ x * κ u) * (b : G)⁻¹) * (κ u)⁻¹ := by rw [hb']
      _ = κ u * (b : G) * (κ u)⁻¹ * κ x * (κ u * (b : G) * (κ u)⁻¹)⁻¹ := by
          simp only [map_inv]
          group
      _ = κ A₀ * κ (τ (t (φ b))) * (κ A₀)⁻¹ * κ x *
            (κ A₀ * κ (τ (t (φ b))) * (κ A₀)⁻¹)⁻¹ := hφb
  set w := A₀⁻¹ * u * A₀ with hw
  have hwt : ∀ b : ↥Bs, w * τ (t b) * w⁻¹ = τ (t (φ b)) := by
    intro b
    have h := hkey b
    calc w * τ (t b) * w⁻¹ = A₀⁻¹ * (u * (A₀ * τ (t b) * A₀⁻¹) * u⁻¹) * A₀ := by
          rw [hw]
          group
      _ = τ (t (φ b)) := by
          rw [h]
          group
  have hnorm : ∀ t₀ : Fin s → ZMod 3, ∃ t₁ : Fin s → ZMod 3,
      w * τ (ofAdd t₀) * w⁻¹ = τ (ofAdd t₁) := by
    intro t₀
    obtain ⟨b, hb⟩ := hTs (ofAdd t₀)
    refine ⟨toAdd (T (φ b)), ?_⟩
    rw [ofAdd_toAdd, ← hb]
    exact hwt b
  have h3 : 3 ∣ Nat.card F + 1 := by
    rw [hF]
  obtain ⟨π, σ, hσ, hrel⟩ := SlNsRootGen.exists_signedPerm_of_conj (p := 3) h3 hgd ε hC hCp w hnorm
  refine ⟨π, σ, hσ, fun b i => hrel _ _ ?_ i⟩
  rw [ofAdd_toAdd, ofAdd_toAdd]
  exact hwt b

theorem ggSecFiveBPermQTwoK_exists_align {G : Type} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {g : F[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic 3 F) {m r ρ : ℕ} (hr : 2 ≤ r)
    {Bs K : Subgroup G} {κ : SpecialLinearGroup (Fin m) F →* G} (hκ : Function.Injective κ)
    (hκK : κ.range = K) (ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin ρ)
    (A₀ : SpecialLinearGroup (Fin m) F) (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1)
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod 3))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) 3 i0)
    (T : ↥Bs →* Multiplicative (Fin (r + 1) → ZMod 3)) (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) (x : SpecialLinearGroup (Fin m) F), (b : G) * κ x * (b : G)⁻¹ =
      frameHom κ A₀ ε hC hCp (T b) * κ x * (frameHom κ A₀ ε hC hCp (T b))⁻¹) :
    ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧
      ∃ σ : Fin (r + 1) → ZMod 3, (∀ k, σ k = 1 ∨ σ k = -1) ∧
        ∀ (b : ↥Bs) (k : Fin (r + 1)), toAdd (T b) k = σ k * toAdd (eta b (π' k.succ)) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  let T' : (Fin (r + 2) → Multiplicative (ZMod 3)) →* (Fin (r + 1) → Multiplicative (ZMod 3)) :=
    (MulEquiv.piMultiplicative fun _ => ZMod 3).toMonoidHom.comp (T.comp eta.symm.toMonoidHom)
  have hT'apply : ∀ x k, toAdd (T' x k) = toAdd (T (eta.symm x)) k := fun x k => by
    simp [T', MulEquiv.piMultiplicative_apply]
  have hTs' : Function.Surjective T' := by
    intro z
    obtain ⟨b, hb⟩ := hTs ((MulEquiv.piMultiplicative fun _ => ZMod 3).symm z)
    refine ⟨eta b, ?_⟩
    show (MulEquiv.piMultiplicative fun _ => ZMod 3) (T (eta.symm (eta b))) = z
    rw [MulEquiv.symm_apply_apply, hb, MulEquiv.apply_symm_apply]
  have hker' : ∀ x, T' x = 1 → ∀ j, j ≠ i0 → x j = 1 := by
    intro x hx j hj
    have h1 : T (eta.symm x) = 1 := by
      have h : (MulEquiv.piMultiplicative fun _ => ZMod 3) (T (eta.symm x)) = 1 := hx
      rwa [MulEquiv.map_eq_one_iff] at h
    have hmem : ((eta.symm x : ↥Bs) : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ hk
      rw [← hκK] at hk
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hk
      have h := hT (eta.symm x) y
      rw [h1, map_one, one_mul, inv_one, mul_one] at h
      calc κ y * ((eta.symm x : ↥Bs) : G) =
            ((eta.symm x : ↥Bs) : G) * κ y * ((eta.symm x : ↥Bs) : G)⁻¹ *
              ((eta.symm x : ↥Bs) : G) := by rw [h]
        _ = ((eta.symm x : ↥Bs) : G) * κ y := by group
    have h := ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer hp2 hA hmem hj
    simpa using h
  have hW : ∀ w ∈ bCoordinateBlock (r + 2) 3 i0, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (σ : Fin (r + 1) → ZMod 3), (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ x i, toAdd (T' (w x) (π i)) = σ i * toAdd (T' x i) := by
    intro w hw
    rw [← hA] at hw
    obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp hw
    obtain ⟨π, σ, hσ, hπ⟩ := ggSecFiveBPermQTwoK_signedPerm_of_mem_automizer hF hgd hκ hκK ε A₀
      hC hCp T hTs hT hφ
    refine ⟨π, σ, hσ, fun x i => ?_⟩
    have hwx : w x = eta (φ (eta.symm x)) := by
      rw [← hφw]
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hT'apply, hT'apply, hwx, MulEquiv.symm_apply_apply]
    exact hπ (eta.symm x) i
  obtain ⟨π', hπ'0, c, hc, σ, hσ, halign⟩ :=
    ggSecFiveBPermSpK_exists_align hp2 hr T' hTs' hker' hW
  have hunit : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
  refine ⟨π', hπ'0, fun k => σ k * c, fun k => ?_, fun b k => ?_⟩
  · show σ k * c = 1 ∨ σ k * c = -1
    rcases hσ k with h | h <;> rcases hunit c hc with h' | h' <;> rw [h, h'] <;> decide
  · have h := halign (eta b) k
    rw [hT'apply, MulEquiv.symm_apply_apply] at h
    exact h

end CFSG.StandardType

end
