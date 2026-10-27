module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Ctx

structure GGFarCtx {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) {n : ℕ} {F : Type} [Field F]
    (φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G) (x y : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  two : (2 : F) = 0
  three_le : 3 ≤ n
  lifts : GGFarLifts φ₁ φ₂ Bs
  exp : ∀ b ∈ Bs, b ^ p = 1
  cent : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs
  x_mem : x ∈ Bs
  y_mem : y ∈ Bs
  y_ne : y ≠ 1
  x_comm : ∀ s, x * φ₁ s = φ₁ s * x
  x_ncomm : ¬ ∀ s, x * φ₂ s = φ₂ s * x
  y_comm : ∀ s, y * φ₂ s = φ₂ s * y
  inj : ∀ g ∈ Bs, (∀ s, g * φ₁ s = φ₁ s * g) → (∀ s, g * φ₂ s = φ₂ s * g) → g = 1

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.perm_mem_normalizer₁ (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (π : Equiv.Perm (Fin (n + 1))) :
    φ₁ (slPerm hC.two π) ∈ Subgroup.normalizer (Bs : Set G) :=
  slPerm_mem_normalizer_of_actsDiag hC.two hC.exp hC.cent hC.lifts.ker₁ hC.lifts.diag₁ π

theorem GGFarCtx.perm_mem_normalizer₂ (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (π : Equiv.Perm (Fin (n + 1))) :
    φ₂ (slPerm hC.two π) ∈ Subgroup.normalizer (Bs : Set G) :=
  slPerm_mem_normalizer_of_actsDiag hC.two hC.exp hC.cent hC.lifts.ker₂ hC.lifts.diag₂ π

@[expose] noncomputable def GGFarCtx.permAut₁ (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs where
  toFun π := ggConjAut Bs (hC.perm_mem_normalizer₁ π)
  map_one' := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply]
    simp
  map_mul' π π' := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply]
    simp only [map_mul]
    group

@[expose] noncomputable def GGFarCtx.permAut₂ (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs where
  toFun π := ggConjAut Bs (hC.perm_mem_normalizer₂ π)
  map_one' := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply]
    simp
  map_mul' π π' := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply]
    simp only [map_mul]
    group

theorem GGFarCtx.permAut₁_apply (hC : GGFarCtx p Bs φ₁ φ₂ x y) (π : Equiv.Perm (Fin (n + 1)))
    (b : ↥Bs) :
    ((hC.permAut₁ π b : ↥Bs) : G) = φ₁ (slPerm hC.two π) * b * (φ₁ (slPerm hC.two π))⁻¹ :=
  rfl

theorem GGFarCtx.permAut₂_apply (hC : GGFarCtx p Bs φ₁ φ₂ x y) (π : Equiv.Perm (Fin (n + 1)))
    (b : ↥Bs) :
    ((hC.permAut₂ π b : ↥Bs) : G) = φ₂ (slPerm hC.two π) * b * (φ₂ (slPerm hC.two π))⁻¹ :=
  rfl

theorem GGFarCtx.map_slPerm_swap_compat (hC : GGFarCtx p Bs φ₁ φ₂ x y) (i j : Fin n) :
    φ₁ (slPerm hC.two (Equiv.swap i.succ j.succ)) =
      φ₂ (slPerm hC.two (Equiv.swap i.castSucc j.castSucc)) := by
  have h1 := DFunLike.congr_fun hC.lifts.compat (slPerm hC.two (Equiv.swap i j))
  simp only [MonoidHom.comp_apply] at h1
  rw [slUpperBlockHom_slPerm_swap hC.two i j] at h1
  rw [← slLowerBlockHom_slPerm_swap hC.two i j]
  exact h1

theorem GGFarCtx.permAut_compat (hC : GGFarCtx p Bs φ₁ φ₂ x y) (i j : Fin n) :
    hC.permAut₁ (Equiv.swap i.succ j.succ) = hC.permAut₂ (Equiv.swap i.castSucc j.castSucc) := by
  refine MulEquiv.ext fun b => Subtype.ext ?_
  rw [GGFarCtx.permAut₁_apply, GGFarCtx.permAut₂_apply, hC.map_slPerm_swap_compat i j]

theorem GGFarCtx.permAut₁_fix_x (hC : GGFarCtx p Bs φ₁ φ₂ x y) (σ : Equiv.Perm (Fin (n + 1))) :
    hC.permAut₁ σ ⟨x, hC.x_mem⟩ = ⟨x, hC.x_mem⟩ := by
  apply Subtype.ext
  rw [GGFarCtx.permAut₁_apply, ← hC.x_comm (slPerm hC.two σ)]
  group

theorem GGFarCtx.abab_mem_centralizer (hC : GGFarCtx p Bs φ₁ φ₂ x y) {i j : Fin n}
    (hcomm : hC.permAut₁ (Equiv.swap i.castSucc i.succ) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ) =
      hC.permAut₂ (Equiv.swap j.castSucc j.succ) * hC.permAut₁ (Equiv.swap i.castSucc i.succ)) :
    φ₁ (weylRep n F i) * φ₂ (weylRep n F j) * φ₁ (weylRep n F i) * φ₂ (weylRep n F j) ∈
      Subgroup.centralizer (Bs : Set G) := by
  set a : G := φ₁ (weylRep n F i) with ha
  set b : G := φ₂ (weylRep n F j) with hb
  have ha' : a = φ₁ (slPerm hC.two (Equiv.swap i.castSucc i.succ)) := by
    rw [ha, ← slPerm_swap_castSucc_succ hC.two i]
  have hb' : b = φ₂ (slPerm hC.two (Equiv.swap j.castSucc j.succ)) := by
    rw [hb, ← slPerm_swap_castSucc_succ hC.two j]
  set A : MulAut ↥Bs := hC.permAut₁ (Equiv.swap i.castSucc i.succ) with hA
  set B : MulAut ↥Bs := hC.permAut₂ (Equiv.swap j.castSucc j.succ) with hB
  have hcomm' : A * B = B * A := by simpa only [hA, hB] using hcomm
  have hA2 : A * A = 1 := by
    rw [hA, ← map_mul, Equiv.swap_mul_self, map_one]
  have hB2 : B * B = 1 := by
    rw [hB, ← map_mul, Equiv.swap_mul_self, map_one]
  have hsq : (A * B) * (A * B) = 1 := by
    calc (A * B) * (A * B) = A * (B * A) * B := by group
      _ = A * (A * B) * B := by rw [← hcomm']
      _ = (A * A) * (B * B) := by group
      _ = 1 := by rw [hA2, hB2, one_mul]
  have hA_apply : ∀ c : ↥Bs, ((A c : ↥Bs) : G) = a * (c : G) * a⁻¹ := by
    intro c
    rw [hA, ha']
    exact GGFarCtx.permAut₁_apply hC (Equiv.swap i.castSucc i.succ) c
  have hB_apply : ∀ c : ↥Bs, ((B c : ↥Bs) : G) = b * (c : G) * b⁻¹ := by
    intro c
    rw [hB, hb']
    exact GGFarCtx.permAut₂_apply hC (Equiv.swap j.castSucc j.succ) c
  have hABAB : ∀ c : ↥Bs,
      (((A * B) * (A * B)) c : G) =
        a * b * a * b * (c : G) * (a * b * a * b)⁻¹ := by
    intro c
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply]
    simp only [hA_apply, hB_apply]
    group
  have hconj : ∀ c : ↥Bs,
      a * b * a * b * (c : G) * (a * b * a * b)⁻¹ = (c : G) := by
    intro c
    have h1 : ((A * B) * (A * B)) c = c := by rw [hsq]; rfl
    rw [← hABAB c]
    exact congrArg Subtype.val h1
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro c hc
  exact (mul_inv_eq_iff_eq_mul.mp (hconj ⟨c, hc⟩)).symm

end Ctx

end CFSG.StandardType
