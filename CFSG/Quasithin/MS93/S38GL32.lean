module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Fixed

public section

namespace CFSG.Quasithin.MS93.GL32F

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family

@[expose] def tAll : List Mat3 := [unitri 0 0 0, unitri 0 0 1, unitri 0 1 0, unitri 0 1 1,
  unitri 1 0 0, unitri 1 0 1, unitri 1 1 0, unitri 1 1 1]

theorem mem_tAll : ∀ x y z : ZMod 2, unitri x y z ∈ tAll := by decide

theorem tinvols_transv : ∀ b ∈ tinvols, ∃ c : Fin 3 → ZMod 2, c ≠ 0 ∧
    (∀ v, (b - 1) *ᵥ v = 0 ∨ (b - 1) *ᵥ v = c) ∧ ∃ v, (b - 1) *ᵥ v = c := by
  decide +kernel

theorem tinvols_uniq : ∀ b₁ ∈ tinvols, ∀ b₂ ∈ tinvols, ∀ b₁' ∈ tinvols, ∀ b₂' ∈ tinvols,
    b₁ ≠ b₂ → b₁ * b₂ = b₂ * b₁ → (∀ v, ∃ w, (b₁ - 1) *ᵥ v = (b₂ - 1) *ᵥ w) →
    b₁' ≠ b₂' → b₁' * b₂' = b₂' * b₁' → (∀ v, ∃ w, (b₁' - 1) *ᵥ v = (b₂' - 1) *ᵥ w) →
    (b₁' = b₁ ∨ b₁' = b₂ ∨ b₁' = b₁ * b₂) := by
  decide +kernel

theorem tinvols_cent : ∀ b₁ ∈ tinvols, ∀ b₂ ∈ tinvols, b₁ ≠ b₂ → b₁ * b₂ = b₂ * b₁ →
    ∀ g ∈ tAll, g * b₁ = b₁ * g → g * b₂ = b₂ * g →
      (g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂) := by
  decide +kernel

open scoped Pointwise in
theorem exists_conj_mem_sylowT {P : Subgroup GL32} (hP : IsPGroup 2 P) :
    ∃ g : GL32, ∀ x ∈ P, g⁻¹ * x * g ∈ sylowT := by
  obtain ⟨U, hU⟩ := exists_sylow_T
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL32 U S
  refine ⟨g, fun x hx => ?_⟩
  have h1 : x ∈ (S : Subgroup GL32) := hS hx
  rw [← hg] at h1
  have h2 : x ∈ MulAut.conj g • (U : Subgroup GL32) := h1
  rw [Subgroup.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨u, hu, rfl⟩ := h2
  have : g⁻¹ * (MulAut.conj g • u) * g = u := by
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [this, ← hU]
  exact hu

theorem conj_sub_one (g b : GL32) :
    ((g⁻¹ * b * g : GL32) : Mat3) - 1 = ((g⁻¹ : GL32) : Mat3) * ((b : Mat3) - 1) * (g : Mat3) := by
  have h1 : ((g⁻¹ : GL32) : Mat3) * (g : Mat3) = 1 := Units.inv_mul g
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Units.val_mul, Units.val_mul]

theorem conj_sq {g b : GL32} (hb : b ^ 2 = 1) : (g⁻¹ * b * g) ^ 2 = 1 := by
  rw [pow_two] at hb ⊢
  calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
    _ = 1 := by rw [hb]; group

theorem conj_ne_one {g b : GL32} (hb : b ≠ 1) : g⁻¹ * b * g ≠ 1 := by
  intro h
  apply hb
  calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem conj_comm {g a b : GL32} (h : a * b = b * a) :
    (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
  calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
    _ = g⁻¹ * (b * a) * g := by rw [h]
    _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group

theorem mem_tinvols_of_conj {g b : GL32} (hT : g⁻¹ * b * g ∈ sylowT) (hb : b ^ 2 = 1)
    (hb1 : b ≠ 1) : ((g⁻¹ * b * g : GL32) : Mat3) ∈ tinvols :=
  val_mem_tinvols hT (conj_sq hb) (conj_ne_one hb1)

theorem sub_one_eq_conj (g A : GL32) :
    (A : Mat3) - 1 = (g : Mat3) * (((g⁻¹ * A * g : GL32) : Mat3) - 1) * ((g⁻¹ : GL32) : Mat3) := by
  have h1 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
  rw [conj_sub_one]
  calc (A : Mat3) - 1 = ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) * ((A : Mat3) - 1) *
        ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sub_one_mulVec_eq (g A : GL32) (v : Fin 3 → ZMod 2) :
    ((A : Mat3) - 1) *ᵥ v =
      (g : Mat3) *ᵥ ((((g⁻¹ * A * g : GL32) : Mat3) - 1) *ᵥ (((g⁻¹ : GL32) : Mat3) *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← sub_one_eq_conj]

theorem zpowers_sq {A : GL32} (hA : A ^ 2 = 1) : ∀ a ∈ Subgroup.zpowers A, a * a = 1 := by
  rintro _ ⟨k, rfl⟩
  show A ^ k * A ^ k = 1
  rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul]
  have : A ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, hA]
  rw [this, _root_.one_zpow]

theorem transv {A : GL32} (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    ∃ c : Fin 3 → ZMod 2, c ≠ 0 ∧ (∀ v, ((A : Mat3) - 1) *ᵥ v = 0 ∨ ((A : Mat3) - 1) *ᵥ v = c) ∧
      ∃ v, ((A : Mat3) - 1) *ᵥ v = c := by
  obtain ⟨U, hU⟩ := exists_sylow_T
  obtain ⟨g, hg⟩ := exists_conj_le_sylow_two U (Subgroup.zpowers A) (zpowers_sq hA)
  have hT : g⁻¹ * A * g ∈ sylowT := hU ▸ hg A (Subgroup.mem_zpowers A)
  obtain ⟨c, hc0, hc, ⟨v₀, hv₀⟩⟩ := tinvols_transv _ (mem_tinvols_of_conj hT hA hA1)
  have hgc : (g : Mat3) *ᵥ c ≠ 0 := by
    intro h
    apply hc0
    have h1 : ((g⁻¹ : GL32) : Mat3) * (g : Mat3) = 1 := Units.inv_mul g
    calc c = (((g⁻¹ : GL32) : Mat3) * (g : Mat3)) *ᵥ c := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  refine ⟨(g : Mat3) *ᵥ c, hgc, fun v => ?_, ⟨(g : Mat3) *ᵥ v₀, ?_⟩⟩
  · rw [sub_one_mulVec_eq g A v]
    rcases hc (((g⁻¹ : GL32) : Mat3) *ᵥ v) with h | h
    · left
      rw [h, Matrix.mulVec_zero]
    · right
      rw [h]
  · have h1 : ((g⁻¹ : GL32) : Mat3) * (g : Mat3) = 1 := Units.inv_mul g
    have h2 : ((g⁻¹ : GL32) : Mat3) *ᵥ ((g : Mat3) *ᵥ v₀) = v₀ := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [sub_one_mulVec_eq g A, h2, hv₀]

theorem conj_sub_one_mulVec (g b : GL32) (v : Fin 3 → ZMod 2) :
    (((g⁻¹ * b * g : GL32) : Mat3) - 1) *ᵥ v =
      ((g⁻¹ : GL32) : Mat3) *ᵥ (((b : Mat3) - 1) *ᵥ ((g : Mat3) *ᵥ v)) := by
  rw [conj_sub_one, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem conj_img {g b₁ b₂ : GL32}
    (himg : ∀ v, ∃ w, ((b₁ : Mat3) - 1) *ᵥ v = ((b₂ : Mat3) - 1) *ᵥ w) :
    ∀ v, ∃ w, (((g⁻¹ * b₁ * g : GL32) : Mat3) - 1) *ᵥ v =
      (((g⁻¹ * b₂ * g : GL32) : Mat3) - 1) *ᵥ w := by
  intro v
  obtain ⟨w, hw⟩ := himg ((g : Mat3) *ᵥ v)
  refine ⟨((g⁻¹ : GL32) : Mat3) *ᵥ w, ?_⟩
  have h1 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
  have h2 : (g : Mat3) *ᵥ (((g⁻¹ : GL32) : Mat3) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [conj_sub_one_mulVec, conj_sub_one_mulVec, hw, h2]

theorem conj_inj {g a b : GL32}
    (h : ((g⁻¹ * a * g : GL32) : Mat3) = ((g⁻¹ * b * g : GL32) : Mat3)) : a = b := by
  have h' : g⁻¹ * a * g = g⁻¹ * b * g := Units.ext h
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h']
    _ = b := by group

theorem eq_of_center_four {P : Subgroup GL32} (hP : IsPGroup 2 P)
    {b₁ b₂ b₁' b₂' : GL32} (h₁ : b₁ ∈ P) (h₂ : b₂ ∈ P) (h₁' : b₁' ∈ P) (h₂' : b₂' ∈ P)
    (hs₁ : b₁ ^ 2 = 1) (hs₂ : b₂ ^ 2 = 1) (hs₁' : b₁' ^ 2 = 1) (hs₂' : b₂' ^ 2 = 1)
    (hn₁ : b₁ ≠ 1) (hn₂ : b₂ ≠ 1) (hn₁' : b₁' ≠ 1) (hn₂' : b₂' ≠ 1)
    (hne : b₁ ≠ b₂) (hc : b₁ * b₂ = b₂ * b₁)
    (himg : ∀ v, ∃ w, ((b₁ : Mat3) - 1) *ᵥ v = ((b₂ : Mat3) - 1) *ᵥ w)
    (hne' : b₁' ≠ b₂') (hc' : b₁' * b₂' = b₂' * b₁')
    (himg' : ∀ v, ∃ w, ((b₁' : Mat3) - 1) *ᵥ v = ((b₂' : Mat3) - 1) *ᵥ w) :
    b₁' = b₁ ∨ b₁' = b₂ ∨ b₁' = b₁ * b₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowT hP
  have hmat : ∀ {x y : GL32}, x * y = y * x →
      ((g⁻¹ * x * g : GL32) : Mat3) * ((g⁻¹ * y * g : GL32) : Mat3) =
        ((g⁻¹ * y * g : GL32) : Mat3) * ((g⁻¹ * x * g : GL32) : Mat3) := fun hxy => by
    rw [← Units.val_mul, ← Units.val_mul, conj_comm hxy]
  have hne₀ : ∀ {x y : GL32}, x ≠ y →
      ((g⁻¹ * x * g : GL32) : Mat3) ≠ ((g⁻¹ * y * g : GL32) : Mat3) := fun hxy h =>
    hxy (conj_inj h)
  rcases tinvols_uniq _ (mem_tinvols_of_conj (hg _ h₁) hs₁ hn₁)
      _ (mem_tinvols_of_conj (hg _ h₂) hs₂ hn₂) _ (mem_tinvols_of_conj (hg _ h₁') hs₁' hn₁')
      _ (mem_tinvols_of_conj (hg _ h₂') hs₂' hn₂') (hne₀ hne) (hmat hc) (conj_img himg)
      (hne₀ hne') (hmat hc') (conj_img himg') with h | h | h
  · exact Or.inl (conj_inj h)
  · exact Or.inr (Or.inl (conj_inj h))
  · right; right
    apply conj_inj (g := g)
    rw [h, ← Units.val_mul]
    congr 1
    group

theorem mem_of_comm_four {P : Subgroup GL32} (hP : IsPGroup 2 P)
    {b₁ b₂ y : GL32} (h₁ : b₁ ∈ P) (h₂ : b₂ ∈ P) (hy : y ∈ P)
    (hs₁ : b₁ ^ 2 = 1) (hs₂ : b₂ ^ 2 = 1) (hn₁ : b₁ ≠ 1) (hn₂ : b₂ ≠ 1)
    (hne : b₁ ≠ b₂) (hc : b₁ * b₂ = b₂ * b₁) (hy₁ : y * b₁ = b₁ * y) (hy₂ : y * b₂ = b₂ * y) :
    y = 1 ∨ y = b₁ ∨ y = b₂ ∨ y = b₁ * b₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowT hP
  have hmat : ∀ {x z : GL32}, x * z = z * x →
      ((g⁻¹ * x * g : GL32) : Mat3) * ((g⁻¹ * z * g : GL32) : Mat3) =
        ((g⁻¹ * z * g : GL32) : Mat3) * ((g⁻¹ * x * g : GL32) : Mat3) := fun hxz => by
    rw [← Units.val_mul, ← Units.val_mul, conj_comm hxz]
  have hyT : ((g⁻¹ * y * g : GL32) : Mat3) ∈ tAll := by
    obtain ⟨a, b, c, he⟩ := hg y hy
    rw [he]
    exact mem_tAll a b c
  rcases tinvols_cent _ (mem_tinvols_of_conj (hg _ h₁) hs₁ hn₁)
      _ (mem_tinvols_of_conj (hg _ h₂) hs₂ hn₂) (fun h => hne (conj_inj h)) (hmat hc)
      _ hyT (hmat hy₁) (hmat hy₂) with h | h | h | h
  · left
    apply conj_inj (g := g)
    rw [h]
    simp
  · exact Or.inr (Or.inl (conj_inj h))
  · exact Or.inr (Or.inr (Or.inl (conj_inj h)))
  · right; right; right
    apply conj_inj (g := g)
    rw [h, ← Units.val_mul]
    congr 1
    group

end CFSG.Quasithin.MS93.GL32F
