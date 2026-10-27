module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearNat
public import CFSG.Quasithin.Background.JonesParshallWedge
public import CFSG.Quasithin.Background.B5FinWedge

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.FFL

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem wedgeMat_cert5 :
    JonesParshall.wedgeMat (transvection (2 : Fin 5) 3 (1 : ZMod 2) * transvection 3 2 1) - 1 =
      !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 1, 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] *
        (JonesParshall.wedgeMat (transvection (0 : Fin 5) 1 (1 : ZMod 2)) - 1) +
      !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] *
        (JonesParshall.wedgeMat (transvection (1 : Fin 5) 2 (1 : ZMod 2)) - 1) +
      !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] *
        (JonesParshall.wedgeMat (transvection (2 : Fin 5) 3 (1 : ZMod 2)) - 1) := by
  decide

theorem wedgeMat_cert4 :
    B5FinWedge.wedgeMat4 (transvection (2 : Fin 4) 3 (1 : ZMod 2) * transvection 3 2 1) - 1 =
      !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0;
        0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] *
        (B5FinWedge.wedgeMat4 (transvection (0 : Fin 4) 1 (1 : ZMod 2)) - 1) +
      !![0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] *
        (B5FinWedge.wedgeMat4 (transvection (1 : Fin 4) 2 (1 : ZMod 2)) - 1) +
      !![0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] *
        (B5FinWedge.wedgeMat4 (transvection (2 : Fin 4) 3 (1 : ZMod 2)) - 1) := by
  decide

theorem mulVec_eq_of_cert {m : Type} [Fintype m] [DecidableEq m] {R : Type} [CommRing R]
    {M M₀ M₁ M₂ Y₀ Y₁ Y₂ : Matrix m m R} {c : m → R}
    (h : M - 1 = Y₀ * (M₀ - 1) + Y₁ * (M₁ - 1) + Y₂ * (M₂ - 1)) (h₀ : M₀ *ᵥ c = c)
    (h₁ : M₁ *ᵥ c = c) (h₂ : M₂ *ᵥ c = c) : M *ᵥ c = c := by
  have hz : ∀ {N : Matrix m m R}, N *ᵥ c = c → (N - 1) *ᵥ c = 0 := fun hN => by
    rw [sub_mulVec, one_mulVec, hN, sub_self]
  have hM : (M - 1) *ᵥ c = 0 := by
    rw [h, add_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hz h₀,
      hz h₁, hz h₂, mulVec_zero, mulVec_zero, mulVec_zero, add_zero, add_zero]
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hM
  exact hM

theorem fixesFixed_extSq5 :
    FixesFixed (FFModel.extSq (ZMod 2) 5) (unitri 5 (ZMod 2))
      (slGamma (a := (2 : Fin 5)) (b := 3) (by decide)) := by
  intro m _ hm
  obtain ⟨x, rfl⟩ : ∃ x : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2), Multiplicative.ofAdd x = m :=
    ⟨_, rfl⟩
  have hfix : ∀ τ ∈ unitri 5 (ZMod 2),
      JonesParshall.wedgeMat (slMat τ) *ᵥ JonesParshall.wedgeCoord x =
        JonesParshall.wedgeCoord x := by
    intro τ hτ
    have h1 := congrArg Multiplicative.toAdd (mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hm τ hτ)))
    rw [← JonesParshall.wedgeCoord_map]
    exact congrArg JonesParshall.wedgeCoord h1
  have h₀ := hfix _ (slT_mem_unitri (i := (0 : Fin 5)) (j := 1) (by decide) 1)
  have h₁ := hfix _ (slT_mem_unitri (i := (1 : Fin 5)) (j := 2) (by decide) 1)
  have h₂ := hfix _ (slT_mem_unitri (i := (2 : Fin 5)) (j := 3) (by decide) 1)
  rw [slMat_slT] at h₀ h₁ h₂
  have key := mulVec_eq_of_cert wedgeMat_cert5 h₀ h₁ h₂
  apply Subgroup.mem_bot.mpr
  apply mul_inv_eq_one.mpr
  change Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin' (slMat (slGamma _))) x) =
    Multiplicative.ofAdd x
  congr 1
  apply JonesParshall.wedgeCoord_bijective.1
  rw [JonesParshall.wedgeCoord_map]
  exact key

theorem fixesFixed_extSq4 :
    FixesFixed (FFModel.extSq (ZMod 2) 4) (unitri 4 (ZMod 2))
      (slGamma (a := (2 : Fin 4)) (b := 3) (by decide)) := by
  intro m _ hm
  obtain ⟨x, rfl⟩ : ∃ x : ⋀[ZMod 2]^2 (Fin 4 → ZMod 2), Multiplicative.ofAdd x = m :=
    ⟨_, rfl⟩
  have hfix : ∀ τ ∈ unitri 4 (ZMod 2),
      B5FinWedge.wedgeMat4 (slMat τ) *ᵥ B5FinWedge.wedgeCoord4 x =
        B5FinWedge.wedgeCoord4 x := by
    intro τ hτ
    have h1 := congrArg Multiplicative.toAdd (mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hm τ hτ)))
    rw [← B5FinWedge.wedgeCoord4_map]
    exact congrArg B5FinWedge.wedgeCoord4 h1
  have h₀ := hfix _ (slT_mem_unitri (i := (0 : Fin 4)) (j := 1) (by decide) 1)
  have h₁ := hfix _ (slT_mem_unitri (i := (1 : Fin 4)) (j := 2) (by decide) 1)
  have h₂ := hfix _ (slT_mem_unitri (i := (2 : Fin 4)) (j := 3) (by decide) 1)
  rw [slMat_slT] at h₀ h₁ h₂
  have key := mulVec_eq_of_cert wedgeMat_cert4 h₀ h₁ h₂
  apply Subgroup.mem_bot.mpr
  apply mul_inv_eq_one.mpr
  change Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin' (slMat (slGamma _))) x) =
    Multiplicative.ofAdd x
  congr 1
  apply B5FinWedge.wedgeCoord4_bijective.1
  rw [B5FinWedge.wedgeCoord4_map]
  exact key

end CFSG.Quasithin.EmptyFaithfulMultiple.FFL
