module

public import CFSG.Quasithin.Vol2.Ch11SecB414MJ
public import CFSG.Quasithin.Vol2.Ch11SecB414MC
public import CFSG.Quasithin.Vol2.Ch11SecB414MH

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {F : Type} [Field F]

theorem entries_of_mem_stabilizer {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ stabilizer (flagSpace 3 F 1)) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  have he : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 1 := by
    rw [mem_flagSpace]
    intro j hj
    have : j ≠ 0 := fun h => by subst h; simp at hj
    simp [this]
  have h1 : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ∈ flagSpace 3 F 1 := by
    rw [← (mem_stabilizer.mp hA)]
    exact ⟨_, he, rfl⟩
  rw [mem_flagSpace] at h1
  have a1 := h1 1 (by simp)
  have a2 := h1 2 (by simp)
  simp only [Matrix.mulVec_single_one] at a1 a2
  exact ⟨a1, a2⟩

theorem exists_rep_of_mem_Ptheta {y : PGL3 F} (hy : y ∈ Ptheta F 0) :
    ∃ A : SpecialLinearGroup (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) = y := by
  obtain ⟨x, ⟨A, hA, rfl⟩, rfl⟩ := hy
  obtain ⟨h10, h20⟩ := entries_of_mem_stabilizer hA
  exact ⟨A, h10, h20, (thetaP_proj A).symm⟩

theorem rhoMatG_toGL (A : SpecialLinearGroup (Fin 3) F) :
    rhoMatG (SpecialLinearGroup.toGL A) = rhoA (A : Matrix (Fin 3) (Fin 3) F) := by
  ext i k
  simp only [rhoMatG, rhoA, Matrix.of_apply, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

section Normal

variable {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F}
  (m : Model Γ V Z F k α)

theorem exists_dg_of_mem (hXΓ : X ≤ Γ) {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {x : G} (hx : x ∈ X) : ∃ c : Fˣ, α ⟨x, hXΓ hx⟩ = ProjGenLinGroup.mk (dgHom c) := by
  have h : α ⟨x, hXΓ hx⟩ ∈ (X.subgroupOf Γ).map α :=
    ⟨⟨x, hXΓ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hX] at h
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp h
  exact ⟨ν ^ z, by rw [← hz, ← map_zpow, ← map_zpow]⟩

theorem exists_rep_of_mem_L (hLΓ : L ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {l : G}
    (hl : l ∈ L) : ∃ A : SpecialLinearGroup (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) = α ⟨l, hLΓ hl⟩ := by
  have h : α ⟨l, hLΓ hl⟩ ∈ (L.subgroupOf Γ).map α :=
    ⟨⟨l, hLΓ hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [hL] at h
  exact exists_rep_of_mem_Ptheta h

theorem le_normalizer_pre_L (hLΓ : L ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
    {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (hW : ∀ A : Matrix (Fin 3) (Fin 3) F, A 1 0 = 0 → A 2 0 = 0 → A.det = 1 →
      ∀ M ∈ W, cnj A M ∈ W) :
    L ≤ Subgroup.normalizer (m.pre W : Set G) := by
  refine m.le_normalizer_pre hLΓ fun l hl => ?_
  obtain ⟨A, h10, h20, hA⟩ := exists_rep_of_mem_L hLΓ hL hl
  refine ⟨SpecialLinearGroup.toGL A, hA, fun M hM => ?_⟩
  rw [twAdj_toGL]
  exact hW _ h10 h20 A.prop M hM

theorem le_normalizer_pre_X (hXΓ : X ≤ Γ) {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (hW : ∀ c : Fˣ, ∀ M ∈ W, twAdj k (dgHom c) M ∈ W) :
    X ≤ Subgroup.normalizer (m.pre W : Set G) := by
  refine m.le_normalizer_pre hXΓ fun x hx => ?_
  obtain ⟨c, hc⟩ := exists_dg_of_mem hXΓ hX hx
  exact ⟨dgHom c, hc.symm, hW c⟩

end Normal

end CFSG.Quasithin.H13.Ch4.B414.M
