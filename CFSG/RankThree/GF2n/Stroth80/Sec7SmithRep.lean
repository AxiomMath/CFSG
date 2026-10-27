module

public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7SiegelGroup
public import CFSG.RankThree.GF2n.Stroth80.Sec7SmithAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def Sec7Siegel (e : Fin 4 ⊕ Fin 4 → K) (g : StatedOmega (StatedQuadPlus 4 K)) : Prop :=
  ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = e ∧
    (∀ x : Fin 4 ⊕ Fin 4 → K, StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x -
        StatedQuadPlus 4 K e = 0 →
      ∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x = c • e) ∧
    (∀ x : Fin 4 ⊕ Fin 4 → K,
      StatedQuadPlus 4 K ((((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) + e) -
        StatedQuadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) -
        StatedQuadPlus 4 K e = 0)

theorem sec7Siegel_iff {e : Fin 4 ⊕ Fin 4 → K} (he : StatedQuadPlus 4 K e = 0) (he0 : e ≠ 0)
    (g : StatedOmega (StatedQuadPlus 4 K)) :
    Sec7Siegel e g ↔ (g : GL (Fin 4 ⊕ Fin 4) K) ∈ rootGroupGL (quadPlus 4 K) e :=
  sec7_siegel_iff_rootGroupGL he he0 g

@[expose] noncomputable def sec7SiegelGroup (K : Type) [Field K] (e : Fin 4 ⊕ Fin 4 → K) :
    Subgroup (StatedOmega (StatedQuadPlus 4 K)) :=
  (rootGroupGL (quadPlus 4 K) e).subgroupOf (StatedOmega (StatedQuadPlus 4 K))

theorem mem_sec7SiegelGroup {e : Fin 4 ⊕ Fin 4 → K} (he : StatedQuadPlus 4 K e = 0)
    (he0 : e ≠ 0) (g : StatedOmega (StatedQuadPlus 4 K)) :
    g ∈ sec7SiegelGroup K e ↔ Sec7Siegel e g :=
  (sec7Siegel_iff he he0 g).symm

theorem isPGroup_sec7SiegelGroup [Finite K] [CharP K 2] {e : Fin 4 ⊕ Fin 4 → K}
    (he : StatedQuadPlus 4 K e = 0) (he0 : e ≠ 0) : IsPGroup 2 (sec7SiegelGroup K e) := by
  have hcard : Nat.card (sec7SiegelGroup K e) = Nat.card K ^ 6 := by
    rw [← sec7_card_siegel he he0]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_sec7SiegelGroup he he0 g)
  haveI := Fintype.ofFinite K
  obtain ⟨r, -, hr⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hr
  exact IsPGroup.of_card (n := r * 6) (by rw [hcard, hK, ← pow_mul])

end

section

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem sec7_smith_fix (hSmith : SmithOmegaPlusEightStatement)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Y : Type} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (ρ : Representation K (StatedOmega (StatedQuadPlus 4 K)) Y)
    (hirr : ∀ A : AddSubgroup Y, (∀ g y, y ∈ A → ρ g y ∈ A) → A = ⊥ ∨ A = ⊤)
    (hbig : 2 < Nat.card Y)
    {e : Fin 4 ⊕ Fin 4 → K} (he : StatedQuadPlus 4 K e = 0) (he0 : e ≠ 0)
    (D F : Submodule K Y)
    (hF : ∀ y, y ∈ F ↔ ∀ g, Sec7Siegel e g → ρ g y = y)
    (hD : ∀ g : StatedOmega (StatedQuadPlus 4 K),
      (∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = c • e) →
      ∀ y ∈ D, ρ g y ∈ D)
    (hFinv : ∀ g : StatedOmega (StatedQuadPlus 4 K),
      (∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = c • e) →
      ∀ y ∈ F, ρ g y ∈ F) :
    D = ⊥ ∨ F ≤ D := by
  have hnontriv := sec7_nontrivial_of_irred ρ hirr hbig
  by_cases hD0 : D = ⊥
  · exact Or.inl hD0
  refine Or.inr ?_
  let W : Submodule K Y := D ⊓ F
  have hW := hSmith K Y ρ hirr hnontriv e he0 he W
    (fun g hg y hy => (hF y).mp hy.2 g hg)
    (fun g hg y hy => ⟨hD g hg y hy.1, hFinv g hg y hy.2⟩)
  rcases hW with hW | hW
  · exfalso
    obtain ⟨y, hyD, hy0, hyfix⟩ := sec7_exists_fixed_of_two_group ρ (sec7SiegelGroup K e)
      (isPGroup_sec7SiegelGroup he he0) D hD0 (fun l hl y hy => hD l ⟨1, by
        have h1 := ((mem_sec7SiegelGroup he he0 l).mp hl).1
        rw [h1, one_smul]⟩ y hy)
    have hyF : y ∈ F := (hF y).mpr fun g hg => hyfix g ((mem_sec7SiegelGroup he he0 g).mpr hg)
    have hyW : y ∈ W := ⟨hyD, hyF⟩
    rw [hW] at hyW
    exact hy0 ((Submodule.mem_bot K).mp hyW)
  · intro y hy
    exact (hW y ((hF y).mp hy)).1

end

section

open CFSG.Open
open scoped Matrix

theorem sec7_omega_subquotient_rep {K : Type} {E H : Type*} [Field K] [AddCommGroup E]
    [Module K E]
    [Group H] (T : H →* Module.End K E) (P U : Submodule K E)
    (hP : ∀ h, ∀ p ∈ P, T h p ∈ P) (hU : ∀ h, ∀ p ∈ U, T h p ∈ U)
    (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hker : ∀ h ∈ φ.ker, ∀ p ∈ P, T h p - p ∈ U) :
    ∃ ρ' : Representation K (StatedOmega (StatedQuadPlus 4 K)) (↥P ⧸ U.submoduleOf P),
      ∀ (h : H) (g : StatedOmega (StatedQuadPlus 4 K)),
        (g : GL (Fin 4 ⊕ Fin 4) K) = φ h → ∀ p : ↥P,
          ρ' g (Submodule.Quotient.mk p) = Submodule.Quotient.mk ⟨T h p, hP h p p.2⟩ := by
  obtain ⟨ρR, hρR⟩ := sec7_subquotient_rep T P U hP hU
  have hmem : ∀ h, φ h ∈ StatedOmega (StatedQuadPlus 4 K) := fun h =>
    hφ ▸ MonoidHom.mem_range.mpr ⟨h, rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : H →* ↥(StatedOmega (StatedQuadPlus 4 K)),
      ∀ h, (φ' h : GL (Fin 4 ⊕ Fin 4) K) = φ h :=
    ⟨φ.codRestrict (StatedOmega (StatedQuadPlus 4 K)) hmem, fun h => rfl⟩
  have hsurj : Function.Surjective φ' := by
    intro g
    have hg : (g : GL (Fin 4 ⊕ Fin 4) K) ∈ φ.range := by
      rw [hφ]
      exact g.2
    obtain ⟨h, hh⟩ := hg
    exact ⟨h, Subtype.ext ((hφ' h).trans hh)⟩
  have hkerle : φ'.ker ≤ ρR.toHomUnits.ker := by
    intro h hh
    have hφh : h ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hh ⊢
      rw [← hφ' h, hh]
      rfl
    rw [MonoidHom.mem_ker]
    refine Units.ext (LinearMap.ext fun y => ?_)
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (U.submoduleOf P) y
    show ρR h (Submodule.Quotient.mk p) = Submodule.Quotient.mk p
    rw [hρR]
    exact (Submodule.Quotient.eq _).mpr (hker h hφh p p.2)
  obtain ⟨ρ'U, hρ'U⟩ : ∃ ρ'U : ↥(StatedOmega (StatedQuadPlus 4 K)) →*
      (Module.End K (↥P ⧸ U.submoduleOf P))ˣ, ∀ h, ρ'U (φ' h) = ρR.toHomUnits h :=
    ⟨MonoidHom.liftOfSurjective φ' hsurj ⟨ρR.toHomUnits, hkerle⟩, fun h =>
      MonoidHom.liftOfRightInverse_comp_apply φ' (Function.surjInv hsurj)
        (Function.rightInverse_surjInv hsurj) ⟨ρR.toHomUnits, hkerle⟩ h⟩
  refine ⟨(Units.coeHom _).comp ρ'U, fun h g hg p => ?_⟩
  have hgφ : g = φ' h := Subtype.ext (hg.trans (hφ' h).symm)
  rw [hgφ, MonoidHom.comp_apply, hρ'U, Units.coeHom_apply]
  exact hρR h p

end

end CFSG.RankThree.GF2n.Stroth80
