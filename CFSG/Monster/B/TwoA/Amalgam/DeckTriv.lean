module

public import CFSG.Monster.B.TwoA.Amalgam.DeckPanels
public import CFSG.Monster.B.TwoA.Amalgam.DeckGallery
public import CFSG.Monster.B.TwoA.Amalgam.DeckIso
public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Cover

variable {X : ChamberSystem (Fin Tag.F4.rank) Chamber}

theorem mem_Qam_of_residue
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j)
    {i : Fin 4} {h : Eam} (hh : chamberOf h ∈ X.residue {i} (chamberOf 1)) :
    (h : Dfull) ∈ Qam i := by
  have h1 := (hres {i} 1 h).1 hh
  have hsup : (⨆ (j : Fin 4) (_ : j ∈ ({i} : Set (Fin Tag.F4.rank))), Qam j) = Qam i :=
    le_antisymm (iSup₂_le fun j hj => (Set.mem_singleton_iff.1 hj) ▸ le_rfl)
      (le_iSup₂_of_le i (Set.mem_singleton i) le_rfl)
  rw [hsup, sup_eq_right.2 (Bam_le_Qam i), inv_one, mul_one] at h1
  exact h1

theorem exists_smul_ne_of_cover_adj
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1)
    {P₁ P₄ : Subgroup (X.LiftPair (chamberOf 1))}
    {φ₁ : Pc 0 →* P₁} (hφ₁ : Function.Surjective φ₁)
    (hφ₁p : ∀ (g : Pc 0) (c : Chamber),
      ((X.liftProj (chamberOf 1) (φ₁ g : X.LiftPair (chamberOf 1)) : X.typeAut) :
        Equiv.Perm Chamber) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 0) g)⁻¹)
    {α₁ : P₁ →* SigmaU6} (hα₁ : ∀ g, α₁ (φ₁ g) = rhoP1 g)
    {φ₄ : P4 →* P₄} (hφ₄ : Function.Surjective φ₄)
    (hφ₄p : ∀ (g : P4) (c : Chamber),
      ((X.liftProj (chamberOf 1) (φ₄ g : X.LiftPair (chamberOf 1)) : X.typeAut) :
        Equiv.Perm Chamber) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g)⁻¹)
    {α₄ : P₄ →* OA8} (hα₄ : ∀ g, α₄ (φ₄ g) = p4Proj g)
    {T : Set (X.LiftPair (chamberOf 1))}
    (hTU : ∀ u ∈ psuSub ⊓ flagStabU, ∃ z : P₁, (z : X.LiftPair (chamberOf 1)) ∈ T ∧ α₁ z = u)
    (hTO : ∀ d ∈ orthD ⊓ flagStabO, ∃ z : P₄, (z : X.LiftPair (chamberOf 1)) ∈ T ∧ α₄ z = d)
    {i : Fin Tag.F4.rank} {y : X.Cover (chamberOf 1)}
    (hy : (X.universalCover (chamberOf 1)).adj i a y) (hya : y ≠ a) :
    ∃ t ∈ T, t • y ≠ y := by
  have hyR : y ∈ (X.universalCover (chamberOf 1)).residue {i} a :=
    ChamberSystem.mem_residue_singleton.2 hy
  have hbij := ChamberSystem.bijOn_coverProj_panel (X := X) (c₀ := chamberOf 1) i a
  have hπy : X.coverProj (chamberOf 1) y ∈ X.residue {i} (chamberOf 1) := by
    have h := hbij.mapsTo hyR
    rwa [ha] at h
  have hne : X.coverProj (chamberOf 1) y ≠ chamberOf 1 := fun e =>
    hya (hbij.injOn hyR (ChamberSystem.self_mem_residue _ _) (e.trans ha.symm))
  obtain ⟨h, hh⟩ := chamberOf_surjective (X.coverProj (chamberOf 1) y)
  have hQ : (h : Dfull) ∈ Qam (i : Fin 4) := mem_Qam_of_residue hres (hh ▸ hπy)
  have hB : (h : Dfull) ∉ Bam := fun hB => hne (hh.symm.trans (chamberOf_eq_iff.2 (by
    simp only [one_mul, Subgroup.coe_inv]
    exact Bam.inv_mem hB)))
  have hπ : ∀ (z : X.LiftPair (chamberOf 1)) (d : X.Cover (chamberOf 1)),
      X.coverProj (chamberOf 1) (z • d) =
        ((X.liftProj (chamberOf 1) z : X.typeAut) : Equiv.Perm Chamber)
          (X.coverProj (chamberOf 1) d) := fun z d => ChamberSystem.coverProj_smul z d
  by_cases hi : (i : ℕ) = 0
  · have e : (show Fin 4 from i) = 0 := Fin.ext hi
    have hQ0 : (h : Dfull) ∈ Qam 0 := by
      rw [← e]
      exact hQ
    exact exists_smul_ne_of_orth_panel hπ hφ₄ hφ₄p hα₄ hTO hh.symm hQ0 hB
  · exact exists_smul_ne_of_unitary_panel hπ hφ₁ hφ₁p hα₁ hTU (i := i)
      (fun e => hi (congrArg Fin.val e)) hh.symm hQ hB

theorem deck_trivial_of
    (hconn : X.Connected)
    {δ : X.Cover (chamberOf 1) → X.Cover (chamberOf 1) → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hadj : ∀ (i : Fin Tag.F4.rank) (A B : X.Cover (chamberOf 1)),
      (X.universalCover (chamberOf 1)).adj i A B ↔
        δ A B = 1 ∨ δ A B = (coxeterSystem .F4).simple i)
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j)
    {a : X.Cover (chamberOf 1)} (ha : X.coverProj (chamberOf 1) a = chamberOf 1)
    {P₁ P₄ : Subgroup (X.LiftPair (chamberOf 1))}
    {φ₁ : Pc 0 →* P₁} (hφ₁ : Function.Surjective φ₁)
    (hφ₁p : ∀ (g : Pc 0) (c : Chamber),
      ((X.liftProj (chamberOf 1) (φ₁ g : X.LiftPair (chamberOf 1)) : X.typeAut) :
        Equiv.Perm Chamber) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 0) g)⁻¹)
    {α₁ : P₁ →* SigmaU6} (hα₁ : ∀ g, α₁ (φ₁ g) = rhoP1 g)
    {φ₄ : P4 →* P₄} (hφ₄ : Function.Surjective φ₄)
    (hφ₄p : ∀ (g : P4) (c : Chamber),
      ((X.liftProj (chamberOf 1) (φ₄ g : X.LiftPair (chamberOf 1)) : X.typeAut) :
        Equiv.Perm Chamber) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g)⁻¹)
    {α₄ : P₄ →* OA8} (hα₄ : ∀ g, α₄ (φ₄ g) = p4Proj g)
    {T : Set (X.LiftPair (chamberOf 1))} (hTa : ∀ t ∈ T, t • a = a)
    (hTK : ∀ t ∈ T, ∀ k ∈ X.pi2 (chamberOf 1), k * t = t * k)
    (hTU : ∀ u ∈ psuSub ⊓ flagStabU, ∃ z : P₁, (z : X.LiftPair (chamberOf 1)) ∈ T ∧ α₁ z = u)
    (hTO : ∀ d ∈ orthD ⊓ flagStabO, ∃ z : P₄, (z : X.LiftPair (chamberOf 1)) ∈ T ∧ α₄ z = d) :
    X.pi2 (chamberOf 1) = ⊥ := by
  refine eq_bot_iff.2 fun k hk => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_commute_of_free hδ (T := T) (a := a)
    (fun t _ => typeAut_le_of_adj hδ hadj (ChamberSystem.liftPerm_mem_typeAut t)) hTa
    (fun i y hy => ?_) (fun t ht => hTK t ht k hk)
    (fun hka => ChamberSystem.eq_one_of_mem_ker_of_smul_eq hconn hk hka)
  obtain ⟨hadjy, hya⟩ := (eq_simple_iff_adj hδ hadj i a y).1 hy
  exact exists_smul_ne_of_cover_adj hres ha hφ₁ hφ₁p hα₁ hφ₄ hφ₄p hα₄ hTU hTO hadjy hya.symm

end Cover

end CFSG.Monster.B.TwoA.Amalgam
