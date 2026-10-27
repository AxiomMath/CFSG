module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard.OrthonormalBases
public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard.OrthogonalGroup

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

abbrev OrthonormalBasis5 : Type := {S : Finset (Fin 5 → ZMod 2) // IsOrthonormalBasis5 S}

theorem IsOrthonormalBasis5.image {B : GL (Fin 5) (ZMod 2)} (hB : IsOrthGL B)
    {S : Finset (Fin 5 → ZMod 2)} (hS : IsOrthonormalBasis5 S) :
    IsOrthonormalBasis5 (S.image fun x => (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) := by
  obtain ⟨hcard, hnorm, horth⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _
      (Matrix.mulVec_injective_of_isUnit (Units.isUnit B)), hcard]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [hB.dotProduct_mulVec_mulVec]
    exact hnorm y hy
  · intro x hx x' hx' hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hx'
    rw [hB.dotProduct_mulVec_mulVec]
    exact horth y hy y' hy' fun h => hne (congrArg _ h)

def orthBasisImage (B : {B : GL (Fin 5) (ZMod 2) // IsOrthGL B}) (S : OrthonormalBasis5) :
    OrthonormalBasis5 :=
  ⟨S.1.image fun x => (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x, S.2.image B.2⟩

theorem orthBasisImage_injective (B : {B : GL (Fin 5) (ZMod 2) // IsOrthGL B}) :
    Function.Injective (orthBasisImage B) := by
  intro S S' h
  exact Subtype.ext (Finset.image_injective
    (Matrix.mulVec_injective_of_isUnit (Units.isUnit B.1)) (congrArg Subtype.val h))

noncomputable def orthBasisPerm (B : {B : GL (Fin 5) (ZMod 2) // IsOrthGL B}) :
    Equiv.Perm OrthonormalBasis5 :=
  Equiv.ofBijective (orthBasisImage B) (orthBasisImage_injective B).bijective_of_finite

theorem orthBasisPerm_injective : Function.Injective orthBasisPerm := by
  intro B B' h
  have key : ∀ S : OrthonormalBasis5, orthBasisImage B S = orthBasisImage B' S :=
    fun S => Equiv.congr_fun h S
  have hcol : ∀ i : Fin 5, (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single i 1 =
      (B'.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single i 1 := by
    intro i
    have hE : stdBasis5.image (fun x => (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) =
        stdBasis5.image (fun x => (B'.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) :=
      congrArg Subtype.val (key ⟨stdBasis5, isOrthonormalBasis5_stdBasis5⟩)
    have hF : (otherBasis5 i).image (fun x => (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) =
        (otherBasis5 i).image (fun x => (B'.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) :=
      congrArg Subtype.val (key ⟨otherBasis5 i, isOrthonormalBasis5_otherBasis5 i⟩)
    have h1 : (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single i 1 ∈
        stdBasis5.image fun x => (B'.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x := by
      rw [← hE]
      exact Finset.mem_image_of_mem _ (single_mem_stdBasis5 i)
    have h2 : (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single i 1 ∈
        (otherBasis5 i).image fun x => (B'.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x := by
      rw [← hF]
      exact Finset.mem_image_of_mem _ (single_mem_otherBasis5 i)
    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp h1
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp h2
    have hxy : x = y :=
      Matrix.mulVec_injective_of_isUnit (Units.isUnit B'.1) (hxv.trans hyv.symm)
    rw [← hxv, stdBasis5_inter_otherBasis5 i hx (hxy ▸ hy)]
  exact Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single hcol))

theorem card_orthonormalBasis5_le : Nat.card OrthonormalBasis5 ≤ 6 := by
  have h := Nat.card_le_card_of_surjective
    (fun i : Fin 6 => (⟨bases5 i, isOrthonormalBasis5_bases5 i⟩ : OrthonormalBasis5))
    (fun S => by
      obtain ⟨i, hi⟩ := eq_basis_of_isOrthonormalBasis5 S.2
      exact ⟨i, Subtype.ext hi.symm⟩)
  simpa using h

theorem card_perm_orthonormalBasis5_le : Nat.card (Equiv.Perm OrthonormalBasis5) ≤ 720 := by
  rw [Nat.card_perm]
  calc (Nat.card OrthonormalBasis5).factorial ≤ (6 : ℕ).factorial :=
        Nat.factorial_le card_orthonormalBasis5_le
    _ = 720 := by decide

end CFSG.ASVolI.ChH
