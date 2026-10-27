module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {M : Type} [Group M] {φ : ↥L →* M}

theorem wcgapt_barPre_mono {A B : Subgroup M} (hAB : A ≤ B) :
    barPre L φ A ≤ barPre L φ B := by
  intro g hg
  obtain ⟨hgL, hgA⟩ := mem_barPre.mp hg
  exact mem_barPre.mpr ⟨hgL, hAB hgA⟩

theorem wcgapt_barSub_mono {A B : Subgroup Y} (hAB : A ≤ B) :
    barSub L φ A ≤ barSub L φ B := by
  change (A.subgroupOf L).map φ ≤ (B.subgroupOf L).map φ
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hAB)

theorem wcgapt_barSub_inf (hφinj : Function.Injective φ) (A B : Subgroup Y) :
    barSub L φ (A ⊓ B) = barSub L φ A ⊓ barSub L φ B := by
  change ((A ⊓ B).comap L.subtype).map φ =
    (A.comap L.subtype).map φ ⊓ (B.comap L.subtype).map φ
  rw [Subgroup.comap_inf, Subgroup.map_inf_eq _ _ _ hφinj]

theorem wcgapt_relIndex_barPre' {C : Subgroup Y} (hφ : IsBarMap L C φ)
    (A B : Subgroup M) :
    (barPre L φ A).relIndex (barPre L φ B) = A.relIndex B := by
  simp only [barPre]
  rw [Subgroup.relIndex_map_map_of_injective (f := L.subtype) (A.comap φ) (B.comap φ)
      L.subtype_injective,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hφ.surjective B]

theorem wcgapt_relIndex_barPre {C : Subgroup Y} (hφ : IsBarMap L C φ)
    {Pb : Subgroup M} {X : Subgroup Y} (hCX : C ≤ X) (hX : X ≤ barPre L φ Pb) :
    X.relIndex (barPre L φ Pb) = (barSub L φ X).relIndex Pb := by
  have hsub : (barPre L φ Pb).subgroupOf L = Pb.comap φ := by
    change ((Pb.comap φ).map L.subtype).comap L.subtype = Pb.comap φ
    rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hA : X.subgroupOf L = (barSub L φ X).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_barSub]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hyX, hyφ⟩
      have hker : (x * y⁻¹) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyφ]
        group
      have hC : ((x : Y)) * ((y : Y))⁻¹ ∈ C := by
        have h' := (hφ.ker_iff (x * y⁻¹)).mp hker
        simpa using h'
      have hx' : (x : Y) = ((x : Y) * (y : Y)⁻¹) * (y : Y) := by group
      rw [hx']
      exact X.mul_mem (hCX hC) hyX
  rw [← Subgroup.relIndex_subgroupOf (barPre_le L φ Pb)]
  rw [hA, hsub, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective hφ.surjective Pb]

end CFSG.LocalAnalysis.WeakClosure81

end
