module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G]

theorem qTwoFrameL_fieldIso {L : Subgroup G} {m : ℕ}
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (_ : Fact (Nat.Prime 2)),
      Nat.card F0 = 4 ∧
        Nonempty (L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))) := by
  have h := hL.statedClassicalModel (by decide : .PSU ∈ classicalTags)
  dsimp only [StatedClassicalModel] at h
  obtain ⟨-, F0, hF0, hF0f, hF0c, ⟨e⟩⟩ := h
  have hUF := @TableBU.unitaryFieldData_of_card F0 hF0 1 hF0c (by norm_num : 1 ≤ 1)
  refine ⟨F0, hF0, hF0f, ?_, ⟨Nat.prime_two⟩, by rw [hF0c]; norm_num, ⟨e⟩⟩
  exact @CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.charP 2 1 F0 hF0 hUF

theorem qTwoFrameL_autInn {Bs L : Subgroup G} {m : ℕ} (hm : 5 ≤ m)
    {F0 : Type} [Field F0] [Finite F0] (hcard : Nat.card F0 = 4)
    (e : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ∀ b : ↥Bs, b ^ 3 = 1)
    (ρ : ↥Bs →* MulAut (L ⧸ Subgroup.center L))
    (_hρ : ∀ (b : ↥Bs) (l : ↥L),
      ρ b (QuotientGroup.mk l) =
        QuotientGroup.mk ⟨(b : G) * l * (b : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩) :
    ∀ b : ↥Bs, MulAut.congr e (ρ b) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))
        (LargeEvenGUSet (Fin m) F0 (2 ^ 1)) := by
  intro b
  have hφ : (MulAut.congr e (ρ b)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3 b, map_one, map_one]
  exact CorFourTwoOpen.mem_conjImage_of_pow_unitary (K := F0) (n := 1) (d := m) (p := 3)
    (by rw [hcard]; norm_num) le_rfl (by omega) (by rintro ⟨rfl, -⟩; omega)
    Nat.prime_three (by norm_num) (by norm_num) hφ

end CFSG.StandardType.QTwo
