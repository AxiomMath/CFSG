module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenDiag
public import CFSG.Quasithin.Background.E6TwentyA
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Hyperplanes
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

namespace SevenSevenB

@[expose] def normalizerInA (A K : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  A ⊓ Subgroup.normalizer (K : Set (MulAut W))

@[expose] def centralizerInA (A K : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  A ⊓ Subgroup.centralizer (K : Set (MulAut W))

@[expose] def centralizerProductD (A K D : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  centralizerInA A K ⊔ D

@[expose] noncomputable def fixVProduct (A K D : Subgroup (MulAut W)) : Subgroup W :=
  fixV (centralizerProductD A K D)

variable {Y K A D : Subgroup (MulAut W)} {k : ℕ}
variable [Fintype ↥D] [DecidableEq ↥D]

theorem le_y_of_le_a_77 {k : ℕ} (hA : A ∈ E3.aSet k Y) (hDA : D ≤ A) : D ≤ Y :=
  hDA.trans hA.1

theorem centralizerProductD_le_a_77 (hDA : D ≤ A) : centralizerProductD A K D ≤ A := by
  rw [centralizerProductD]
  exact sup_le inf_le_left hDA

theorem exists_compl_normalizerInA_77 {Y K A : Subgroup (MulAut W)} {k : ℕ}
    (hA : A ∈ E3.aSet k Y) :
    ∃ D : Subgroup (MulAut W), D ≤ A ∧ D ⊓ normalizerInA A K = ⊥ ∧
      normalizerInA A K ⊔ D = A := by
  have hB : normalizerInA A K ≤ A := inf_le_left
  have hV : IsElemAbelian 2 A := (CFSG.Quasithin.H.isElemAbelian2_iff).1 hA.2.2.1
  obtain ⟨D, hDA, hDB, hBD⟩ := CFSG.Quasithin.E6.exists_compl_of_le (V := A) hV hB
  exact ⟨D, hDA, by rwa [inf_comm], hBD⟩

theorem commute_centralizerInA_77 {k : ℕ} (hA : A ∈ E3.aSet k Y) (hDA : D ≤ A) :
    ∀ c ∈ centralizerInA A K, ∀ d ∈ D, c * d = d * c := by
  intro c hc d hd
  exact hA.2.2.1.1 c hc.1 d (hDA hd)

theorem stableUnder_fixVProduct_77 {k : ℕ} (hA : A ∈ E3.aSet k Y) (hDA : D ≤ A) :
    ∀ a ∈ A, ∀ u ∈ fixVProduct A K D, a u ∈ fixVProduct A K D := by
  have hAN : A ≤ Subgroup.normalizer (centralizerProductD A K D : Set (MulAut W)) :=
    (Subgroup.le_centralizer_iff.mpr fun e he => by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hA.2.2.1.1 e (centralizerProductD_le_a_77 hDA he) a ha).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  exact fun a ha u hu =>
    CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hAN ha) hu

theorem isPGroup_centralizerProductD_77 {k : ℕ} (hA : A ∈ E3.aSet k Y) (hDA : D ≤ A) :
    IsPGroup 2 ↥(centralizerProductD A K D) := by
  intro e
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show ((e : MulAut W) ^ (2 ^ 1)) = 1
  simpa using hA.2.2.1.2 (e : MulAut W) (centralizerProductD_le_a_77 hDA e.2)

theorem centralizerInA_le_centralizer_diag_77 (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hDY : D ≤ Y) (hDA : D ≤ A)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    centralizerInA A K ≤
      Subgroup.centralizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  have h := diagHom_conj_mem_centralizer hK hDY hDreg (c := c) hc.2
    (fun d hd => commute_centralizerInA_77 hA hDA c hc d hd) x
  rw [MulAut.conj_apply] at h
  have h1 : c * diagHom77 hK hDY hDreg x = diagHom77 hK hDY hDreg x * c := by
    calc c * diagHom77 hK hDY hDreg x
        = (c * diagHom77 hK hDY hDreg x * c⁻¹) * c := by group
      _ = diagHom77 hK hDY hDreg x * c := by rw [h]
  exact h1.symm

theorem D_le_centralizer_diag_77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    D ≤ Subgroup.centralizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  have h := diagHom_conj_mem_D hK hDY hDreg (e := d) hd x
  rw [MulAut.conj_apply] at h
  have h1 : d * diagHom77 hK hDY hDreg x = diagHom77 hK hDY hDreg x * d := by
    calc d * diagHom77 hK hDY hDreg x
        = (d * diagHom77 hK hDY hDreg x * d⁻¹) * d := by group
      _ = diagHom77 hK hDY hDreg x * d := by rw [h]
  exact h1.symm

theorem centralizerProductD_le_centralizer_diag_77 (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    centralizerProductD A K D ≤
      Subgroup.centralizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) :=
  sup_le (centralizerInA_le_centralizer_diag_77 hK hA hDY hDA hDreg)
    (D_le_centralizer_diag_77 hK hDY hDreg)

theorem diagHom_range_le_normalizer_centralizerProductD_77 (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (diagHom77 hK hDY hDreg).range ≤
      Subgroup.normalizer (centralizerProductD A K D : Set (MulAut W)) :=
  (Subgroup.le_centralizer_iff.mp
    (centralizerProductD_le_centralizer_diag_77 hK hA hDY hDA hDreg)).trans
    (Subgroup.centralizer_le_normalizer _)

theorem stableUnder_fixVProduct_diag_77 (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hDA : D ≤ A) (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    ∀ y ∈ (diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg).range,
      ∀ u ∈ fixVProduct A K D, y u ∈ fixVProduct A K D := by
  intro y hy u hu
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [fixVProduct, mem_fixV] at hu ⊢
  intro e he
  have he_comm : e * diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x =
      diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x * e :=
    (Subgroup.mem_centralizer_iff.mp
      (centralizerProductD_le_centralizer_diag_77 hK hA
        (le_y_of_le_a_77 hA hDA) hDA hDreg he)
      (diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x)
      (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).symm
  calc e (diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x u)
      = (e * diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x) u := rfl
    _ = (diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x * e) u := by rw [he_comm]
    _ = diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x (e u) := rfl
    _ = diagHom77 hK (le_y_of_le_a_77 hA hDA) hDreg x u := by rw [hu e he]

end SevenSevenB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
