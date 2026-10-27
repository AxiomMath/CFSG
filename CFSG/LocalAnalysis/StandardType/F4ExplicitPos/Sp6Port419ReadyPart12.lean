module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart11

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

public section

public section
open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.TitsSimplicity CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KF4

public section
open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal CFSG.StandardType

public section
open CFSG.LieType.Universal CFSG.StandardType

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.GeometricRank
open Matrix CFSG.Open
variable {K L : Type} [Field K] [Field L]

theorem spMapHom_injective {n : ℕ} {φ : K →+* L} (hφ : Function.Injective φ) :
    Function.Injective (spMapHom (n := n) φ) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply hφ
  have h' : GeneralLinearGroup.map φ (g : GL (Fin n ⊕ Fin n) K) =
      GeneralLinearGroup.map φ (h : GL (Fin n ⊕ Fin n) K) := Subtype.ext_iff.mp hgh
  have h2 := congrArg (fun z : GL (Fin n ⊕ Fin n) L =>
    ((z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) i j)) h'
  rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.val_map_apply,
    Matrix.map_apply, Matrix.map_apply] at h2
  exact h2

theorem mem_statedSp_of_map_mem {n : ℕ} {φ : K →+* L} (hφ : Function.Injective φ)
    {g : GL (Fin n ⊕ Fin n) K}
    (h : GeneralLinearGroup.map φ g ∈ StatedSp n L) : g ∈ StatedSp n K := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff] at h ⊢
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map φ =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, apply_ite φ]
  have hmap : ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).map φ =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map φ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ]
    simpa only [Matrix.GeneralLinearGroup.val_map_apply] using h
  exact Matrix.map_injective hφ hmap

theorem mem_range_spMapHom_of_entries {n : ℕ} {φ : K →+* L} (hφ : Function.Injective φ)
    {g : StatedSp n L}
    (hM : ∀ i j, (((g : StatedSp n L) : GL (Fin n ⊕ Fin n) L) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) i j ∈ Set.range φ)
    (hMi : ∀ i j, ((((g⁻¹ : StatedSp n L)) : GL (Fin n ⊕ Fin n) L) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) i j ∈ Set.range φ) :
    g ∈ (spMapHom (n := n) φ).range := by
  classical
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fun i j => Classical.choose (hM i j)
  let N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fun i j => Classical.choose (hMi i j)
  have hMmap : M.map φ = (((g : StatedSp n L) : GL (Fin n ⊕ Fin n) L) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) := by
    ext i j
    rw [Matrix.map_apply]
    exact Classical.choose_spec (hM i j)
  have hNmap : N.map φ = ((((g⁻¹ : StatedSp n L)) : GL (Fin n ⊕ Fin n) L) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) := by
    ext i j
    rw [Matrix.map_apply]
    exact Classical.choose_spec (hMi i j)
  have hMN : M * N = 1 := by
    apply Matrix.map_injective hφ
    change (M * N).map (⇑φ) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (⇑φ)
    rw [Matrix.map_mul, hMmap, hNmap, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    exact (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  have hNM : N * M = 1 := by
    apply Matrix.map_injective hφ
    change (N * M).map (⇑φ) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (⇑φ)
    rw [Matrix.map_mul, hNmap, hMmap, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
    exact (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  let h : GL (Fin n ⊕ Fin n) K := Units.mk M N hMN hNM
  have hval : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = M :=
    Units.val_mk M N hMN hNM
  have hmap : GeneralLinearGroup.map φ h = (g : GL (Fin n ⊕ Fin n) L) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_map_apply, hval, hMmap]
  have hmem : h ∈ StatedSp n K :=
    mem_statedSp_of_map_mem (n := n) hφ (by rw [hmap]; exact g.2)
  exact MonoidHom.mem_range.mpr ⟨⟨h, hmem⟩, Subtype.ext hmap⟩

theorem card_le_sq_of_isElemAbelian_statedSp_two
    {F Ω : Type} [Field F] [Finite F] [CharP F 2] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (StatedSp 2 Ω)) [Finite E] (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : CharP Ω 2 :=
    charP_of_injective_ringHom (f := algebraMap F Ω) (algebraMap F Ω).injective 2
  let : Fintype E := Fintype.ofFinite E
  let entry (X : E) : Finset Ω :=
    Finset.univ.image fun ij : (Fin 2 ⊕ Fin 2) × (Fin 2 ⊕ Fin 2) =>
      (((X : StatedSp 2 Ω) : GL (Fin 2 ⊕ Fin 2) Ω) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Ω) ij.1 ij.2
  let S : Finset Ω := Finset.univ.biUnion fun X : E => entry X ∪ entry X⁻¹
  obtain ⟨F', hF'fin, hSF', -⟩ :=
    CFSG.LieType.Chevalley.exists_finite_subfield_of_finset (K := F) (L := Ω) S
  have : Finite F' := hF'fin
  have hmemX (X : E) (i j : Fin 2 ⊕ Fin 2) :
      (((X : StatedSp 2 Ω) : GL (Fin 2 ⊕ Fin 2) Ω) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Ω) i j ∈ F' := by
    apply hSF'
    exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_univ X,
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩
  have hmemXi (X : E) (i j : Fin 2 ⊕ Fin 2) :
      ((((X⁻¹ : E) : StatedSp 2 Ω) : GL (Fin 2 ⊕ Fin 2) Ω) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Ω) i j ∈ F' := by
    apply hSF'
    exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_univ X,
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩
  have hrange : E ≤ (spMapHom (n := 2) F'.subtype).range := by
    intro g hg
    exact mem_range_spMapHom_of_entries (n := 2) F'.subtype_injective
      (fun i j => ⟨⟨_, hmemX ⟨g, hg⟩ i j⟩, rfl⟩)
      (fun i j => ⟨⟨_, hmemXi ⟨g, hg⟩ i j⟩, rfl⟩)
  have hE' : CFSG.Open.IsElemAbelian p (E.comap (spMapHom (n := 2) F'.subtype)) :=
    hE.comap (spMapHom_injective (n := 2) F'.subtype_injective)
  have hcard : Nat.card (E.comap (spMapHom (n := 2) F'.subtype)) = Nat.card E := by
    have h1 := Subgroup.card_map_of_injective
      (K := E.comap (spMapHom (n := 2) F'.subtype))
      (f := spMapHom (n := 2) F'.subtype)
      (spMapHom_injective (n := 2) F'.subtype_injective)
    have h2 : (E.comap (spMapHom (n := 2) F'.subtype)).map
        (spMapHom (n := 2) F'.subtype) = E :=
      Subgroup.map_comap_eq_self hrange
    rw [← h1, h2]
  have hpF' : (p : F') ≠ 0 := by
    intro h0
    have hpΩ : (p : Ω) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (R := Ω) (p := 2) hp (Ne.symm hp2)
    apply hpΩ
    rw [← map_natCast F'.subtype p, h0, map_zero]
  have hbound : Nat.card (E.comap (spMapHom (n := 2) F'.subtype)) ≤ p ^ 2 :=
    CFSG.StandardType.SpJoin.card_le_pow_of_isElemAbelian
      (F := F') hp hp2 hpF' (E.comap (spMapHom (n := 2) F'.subtype)) hE'
  rw [← hcard]
  exact hbound

end CFSG.StandardType.F4ExplicitPos.GeometricRank

public section

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

open CFSG.StandardType.F4ExplicitPos.CubicAction

open CFSG.StandardType.F4ExplicitPos.Neighbors

namespace CFSG.StandardType.F4ExplicitPos.CubicLiteral

variable {X : Type} [Group X] [Finite X]

variable {n f : ℕ} {p : ℕ}

variable {G₀ B₁ D J L : Subgroup X} {x : X}

theorem cubic_action_neighbor
    {ψ : (ggU .F4 n f).K →* X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J) :
    IsElemAbelian p (conjAction (f4_neighbor_normalized_by_B1 hH he hKG hKcomp hJK)).range ∧
      p ^ 3 ≤ Nat.card (conjAction (f4_neighbor_normalized_by_B1 hH he hKG hKcomp hJK)).range ∧
      (∀ (b : B₁) (y : ↥K),
        ((conjAction (f4_neighbor_normalized_by_B1 hH he hKG hKcomp hJK) b y : ↥K) : X)
          = (b : X) * (y : X) * (b : X)⁻¹) ∧
      p ^ 3 ∣ Nat.card (MulAut ↥K) := by
  have hH' := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hBN := f4_neighbor_normalized_by_B1 hH he hKG hKcomp hJK
  have hDnc := f4_neighbor_not_centralized_by_D hH he hKG hKcomp hJK hKne
  have hα := cubic_action_image (B := B₁) (D := D) (J := J) (K := K)
    h5 h6 h9 h10 h12 h14.symm hJK hBN hDnc
  exact ⟨hα.1, hα.2.1, hα.2.2,
    cubic_dvd_card_mulAut (B := B₁) (D := D) (J := J) (K := K)
      h5 h6 h9 h10 h12 h14.symm hJK hBN hDnc⟩

end CFSG.StandardType.F4ExplicitPos.CubicLiteral

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end
end
end
end
end

end
