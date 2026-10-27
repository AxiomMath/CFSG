module

public import CFSG.ClassicalGroups.Symplectic.PSp45.Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentU2Five
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Matrix Subgroup CFSG.Open CFSG.ClassicalGroups.Symplectic.PSp45
open CFSG.ComponentClassification.CatFactsSp4 CFSG.LocalAnalysis.ComponentInitial

theorem genMat_six_eq : genMat 6 = kron 1 J₁ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> rfl

theorem genMat_five_eq : genMat 5 = fromBlocks (diag2 1 2) 0 0 (diag2 1 3) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> rfl

theorem psp45Gen_six_eq : psp45Gen 6 = T2 (ZMod 5) :=
  sp_ext genMat_six_eq

theorem psp45Gen_five_sq_eq : psp45Gen 5 ^ 2 = T1 (ZMod 5) := by
  apply sp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul]
  change genMat 5 * genMat 5 = blk 1 (-1)
  rw [genMat_five_eq, fromBlocks_multiply, diag2_mul, diag2_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, blk]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> rfl

theorem psp45GenP_six_eq : psp45GenP 6 = u2 (ZMod 5) := by
  rw [psp45GenP, psp45Gen_six_eq]
  rfl

theorem psp45GenP_five_sq_eq : psp45GenP 5 ^ 2 = u1 (ZMod 5) := by
  rw [psp45GenP, ← QuotientGroup.mk_pow, psp45Gen_five_sq_eq]
  rfl

variable {G : Type*} [Group G] {G₀ : Subgroup G}

theorem exists_conj_of_mulEquiv (ψ : G₀ ≃* StatedProj (StatedSp 2 (ZMod 5))) {t u : G}
    (ht : t ∈ G₀) (hu : u ∈ G₀) (hψt : ψ ⟨t, ht⟩ = u1 (ZMod 5)) (hψu : ψ ⟨u, hu⟩ = u2 (ZMod 5))
    {a : G} (ha : a ∈ G₀) (ha2 : orderOf a = 2) :
    (∃ g ∈ G₀, g⁻¹ * t * g = a) ∨ ∃ g ∈ G₀, g⁻¹ * u * g = a := by
  have hodd : Odd (Nat.card (ZMod 5)) := by
    rw [Nat.card_zmod]
    decide
  have hord : orderOf (ψ ⟨a, ha⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ha2]
  have key : ∀ {s : G} (hs : s ∈ G₀) (h : StatedProj (StatedSp 2 (ZMod 5))),
      h⁻¹ * ψ ⟨a, ha⟩ * h = ψ ⟨s, hs⟩ → ∃ g ∈ G₀, g⁻¹ * s * g = a := by
    intro s hs h hh
    refine ⟨((ψ.symm h)⁻¹ : G₀), ((ψ.symm h)⁻¹ : G₀).2, ?_⟩
    have h1 : (ψ.symm h)⁻¹ * ⟨a, ha⟩ * ψ.symm h = ⟨s, hs⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hh]
    have h2 : ((ψ.symm h)⁻¹)⁻¹ * ⟨s, hs⟩ * (ψ.symm h)⁻¹ = (⟨a, ha⟩ : G₀) := by
      rw [← h1]
      group
    simpa using congrArg Subtype.val h2
  obtain ⟨h, hh | hh⟩ := exists_conj_of_orderOf_eq_two hodd hord
  · exact Or.inl (key ht h (hh.trans hψt.symm))
  · exact Or.inr (key hu h (hh.trans hψu.symm))

theorem centralizer_conj_le {s : G} (hs : centralizer ({s} : Set G) ≤ G₀) {g : G}
    (hg : g ∈ G₀) : centralizer ({g⁻¹ * s * g} : Set G) ≤ G₀ := by
  intro x hx
  rw [mem_centralizer_singleton_iff] at hx
  have hx' : g * x * g⁻¹ ∈ centralizer ({s} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * s = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by rw [hx]
      _ = s * (g * x * g⁻¹) := by group
  have hmem : g⁻¹ * (g * x * g⁻¹) * g ∈ G₀ :=
    G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg) (hs hx')) hg
  convert hmem using 1
  group

theorem full_centralizers_of_u1_u2 [Finite G]
    (ψ : G₀ ≃* StatedProj (StatedSp 2 (ZMod 5))) {t u : G} (ht : t ∈ G₀) (hu : u ∈ G₀)
    (hψt : ψ ⟨t, ht⟩ = u1 (ZMod 5)) (hψu : ψ ⟨u, hu⟩ = u2 (ZMod 5))
    (hCt : centralizer ({t} : Set G) ≤ G₀) (hCu : Nat.card (centralizer ({u} : Set G)) ≤ 480) :
    centralizer ({u} : Set G) ≤ G₀ ∧
      (∀ a ∈ G₀, orderOf a = 2 → centralizer ({a} : Set G) ≤ G₀) ∧
      ∀ a ∈ G₀, orderOf a = 2 → (∃ g ∈ G₀, g⁻¹ * t * g = a) ∨ ∃ g ∈ G₀, g⁻¹ * u * g = a := by
  have h480 : 480 ≤ Nat.card (G₀ ⊓ centralizer ({u} : Set G) : Subgroup G) :=
    calc 480 ≤ Nat.card (centralizer ({u2 (ZMod 5)} : Set (StatedProj (StatedSp 2 (ZMod 5))))) :=
          le_card_centralizer_u2_zmod_five
      _ = Nat.card (centralizer ({ψ ⟨u, hu⟩} : Set (StatedProj (StatedSp 2 (ZMod 5))))) := by
          rw [hψu]
      _ = Nat.card (centralizer ({(⟨u, hu⟩ : G₀)} : Set G₀)) :=
          (GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv ψ _).symm
      _ = Nat.card (G₀ ⊓ centralizer ({u} : Set G) : Subgroup G) :=
          GH74.GLS.IVK.GHInv.card_centralizer_subtype G₀ ⟨u, hu⟩
  have hCu' : centralizer ({u} : Set G) ≤ G₀ := by
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_right : G₀ ⊓ centralizer ({u} : Set G) ≤ _) (hCu.trans h480)
    rw [← heq]
    exact inf_le_left
  refine ⟨hCu', fun a ha ha2 => ?_, fun a ha ha2 => exists_conj_of_mulEquiv ψ ht hu hψt hψu ha ha2⟩
  rcases exists_conj_of_mulEquiv ψ ht hu hψt hψu ha ha2 with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact centralizer_conj_le hCt hg
  · exact centralizer_conj_le hCu' hg

theorem model_involutions_and_full_centralizers [Finite G] (ψ : G₀ ≃* PSp45) {t u : G}
    (ht : t ∈ G₀) (hu : u ∈ G₀) (hψt : ψ ⟨t, ht⟩ = psp45GenP 5 ^ 2) (hψu : ψ ⟨u, hu⟩ = psp45GenP 6)
    (hCt : centralizer ({t} : Set G) ≤ G₀) (hCu : Nat.card (centralizer ({u} : Set G)) ≤ 480) :
    centralizer ({u} : Set G) ≤ G₀ ∧
      (∀ a ∈ G₀, orderOf a = 2 → centralizer ({a} : Set G) ≤ G₀) ∧
      ∀ a ∈ G₀, orderOf a = 2 → (∃ g ∈ G₀, g⁻¹ * t * g = a) ∨ ∃ g ∈ G₀, g⁻¹ * u * g = a :=
  full_centralizers_of_u1_u2 ψ ht hu (hψt.trans psp45GenP_five_sq_eq)
    (hψu.trans psp45GenP_six_eq) hCt hCu

end CFSG.OddTranspositions.PartThree.Wong
