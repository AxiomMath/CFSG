module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks
import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartThree.EightEight.FibreCentre
import CFSG.OddTranspositions.PartThree.EightEight.Kernel

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem exists_not_commute_of_not_le_center_w4s {X : Type} [Group X] {M : Subgroup X}
    (hMZ : ¬ M ≤ Subgroup.center X) : ∃ m ∈ M, ∃ h : X, m * h ≠ h * m := by
  by_contra hcon
  apply hMZ
  intro m hm
  rw [Subgroup.mem_center_iff]
  intro h
  by_contra hmh
  exact hcon ⟨m, hm, h, Ne.symm hmh⟩

theorem exists_ne_mem_Dalpha_mk_eq_of_not_le_center (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ QZ.O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha)) :
    ∃ β ∈ Dalpha D hC.alpha, ∃ β' ∈ Dalpha D hC.alpha, β ≠ β' ∧
      ∃ b b' : Halpha D hC.alpha, (b : G) ∈ β ∧ (b' : G) ∈ β' ∧
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b' := by
  classical
  obtain ⟨m, hmM, h, hne⟩ := exists_not_commute_of_not_le_center_w4s hMZ
  have hkH : (m : G) ∈ Halpha D hC.alpha := m.2
  have hrhs : ¬ ∀ k ∈ Halpha D hC.alpha, Commute (m : G) k := by
    intro hall
    exact hne (Subtype.ext (by simpa using (hall h h.2).eq))
  have hmove : ∃ β ∈ Dalpha D hC.alpha,
      (fun y => (m : G) * y * (m : G)⁻¹) '' β ≠ β := by
    by_contra hcon
    apply hrhs
    refine (forall_conj_image_eq_iff_commute h87 hC hrad hO4 hF hkH).mp ?_
    intro β hβ
    by_contra hne
    exact hcon ⟨β, hβ, hne⟩
  obtain ⟨β, hβ, hβne⟩ := hmove
  have hβ' : (fun y => (m : G) * y * (m : G)⁻¹) '' β ∈ Dalpha D hC.alpha :=
    smul_mem_Dalpha_of_mem_Halpha hC hkH hβ
  obtain ⟨bG, hbG⟩ :=
    nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty (mem_Dalpha_iff.mp hβ).1
  have hbH : bG ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hbG⟩
  have hb'H : (m : G) * bG * (m : G)⁻¹ ∈ Halpha D hC.alpha :=
    (Halpha D hC.alpha).mul_mem ((Halpha D hC.alpha).mul_mem m.2 hbH)
      ((Halpha D hC.alpha).inv_mem m.2)
  refine ⟨β, hβ, (fun y => (m : G) * y * (m : G)⁻¹) '' β, hβ', Ne.symm hβne,
    ⟨bG, hbH⟩, ⟨(m : G) * bG * (m : G)⁻¹, hb'H⟩, hbG, ⟨bG, hbG, rfl⟩, ?_⟩
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (m : Halpha D hC.alpha) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmM
  have hb'eq : (⟨(m : G) * bG * (m : G)⁻¹, hb'H⟩ : Halpha D hC.alpha) =
      (m : Halpha D hC.alpha) * ⟨bG, hbH⟩ * (m : Halpha D hC.alpha)⁻¹ := Subtype.ext rfl
  rw [hb'eq, map_mul, map_mul, map_inv, hmk]
  simp

omit [Finite G] in
theorem notMem_union_DalphaStar_of_mk_eq {ρ : Set G} (hρ : IsBlock D ρ)
    (hA : FibresAnticlique D ρ) {β β' : Set G} (hβ : β ∈ Dalpha D ρ) (hβ' : β' ∈ Dalpha D ρ)
    (hne : β ≠ β') {b b' : Halpha D ρ} (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b') :
    (b' : G) ∉ β ∪ DalphaStar D β := by
  intro hmem
  rw [Set.mem_union] at hmem
  have hβc : β ∈ blockClass ρ := (mem_Dalpha_iff.mp hβ).1
  have hβ'c : β' ∈ blockClass ρ := (mem_Dalpha_iff.mp hβ').1
  have hb'notβ : (b' : G) ∉ β := fun hmemβ =>
    hne (eq_of_mem_of_mem_blockClass hρ hβc hβ'c ⟨(b' : G), hmemβ, hb'⟩)
  rcases hmem with hb'β | hb'star
  · exact hb'notβ hb'β
  · have hcommG : Commute (b : G) (b' : G) := commute_of_mem_of_mem_DalphaStar hb hb'star
    have hb'S : (b' : G) ∈ DalphaStar D ρ := ⟨β', hβ', hb'⟩
    have hbS : (b : G) ∈ DalphaStar D ρ := ⟨β, hβ, hb⟩
    have hbne : b ≠ b' := fun hEq => hb'notβ (by rw [← hEq]; exact hb)
    exact (hA b b' hbS hb'S hbne hbb')
      (show b * b' = b' * b from Subtype.ext (by simpa using hcommG.eq))

end CFSG.OddTranspositions.PartThree.EightEight