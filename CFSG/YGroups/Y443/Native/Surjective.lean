module

public import CFSG.YGroups.Y443.Native.AlignCgen
public import CFSG.YGroups.Y443.Native.Overgroup
public import CFSG.Monster.AxisCount.BabySetup
public import CFSG.YGroups.Y433.TwoCentral
public import CFSG.YGroups.Y443.Native.Bray
public import CFSG.YGroups.Y443.Native.Assembly
public import CFSG.Monster.B.Co2.KstabMaximal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.VisQuot CFSG.Monster.AxisCount
  CFSG.Open

@[expose] noncomputable def imgConj :
    Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  (fM.range.map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom

theorem conj_mem_imgConj
    (m : MonsterY443Derived) :
    wordLin omegaWord * ((fM m : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹ ∈
      imgConj :=
  ⟨_, ⟨fM m, ⟨m, rfl⟩, rfl⟩, rfl⟩

theorem imgConj_le_Gmat :
    imgConj ≤ Gmat := by
  rintro _ ⟨_, ⟨y, _, rfl⟩, rfl⟩
  exact mul_mem (mul_mem (wordLin_mem_Gmat _) y.2) (inv_mem (wordLin_mem_Gmat _))

theorem natCard_Cgen_eq_Q343N :
    Nat.card Cgen = Q343N := by
  rw [AxisCount.Baby.natCard_Cgen, AxisCount.natCard_Jstar, Q343N]
  norm_num

theorem natCard_map_conj {G : Type*} [Group G] (w : G) (S : Subgroup G) :
    Nat.card (S.map (MulAut.conj w).toMonoidHom) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj w).injective

theorem Cgen_le_imgConj
    (hN : Q343N ≤ Nat.card (y443H.map fM)) : Cgen ≤ imgConj := by
  have hcard : Nat.card (((y443H.map fM).map Gmat.subtype).map
      (MulAut.conj (wordLin omegaWord)).toMonoidHom) = Nat.card (y443H.map fM) := by
    rw [natCard_map_conj, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hG : Finite Gmat := finite_Gmat
  have hfin : Finite Cgen :=
    Finite.of_injective (Subgroup.inclusion Cgen_le_Gmat) (Subgroup.inclusion_injective _)
  have heq := Subgroup.eq_of_le_of_card_ge Hbar_conj_le_Cgen
    (by rw [natCard_Cgen_eq_Q343N, hcard]; exact hN)
  rw [← heq]
  rintro _ ⟨_, ⟨_, ⟨h, _, rfl⟩, rfl⟩, rfl⟩
  exact conj_mem_imgConj h

theorem fM_surjective_of_imgConj
    (h : imgConj = Gmat) : Function.Surjective fM := by
  intro y
  have hy : wordLin omegaWord * (y : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹ ∈ imgConj := by
    rw [h]
    exact mul_mem (mul_mem (wordLin_mem_Gmat _) y.2) (inv_mem (wordLin_mem_Gmat _))
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, hm⟩ := hy
  refine ⟨m, Subtype.ext ?_⟩
  simpa [MulAut.conj_apply] using hm

theorem fM_surjective_of
    (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hmax : ∀ X : Subgroup OLq, Kstab (classOf (vMinus 0 1)) ≤ X →
      X = Kstab (classOf (vMinus 0 1)) ∨ X = ⊤)
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hgK : g ∈ imgConj) (hgx : g * xmat = xmat * g)
    (hg1 : g * tStar * g⁻¹ ≠ tStar) (hg2 : g * tStar * g⁻¹ ≠ xmat * tStar) :
    Function.Surjective fM :=
  fM_surjective_of_imgConj
    (eq_Gmat_of_Cgen_le imgConj_le_Gmat (Cgen_le_imgConj hN) hmax hgK hgx hg1 hg2)

theorem fM_surjective_of_order
    (hN : Q343N ≤ Nat.card (y443H.map fM)) :
    Function.Surjective fM := by
  obtain ⟨g, hgK, hgx, hg1, hg2⟩ := bray_element_image (Cgen_le_imgConj hN)
  exact fM_surjective_of hN Co2.Kstab_v0_eq_or_eq_top hgK hgx hg1 hg2

theorem fam_m_simplicity_of_order
    (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hinj : Set.InjOn fM y443H) (hxL : fM y443X ∉ y443H.map fM)
    (hedge : ∀ h ∈ y443H.map fM, fM y443X * h * fM y443X ∈ y443H.map fM →
      ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ fM k = h)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (y443H.map fM)))
      (p : (rcGraph (y443H.map fM) (fM y443X)).Walk v v),
      MarkedHomotopic (yTri (y443H.map fM) (fM y443X) (fM y443Y)) p SimpleGraph.Walk.nil) :
    IsSimpleGroup MonsterY443Derived :=
  fam_m_simplicity_of hinj hxL hedge htri (fM_surjective_of_order hN)

end CFSG.YGroups.Y443
