module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClB1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {g : G}

theorem C33Core.swap_hyp (hc : C33Core M V g) :
    C33Hyp (conjSubgroup M g) (conjSubgroup V g) g⁻¹ where
  mQuot_le := by
    rw [conjSubgroup_conjSubgroup_inv, BOf_swap]
    have h : E3.mQuot V (UOf M V g) = E3.mQuot V (conjSubgroup M g) := by
      unfold E3.mQuot UOf
      rw [Subgroup.inf_relIndex_left]
    rw [h]
    exact hc.mQuot_U
  not_le := by
    rw [BOf_swap]
    exact hc.comm_ne

theorem c33_not_V_le_conjM (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    ¬ V ≤ conjSubgroup M g := by
  have hc := c33_core hgeo hS hh
  have h := (c33_core hgeo (hS.conj g) hc.swap_hyp).not_conjV_le_M
  rwa [conjSubgroup_conjSubgroup_inv] at h

theorem c33_shape (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    SingLineShape (autI hS.elemAbelian (BOf M V g)) := by
  have hV := hS.elemAbelian
  rcases c33_dichotomy hgeo hS hh with htop | hsh
  · exfalso
    apply c33_not_V_le_conjM hgeo hS hh
    have h := c33_gammaCheck_le hS hh.mQuot_le
    rw [htop] at h
    intro v hv
    exact mem_c33Pull.1 (h (Subgroup.mem_top (IntMod.mk hV ⟨v, hv⟩)))
  · exact hsh

theorem c33_centralizer_le (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    V ⊓ Subgroup.centralizer ((BOf M V g : Subgroup G) : Set G) ≤ conjSubgroup V g := by
  have hV := hS.elemAbelian
  have hBN : BOf M V g ≤ Subgroup.normalizer (V : Set G) := c33_BOf_le_normalizer hS
  have hshape := c33_shape hgeo hS hh
  have hNg : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer, hS.normalizer_eq]
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.1 hx
  have hw : IntMod.mk hV ⟨x, hxV⟩ ∈ fixV (autI hV (BOf M V g)) :=
    (mem_fixV_autI hV hBN _).2 hxC
  obtain ⟨e, he, u, hu, hwe⟩ := hshape.fix_le_comm _ hw
  obtain ⟨b, hbB, rfl⟩ := (mem_autI hV).1 he
  have hu1 : u.val ∈ conjSubgroup M g := c33_gammaCheck_le hS hh.mQuot_le hu
  have h1 := congrArg IntMod.val hwe
  rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv] at h1
  have hbV : (b : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hbB).1
  have huN : u.val ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by rw [hNg]; exact hu1
  have h2 : u.val * (b : G)⁻¹ * u.val⁻¹ ∈ conjSubgroup V g :=
    (Subgroup.mem_normalizer_iff.1 huN _).1 ((conjSubgroup V g).inv_mem hbV)
  have h3 : x = (b : G) * (u.val * (b : G)⁻¹ * u.val⁻¹) := by
    have h4 : x = (b : G) * u.val * (b : G)⁻¹ * u.val⁻¹ := h1.symm
    rw [h4]
    group
  rw [h3]
  exact (conjSubgroup V g).mul_mem hbV h2

theorem c33_mem_of_commutator_mem (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    ∀ b ∈ BOf M V g, b ∉ Subgroup.centralizer (V : Set G) → ∀ v ∈ V,
      ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g → v ∈ conjSubgroup M g := by
  have hV := hS.elemAbelian
  have hBN : BOf M V g ≤ Subgroup.normalizer (V : Set G) := c33_BOf_le_normalizer hS
  have hshape := c33_shape hgeo hS hh
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  intro b hb hbC v hv hcomm
  have hbN : b ∈ Subgroup.normalizer (V : Set G) := hBN hb
  have he : convI hV ⟨b, hbN⟩ ∈ autI hV (BOf M V g) := convI_mem_autI hV hb hbN
  have he1 : convI hV ⟨b, hbN⟩ ≠ 1 := fun h => hbC ((convI_eq_one_iff hV ⟨b, hbN⟩).1 h)
  have hfix : convI hV ⟨b, hbN⟩ (IntMod.mk hV ⟨v, hv⟩) * (IntMod.mk hV ⟨v, hv⟩)⁻¹ ∈
      fixV (autI hV (BOf M V g)) := by
    rw [mem_fixV_autI hV hBN, Subgroup.mem_centralizer_iff]
    intro x hx
    have hval : (convI hV ⟨b, hbN⟩ (IntMod.mk hV ⟨v, hv⟩) * (IntMod.mk hV ⟨v, hv⟩)⁻¹).val =
        (⁅v, b⁆)⁻¹ := by
      rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv]
      show b * v * b⁻¹ * v⁻¹ = _
      rw [commutatorElement_def]
      group
    rw [hval]
    exact CFSG.Open.IsElemAbelian.comm hVg (Subgroup.mem_inf.1 hx).1
      ((conjSubgroup V g).inv_mem (Subgroup.mem_inf.1 hcomm).2)
  exact c33_gammaCheck_le hS hh.mQuot_le (hshape.mem_of_comm _ he he1 _ hfix)

theorem c33_prim (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    C33Prim M V g :=
  have hc := c33_core hgeo hS hh
  { not_conjV_le_M := hc.not_conjV_le_M
    not_V_le_conjM := c33_not_V_le_conjM hgeo hS hh
    mQuot_U := hc.mQuot_U
    centralizer_le := c33_centralizer_le hgeo hS hh
    comm_ne := hc.comm_ne
    mem_of_commutator_mem := c33_mem_of_commutator_mem hgeo hS hh }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
