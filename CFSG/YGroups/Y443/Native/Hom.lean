
module

public import CFSG.YGroups.Y443.Native.HomBase

public import CFSG.YGroups.Y443.Perfect
public import CFSG.YGroups.Y443.Native.CandidateData
public import CFSG.YGroups.Y443.Native.OrderRel
public import CFSG.YGroups.Y443.Native.PairRelA
public import CFSG.YGroups.Y443.Native.PairRelB
public import CFSG.YGroups.Y443.Native.PairRelC
public import CFSG.YGroups.Y443.Native.PairRelD
public import CFSG.YGroups.Y443.Native.SpiderRel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Open

theorem pairRel_all
    {k l : ℕ} (hkl : k < l) (hl : l < 11) :
    (M k * M l ^ (ordI l - 1)) ^ mI k l = 1 := by
  have hk : k < 10 := by omega
  interval_cases k
  · exact pairA_rel (by simp) hkl hl
  · exact pairA_rel (by simp) hkl hl
  · exact pairB_rel (by simp) hkl hl
  · exact pairC_rel (by simp) hkl hl
  · exact pairC_rel (by simp) hkl hl
  · exact pairD_rel (by simp) hkl hl
  · exact pairD_rel (by simp) hkl hl
  · exact pairD_rel (by simp) hkl hl
  · exact pairD_rel (by simp) hkl hl
  · exact pairD_rel (by simp) hkl hl

theorem M_inv
    {k : ℕ} (hk : k < 11) : (M k)⁻¹ = M k ^ (ordI k - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (ordI_pos k)]
  exact M_pow_ord hk

theorem M_inv_eq_wordLin
    {k : ℕ} (hk : k < 11) : (M k)⁻¹ = wordLin (invW k) := by
  rw [M_inv hk, invW, wordLin_powL]
  rfl

theorem rel_core
    (s t : MonsterY443Gen) (hlt : e443Lt s t) (m : ℕ)
    (hm : (MonsterY443Adj s t → m = 3) ∧ (¬ MonsterY443Adj s t → m = 2)) :
    ((e443Ext fGen s)⁻¹ * e443Ext fGen t) ^ m = 1 := by
  rcases s with _ | g
  · rcases t with _ | g'
    · exact hlt.elim
    · have hm' : m = ordI (wIdx g') := by
        by_cases h0 : g'.2.val = 0
        · rw [ordI_of_zero g' h0]
          exact hm.1 h0
        · rw [ordI_of_ne_zero g' h0]
          exact hm.2 h0
      subst hm'
      apply Subtype.ext
      show (((1 : Gmat)⁻¹ * fGen g') ^ ordI (wIdx g') : Gmat).1 = 1
      rw [inv_one, one_mul, Subgroup.coe_pow, coe_fGen, inv_pow, M_pow_ord (wIdx_lt g'), inv_one]
  · rcases t with _ | g'
    · exact hlt.elim
    · have hl := wIdx_lt g'
      have hm' : m = mI (wIdx g) (wIdx g') := by
        by_cases ha : MonsterY443Adj (some g) (some g')
        · rw [mI_of_adj g g' hlt ha]
          exact hm.1 ha
        · rw [mI_of_nadj g g' hlt ha]
          exact hm.2 ha
      subst hm'
      apply Subtype.ext
      show ((((fGen g)⁻¹ * fGen g') ^ mI (wIdx g) (wIdx g') : Gmat)).1 = 1
      rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, coe_fGen, coe_fGen, inv_inv,
        M_inv hl]
      exact pairRel_all (wIdx_lt_of_lt g g' hlt) hl

theorem spider_core :
    (FreeGroup.lift fGen e443R * FreeGroup.lift fGen e443RSharp) ^ 5 = 1 := by
  apply Subtype.ext
  have hprod : ((FreeGroup.lift fGen e443R * FreeGroup.lift fGen e443RSharp : Gmat) :
      SpaceB ≃ₗ[ℚ] SpaceB) = (spiderFactors.map wordLin).prod := by
    rw [Subgroup.coe_mul, e443_lift_R, e443_lift_RSharp]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fGen, inv_inv]
    simp only [spiderFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    show ((M 0)⁻¹ * M 1 * M 4 * (M 5)⁻¹ * (M 8)⁻¹ * M 9) *
        (M 0 * (M 1)⁻¹ * (M 4)⁻¹ * M 5 * M 8 * (M 9)⁻¹) = _
    rw [M_inv_eq_wordLin (k := 0) (by norm_num), M_inv_eq_wordLin (k := 1) (by norm_num),
      M_inv_eq_wordLin (k := 4) (by norm_num), M_inv_eq_wordLin (k := 5) (by norm_num),
      M_inv_eq_wordLin (k := 8) (by norm_num), M_inv_eq_wordLin (k := 9) (by norm_num)]
    simp only [M, mul_assoc]
  rw [Subgroup.coe_pow, hprod]
  exact spider_rel

theorem hadj' :
    ∀ s t : MonsterY443Gen, e443Lt s t → MonsterY443Adj s t →
    ((e443Ext fGen s)⁻¹ * e443Ext fGen t) ^ 3 = 1 :=
  fun s t h a => rel_core s t h 3 ⟨fun _ => rfl, fun h' => absurd a h'⟩

theorem hnadj' :
    ∀ s t : MonsterY443Gen, e443Lt s t → ¬ MonsterY443Adj s t →
    ((e443Ext fGen s)⁻¹ * e443Ext fGen t) ^ 2 = 1 :=
  fun s t h n => rel_core s t h 2 ⟨fun a => absurd a n, fun _ => rfl⟩

@[expose] noncomputable def f443Inv :
    E443 →* Gmat :=
  e443Lift fGen hadj' hnadj' spider_core

theorem f443Inv_of
    (g : E443Gen) : f443Inv (PresentedGroup.of g) = (gGen g)⁻¹ :=
  e443Lift_of fGen g

@[expose] noncomputable def f443 :
    E443 →* Gmat := f443Inv.comp e443AlphaHom

theorem f443_of
    (g : E443Gen) : f443 (PresentedGroup.of g) = gGen g := by
  rw [f443, MonoidHom.comp_apply, e443AlphaHom_of, map_inv, f443Inv_of, inv_inv]

theorem f443_unique
    {f : E443 →* Gmat} (hf : ∀ g : E443Gen, f (PresentedGroup.of g) = gGen g) :
    f = f443 :=
  PresentedGroup.ext fun g => (hf g).trans (f443_of g).symm

@[expose] noncomputable def f443Op :
    E443 →* Gmatᵐᵒᵖ :=
  (MulEquiv.inv' Gmat).toMonoidHom.comp f443Inv

theorem f443Op_of
    (g : E443Gen) : f443Op (PresentedGroup.of g) = MulOpposite.op (gGen g) := by
  show MulOpposite.op ((f443Inv (PresentedGroup.of g))⁻¹) = _
  rw [f443Inv_of, inv_inv]

theorem f443_range :
    f443.range = Subgroup.closure (Set.range gGen) := by
  have h : (⇑f443 ∘ (PresentedGroup.of : E443Gen → E443)) = gGen := funext f443_of
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (rels := e443Rels),
    MonoidHom.map_closure, ← Set.range_comp, h]

theorem f443_b1 :
    f443 (PresentedGroup.of y443U11) = ⟨tauB, tauB_mem_Gmat⟩ := by
  rw [f443_of]
  apply Subtype.ext
  rw [coe_gGen]
  exact M_zero

theorem f443_ne_one :
    f443 ≠ 1 := by
  intro h
  have h1 := f443_b1
  rw [h, MonoidHom.one_apply] at h1
  exact tauB_ne_one (congrArg Subtype.val h1).symm

theorem y443_native_even_presentation_homomorphism :
    (∃! f : E443 →* Gmat, ∀ g : E443Gen, f (PresentedGroup.of g) = gGen g) ∧
      ∀ f : E443 →* Gmat, (∀ g : E443Gen, f (PresentedGroup.of g) = gGen g) →
        f (PresentedGroup.of y443U11) = ⟨tauB, tauB_mem_Gmat⟩ ∧ f ≠ 1 ∧
          f.range = Subgroup.closure (Set.range gGen) := by
  refine ⟨⟨f443, f443_of, fun _ h => f443_unique h⟩, fun f hf => ?_⟩
  rw [f443_unique hf]
  exact ⟨f443_b1, f443_ne_one, f443_range⟩

@[expose] noncomputable def fM :
    MonsterY443Derived →* Gmat :=
  f443.comp e443Phi.symm.toMonoidHom

theorem fM_phi
    (g : E443Gen) : fM (e443Phi (PresentedGroup.of g)) = gGen g := by
  simp [fM, f443_of]

theorem fM_ax
    (g : E443Gen) : fM (axElt g) = gGen g := by
  rw [axElt_eq, fM_phi]

theorem fM_isFM :
    IsFM fM := fM_ax

theorem fM_unique
    {f : MonsterY443Derived →* Gmat}
    (hf : ∀ g : E443Gen, f (e443Phi (PresentedGroup.of g)) = gGen g) : f = fM := by
  have h : f.comp e443Phi.toMonoidHom = fM.comp e443Phi.toMonoidHom :=
    PresentedGroup.ext fun g => (hf g).trans (fM_phi g).symm
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := e443Phi.surjective y
  exact DFunLike.congr_fun h x

theorem fM_unique_ax
    {f : MonsterY443Derived →* Gmat} (hf : IsFM f) : f = fM :=
  fM_unique fun g => by rw [← axElt_eq]; exact hf g

@[expose] noncomputable def fMOp :
    MonsterY443Derived →* Gmatᵐᵒᵖ :=
  f443Op.comp e443Phi.symm.toMonoidHom

theorem fMOp_phi
    (g : E443Gen) :
    fMOp (e443Phi (PresentedGroup.of g)) = MulOpposite.op (gGen g) := by
  simp [fMOp, f443Op_of]

theorem fM_range :
    fM.range = Subgroup.closure (Set.range gGen) := by
  rw [← f443_range]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e443Phi.symm x, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨e443Phi u, by simp [fM]⟩

theorem fM_axElt_b1 :
    fM (axElt y443U11) = ⟨tauB, tauB_mem_Gmat⟩ := by
  rw [fM_ax]
  apply Subtype.ext
  rw [coe_gGen]
  exact M_zero

theorem orderOf_fM_b1 :
    orderOf (fM (axElt y443U11)) = 3 := by
  rw [fM_axElt_b1, Subgroup.orderOf_mk]
  exact orderOf_tauB

theorem fM_ne_one :
    fM ≠ 1 := by
  intro h
  have h1 := fM_axElt_b1
  rw [h, MonoidHom.one_apply] at h1
  exact tauB_ne_one (congrArg Subtype.val h1).symm

theorem fM_range_nontrivial :
    Nontrivial fM.range := by
  refine ⟨⟨1, ⟨fM (axElt y443U11), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩, fun h => ?_⟩⟩
  have h1 : (1 : Gmat) = fM (axElt y443U11) := congrArg Subtype.val h
  rw [fM_axElt_b1] at h1
  exact tauB_ne_one (congrArg Subtype.val h1).symm

theorem fM_range_perfect :
    Group.IsPerfect fM.range :=
  haveI := y443_derived_isPerfect
  Group.IsPerfect.range fM

theorem fM_ker_ne_top :
    fM.ker ≠ ⊤ := by
  intro h
  exact fM_ne_one (MonoidHom.ext fun x => MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))

theorem fM_ker_normal :
    fM.ker.Normal := inferInstance

theorem y443_derived_nontrivial_image :
    (∃! f : MonsterY443Derived →* Gmat, IsFM f) ∧
      ∀ f : MonsterY443Derived →* Gmat, IsFM f →
        f (axElt y443U11) = ⟨tauB, tauB_mem_Gmat⟩ ∧ orderOf (f (axElt y443U11)) = 3 ∧
          f ≠ 1 ∧ Nontrivial f.range ∧ Group.IsPerfect f.range ∧ f.ker ≠ ⊤ ∧ f.ker.Normal := by
  refine ⟨⟨fM, fM_isFM, fun _ h => fM_unique_ax h⟩, fun f hf => ?_⟩
  rw [fM_unique_ax hf]
  exact ⟨fM_axElt_b1, orderOf_fM_b1, fM_ne_one, fM_range_nontrivial, fM_range_perfect,
    fM_ker_ne_top, fM_ker_normal⟩

end CFSG.YGroups.Y443
