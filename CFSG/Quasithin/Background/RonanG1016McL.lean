module

public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsTransvOn (J : Submodule (ZMod 2) V) (s : GLV V) : Prop :=
  ∃ h : conjSub s J = J, Module.finrank (ZMod 2) (LinearMap.range (commMap s J h)) = 1

section Restrict

variable {K : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

@[expose] noncomputable def restrictG (K : Subgroup (GLV V)) (J : Submodule (ZMod 2) V)
    (hK : Invariant K J) : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) ↥J) :=
  (restrictRange K J hK).map
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm.toMonoidHom

theorem mem_restrictG_iff (hK : Invariant K J) (t : LinearMap.GeneralLinearGroup (ZMod 2) ↥J) :
    t ∈ restrictG K J hK ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J t ∈ restrictRange K J hK := by
  rw [restrictG, Subgroup.mem_map_equiv]
  rfl

theorem id_add_eq_sub {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (f : M →ₗ[ZMod 2] M) :
    LinearMap.id + f = f - LinearMap.id := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.sub_apply]
  rw [add_comm, sub_eq_add_neg, CFSG.ComponentClassification.OutcomeLocal.zmod2_neg]

theorem coe_symm_generalLinearEquiv (g : ↥J ≃ₗ[ZMod 2] ↥J) (x : ↥J) :
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g :
      LinearMap.GeneralLinearGroup (ZMod 2) ↥J).val x = g x := by
  have h := LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv (R := ZMod 2) (M := ↥J)
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact (congrFun h x).symm

open CFSG.ComponentClassification.OutcomeLocal in
theorem restrictG_gen (hJ : IsIrr K J)
    (hgen : K ≤ Subgroup.closure {s | s ∈ K ∧ IsTransvOn J s}) :
    ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) ↥J),
      (∀ t ∈ S, IsF2Transvection t) ∧ restrictG K J hJ.1 = Subgroup.closure S := by
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J with he
  set S : Set (LinearMap.GeneralLinearGroup (ZMod 2) ↥J) :=
    {t | t ∈ restrictG K J hJ.1 ∧ IsF2Transvection t} with hS
  refine ⟨S, fun t ht => ht.2, le_antisymm ?_ ((Subgroup.closure_le (restrictG K J hJ.1)).2 fun t ht => ht.1)⟩
  set S₀ : Set (GLV V) := {s | s ∈ K ∧ IsTransvOn J s} with hS₀
  have hcl : Subgroup.closure S₀ ≤ K := (Subgroup.closure_le K).2 fun s hs => hs.1
  have key : ∀ k ∈ Subgroup.closure S₀, ∀ h : conjSub k J = J,
      e.symm (restrictEquiv k J h) ∈ Subgroup.closure S := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem s hs =>
      intro h
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [mem_restrictG_iff hJ.1, MulEquiv.apply_symm_apply]
        exact restrictEquiv_mem_restrictRange hJ.1 hs.1
      · obtain ⟨h', hfr⟩ := hs.2
        have hcs : commutatorSpace (e.symm (restrictEquiv s J h)) =
            LinearMap.range (commMap s J h') := by
          have hlin : ((e.symm (restrictEquiv s J h) : LinearMap.GeneralLinearGroup (ZMod 2) ↥J) :
              ↥J →ₗ[ZMod 2] ↥J) = (restrictEquiv s J h : ↥J →ₗ[ZMod 2] ↥J) :=
            LinearMap.ext fun x => coe_symm_generalLinearEquiv _ x
          rw [commutatorSpace, hlin, id_add_eq_sub]
          rfl
        refine ⟨fun h1 => ?_, by rw [hcs]; exact hfr⟩
        rw [h1] at hcs
        have h0 : commutatorSpace (1 : LinearMap.GeneralLinearGroup (ZMod 2) ↥J) = ⊥ := by
          rw [commutatorSpace, eq_bot_iff]
          rintro _ ⟨x, rfl⟩
          simp only [LinearMap.add_apply, LinearMap.id_apply, Units.val_one, Module.End.one_apply,
            Submodule.mem_bot]
          exact CFSG.ComponentClassification.OutcomeLocal.zmod2_add_self x
        rw [h0] at hcs
        rw [← hcs, finrank_bot] at hfr
        omega
    | one =>
      intro h
      have : e.symm (restrictEquiv (1 : GLV V) J h) = 1 := by
        have : restrictEquiv (1 : GLV V) J h = 1 := by ext i; rfl
        rw [this, map_one]
      rw [this]
      exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      intro h
      have ha' : conjSub a J = J := hJ.1.conjSub_eq (hcl ha)
      have hb' : conjSub b J = J := hJ.1.conjSub_eq (hcl hb)
      have : restrictEquiv (a * b) J h = restrictEquiv a J ha' * restrictEquiv b J hb' := by
        ext i; rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (iha ha') (ihb hb')
    | inv a ha iha =>
      intro h
      have ha' : conjSub a J = J := hJ.1.conjSub_eq (hcl ha)
      have : restrictEquiv a⁻¹ J h = (restrictEquiv a J ha')⁻¹ := by
        ext i
        show a⁻¹ (i : V) = ((restrictEquiv a J ha').symm i : V)
        have h1 : a ((restrictEquiv a J ha').symm i : V) = (i : V) := by
          have := (restrictEquiv a J ha').apply_symm_apply i
          exact congrArg Subtype.val this
        conv_lhs => rw [← h1]
        simp
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (iha ha')
  intro t ht
  rw [mem_restrictG_iff hJ.1, mem_restrictRange_iff' hJ.1] at ht
  obtain ⟨k, hk, hkt⟩ := ht
  have := key k (hgen hk) (hJ.1.conjSub_eq hk)
  rw [← hkt, MulEquiv.symm_apply_apply] at this
  exact this

theorem restrictG_irr (hJ : IsIrr K J) :
    ∀ W : Submodule (ZMod 2) ↥J, (∀ g ∈ restrictG K J hJ.1, ∀ w ∈ W,
      (g : ↥J →ₗ[ZMod 2] ↥J) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  refine (isIrr_restrictRange_top hJ).2.2 W ?_ bot_le le_top
  intro g hg w hw
  have := hW ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g)
    ((mem_restrictG_iff hJ.1 _).2 (by rw [MulEquiv.apply_symm_apply]; exact hg)) w hw
  rwa [show ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J).symm g :
      LinearMap.GeneralLinearGroup (ZMod 2) ↥J).val w = g w from coe_symm_generalLinearEquiv g w]
    at this

end Restrict

end G11

end CFSG.Quasithin
