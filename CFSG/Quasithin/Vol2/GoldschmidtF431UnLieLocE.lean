module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocA
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem K0_le_gramSU :
    (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) ≤ gramSU h (miyamotoJ4 K) :=
  sup_le (inf_le_left.trans (miyamotoUnipotent_le_SU h true false))
    (inf_le_left.trans (miyamotoN1_le_gramSU h))

theorem Kx_perfect (hf : 2 ≤ f) : ⁅Kx h, Kx h⁆ = Kx h := by
  have e := miyamotoPull_commutator h (⊤ : Subgroup (Xg h)) (etaX h) (K0_le_gramSU h)
    (K0_le_gramSU h)
  have h1 : Kx h = miyamotoPull h ⊤ (etaX h)
      ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h)) := sg_eq_pull h _
  rw [h1, ← e, commutator_miyamotoA1Cu_sup_N1Cu h hf]

theorem Vx_le_Kx : Vx h ≤ Kx h := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx))

theorem Kx_le_Cx : Kx h ≤ Cx h := by
  rw [cent_z2X h]
  intro x hx
  refine Subgroup.mem_subgroupOf.2 ?_
  have hx' := Subgroup.mem_subgroupOf.1 hx
  refine (sup_le (inf_le_left.trans le_sup_left) ?_ : _ ≤ miyamotoA1 h ⊔ miyamotoN1F h) hx'
  rw [miyamotoN1_inf_Cu h]
  exact le_sup_right

theorem Vx_le_Cx : Vx h ≤ Cx h := (Vx_le_Kx h).trans (Kx_le_Cx h)

abbrev N1Fx : Subgroup (Xg h) := sg h (miyamotoN1F h)

theorem N1Fx_le_Cx : N1Fx h ≤ Cx h := by
  rw [cent_z2X h]
  exact fun x hx => Subgroup.mem_subgroupOf.2
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))

theorem sl2_commutator_top (hf : 2 ≤ f) :
    commutator (SpecialLinearGroup (Fin 2) h.fixedField) = ⊤ := by
  obtain ⟨t, htF, ht⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht0 : (⟨(t : K), htF⟩ : h.fixedField) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
  have ht' : ((Units.mk0 _ ht0 : h.fixedFieldˣ) : h.fixedField) ^ 2 ≠ 1 := fun e =>
    ht (by simpa using congrArg Subtype.val e)
  refine eq_top_iff.2 fun m _ => ?_
  have := mem_commutator_range_of_SL2 (MonoidHom.id (SpecialLinearGroup (Fin 2) h.fixedField))
    ht' m
  have hr : (MonoidHom.id (SpecialLinearGroup (Fin 2) h.fixedField)).range = ⊤ :=
    MonoidHom.range_eq_top.2 fun x => ⟨x, rfl⟩
  rw [hr] at this
  exact this

theorem not_isSolvable_N1Fx (hf : 2 ≤ f) : ¬ Group.IsSolvable (N1Fx h) := by
  intro hsol
  have hle : miyamotoN1F h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoN1F_le_N1 h).trans (miyamotoN1_le_gramSU h)
  let φ : SpecialLinearGroup (Fin 2) h.fixedField →* N1Fx h :=
    ((subgroupOfEquivOfLe hle).symm.toMonoidHom).comp (miyamotoN1FEquiv h).toMonoidHom
  have hinj : Function.Injective φ :=
    ((subgroupOfEquivOfLe hle).symm.injective).comp (miyamotoN1FEquiv h).injective
  have := Group.isSolvable_of_isSolvable_injective hinj
  have hn : Nontrivial (SpecialLinearGroup (Fin 2) h.fixedField) := by
    refine ⟨⟨1, upperSL2 1, fun e => ?_⟩⟩
    have := congrArg (fun m : SpecialLinearGroup (Fin 2) h.fixedField =>
      (m : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1) e
    simp [coe_upperSL2] at this
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial
    (SpecialLinearGroup (Fin 2) h.fixedField)
  rw [sl2_commutator_top h hf] at hlt
  exact lt_irrefl _ hlt

end CFSG.Quasithin.H13.F431.Un.LL
