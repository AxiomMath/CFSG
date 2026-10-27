module

public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Sporadic.Schreier.Co1StabLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier Matrix

@[expose] def certP0 : Subgroup (Equiv.Perm (Fin 98280)) :=
  certP ⊓ MulAction.stabilizer (Equiv.Perm (Fin 98280)) (0 : Fin 98280)

@[expose] def stabRestrHom :
    stabH →* Equiv.Perm (Fin 98280) :=
  certRhoHom.comp (Subgroup.inclusion stabH_le_GA)

theorem stabRestrHom_apply
    (h : stabH) :
    stabRestrHom h = certRhoHom ⟨(h : GL24), stabH_le_GA h.2⟩ := rfl

theorem stabRestrHom_injective :
    Function.Injective stabRestrHom := by
  intro x y h
  rw [stabRestrHom_apply, stabRestrHom_apply] at h
  have h' := congrArg Subtype.val (certRhoHom_injective h)
  dsimp only at h'
  exact Subtype.ext h'

section Action

attribute [local instance] xAct

theorem fix_iff_rho
    (g : GA) : certRhoHom g 0 = 0 ↔
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 = certVec 0 := by
  have h := certVec_rho g 0
  simp only [Fin.val_zero] at h
  rw [← h]
  constructor
  · intro e
    rw [e]
    rfl
  · intro e
    exact Fin.ext (certVec_injective (Fin.isLt _) (by norm_num) e)

theorem fix_iff_stabH
    (g : GA) :
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 = certVec 0 ↔
      (g : GL24) ∈ stabH := by
  rw [← mem_stab_iff, MulAction.mem_stabilizer_iff, certVec_zero]
  constructor
  · intro h
    apply Subtype.ext
    rw [xAct_val]
    exact h
  · intro h
    have h' := congrArg Subtype.val h
    rwa [xAct_val] at h'

theorem certRhoHom_fix_zero_iff
    (g : GA) : certRhoHom g 0 = 0 ↔ (g : GL24) ∈ stabH :=
  (fix_iff_rho g).trans (fix_iff_stabH g)

end Action

theorem stabRestrHom_range :
    stabRestrHom.range = certP0 := by
  ext σ
  constructor
  · rintro ⟨h, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← certRhoHom_range, stabRestrHom_apply]
      exact ⟨_, rfl⟩
    · rw [MulAction.mem_stabilizer_iff, stabRestrHom_apply, Equiv.Perm.smul_def]
      exact (certRhoHom_fix_zero_iff _).2 h.2
  · intro hσ
    obtain ⟨hσP, hσ0⟩ := Subgroup.mem_inf.1 hσ
    rw [← certRhoHom_range] at hσP
    obtain ⟨g, rfl⟩ := hσP
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hσ0
    exact ⟨⟨(g : GL24), (certRhoHom_fix_zero_iff g).1 hσ0⟩, by rw [stabRestrHom_apply]⟩

@[expose] def stabRestr :
    stabH ≃* certP0 :=
  (MonoidHom.ofInjective stabRestrHom_injective).trans (MulEquiv.subgroupCongr stabRestrHom_range)

theorem stabRestr_apply
    (h : stabH) :
    (stabRestr h : Equiv.Perm (Fin 98280)) = certRhoHom ⟨(h : GL24), stabH_le_GA h.2⟩ := rfl

theorem stabT_mem : stabH0 * stabW⁻¹ * stabH1 * stabW ∈ stabH := by
  have hw : stabW ∈ stabH := by
    rw [stabW]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem stabH0_mem) stabH1_mem)
      stabH1_mem) stabH0_mem) stabH1_mem) (inv_mem stabH0_mem)
  exact mul_mem (mul_mem (mul_mem stabH0_mem (inv_mem hw)) stabH1_mem) hw

theorem fam_co1_order_point_stabilizer :
    (∀ x ∈ certX, ∀ y ∈ certX, ∃ g ∈ GA,
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x = y) ∧
    (∀ g ∈ GA, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec 0 = certVec 0 ↔
      g ∈ stabH) ∧
    stabH ≤ GA ∧
    (∀ h : stabH, (stabRestr h : Equiv.Perm (Fin 98280)) =
      certRhoHom ⟨(h : GL24), stabH_le_GA h.2⟩) ∧
    Nontrivial certP0 ∧ IsSimpleGroup certP0 ∧ Nat.card certP0 = 42305421312000 ∧
    (stabRestr ⟨_, stabT_mem⟩ : Equiv.Perm (Fin 98280)) ∈ certP0 ∧
    orderOf (stabRestr ⟨_, stabT_mem⟩ : Equiv.Perm (Fin 98280)) = 23 ∧
    Nat.card certP = Nat.card GA ∧ Nat.card GA = Nat.card CFSG.Blueprint.NativeSporadic.Co1 ∧
    Nat.card CFSG.Blueprint.NativeSporadic.Co1 = 98280 * 42305421312000 ∧
    98280 * 42305421312000 = 4157776806543360000 := by
  have hsimple : IsSimpleGroup certP0 :=
    @MulEquiv.isSimpleGroup certP0 _ stabH _ isSimpleGroup_stabH stabRestr.symm
  refine ⟨fun x hx y hy => ?_, fun g hg => ?_, stabH_le_GA, stabRestr_apply, inferInstance,
    hsimple, ?_, (stabRestr _).2, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [certX_eq_co1X] at hx hy
    let _ := xAct
    obtain ⟨g, hg⟩ := xAct_pretransitive.exists_smul_eq ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨g, g.2, ?_⟩
    have := congrArg Subtype.val hg
    rwa [xAct_val] at this
  · exact fix_iff_stabH ⟨g, hg⟩
  · rw [← Nat.card_congr stabRestr.toEquiv, card_stabH]
  · have e : orderOf (stabRestr ⟨_, stabT_mem⟩) = orderOf (⟨_, stabT_mem⟩ : stabH) := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [← map_pow, ← map_one stabRestr, stabRestr.injective.eq_iff]
    rw [Subgroup.orderOf_coe, e, Subgroup.orderOf_mk]
    exact orderOf_stabT
  · exact (Nat.card_congr certRho.toEquiv).symm
  · rw [card_GA_eq, CFSG.Sporadic.Co1.card_Co1]
  · rw [CFSG.Sporadic.Co1.card_Co1]

end CFSG.Sporadic.Co1Block
