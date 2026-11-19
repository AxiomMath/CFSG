
module

public import CFSG.Monster.B.TwoA.Par2.Class
public import CFSG.Monster.B.TwoA.Unitary.LinThreeBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Classical.ThreePlane CFSG.Monster.B.TwoA.Unitary.LinThree

attribute [local instance] restAction

theorem pCore_two_eq_bot_of_odd {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (hX : ¬ 2 ∣ Nat.card X) :
    CFSG.pCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀⟩ :=
    (CFSG.pCore_isPGroup (p := 2) (G := G)).nonempty_fixed_point_of_prime_not_dvd_card X hX
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ x
  rw [one_smul]
  have hm : g⁻¹ * n * g ∈ CFSG.pCore 2 G := by
    have := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem n hn g⁻¹
    rwa [inv_inv] at this
  have h1 : (g⁻¹ * n * g) • x₀ = x₀ := hx₀ ⟨_, hm⟩
  have e : n * g = g * (g⁻¹ * n * g) := by group
  calc n • g • x₀ = (n * g) • x₀ := (mul_smul n g x₀).symm
    _ = (g * (g⁻¹ * n * g)) • x₀ := by rw [e]
    _ = g • (g⁻¹ * n * g) • x₀ := mul_smul _ _ _
    _ = g • x₀ := by rw [h1]

@[instance_reducible] def nativeAction : MulAction P₂ NativeCoord :=
  MulAction.compHom NativeCoord restP

attribute [local instance] nativeAction

theorem nativeAction_smul (p : P₂) (i : NativeCoord) : p • i = restP p i := rfl

theorem nativeAction_faithful : FaithfulSMul P₂ NativeCoord :=
  ⟨fun h => restP_injective (Equiv.ext fun i => h i)⟩

def nativeRest (i : NativeCoord) : Rest :=
  ⟨i, fun h => by have := i.2; rw [h] at this; exact absurd this (by decide),
    fun h => by have := i.2; rw [h] at this; exact absurd this (by decide)⟩

theorem nativeAction_pretransitive :
    MulAction.IsPretransitive P₂ NativeCoord := by
  refine ⟨fun i k => ?_⟩
  have h2 := isMultiplyPretransitive_rest
  rw [MulAction.is_two_pretransitive_iff] at h2
  have hi : rest2 ≠ nativeRest i := fun h => by
    have := i.2
    rw [← show ((nativeRest i : Rest) : Fin 24) = i from rfl, ← h] at this
    exact absurd this (by decide)
  have hk : rest2 ≠ nativeRest k := fun h => by
    have := k.2
    rw [← show ((nativeRest k : Rest) : Fin 24) = k from rfl, ← h] at this
    exact absurd this (by decide)
  obtain ⟨g, g2, gi⟩ := h2 hi hk
  have hg : ((g : AutPerm) : Equiv.Perm (Fin 24)) ∈ P₂ := by
    rw [mem_P₂_iff, Unitary.mem_P2]
    exact ⟨g.2, congrArg Subtype.val g2⟩
  refine ⟨⟨_, hg⟩, Subtype.ext ?_⟩
  rw [nativeAction_smul, restP_apply]
  exact congrArg Subtype.val gi

theorem natCard_nativeCoord : Nat.card NativeCoord = 21 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem pCore_P₂ : CFSG.pCore 2 P₂ = ⊥ := by
  have := nativeAction_faithful
  have := nativeAction_pretransitive
  exact pCore_two_eq_bot_of_odd (X := NativeCoord) (by rw [natCard_nativeCoord]; decide)

def inclH : H2 →* Ntwo := Subgroup.inclusion H2_le_Ntwo

def phiH :
    H2 →* Ppair × Equiv.Perm (Fin 3) :=
  twoCoreEquiv.toMonoidHom.comp (mkK.comp inclH)

theorem phiH_apply
    (h : H2) : phiH h = twoCoreEquiv (QuotientGroup.mk (inclH h)) := rfl

theorem phiH_fst
    (h : H2) : (phiH h).1 = blockP (inclH h) := rfl

theorem blockP_inclH_rest2
    (h : H2) : blockP (inclH h) • rest2 = rest2 := by
  have hc : (h : Dfull) * cQ * (h : Dfull)⁻¹ = cQ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h.2).2
  have h1 := conj_blk_Ntwo (inclH h) cQ_mem_blk
  change (h : Dfull) * cQ * (h : Dfull)⁻¹ ∈ _ at h1
  rw [hc] at h1
  exact eq_of_mem_blk h1 cQ_mem_blk

theorem phiH_fst_mem
    (h : H2) : (((phiH h).1 : Ppair) : AutPerm) ∈ Unitary.P2 := by
  rw [Unitary.mem_P2]
  exact ⟨(phiH h).1.2, congrArg Subtype.val (blockP_inclH_rest2 h)⟩

def psiH :
    H2 →* P₂ :=
  ((AutPerm.subtype.comp Ppair.subtype).comp ((MonoidHom.fst _ _).comp phiH)).codRestrict P₂
    fun h => (mem_P₂_iff _).2 (phiH_fst_mem h)

theorem coe_psiH
    (h : H2) :
    (psiH h : Equiv.Perm (Fin 24)) = (((phiH h).1 : Ppair) : AutPerm) := rfl

theorem R2_inf_le_H2 :
    R2 ⊓ Subgroup.centralizer {cQ} ≤ H2 :=
  inf_le_inf_right _ R2_le_Ntwo

def toRest (j : Fin 24) (hj : 2 ≤ j) : Rest :=
  ⟨j, fun h => by rw [h] at hj; exact absurd hj (by decide),
    fun h => by rw [h] at hj; exact absurd hj (by decide)⟩

theorem two_le_rest (j : Rest) : (2 : Fin 24) ≤ j := by
  rcases j with ⟨j, h0, h1⟩
  change (2 : ℕ) ≤ (j : ℕ)
  have h0' : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : (j : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
  omega

theorem blk_toRest (j : Fin 24) (hj : 2 ≤ j) :
    blk (toRest j hj) = {d | ∃ v ∈ Vhat, dhat 0 j * v = d} := rfl

theorem conjClass_eq' :
    {d : Dfull | ∃ n ∈ Ntwo, n * cQ * n⁻¹ = d} =
    {d | ∃ j : Fin 24, 2 ≤ j ∧ ∃ v ∈ Vhat, dhat 0 j * v = d} := by
  change conjClass = _
  rw [conjClass_eq]
  ext d
  constructor
  · rintro ⟨j, v, hv, hd⟩
    exact ⟨j, two_le_rest j, v, hv, hd⟩
  · rintro ⟨j, hj, v, hv, hd⟩
    exact ⟨toRest j hj, v, hv, hd⟩

end CFSG.Monster.B.TwoA.Par2
