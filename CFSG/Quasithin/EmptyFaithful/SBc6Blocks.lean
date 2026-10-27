module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithful.S153D30

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc6

section Generic

theorem not_isQuasisimple_of_comm {Q : Type*} [Group Q] (h : ∀ a b : Q, a * b = b * a) :
    ¬ CFSG.IsQuasisimple Q := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a b])

theorem comm_of_card_three {Q : Type*} [Group Q] (h : Nat.card Q = 3) :
    ∀ a b : Q, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : IsCyclic Q := isCyclic_of_prime_card h
  intro a b
  exact (IsCyclic.commGroup (α := Q)).mul_comm a b

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem twoResidual_eq_of_ctx (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) : twoResidual I = L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hLY : ⁅L, Yp⁆ = L := c25.conc.2.2.2.1
  have h2L : ∀ y ∈ I, ∃ k : ℕ, y ^ 2 ^ k ∈ L := fun y hy =>
    InternalSec.two_of_sup hS2 (hSI.trans hIL) y (hIeq ▸ hy)
  refine le_antisymm (twoResidual_le_of_isTwoQuotient hLI hIL h2L) ?_
  intro x hx
  rw [mem_twoResidual_iff]
  intro N hNI hIN h2N
  have hYpN : Yp ≤ N := by
    rw [hF.yp_eq]
    unfold oPrimeResidualOf
    refine (Subgroup.closure_le N).2 fun y hy => ?_
    obtain ⟨⟨-, hyI⟩, j, hj⟩ := hy
    obtain ⟨k, hk⟩ := h2N y hyI
    have hcop : Nat.Coprime (2 ^ k) (orderOf y) := by
      rw [hj]
      exact Nat.Coprime.pow k j (by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact N.pow_mem hk m
  have hLN : L ≤ N := by
    rw [← hLY]
    refine Subgroup.commutator_le.mpr fun l hl y hy => ?_
    rw [commutatorElement_def]
    have h1 : l * y * l⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hIN (hLI hl)) y).mp (hYpN hy)
    exact N.mul_mem h1 (N.inv_mem (hYpN hy))
  exact hLN hx

end Main

end SBc6

end CFSG.Quasithin
