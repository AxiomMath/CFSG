module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Loc
public import CFSG.Quasithin.Vol2.F134LieSp4

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

namespace E9P2.Sp4

section Datum

variable {X : Type} [Group X] {L Th Hh Eh R : Subgroup X}

theorem mul_inf (h : E9Local L Th Hh Eh R) :
    ∀ u ∈ Th ⊓ L, ∀ x ∈ Eh, ∃ y ∈ Eh, ∃ s ∈ Th ⊓ L, u * x = y * s := by
  intro u hu x hx
  obtain ⟨y, hy, t, ht, hyt⟩ := h.dec (u * x) (Hh.mul_mem (h.T_le hu.1) (h.E_le_H hx))
  refine ⟨y, hy, t, ⟨ht, ?_⟩, hyt⟩
  have : t = y⁻¹ * (u * x) := by rw [hyt]; group
  rw [this]
  exact L.mul_mem (L.inv_mem (h.E_le_L hy)) (L.mul_mem hu.2 (h.E_le_L hx))

end Datum

section Finite

variable {X : Type} [Group X] [Finite X] {L Th Hh Eh R : Subgroup X}

theorem isSylowTwoOf_inf (h : E9Local L Th Hh Eh R) : IsSylowTwoOf (Th ⊓ L) L :=
  ⟨inf_le_right, h.sylow_T.2.1.to_inf_left,
    E9P2.Loc.not_two_dvd_relIndex_inf h.sylow_T h.normal_L⟩

end Finite

theorem exists_equiv_unipotent {A : Type*} [Group A] [Finite A] {L U : Subgroup A} {K : Type}
    [Field K] [Finite K] [CharP K 2] (ψ₀ : ↥L ≃* StatedSp 2 K) (hU : IsSylowTwoOf U L) :
    ∃ ψ : ↥L ≃* StatedSp 2 K, ∀ l : L, ψ l ∈ unipotent 2 K ↔ (l : A) ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₁ := (U.subgroupOf L).map ψ₀.toMonoidHom with hU₁def
  have hU₁ : IsSylowTwoOf U₁ (⊤ : Subgroup (StatedSp 2 K)) := by
    refine ⟨le_top, (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, hU₁def]
    erw [Subgroup.index_map_equiv]
    exact hU.2.2
  obtain ⟨g, -, hg⟩ := IsSylowTwoOf.exists_conj hU₁
    (CFSG.Quasithin.F134.Sp4.isSylowTwoOf_unipotent (K := K))
  refine ⟨ψ₀.trans (MulAut.conj g), fun l => ?_⟩
  rw [hg, Subgroup.mem_map_equiv, hU₁def, Subgroup.mem_map_equiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

end E9P2.Sp4

section Local

variable {X : Type} [Group X] [Finite X] {L Th Hh Eh R : Subgroup X}

theorem E9Local.sp4_normalizes (h : E9Local L Th Hh Eh R) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : 4 ≤ Nat.card F) (ψ₀ : ↥L ≃* StatedSp 2 F) :
    (∀ x ∈ Hh, x ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X)) ∧
      3 ∣ Nat.card F - 1 := by
  obtain ⟨hPU, h3⟩ := CFSG.Quasithin.F134.Sp4.normalizes_of_mulEquiv hF ψ₀
    (E9P2.Sp4.isSylowTwoOf_inf h) h.E_le_L h.card_E h.exp_E (E9P2.Sp4.mul_inf h)
  refine ⟨h.normalizes_of_E fun e he => ?_, h3⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => hPU e he u hu, fun hu => ?_⟩
  have := hPU e⁻¹ (Eh.inv_mem he) _ hu
  simpa [mul_assoc] using this

end Local

end CFSG.Quasithin
