module

public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA2
public import CFSG.Quasithin.Vol2.Ch11SecS12ZQ
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult

open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

@[expose] def NoPerfectTripleCoverM24 : Prop :=
  NoPerfectTripleCover CFSG.Blueprint.NativeSporadic.M24

@[expose] def J4LocalM24 : Prop :=
  ∃ (H : Subgroup (Spor .J4)) (φ : H →* CFSG.Blueprint.NativeSporadic.M24),
    Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧ ¬ 3 ∣ H.index

theorem isPerfect_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have hmem : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have : IsMulCommutative G := ⟨⟨hcomm⟩⟩
    exact h ((Group.is_simple_iff_prime_card (α := G)).1 inferInstance)
  · exact hc

theorem isPerfect_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [Group.IsPerfect G] : Group.IsPerfect H :=
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

section Certified


theorem factJ4Multiplier_of_mulEquiv (e : CFSG.Blueprint.NativeSporadic.J4 ≃* Spor .J4)
    (hH : J4LocalM24) (hM24 : NoPerfectTripleCoverM24) : FactJ4Multiplier := by
  obtain ⟨H, φ, hφ, h2, h3⟩ := hH
  have hcard₀ := CFSG.Sporadic.J4.card_J4
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr e.toEquiv, hcard₀]
  have : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have := CFSG.Sporadic.J4.isSimpleGroup_J4
  have : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J4 :=
    isPerfect_of_isSimpleGroup fun h => by
      have h2 := h.eq_one_or_self_of_dvd 2 (by rw [hcard₀]; norm_num)
      rw [hcard₀] at h2
      omega
  have : Group.IsPerfect (Spor .J4) :=
    isPerfect_of_mulEquiv (G := CFSG.Blueprint.NativeSporadic.J4) (H := Spor .J4) e
  have := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hcM := CFSG.Sporadic.Mathieu.card_M24
  have : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M24 :=
    isPerfect_of_isSimpleGroup fun h => by
      have h2 := h.eq_one_or_self_of_dvd 2 (by rw [hcM]; norm_num)
      rw [hcM] at h2
      omega
  have hcop : Nat.Coprime (Nat.card φ.ker) 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    rw [hn]
    exact Nat.Coprime.pow_left n (by norm_num)
  exact not_dvd_card_hopfMultiplier (noPerfectCentralCover_of_subgroup Nat.prime_three
    (NoPerfectTripleCover.noPerfectCentralCover hM24) H h3 φ hφ hcop)

end Certified

end CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult
