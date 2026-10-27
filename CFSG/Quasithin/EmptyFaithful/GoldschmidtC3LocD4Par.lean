module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocD4Grp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocAsm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6

namespace GoldC3

theorem map_oPrimeResidualOf_equiv (p : ℕ) {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (A : Subgroup X) :
    (oPrimeResidualOf p A).map e.toMonoidHom = oPrimeResidualOf p (A.map e.toMonoidHom) := by
  unfold oPrimeResidualOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, k, (orderOf_injective e.toMonoidHom e.injective x).trans hk⟩
  · rintro ⟨⟨x, hxA, rfl⟩, k, hk⟩
    exact ⟨x, ⟨hxA, k, (orderOf_injective e.toMonoidHom e.injective x).symm.trans hk⟩, rfl⟩

section Par

variable {X : Type} [Group X] [Finite X] {U P₁ : Subgroup X}

omit [Finite X] in
theorem exists_orderOf_eq_two_pow {u : X} (h : ∃ n : ℕ, u ^ 2 ^ n = 1) :
    ∃ k : ℕ, orderOf u = 2 ^ k := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
  exact ⟨k, hk⟩

omit [Finite X] in
theorem mem_oPrime_two {x : X} (hx : x ∈ P₁) (h : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    x ∈ oPrimeResidualOf 2 P₁ :=
  Subgroup.subset_closure ⟨hx, exists_orderOf_eq_two_pow h⟩

omit [Finite X] in
theorem oPrime_two_le : oPrimeResidualOf 2 P₁ ≤ P₁ := (Subgroup.closure_le P₁).2 fun _ hx => hx.1

omit [Finite X] in
theorem le_oPrime_two (hU2 : IsPGroup 2 U) (hUP : U ≤ P₁) : U ≤ oPrimeResidualOf 2 P₁ :=
  fun u hu => mem_oPrime_two (hUP hu) (by
    obtain ⟨n, hn⟩ := hU2 ⟨u, hu⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩)

omit [Finite X] in
theorem closure_twoElts_oPrime :
    Subgroup.closure {x : ↥(oPrimeResidualOf 2 P₁) | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
  refine eq_top_iff.2 ?_
  have h : Subgroup.closure (Subtype.val ⁻¹' {x : X | x ∈ P₁ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} :
      Set ↥(oPrimeResidualOf 2 P₁)) = ⊤ := Subgroup.closure_closure_coe_preimage
  refine le_trans (le_of_eq h.symm) (Subgroup.closure_mono ?_)
  rintro x ⟨-, k, hk⟩
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩

theorem not_oPrime_two_le (hU : IsSylowTwoOf U ⊤) (hcov : Subgroup.normalizer (U : Set X) ⋖ P₁) :
    ¬ oPrimeResidualOf 2 P₁ ≤ Subgroup.normalizer (U : Set X) := by
  intro hPN
  have hUP₁ : U ≤ P₁ := Subgroup.le_normalizer.trans hcov.le
  refine hcov.lt.not_ge fun g hg => ?_
  have hconj : U.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (U : Set X) := by
    rintro _ ⟨u, hu, rfl⟩
    refine hPN (mem_oPrime_two ?_ ?_)
    · exact P₁.mul_mem (P₁.mul_mem hg (hUP₁ hu)) (P₁.inv_mem hg)
    · obtain ⟨n, hn⟩ := hU.2.1 ⟨u, hu⟩
      refine ⟨n, ?_⟩
      have h1 : u ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      show (g * u * g⁻¹) ^ 2 ^ n = 1
      rw [conj_pow, h1]
      group
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U :=
    FLc.le_of_normalizes_of_sylow hU le_rfl le_top le_top (hU.2.1.map _) hconj
  have heq : U.map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem relIndex_oPrime_two (hU : IsSylowTwoOf U ⊤) (hcov : Subgroup.normalizer (U : Set X) ⋖ P₁)
    (hidx : (Subgroup.normalizer (U : Set X)).relIndex P₁ = 3) :
    (Subgroup.normalizer (U : Set X)).relIndex (oPrimeResidualOf 2 P₁) = 3 := by
  set P := oPrimeResidualOf 2 P₁ with hP
  set N := Subgroup.normalizer (U : Set X) with hN
  have hUP : U ≤ P := le_oPrime_two hU.2.1 (Subgroup.le_normalizer.trans hcov.le)
  have h1 : N.relIndex P ≤ 3 := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right oPrime_two_le (by rw [hidx]; norm_num)
  have h2 : N.relIndex P ≠ 1 := fun h => not_oPrime_two_le hU hcov (Subgroup.relIndex_eq_one.1 h)
  have h3 : ¬ 2 ∣ N.relIndex P := fun hd =>
    (isSylowTwoOf_of_le hU hUP).2.2
      (hd.trans (Subgroup.relIndex_dvd_of_le_left P Subgroup.le_normalizer))
  have h0 : N.relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem card_oPrime_two (hU : IsSylowTwoOf U ⊤) (hcov : Subgroup.normalizer (U : Set X) ⋖ P₁)
    (hidx : (Subgroup.normalizer (U : Set X)).relIndex P₁ = 3)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.normalizer (U : Set X))) :
    Nat.card (oPrimeResidualOf 2 P₁) = 3 * Nat.card U := by
  set P := oPrimeResidualOf 2 P₁ with hP
  set N := Subgroup.normalizer (U : Set X) with hN
  have hUP : U ≤ P := le_oPrime_two hU.2.1 (Subgroup.le_normalizer.trans hcov.le)
  have hUsyl : IsSylowTwoOf (U.subgroupOf P) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_of_le hU hUP)
  have hnorm : Subgroup.normalizer ((U.subgroupOf P : Subgroup ↥P) : Set ↥P) = N.subgroupOf P := by
    ext y
    rw [mem_normalizer_subgroupOf_iff hUP y]
    rfl
  have hid3 : (Subgroup.normalizer ((U.subgroupOf P : Subgroup ↥P) : Set ↥P)).index = 3 := by
    rw [hnorm]
    exact relIndex_oPrime_two hU hcov hidx
  have h3' : ¬ 3 ∣ Nat.card (Subgroup.normalizer ((U.subgroupOf P : Subgroup ↥P) : Set ↥P)) := by
    rw [hnorm]
    intro hd
    apply h3
    refine hd.trans ?_
    have e : Nat.card (N.subgroupOf P) = Nat.card (N ⊓ P : Subgroup X) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [e]
    exact Subgroup.card_dvd_of_le inf_le_left
  have heq := normalizer_eq_of_three_sylow hUsyl closure_twoElts_oPrime hid3 h3'
  rw [heq] at hid3
  have h := Subgroup.card_mul_index (U.subgroupOf P)
  rw [hid3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv] at h
  omega

theorem oPrime_two_sup_eq (hU : IsSylowTwoOf U ⊤) (hcov : Subgroup.normalizer (U : Set X) ⋖ P₁) :
    oPrimeResidualOf 2 P₁ ⊔ Subgroup.normalizer (U : Set X) = P₁ := by
  have hle : oPrimeResidualOf 2 P₁ ⊔ Subgroup.normalizer (U : Set X) ≤ P₁ :=
    sup_le oPrime_two_le hcov.le
  rcases hcov.eq_or_eq le_sup_right hle with h | h
  · exact absurd (h ▸ le_sup_left) (not_oPrime_two_le hU hcov)
  · exact h

theorem isSolvable_oPrime_two (hU : IsSylowTwoOf U ⊤) (hcov : Subgroup.normalizer (U : Set X) ⋖ P₁)
    (hidx : (Subgroup.normalizer (U : Set X)).relIndex P₁ = 3)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.normalizer (U : Set X))) :
    Group.IsSolvable ↥(oPrimeResidualOf 2 P₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := card_oPrime_two hU hcov hidx h3
  obtain ⟨a, ha⟩ := hU.2.1.exists_card_eq
  have : Fintype ↥(oPrimeResidualOf 2 P₁) := Fintype.ofFinite _
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
    (a := a) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, hc, ha]
  ring

omit [Finite X] in
theorem map_oPrime_two (α : MulAut X) (h : P₁.map α.toMonoidHom = P₁) :
    (oPrimeResidualOf 2 P₁).map α.toMonoidHom = oPrimeResidualOf 2 P₁ := by
  rw [map_oPrimeResidualOf_equiv 2 α P₁, h]

end Par

end GoldC3

end CFSG.Quasithin
