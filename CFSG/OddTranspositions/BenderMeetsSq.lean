module

public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G]

theorem bender_meetsSq (hB : CFSG.BenderSuzuki.IsBenderGroup G)
    {D : Set G} (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d₀, hD⟩ := hcls
  have hd₀ : d₀ ∈ D := by
    rw [hD]
    exact IsConj.refl d₀
  have hd₀ord : orderOf d₀ = 2 := hinv d₀ hd₀
  have mem_D : ∀ x : G, x * x = 1 → x ≠ 1 → x ∈ D := by
    intro x hx hx1
    rw [hD]
    exact IsBenderGroup.isConj_of_orderOf_eq_two hB hd₀ord
      (orderOf_eq_prime (by rw [pow_two]; exact hx) hx1)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  let Z : Subgroup (Q : Subgroup G) := Subgroup.center (Q : Subgroup G)
  have hZcard : 4 ≤ Nat.card Z := IsBenderGroup.four_le_card_center hB Q
  haveI : Fintype Z := Fintype.ofFinite Z
  have hZ4 : 4 ≤ Fintype.card Z := by
    simpa [Nat.card_eq_fintype_card] using hZcard
  have hZ1 : 1 < Fintype.card Z := by omega
  obtain ⟨z, hz1⟩ := Fintype.exists_ne_of_one_lt_card hZ1 (1 : Z)
  have hcardT : Fintype.card {x : Z // x ≠ 1} = Fintype.card Z - 1 := by
    rw [Fintype.card_subtype_compl (fun x : Z => x = 1), Fintype.card_subtype_eq (1 : Z)]
  have hT : 1 < Fintype.card {x : Z // x ≠ 1} := by omega
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hT ⟨z, hz1⟩
  have hw1 : w.1 ≠ 1 := w.2
  have hwz : w.1 ≠ z := fun h => hw (Subtype.ext h)
  have hcenter : ∀ z : Z, ∀ y ∈ (Q : Subgroup G), Commute (z : G) y := by
    intro z y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)).symm
  have hsq : ∀ z : Z, (z : G) * (z : G) = 1 := fun z =>
    IsBenderGroup.mul_self_eq_one_of_commute hB Q (z : Q).2 (fun y hy => hcenter z y hy)
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hwG1 : (w.1 : G) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  have hzw : Commute (z : G) (w.1 : G) := hcenter z (w.1 : G) (w.1 : Q).2
  have hne : (z : G) ≠ (w.1 : G) := fun h =>
    hwz (Subtype.ext (Subtype.ext h)).symm
  refine ⟨(z : G), mem_D (z : G) (hsq z) hzG1, (w.1 : G),
    mem_D (w.1 : G) (hsq w.1) hwG1, hne, hzw, ?_⟩
  have hsq_mul : ((z : G) * (w.1 : G)) * ((z : G) * (w.1 : G)) = 1 := by
    have h := hzw.mul_pow 2
    simp only [pow_two] at h
    rw [h, hsq z, hsq w.1]
    simp
  have hne_mul : (z : G) * (w.1 : G) ≠ 1 := by
    intro h
    apply hne
    calc (z : G) = (z : G) * 1 := (mul_one _).symm
      _ = (z : G) * ((w.1 : G) * (w.1 : G)) := by rw [hsq w.1]
      _ = ((z : G) * (w.1 : G)) * (w.1 : G) := (mul_assoc _ _ _).symm
      _ = 1 * (w.1 : G) := by rw [h]
      _ = (w.1 : G) := one_mul _
  exact mem_D ((z : G) * (w.1 : G)) hsq_mul hne_mul

end CFSG.OddTranspositions
