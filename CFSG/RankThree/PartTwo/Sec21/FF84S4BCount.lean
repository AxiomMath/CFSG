module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem B_order5_fixed {S : Subgroup G} (hS : IsElemAb 2 6 S) {y : G} (hy : orderOf y = 5)
    (hn : y ∈ Nor S) (hnc : ¬ S ≤ Cen y) : Nat.card ↥(S ⊓ Cen y) = 4 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := hS.1
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hy5 : y ^ 5 = 1 := hy ▸ pow_orderOf_eq_one y
  let g : ↥S → ↥S := fun s => ⟨y * s * y⁻¹, (Subgroup.mem_normalizer_iff.1 hn s).1 s.2⟩
  let F : Function.End ↥S := g
  have hfk : ∀ (k : ℕ) (s : ↥S), ((g^[k]) s : G) = y ^ k * s * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [Function.iterate_succ_apply']
      show y * ((g^[k]) s : G) * y⁻¹ = _
      rw [ih s]
      group
  have hpowF : ∀ n : ℕ, F ^ n = g^[n] := fun n => rfl
  have hf5 : F ^ 5 ^ 1 = 1 := by
    rw [hpowF]
    funext s
    apply Subtype.ext
    rw [hfk, pow_one, hy5, inv_one, mul_one, one_mul]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 5) (n := 1) hf5
  have e : F.fixedPoints ≃ ↥(S ⊓ Cen y) :=
    { toFun := fun x => ⟨(x.1 : G), by
        have hx : g x.1 = x.1 := x.2
        have hx' : y * (x.1 : G) * y⁻¹ = x.1 := congrArg Subtype.val hx
        refine Subgroup.mem_inf.2 ⟨x.1.2, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hx').symm⟩
      invFun := fun z => ⟨⟨(z.1 : G), (Subgroup.mem_inf.1 z.2).1⟩, by
        show g _ = _
        apply Subtype.ext
        show y * (z.1 : G) * y⁻¹ = z.1
        have hz : z.1 ∈ Cen y := (Subgroup.mem_inf.1 z.2).2
        exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_singleton_iff.1 hz).symm⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun z => by
        apply Subtype.ext
        rfl }
  have hcf : Nat.card F.fixedPoints = Nat.card ↥(S ⊓ Cen y) := Nat.card_congr e
  have hmod' : Nat.card ↥S ≡ Nat.card F.fixedPoints [MOD 5] := by
    simpa [Nat.card_eq_fintype_card] using hmod
  have hI : IsPGroup 2 ↥(S ⊓ Cen y) := (IsElementaryAbelian.isPGroup 2 S).to_inf_left
  obtain ⟨k, hk⟩ := hI.exists_card_eq
  have hdvd : Nat.card ↥(S ⊓ Cen y) ∣ Nat.card ↥S :=
    Subgroup.card_dvd_of_le (inf_le_left : S ⊓ Cen y ≤ S)
  rw [hk, hS.2] at hdvd
  have hk6 : k ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hk6' : k ≠ 6 := by
    intro h6
    have heq : S ⊓ Cen y = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, h6, hS.2])
    apply hnc
    intro x hx
    have hx' : x ∈ S ⊓ Cen y := by rw [heq]; exact hx
    exact (Subgroup.mem_inf.1 hx').2
  have hk5 : k < 6 := lt_of_le_of_ne hk6 hk6'
  rw [hS.2, hcf, hk] at hmod'
  have hk2 : k = 2 := by
    interval_cases k <;> first | rfl | (norm_num [Nat.ModEq] at hmod')
  rw [hk, hk2]
  norm_num

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
