module

public import CFSG.Quasithin.Vol2.Ch3E213MLift

public section

namespace CFSG.Quasithin.RonanE211

open CFSG.Quasithin.Ch3E213M

private def ronanTwoPart {Q : Type} [Group Q] (J₀ : Subgroup Q) (hJc : J₀ ≤ Subgroup.center Q) :
    Subgroup Q where
  carrier := {x | x ∈ J₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  one_mem' := ⟨J₀.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
    have hc : Commute a b := (Subgroup.mem_center_iff.mp (hJc ha) b).symm
    have ha' : a ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have hb' : b ^ 2 ^ (k + l) = 1 := by rw [add_comm, pow_add, pow_mul, hl, one_pow]
    exact ⟨J₀.mul_mem ha hb, k + l, by rw [hc.mul_pow, ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk⟩
    exact ⟨J₀.inv_mem ha, k, by rw [inv_pow, hk, inv_one]⟩

private theorem mem_ronanTwoPart {Q : Type} [Group Q] (J₀ : Subgroup Q)
    (hJc : J₀ ≤ Subgroup.center Q) (x : Q) :
    x ∈ ronanTwoPart J₀ hJc ↔ x ∈ J₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 :=
  Iff.rfl

theorem isPGroup_two_of_oddCoverExact {Q : Type} [Group Q] [Finite Q] (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) {F : Type} [Group F] (hOdd : OddCoverExact F)
    (e : Q ⧸ J₀ ≃* F) (hgen : Subgroup.closure {x : Q | x * x = 1} = ⊤) : IsPGroup 2 J₀ := by
  obtain ⟨S₂, hS₂⟩ : ∃ S : Subgroup Q, ∀ x, x ∈ S ↔ (x ∈ J₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1) :=
    ⟨ronanTwoPart J₀ hJc, mem_ronanTwoPart J₀ hJc⟩
  have hle : S₂ ≤ J₀ := fun x hx => ((hS₂ x).mp hx).1
  have hSn : S₂.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hJc ((hS₂ n).mp hn).1) g
    have hgn : g * n * g⁻¹ = n := by rw [hc, mul_inv_cancel_right]
    rw [hgn]
    exact hn
  have hmkSurj : Function.Surjective (QuotientGroup.mk' S₂ : Q →* Q ⧸ S₂) :=
    QuotientGroup.mk'_surjective S₂
  have hRc : Subgroup.map (QuotientGroup.mk' S₂) J₀ ≤ Subgroup.center (Q ⧸ S₂) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective S₂ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hJc hj) q]
  have hRodd : Odd (Nat.card ↥(Subgroup.map (QuotientGroup.mk' S₂) J₀)) := by
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.map (QuotientGroup.mk' S₂) J₀)) with hev | hod
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
      have hx' : orderOf (x : Q ⧸ S₂) = 2 := by rw [Subgroup.orderOf_coe, hx]
      have hsq : (x : Q ⧸ S₂) * (x : Q ⧸ S₂) = 1 := by
        have h1 := pow_orderOf_eq_one (x : Q ⧸ S₂)
        rw [hx', sq] at h1
        exact h1
      obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp x.2
      rw [← hjx, ← map_mul, QuotientGroup.mk'_apply] at hsq
      obtain ⟨-, k, hk⟩ := (hS₂ (j * j)).mp ((QuotientGroup.eq_one_iff (j * j)).mp hsq)
      have hj2 : j ^ 2 ^ (k + 1) = 1 := by
        rw [pow_succ' (2 : ℕ) k, pow_mul, sq]
        exact hk
      have hjS : j ∈ S₂ := (hS₂ j).mpr ⟨hj, k + 1, hj2⟩
      have hmkj : (QuotientGroup.mk' S₂ j : Q ⧸ S₂) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff j).mpr hjS
      rw [hjx] at hmkj
      rw [hmkj, orderOf_one] at hx'
      norm_num at hx'
    · exact hod
  have hgenE : Subgroup.closure {x : Q ⧸ S₂ | orderOf x = 2} = ⊤ := by
    have hmap : (Subgroup.closure {x : Q | x * x = 1}).map (QuotientGroup.mk' S₂) = ⊤ := by
      rw [hgen]
      exact Subgroup.map_top_of_surjective _ hmkSurj
    rw [MonoidHom.map_closure] at hmap
    rw [eq_top_iff, ← hmap, Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q * q = 1 := hq
    by_cases h1 : QuotientGroup.mk' S₂ q = 1
    · rw [h1]
      exact SetLike.mem_coe.mpr (one_mem _)
    · have hpow : QuotientGroup.mk' S₂ q ^ 2 = 1 := by
        rw [sq, ← map_mul, hq', map_one]
      have h2 : orderOf (QuotientGroup.mk' S₂ q) = 2 := orderOf_eq_prime hpow h1
      have h3 : QuotientGroup.mk' S₂ q ∈ {x : Q ⧸ S₂ | orderOf x = 2} := h2
      exact SetLike.mem_coe.mpr (Subgroup.subset_closure h3)
  have hRbot : Subgroup.map (QuotientGroup.mk' S₂) J₀ = ⊥ :=
    hOdd (Q ⧸ S₂) hgenE (Subgroup.map (QuotientGroup.mk' S₂) J₀) hRc hRodd
      ⟨(QuotientGroup.quotientQuotientEquivQuotient S₂ J₀ hle).trans e⟩
  intro g
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (g : Q) ^ 2 ^ k = 1 := by
    have hmem : QuotientGroup.mk' S₂ (g : Q) ∈ Subgroup.map (QuotientGroup.mk' S₂) J₀ :=
      Subgroup.mem_map_of_mem _ g.2
    rw [hRbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
    exact ((hS₂ _).mp ((QuotientGroup.eq_one_iff (g : Q)).mp hmem)).2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.Quasithin.RonanE211
