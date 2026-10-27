module

public import CFSG.RankThree.PartOne.Q1327T.Pair

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G}

theorem single_geometry (hd : RefFacts.ElemData p E) (hcard : Nat.card E = p ^ 3)
    {t : MulAut E} (h : IsAutReflection p E t) {v : E} (hv1 : v ≠ 1) (hvt : t v = v) :
    ∃ c₀ x : E, c₀ ≠ 1 ∧ t c₀ = c₀ ∧ x ∈ autMoved E t ∧ x ≠ 1 ∧
      Nat.card ↥(Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) = p ^ 2 ∧
      autFixed E t = Subgroup.zpowers v ⊔ Subgroup.zpowers c₀ ∧
      v ∉ Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x ∧
      Subgroup.zpowers v ⊔ (Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) = ⊤ := by
  have hp := hd.prime
  have hcomm : ∀ A B : Subgroup E, ∀ k ∈ A, ∀ l ∈ B, k * l = l * k :=
    fun _ _ k _ l _ => hd.comm k l
  have hC : Nat.card (autFixed E t) = p ^ 2 := card_autFixed hd hcard h
  have hFM : autFixed E t ⊓ autMoved E t = ⊥ :=
    Sec13Base.fixed_inf_moved hd.comm t hp hd.ne_two hd.pow (RefFacts.mul_self_eq_one h)
  have hvF : v ∈ autFixed E t := hvt
  have hvord : orderOf v = p := orderOf_eq_of_ne_one hd hv1
  have hzv : Nat.card ↥(Subgroup.zpowers v) = p := by rw [Nat.card_zpowers, hvord]
  obtain ⟨c₀, hc₀F, hc₀v⟩ : ∃ c₀ ∈ autFixed E t, c₀ ∉ Subgroup.zpowers v := by
    by_contra hcon
    push Not at hcon
    have hle : autFixed E t ≤ Subgroup.zpowers v := fun c hc => hcon c hc
    have h1 := Subgroup.card_le_of_le hle
    rw [hC, hzv] at h1
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hc₀1 : c₀ ≠ 1 := fun h1 => hc₀v (h1 ▸ Subgroup.one_mem _)
  have hc₀t : t c₀ = c₀ := hc₀F
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_prime hd h.2
  have hc₀ord : orderOf c₀ = p := orderOf_eq_of_ne_one hd hc₀1
  have hxord : orderOf x = p := orderOf_eq_of_ne_one hd hx1
  have hzc : Nat.card ↥(Subgroup.zpowers c₀) = p := by rw [Nat.card_zpowers, hc₀ord]
  have hzx : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hcx : Subgroup.zpowers c₀ ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff, ← hFM]
    exact inf_le_inf (Subgroup.zpowers_le.2 hc₀F) (Subgroup.zpowers_le.2 hx)
  have hcardP : Nat.card ↥(Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) = p ^ 2 := by
    rw [card_sup_of_commute_disjoint (hcomm _ _) (disjoint_iff.2 hcx), hzc, hzx, pow_two]
  have hFix : autFixed E t = Subgroup.zpowers v ⊔ Subgroup.zpowers c₀ := by
    have hne : Subgroup.zpowers v ≠ Subgroup.zpowers c₀ := fun heq =>
      hc₀v (heq ▸ Subgroup.mem_zpowers c₀)
    have hdisj : Subgroup.zpowers v ⊓ Subgroup.zpowers c₀ = ⊥ :=
      inf_eq_bot_of_card_prime hp hzv hzc hne
    have hle : Subgroup.zpowers v ⊔ Subgroup.zpowers c₀ ≤ autFixed E t :=
      sup_le (Subgroup.zpowers_le.2 hvF) (Subgroup.zpowers_le.2 hc₀F)
    have hcs : Nat.card ↥(Subgroup.zpowers v ⊔ Subgroup.zpowers c₀) = p ^ 2 := by
      rw [card_sup_of_commute_disjoint (hcomm _ _) (disjoint_iff.2 hdisj), hzv, hzc, pow_two]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcs, hC])).symm
  have hvP : v ∉ Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x := by
    intro hvP
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute (hcomm _ _) hvP
    have haF : a ∈ autFixed E t := Subgroup.zpowers_le.2 hc₀F ha
    have hbF : b ∈ autFixed E t := by
      have : b = a⁻¹ * v := by rw [hab]; group
      rw [this]
      exact (autFixed E t).mul_mem ((autFixed E t).inv_mem haF) hvF
    have hbM : b ∈ autMoved E t := Subgroup.zpowers_le.2 hx hb
    have hb1 : b = 1 := by
      have : b ∈ autFixed E t ⊓ autMoved E t := ⟨hbF, hbM⟩
      rw [hFM] at this
      exact this
    rw [hb1, mul_one] at hab
    apply hc₀v
    have hzle : Subgroup.zpowers v ≤ Subgroup.zpowers c₀ := by
      rw [Subgroup.zpowers_le, hab]
      exact ha
    have heq : Subgroup.zpowers v = Subgroup.zpowers c₀ :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hzv, hzc])
    rw [heq]
    exact Subgroup.mem_zpowers c₀
  refine ⟨c₀, x, hc₀1, hc₀t, hx, hx1, hcardP, hFix, hvP, ?_⟩
  have hvz : Subgroup.zpowers v ⊓ (Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) = ⊥ := by
    have hd' : Nat.card ↥(Subgroup.zpowers v ⊓ (Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x)) ∣ p :=
      hzv ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd' with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hvP
      have e : Subgroup.zpowers v ⊓ (Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) =
          Subgroup.zpowers v := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzv])
      have : v ∈ Subgroup.zpowers v ⊓ (Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) := by
        rw [e]
        exact Subgroup.mem_zpowers v
      exact this.2
  rw [← Subgroup.card_eq_iff_eq_top,
    card_sup_of_commute_disjoint (hcomm _ _) (disjoint_iff.2 hvz), hzv, hcardP, hcard]
  ring

end CFSG.RankThree.PartOne.K133B
