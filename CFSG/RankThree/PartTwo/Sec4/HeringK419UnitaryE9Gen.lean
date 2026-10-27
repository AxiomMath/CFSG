module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

theorem exists_elemAbelian_nine_of_commuting {G : Type} [Group G] (x y : G) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hy (Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcardA : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have hcardB : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
  have hAB : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) ∣ 3 := by
      rw [← hcardB]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      haveI : Finite ↥(Subgroup.zpowers y) :=
        Nat.finite_of_card_ne_zero (by rw [hcardB]; norm_num)
      have hCeq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hcardB, h3]))
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := by
        rw [← hCeq]
        exact inf_le_left
      exact hy (hle (Subgroup.mem_zpowers y))
  have hpx : ∀ g ∈ Subgroup.zpowers x, g ^ 3 = 1 := fun g hg =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers hg).trans (dvd_of_eq hxo))
  have hpy : ∀ g ∈ Subgroup.zpowers y, g ^ 3 = 1 := fun g hg =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers hg).trans (dvd_of_eq hyo))
  have hXX : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers x, Commute a c := by
    rintro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact Commute.zpow_zpow (Commute.refl x) i j
  have hYY : ∀ b ∈ Subgroup.zpowers y, ∀ d ∈ Subgroup.zpowers y, Commute b d := by
    rintro b hb d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact Commute.zpow_zpow (Commute.refl y) i j
  have hXY : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, Commute a b := by
    rintro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact Commute.zpow_zpow (show Commute x y from hxy) i j
  have hkey : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y,
      ∀ c ∈ Subgroup.zpowers x, ∀ d ∈ Subgroup.zpowers y, Commute (a * b) (c * d) := by
    intro a ha b hb c hc d hd
    exact Commute.mul_right (Commute.mul_left (hXX a ha c hc) (hXY c hc b hb).symm)
      (Commute.mul_left (hXY a ha d hd) (hYY b hb d hd))
  have hcomm : ∀ (m : Subgroup.zpowers x) (n : Subgroup.zpowers y), Commute (m : G) (n : G) :=
    fun m n => hXY (m : G) m.2 (n : G) n.2
  let phi : Subgroup.zpowers x × Subgroup.zpowers y →* G :=
    (Subgroup.zpowers x).subtype.noncommCoprod (Subgroup.zpowers y).subtype hcomm
  have hphi : ∀ (a : Subgroup.zpowers x) (b : Subgroup.zpowers y),
      phi (a, b) = (a : G) * (b : G) := fun a b => rfl
  have hinj : Function.Injective phi := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
    rw [hphi] at h
    have hab : a * b = 1 := h
    have haB : a ∈ Subgroup.zpowers y := by
      rw [eq_inv_of_mul_eq_one_left hab]
      exact (Subgroup.zpowers y).inv_mem hb
    have ha1 : a = 1 := by
      have haAB : a ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y :=
        Subgroup.mem_inf.2 ⟨ha, haB⟩
      rw [hAB, Subgroup.mem_bot] at haAB
      exact haAB
    have hb1 : b = 1 := by
      rw [ha1, one_mul] at hab
      exact hab
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  refine ⟨phi.range, ?_, ?_⟩
  · show IsMulCommutative ↥phi.range ∧ ∀ g ∈ phi.range, g ^ 3 = 1
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      rintro ⟨u, hu⟩ ⟨v, hv⟩
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := MonoidHom.mem_range.1 hu
      obtain ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, rfl⟩ := MonoidHom.mem_range.1 hv
      apply Subtype.ext
      exact (hkey a ha b hb c hc d hd).eq
    · intro g hg
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := MonoidHom.mem_range.1 hg
      show (a * b) ^ 3 = 1
      rw [(hXY a ha b hb).mul_pow, hpx a ha, hpy b hb, one_mul]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_prod, hcardA, hcardB] <;> norm_num

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
