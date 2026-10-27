module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open StrongP

variable {H : Type*} [Group H] {p : ℕ} {Y : Subgroup H}

namespace StrongP

theorem exists_lift_mem_inf_conjSub {N : Subgroup H} [N.Normal] (hNY : N ≤ Y) {g : H}
    {x : H ⧸ N} (h1 : x ∈ Y.map (QuotientGroup.mk' N))
    (h2 : x ∈ conjSub (QuotientGroup.mk g) (Y.map (QuotientGroup.mk' N))) :
    ∃ y ∈ Y ⊓ conjSub g Y, QuotientGroup.mk' N y = x := by
  obtain ⟨y, hy, rfl⟩ := h1
  rw [mem_conjSub_iff] at h2
  obtain ⟨y', hy', hy'eq⟩ := h2
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, mem_conjSub_iff.mpr ?_⟩, rfl⟩
  have h3 : y'⁻¹ * (g⁻¹ * y * g) ∈ N := by
    have := QuotientGroup.eq.mp (by simpa using hy'eq : (QuotientGroup.mk y' : H ⧸ N) =
      QuotientGroup.mk (g⁻¹ * y * g))
    exact this
  have h4 : g⁻¹ * y * g = y' * (y'⁻¹ * (g⁻¹ * y * g)) := by group
  rw [h4]
  exact Y.mul_mem hy' (hNY h3)

end StrongP

theorem IsStronglyPEmbedded.map_quotient [Finite H] [Fact p.Prime]
    (hY : IsStronglyPEmbedded p Y)
    {N : Subgroup H} [N.Normal] (hNY : N ≤ Y) (hpN : ¬ p ∣ Nat.card N) :
    IsStronglyPEmbedded p (Y.map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    refine hY.1 (eq_top_iff.mpr fun g _ => ?_)
    have hg : QuotientGroup.mk' N g ∈ Y.map (QuotientGroup.mk' N) := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyg⟩ := hg
    have h1 : y⁻¹ * g ∈ N := QuotientGroup.eq.mp hyg
    have h2 : g = y * (y⁻¹ * g) := by group
    rw [h2]
    exact Y.mul_mem hy (hNY h1)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hY.2.1
    have hxN : (x : H) ∉ N := by
      intro hxN
      have hle : Subgroup.zpowers (x : H) ≤ N := Subgroup.zpowers_le.mpr hxN
      have := Subgroup.card_dvd_of_le hle
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx] at this
      exact hpN this
    have hxp : (QuotientGroup.mk' N (x : H)) ^ p = 1 := by
      rw [← map_pow]
      have : (x : H) ^ p = 1 := by
        have := pow_orderOf_eq_one x
        rw [hx] at this
        simpa using congrArg Subtype.val this
      rw [this, map_one]
    have hx1 : QuotientGroup.mk' N (x : H) ≠ 1 := fun h => hxN ((QuotientGroup.eq_one_iff _).mp h)
    have hord : orderOf (QuotientGroup.mk' N (x : H)) = p := orderOf_eq_prime hxp hx1
    have hmem : QuotientGroup.mk' N (x : H) ∈ Y.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ x.2
    have := orderOf_dvd_natCard (⟨_, hmem⟩ : Y.map (QuotientGroup.mk' N))
    rwa [Subgroup.orderOf_mk, hord] at this
  · intro gbar hgbar hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hg : g ∉ Y := fun hgY => hgbar (Subgroup.mem_map_of_mem _ hgY)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp x.2
    obtain ⟨y, hy, hyx⟩ := exists_lift_mem_inf_conjSub hNY hx1 (by simpa using hx2)
    refine hY.2.2 g hg ?_
    have hord : p ∣ orderOf y := by
      have h1 : orderOf (QuotientGroup.mk' N y) ∣ orderOf y := orderOf_map_dvd _ y
      have h2 : orderOf (QuotientGroup.mk' N y) = p := by
        rw [hyx]
        simpa using hx
      rwa [h2] at h1
    exact hord.trans (by
      simpa [Subgroup.orderOf_mk] using
        orderOf_dvd_natCard (⟨y, hy⟩ : (Y ⊓ conjSub g Y : Subgroup H)))

namespace StrongP

theorem card_map_quotient_of_coprime [Finite H] {E N : Subgroup H} [N.Normal] (hE : IsPGroup p E)
    [Fact p.Prime] (hpN : ¬ p ∣ Nat.card N) :
    Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hxE⟩ hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff _).mp (by simpa using hx)
    obtain ⟨k, hk⟩ := hE ⟨x, hxE⟩
    have hordx : orderOf x = 1 := by
      have h1 : orderOf x ∣ Nat.card N := by
        simpa [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
        simpa using congrArg Subtype.val hk)
      have hcop : Nat.Coprime (Nat.card N) (p ^ k) :=
        (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm)
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have : x = 1 := orderOf_eq_one_iff.mp hordx
    simp [this]
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hrange : ((QuotientGroup.mk' N).comp E.subtype).range = E.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at h
  exact h.symm

end StrongP

end CFSG.RankThree.PartOne
