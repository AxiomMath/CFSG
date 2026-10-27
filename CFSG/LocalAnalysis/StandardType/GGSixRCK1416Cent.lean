module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs

public section

namespace CFSG.StandardType.RCKC1

theorem rck_cent96At_false_of_le {X : Type} [Group X] [Finite X] {J T : Subgroup X} {r : X}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hC : Cent96At J r) (hTJ : T ≤ J)
    (hTr : ∀ t ∈ T, t * r = r * t) (hT : Nat.card T = 64) : False := by
  obtain ⟨rJ, hrJ, hcard⟩ := hC
  change Nat.card (Subgroup.centralizer
    ({QuotientGroup.mk' (Subgroup.center ↥J) rJ} : Set (↥J ⧸ Subgroup.center ↥J))) = 96 at hcard
  set π := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set T' : Subgroup ↥J := T.subgroupOf J with hT'def
  have hT' : Nat.card T' = 64 := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv
  have hinj : ∀ a ∈ T', ∀ b ∈ T', π a = π b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ Subgroup.center ↥J := by
      rw [← QuotientGroup.eq]
      exact hab
    have h1 : orderOf (a⁻¹ * b) ∣ 64 := by
      rw [← hT']
      exact Subgroup.orderOf_dvd_natCard T' (T'.mul_mem (T'.inv_mem ha) hb)
    have h2 : orderOf (a⁻¹ * b) ∣ Nat.card (Subgroup.center ↥J) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have hcop : Nat.Coprime 64 (Nat.card (Subgroup.center ↥J)) := by
      have : Nat.Coprime 2 (Nat.card (Subgroup.center ↥J)) := Nat.coprime_two_left.2 hZ
      simpa using Nat.Coprime.pow_left 6 this
    have h3 : orderOf (a⁻¹ * b) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h3
    exact h3
  set T'' : Subgroup (↥J ⧸ Subgroup.center ↥J) := T'.map π with hT''def
  have hT'' : Nat.card T'' = 64 := by
    rw [← hT']
    symm
    refine Nat.card_eq_of_bijective (fun t : T' => (⟨π t, Subgroup.mem_map_of_mem π t.2⟩ : T''))
      ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hle : T'' ≤ Subgroup.centralizer ({π rJ} : Set (↥J ⧸ Subgroup.center ↥J)) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htr : rJ * t = t * rJ := by
      apply Subtype.ext
      have := hTr (t : X) (Subgroup.mem_subgroupOf.1 ht)
      simp only [Subgroup.coe_mul, hrJ]
      exact this.symm
    rw [← map_mul, ← map_mul, htr]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hT'', hcard] at hdvd
  norm_num at hdvd

end CFSG.StandardType.RCKC1
