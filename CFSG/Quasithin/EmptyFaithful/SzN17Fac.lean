module

public import CFSG.Quasithin.EmptyFaithful.SzN17Prod

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153L
open scoped commutatorElement

variable {Ω : Type} [Group Ω]

theorem mem_or_mul_mem_of_index_two {G N : Subgroup Ω} (hidx : (N.subgroupOf G).index = 2)
    {x y : Ω} (hx : x ∈ G) (hxN : x ∉ N) (hy : y ∈ G) : y ∈ N ∨ x⁻¹ * y ∈ N := by
  by_cases hyN : y ∈ N
  · exact Or.inl hyN
  · right
    have h := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x⁻¹, G.inv_mem hx⟩ : ↥G))
      (b := (⟨y, hy⟩ : ↥G))
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
    refine h.2 ?_
    exact iff_of_false (fun h1 => hxN (by simpa using N.inv_mem h1)) hyN

theorem mem_of_cube_of_index_two {G N : Subgroup Ω} (hidx : (N.subgroupOf G).index = 2) {z : Ω}
    (hz : z ∈ G) (hz3 : z ^ 3 = 1) : z ∈ N := by
  by_contra hzN
  have h := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨z, hz⟩ : ↥G)) (b := (⟨z, hz⟩ : ↥G))
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
  have hzz : z * z ∈ N := h.2 trivial
  apply hzN
  have : z = (z * z)⁻¹ := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = (z * z)⁻¹ := by rw [hz3]; group
  rw [this]
  exact N.inv_mem hzz

theorem orderOf_conj_eq (g x : Ω) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc] : SemiconjBy g x (g * x * g⁻¹))).symm

theorem centerTrivial_of_simple {G : Subgroup Ω} (hs : IsSimpleGroup ↥G)
    (hna : ∃ a b : ↥G, a * b ≠ b * a) : CenterTrivial G := by
  intro a haG hac
  have hcen : (⟨a, haG⟩ : ↥G) ∈ Subgroup.center ↥G :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hac g g.2)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥G) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    obtain ⟨c, d, hcd⟩ := hna
    have hc : c ∈ Subgroup.center ↥G := h ▸ Subgroup.mem_top c
    exact hcd ((Subgroup.mem_center_iff.1 hc d).symm)

theorem goodFactor_of_simple [Finite Ω] {H P G : Subgroup Ω} (hs : IsSimpleGroup ↥G)
    (hn : ¬ (Nat.card ↥G).Prime) : GoodFactor H P G ⊥ ∧ CenterTrivial G := by
  have hq : CFSG.IsQuasisimple ↥G := comp_quasisimple_of_simple hs hn
  have hperf : ⁅G, G⁆ = G := comp_perfect_of_isQuasisimple hq
  have hna : ∃ a b : ↥G, a * b ≠ b * a := InternalSec.exists_noncomm_of_isQuasisimple hq
  refine ⟨⟨bot_le, ?_, Or.inl rfl, ?_⟩, centerTrivial_of_simple hs hna⟩
  · exact (le_perfectCore_of_perfect le_rfl hperf).trans (le_sup_of_le_left le_sup_left)
  · intro Q hQ
    exfalso
    obtain ⟨hQG, hQn, hQc⟩ := hQ
    have hnorm : (Q.subgroupOf G).Normal :=
      ⟨fun n hn' g => Subgroup.mem_subgroupOf.2 (hQn g g.2 n hn')⟩
    obtain ⟨z, hzQ, hz1⟩ := exists_ne_one_of_card_three hQc
    rcases hs.eq_bot_or_eq_top_of_normal (Q.subgroupOf G) with h | h
    · have : (⟨z, hQG hzQ⟩ : ↥G) ∈ Q.subgroupOf G := hzQ
      rw [h, Subgroup.mem_bot] at this
      exact hz1 (congrArg Subtype.val this)
    · have hGQ : G ≤ Q := fun g hg => by
        have : (⟨g, hg⟩ : ↥G) ∈ Q.subgroupOf G := h ▸ Subgroup.mem_top _
        exact this
      have heq : Q = G := le_antisymm hQG hGQ
      apply hn
      have : Nat.card ↥G = 3 := by rw [← hQc, heq]
      rw [this]
      exact Nat.prime_three


theorem centerTrivial_of_card_six {G : Subgroup Ω} (h6 : Nat.card ↥G = 6)
    (hna : ∃ a b : ↥G, a * b ≠ b * a) : CenterTrivial G := by
  intro a haG hac
  by_contra ha1
  have hfin : Finite ↥G := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  have hcen : (⟨a, haG⟩ : ↥G) ∈ Subgroup.center ↥G :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hac g g.2)
  have hne : Subgroup.center ↥G ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hcen
    exact ha1 (congrArg Subtype.val hcen)
  have hcard : Nat.card ↥G = Nat.card (↥G ⧸ Subgroup.center ↥G) * Nat.card (Subgroup.center ↥G) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hc1 : Nat.card (Subgroup.center ↥G) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have hcpos : 0 < Nat.card (Subgroup.center ↥G) := Nat.card_pos
  have hqpos : 0 < Nat.card (↥G ⧸ Subgroup.center ↥G) := Nat.card_pos
  have hq3 : Nat.card (↥G ⧸ Subgroup.center ↥G) ≤ 3 := by
    by_contra hbig
    push Not at hbig
    have : 2 ≤ Nat.card (Subgroup.center ↥G) := by omega
    nlinarith
  have hcyc : IsCyclic (↥G ⧸ Subgroup.center ↥G) := by
    have hq : Nat.card (↥G ⧸ Subgroup.center ↥G) = 1 ∨ Nat.card (↥G ⧸ Subgroup.center ↥G) = 2 ∨
        Nat.card (↥G ⧸ Subgroup.center ↥G) = 3 := by omega
    rcases hq with h | h | h
    · have : Subsingleton (↥G ⧸ Subgroup.center ↥G) := (Nat.card_eq_one_iff_unique.1 h).1
      infer_instance
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card h
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h
  obtain ⟨c, d, hcd⟩ := hna
  have hcomm : IsMulCommutative ↥G :=
    (QuotientGroup.mk' (Subgroup.center ↥G)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
  exact hcd (hcomm.is_comm.comm c d)

theorem goodFactor_of_small [Finite Ω] {H P G : Subgroup Ω} (hP : IsSylowTwoOf P H) (hGH : G ≤ H)
    (hGn : ∀ h ∈ H, ∀ g ∈ G, h * g * h⁻¹ ∈ G) (hG6 : Nat.card ↥G ∣ 6) :
    ∃ Z : Subgroup Ω, GoodFactor H P G Z := by
  have hGnorm : (G.subgroupOf H).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hGn g g.2 n hn)⟩
  by_cases h3 : 3 ∣ Nat.card ↥G
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' (G := ↥G) 3 h3
    set e : Ω := (g : Ω) with he
    have he3 : orderOf e = 3 := by rw [he, Subgroup.orderOf_coe]; exact hg3
    have heG : e ∈ G := g.2
    have hecube : e ^ 3 = 1 := he3 ▸ pow_orderOf_eq_one e
    set Z : Subgroup Ω := Subgroup.zpowers e with hZ
    have hZG : Z ≤ G := Subgroup.zpowers_le.2 heG
    have hZc : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, he3]
    have hidxmul : Nat.card ↥G = 3 * (Z.subgroupOf G).index := by
      have h1 := Subgroup.card_mul_index (Z.subgroupOf G)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZG).toEquiv, hZc] at h1
      exact h1.symm
    have hidx12 : (Z.subgroupOf G).index = 1 ∨ (Z.subgroupOf G).index = 2 := by
      have h1 : 3 * (Z.subgroupOf G).index ∣ 3 * 2 := by
        rw [← hidxmul]; exact hG6
      have h2 : (Z.subgroupOf G).index ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
      exact (Nat.dvd_prime Nat.prime_two).1 h2
    have hZZ : ∀ x ∈ Z, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hecube, one_zpow]
    have hGZ : (Z.subgroupOf G).index = 1 → G ≤ Z := by
      intro h1 y hy
      have : (⟨y, hy⟩ : ↥G) ∈ Z.subgroupOf G := by
        rw [Subgroup.index_eq_one.1 h1]; exact Subgroup.mem_top _
      exact this
    have C1 : ∀ x ∈ G, x ^ 3 = 1 → x ∈ Z := by
      intro x hxG hx3
      rcases hidx12 with h1 | h2
      · exact hGZ h1 hxG
      · exact mem_of_cube_of_index_two h2 hxG hx3
    have C2 : ∀ Q : Subgroup Ω, IsNormalThree G Q → Q = Z := by
      intro Q hQ
      obtain ⟨z, hzQ, hz1⟩ := exists_ne_one_of_card_three hQ.2.2
      obtain ⟨hz3, hQz⟩ := eq_zpowers_of_card_three hQ.2.2 hzQ hz1
      have hzcube : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
      have hzZ : z ∈ Z := C1 z (hQ.1 hzQ) hzcube
      have hQle : Q ≤ Z := by rw [hQz]; exact Subgroup.zpowers_le.2 hzZ
      exact Subgroup.eq_of_le_of_card_ge hQle (by rw [hZc, hQ.2.2])
    have C3 : IsNormalThree H Z := by
      refine ⟨hZG.trans hGH, ?_, hZc⟩
      intro h hh q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have hconjG : h * e * h⁻¹ ∈ G := hGn h hh e heG
      have hconj3 : (h * e * h⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hecube]; group
      have hconjZ : h * e * h⁻¹ ∈ Z := C1 _ hconjG hconj3
      have : h * e ^ k * h⁻¹ = (h * e * h⁻¹) ^ k := conj_zpow.symm
      rw [this]
      exact Subgroup.zpow_mem _ hconjZ k
    have C4 : G ≤ perfectCore G ⊔ Z ⊔ P := by
      rcases hidx12 with h1 | h2
      · exact (hGZ h1).trans (le_sup_of_le_left le_sup_right)
      · have h2n : 2 ∣ Nat.card ↥G := by rw [hidxmul, h2]; exact ⟨3, by ring⟩
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨τ', hτ'⟩ := exists_prime_orderOf_dvd_card' (G := ↥G) 2 h2n
        set τ : Ω := (τ' : Ω) with hτdef
        have hτ2 : orderOf τ = 2 := by rw [hτdef, Subgroup.orderOf_coe]; exact hτ'
        have hτG : τ ∈ G := τ'.2
        have hτp : IsPGroup 2 (Subgroup.zpowers τ) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2]; norm_num)
        obtain ⟨h, hh, hle⟩ :=
          exists_conj_le_of_isSylowTwoOf hP (Subgroup.zpowers_le.2 (hGH hτG)) hτp
        set x : Ω := h * τ * h⁻¹ with hx
        have hxP : x ∈ P := by
          refine hle (mem_cjSub.2 ?_)
          have : h⁻¹ * x * h = τ := by rw [hx]; group
          rw [this]
          exact Subgroup.mem_zpowers τ
        have hxG : x ∈ G := hGn h hh τ hτG
        have hxo : orderOf x = 2 := by rw [hx, orderOf_conj_eq, hτ2]
        have hxZ : x ∉ Z := by
          intro hxZ
          have hx3 := hZZ x hxZ
          have hx2 : x ^ 2 = 1 := hxo ▸ pow_orderOf_eq_one x
          have hx1 : x = 1 := by
            calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
              _ = 1 := by rw [hx3, hx2]; group
          rw [hx1, orderOf_one] at hxo
          omega
        intro y hy
        rcases mem_or_mul_mem_of_index_two h2 hxG hxZ hy with hyZ | hyZ
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hyZ)
        · have : y = x * (x⁻¹ * y) := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxP)
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right hyZ))
    exact ⟨Z, hZG, C4, Or.inr C3, C2⟩
  · have hn12 : Nat.card ↥G = 1 ∨ Nat.card ↥G = 2 := by
      have hd : Nat.card ↥G ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hG6, by norm_num⟩
      have hd' : Nat.divisors 6 = {1, 2, 3, 6} := by decide
      rw [hd'] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (by rw [h]) h3
      · exact absurd (by rw [h]; norm_num) h3
    have hGp : IsPGroup 2 ↥G := by
      rcases hn12 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
      · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
    have hGP : G ≤ P := A4.le_of_normal_of_isSylowTwoOf hP hGH hGnorm hGp
    refine ⟨⊥, bot_le, hGP.trans le_sup_right, Or.inl rfl, ?_⟩
    intro Q hQ
    exfalso
    have : 3 ∣ Nat.card ↥G := hQ.2.2 ▸ Subgroup.card_dvd_of_le hQ.1
    exact h3 this

end CFSG.Quasithin.SzN17
