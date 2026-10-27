module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofKappa
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofNormD
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofEleven
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2112TwoGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ x ∈ Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G),
        x * d * x⁻¹ = d → x * c * x⁻¹ ≠ c * d

@[expose] def KF2112HJReal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), Nonempty (lBar L ≃* NativeSporadic.J2) →
    ∀ d ∈ L, d ≠ 1 → d ^ 3 = 1 → ∃ ℓ ∈ L, ℓ * d * ℓ⁻¹ = d⁻¹

@[expose] def Item2112NoFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G)
    (E' U' : Subgroup G) (b : G) (K : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → Sec21Pair G A E' U' b K → IsList218 K →
      ∀ d ∈ A, d ≠ 1 → IsCentral218 K d → ∀ x : G, x * c * x⁻¹ ≠ d

namespace Item2113Res2Proof

open Subgroup

set_option maxRecDepth 10000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem fixC_matrix : ∀ p q : ZMod 3 × ZMod 3, (∀ v, lin p q v = 0 → v = 0) → q.1 = 0 →
    ¬ (lin p q (0, 1) = (0, 1) ∧ lin p q (1, 0) = (1, 1)) →
    ¬ (lin p q (lin p q (0, 1)) = (0, 1) ∧ lin p q (lin p q (1, 0)) = (1, 1)) →
    ¬ (lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2) (0, 1)))) = (0, 1) ∧
        lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2) (1, 0)))) = (1, 1)) →
    ¬ (lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2)
          (lin p q (lin (1, 0) (0, 2) (0, 1)))))))) = (0, 1) ∧
        lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2) (lin p q (lin (1, 0) (0, 2)
          (lin p q (lin (1, 0) (0, 2) (1, 0)))))))) = (1, 1)) →
    ¬ (lin p q (lin (1, 0) (0, 2) (0, 1)) = (0, 1) ∧
        lin p q (lin (1, 0) (0, 2) (1, 0)) = (1, 1)) →
    ¬ (lin p q (lin p q (lin p q (lin p q (0, 1)))) = (0, 1) ∧
        lin p q (lin p q (lin p q (lin p q (1, 0)))) = (1, 1)) →
    p.2 = 0 := by
  decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem nd_matrix : ∀ p q : ZMod 3 × ZMod 3, (∀ v, lin p q v = 0 → v = 0) →
    (q.1 = 0 → p.2 = 0) → (lin p q (1, 0)).1 ≠ 0 → (lin p q (0, 1)).2 ≠ 0 →
    (lin p q (lin p q (1, 0))).1 ≠ 0 → (lin p q (lin p q (0, 1))).2 ≠ 0 →
    (lin p q (lin (1, 0) (0, 2) (lin p q (1, 0)))).1 ≠ 0 →
    (lin p q (lin (1, 0) (0, 2) (lin p q (0, 1)))).2 ≠ 0 →
    p.2 = 0 := by
  decide

theorem unique_matrix : ∀ v : ZMod 3 × ZMod 3, v ≠ 0 →
    (lin (1, 0) (0, 2) v = 0 ∨ lin (1, 0) (0, 2) v = v ∨
      lin (1, 0) (0, 2) v = (2 * v.1, 2 * v.2)) → v.1 = 0 ∨ v.2 = 0 := by
  decide

variable {G : Type} [Group G]

theorem mem_zpowers_cube {y z : G} (h3 : y ^ 3 = 1) (hz : z ∈ zpowers y) :
    z = 1 ∨ z = y ∨ z = y ^ 2 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have h3' : y ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  rw [zpow_eq_zpow_emod k h3']
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · left; rw [h, zpow_zero]
  · right; left; rw [h, zpow_one]
  · right; right; rw [h]; exact zpow_natCast y 2

theorem mem_normalizer_zpowers [Finite G] {x c : G} (h : x * c * x⁻¹ ∈ zpowers c) :
    x ∈ normalizer ((zpowers c : Subgroup G) : Set G) := by
  apply Item2113Proof.mem_normalizer_of_map_le
  rw [MonoidHom.map_zpowers, zpowers_le]
  exact h

theorem mem_normalizer_of_inv [Finite G] {c d ℓ : G} (hℓc : ℓ * c * ℓ⁻¹ = c)
    (hℓd : ℓ * d * ℓ⁻¹ = d⁻¹) :
    ℓ ∈ normalizer (closure ({c, d} : Set G) : Set G) ∧
      ℓ ∈ normalizer ((zpowers d : Subgroup G) : Set G) := by
  refine ⟨Item2113Proof.mem_normalizer_of_map_le ?_, mem_normalizer_zpowers ?_⟩
  · rw [MonoidHom.map_closure, Set.image_pair, closure_le]
    rintro y (rfl | rfl)
    · show ℓ * c * ℓ⁻¹ ∈ _
      rw [hℓc]
      exact subset_closure (Set.mem_insert c _)
    · show ℓ * d * ℓ⁻¹ ∈ _
      rw [hℓd]
      exact inv_mem (subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d)))
  · rw [hℓd]
    exact inv_mem (mem_zpowers d)

structure DData (c d ℓ : G) : Prop where
  c3 : c ^ 3 = 1
  d3 : d ^ 3 = 1
  comm : Commute c d
  c1 : c ≠ 1
  dc : d ∉ zpowers c
  cd : c ∉ zpowers d
  ℓc : ℓ * c * ℓ⁻¹ = c
  ℓd : ℓ * d * ℓ⁻¹ = d⁻¹

namespace DData

variable {c d ℓ : G} (h : DData c d ℓ)
include h

theorem d1 : d ≠ 1 := fun h1 => h.dc (h1 ▸ one_mem _)

theorem inj : Function.Injective (kappa c d) := kappa_injective h.c3 h.d3 h.comm h.c1 h.dc

theorem conj_ℓ (v : ZMod 3 × ZMod 3) :
    ℓ * kappa c d v * ℓ⁻¹ = kappa c d (lin (1, 0) (0, 2) v) :=
  conj_kappa h.c3 h.d3 h.comm (by rw [h.ℓc, kappa_one_zero])
    (by rw [h.ℓd, kappa_zero_two h.d3]) v

theorem conj_ℓinv (v : ZMod 3 × ZMod 3) :
    ℓ⁻¹ * kappa c d v * ℓ⁻¹⁻¹ = kappa c d (lin (1, 0) (0, 2) v) := by
  have hc : ℓ⁻¹ * c * ℓ⁻¹⁻¹ = c := by
    rw [inv_inv]
    calc ℓ⁻¹ * c * ℓ = ℓ⁻¹ * (ℓ * c * ℓ⁻¹) * ℓ := by rw [h.ℓc]
      _ = c := by group
  have e1 : ℓ⁻¹ * d⁻¹ * ℓ = d := by
    rw [← h.ℓd]
    group
  have hd : ℓ⁻¹ * d * ℓ⁻¹⁻¹ = d⁻¹ := by
    rw [inv_inv]
    calc ℓ⁻¹ * d * ℓ = (ℓ⁻¹ * d⁻¹ * ℓ)⁻¹ := by group
      _ = d⁻¹ := by rw [e1]
  exact conj_kappa h.c3 h.d3 h.comm (by rw [hc, kappa_one_zero])
    (by rw [hd, kappa_zero_two h.d3]) v

theorem lin_inj {x : G} {p q : ZMod 3 × ZMod 3}
    (hM : ∀ v, x * kappa c d v * x⁻¹ = kappa c d (lin p q v)) (v : ZMod 3 × ZMod 3)
    (hv : lin p q v = 0) : v = 0 := by
  have h1 : x * kappa c d v * x⁻¹ = 1 := by rw [hM, hv, kappa_zero]
  have h2 : kappa c d v = kappa c d 0 := by
    rw [kappa_zero]
    have := congrArg (fun y => x⁻¹ * y * x) h1
    simpa [mul_assoc] using this
  exact h.inj h2

theorem conj_mem_of_twoGroup [Finite G]
    (hTG : ∀ x ∈ normalizer (closure ({c, d} : Set G) : Set G), x * d * x⁻¹ = d →
      x * c * x⁻¹ ≠ c * d)
    {x : G} (hxD : x ∈ normalizer (closure ({c, d} : Set G) : Set G))
    (hxd : x ∈ normalizer ((zpowers d : Subgroup G) : Set G)) :
    x * c * x⁻¹ ∈ zpowers c := by
  have hℓN := mem_normalizer_of_inv h.ℓc h.ℓd
  obtain ⟨p, q, hp, hq, hM⟩ := exists_conj_kappa h.c3 h.d3 h.comm hxD
  have bad : ∀ g ∈ normalizer (closure ({c, d} : Set G) : Set G),
      ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3, (∀ v, g * kappa c d v * g⁻¹ = kappa c d (f v)) →
        ¬ (f (0, 1) = (0, 1) ∧ f (1, 0) = (1, 1)) := by
    rintro g hg f hf ⟨h01, h10⟩
    apply hTG g hg
    · calc g * d * g⁻¹ = g * kappa c d (0, 1) * g⁻¹ := by rw [kappa_zero_one]
        _ = d := by rw [hf, h01, kappa_zero_one]
    · calc g * c * g⁻¹ = g * kappa c d (1, 0) * g⁻¹ := by rw [kappa_one_zero]
        _ = c * d := by rw [hf, h10, kappa_one_one]
  have hq1 : q.1 = 0 := by
    rw [← kappa_mem_zpowers_right_iff h.d3 h.inj, hq]
    exact (mem_normalizer_iff.mp hxd d).mp (mem_zpowers d)
  have hL := h.conj_ℓ
  have hLi := h.conj_ℓinv
  have hx2 := conj_kappa_mul hM hM
  have hxL := conj_kappa_mul hM hL
  have hxLx := conj_kappa_mul hxL hM
  have hw3 := conj_kappa_mul hxLx hLi
  have hw4 := conj_kappa_mul hw3 hw3
  have hx4 := conj_kappa_mul hx2 hx2
  have hxℓN := mul_mem hxD hℓN.1
  have hw3N := mul_mem (mul_mem hxℓN hxD) (inv_mem hℓN.1)
  have hp2 := fixC_matrix p q (h.lin_inj hM) hq1 (bad x hxD _ hM) (bad _ (mul_mem hxD hxD) _ hx2)
    (bad _ hw3N _ hw3) (bad _ (mul_mem hw3N hw3N) _ hw4) (bad _ hxℓN _ hxL)
    (bad _ (mul_mem (mul_mem hxD hxD) (mul_mem hxD hxD)) _ hx4)
  rw [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj]
  exact hp2

theorem eq_of_normalizes [Finite G] {Y : Subgroup G} (hYD : Y ≤ closure ({c, d} : Set G))
    (hY3 : Nat.card Y = 3) (hℓY : ℓ ∈ normalizer (Y : Set G)) :
    Y = zpowers c ∨ Y = zpowers d := by
  have hne : Y ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hY3
    omega
  obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  obtain ⟨v, rfl⟩ := exists_kappa h.c3 h.d3 h.comm (hYD hyY)
  have hv0 : v ≠ 0 := fun h0 => hy1' (by rw [h0, kappa_zero])
  have hy3 : kappa c d v ^ 3 = 1 := by
    rw [← kappa_nsmul h.c3 h.d3 h.comm]
    have h3a : ∀ a : ZMod 3, (3 : ℕ) • a = 0 := by decide
    have : (3 : ℕ) • v = 0 := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, h3a]
    rw [this, kappa_zero]
  have hYeq : Y = zpowers (kappa c d v) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine (eq_of_le_of_card_ge (zpowers_le.mpr hyY) ?_).symm
    rw [hY3, Nat.card_zpowers, orderOf_eq_prime hy3 hy1']
  have hmem : ℓ * kappa c d v * ℓ⁻¹ ∈ zpowers (kappa c d v) := by
    rw [← hYeq]
    exact (mem_normalizer_iff.mp hℓY _).mp hyY
  rw [h.conj_ℓ] at hmem
  have hcases : lin (1, 0) (0, 2) v = 0 ∨ lin (1, 0) (0, 2) v = v ∨
      lin (1, 0) (0, 2) v = (2 * v.1, 2 * v.2) := by
    rcases mem_zpowers_cube hy3 hmem with h1 | h1 | h1
    · left
      exact h.inj (h1.trans kappa_zero.symm)
    · right; left
      exact h.inj h1
    · right; right
      apply h.inj
      rw [h1, ← kappa_nsmul h.c3 h.d3 h.comm]
      congr 1
      ext <;> simp [nsmul_eq_mul]
  rcases unique_matrix v hv0 hcases with h1 | h2
  · right
    rw [hYeq]
    have hm : kappa c d v ∈ zpowers d := (kappa_mem_zpowers_right_iff h.d3 h.inj v).mpr h1
    exact zpowers_eq_of_mem h.d3 hm hy1'
  · left
    rw [hYeq]
    have hm : kappa c d v ∈ zpowers c := (kappa_mem_zpowers_left_iff h.c3 h.inj v).mpr h2
    exact zpowers_eq_of_mem h.c3 hm hy1'
where
  zpowers_eq_of_mem {x y : G} (hx3 : x ^ 3 = 1) (hy : y ∈ zpowers x) (hy1 : y ≠ 1) :
      zpowers y = zpowers x := by
    apply le_antisymm (zpowers_le.mpr hy)
    rw [zpowers_le]
    rcases mem_zpowers_cube hx3 hy with h1 | h1 | h1
    · exact absurd h1 hy1
    · rw [h1]; exact mem_zpowers x
    · have : (x ^ 2) ^ 2 = x := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
      rw [← this, ← h1]
      exact pow_mem (mem_zpowers y) 2

theorem conj_mem_of_noFusion [Finite G]
    (hX : ∀ x ∈ normalizer (closure ({c, d} : Set G) : Set G),
      x ∈ normalizer ((zpowers d : Subgroup G) : Set G) → x * c * x⁻¹ ∈ zpowers c)
    (hNF₁ : ∀ y : G, y * c * y⁻¹ ∉ zpowers d) (hNF₂ : ∀ y : G, y * d * y⁻¹ ∉ zpowers c)
    {x : G} (hxD : x ∈ normalizer (closure ({c, d} : Set G) : Set G)) :
    x * c * x⁻¹ ∈ zpowers c := by
  obtain ⟨p, q, hp, hq, hM⟩ := exists_conj_kappa h.c3 h.d3 h.comm hxD
  have hL := h.conj_ℓ
  have hx2 := conj_kappa_mul hM hM
  have hxL := conj_kappa_mul hM hL
  have hxLx := conj_kappa_mul hxL hM
  have c_not : ∀ y : G, ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3,
      (∀ v, y * kappa c d v * y⁻¹ = kappa c d (f v)) → (f (1, 0)).1 ≠ 0 := by
    intro y f hf h0
    apply hNF₁ y
    rw [← kappa_one_zero (c := c) (d := d), hf, kappa_mem_zpowers_right_iff h.d3 h.inj]
    exact h0
  have d_not : ∀ y : G, ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3,
      (∀ v, y * kappa c d v * y⁻¹ = kappa c d (f v)) → (f (0, 1)).2 ≠ 0 := by
    intro y f hf h0
    apply hNF₂ y
    rw [← kappa_zero_one (c := c) (d := d), hf, kappa_mem_zpowers_left_iff h.c3 h.inj]
    exact h0
  have hfix : q.1 = 0 → p.2 = 0 := by
    intro hq1
    have hxd : x ∈ normalizer ((zpowers d : Subgroup G) : Set G) := by
      apply mem_normalizer_zpowers
      rw [← hq, kappa_mem_zpowers_right_iff h.d3 h.inj]
      exact hq1
    have := hX x hxD hxd
    rwa [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj] at this
  have hp2 := nd_matrix p q (h.lin_inj hM) hfix (c_not x _ hM) (d_not x _ hM) (c_not _ _ hx2)
    (d_not _ _ hx2) (c_not _ _ hxLx) (d_not _ _ hxLx)
  rw [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj]
  exact hp2

end DData

section Pairs


theorem exists_dData [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5) (hReal : KF2112HJReal)
    {A E U L : Subgroup G} {c d : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdcen : IsCentral218 L d) : ∃ ℓ ∈ L, DData c d ℓ := by
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hdL := Item2113Proof.mem_of_isCentral218 hdcen
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcd : Commute c d := congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hcd' : c ∉ zpowers d := fun h => hcL ((zpowers_le.mpr hdL) h)
  have hdc : d ∉ zpowers c := by
    intro h
    apply hcd'
    exact (DData.eq_of_normalizes.zpowers_eq_of_mem hc3 h hd1) ▸ mem_zpowers c
  obtain ⟨ℓ, hℓL, hℓd⟩ : ∃ ℓ ∈ L, ℓ * d * ℓ⁻¹ = d⁻¹ := by
    rcases starOf_cases_of_isList218 h211 hpair hL with ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨hJ, -⟩
    · obtain ⟨ℓ, hℓL, hinv⟩ := exists_inv_of_isList218 h211 h45 hpair hL hS
      exact ⟨ℓ, hℓL, hinv d ⟨hdA, hdL⟩⟩
    · obtain ⟨ℓ, hℓL, hinv⟩ := exists_inv_of_isList218 h211 h45 hpair hL (Or.inl hS)
      exact ⟨ℓ, hℓL, hinv d ⟨hdA, hdL⟩⟩
    · exact hReal G L hJ d hdL hd1 hd3
  have hℓc : ℓ * c * ℓ⁻¹ = c := by
    rw [mem_centralizer_singleton_iff.mp (hLc hℓL), mul_inv_cancel_right]
  exact ⟨ℓ, hℓL, ⟨hc3, hd3, hcd, hc1, hdc, hcd', hℓc, hℓd⟩⟩

theorem item2112Unique_of (h211 : Item211) (h45 : Sec4.Item4_5) (hTG : Item2112TwoGroup)
    (hReal : KF2112HJReal) : Item2112Unique := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen Y hYD hY3
  obtain ⟨ℓ, -, hD⟩ := exists_dData h211 h45 hReal hpair hL hdA hd1 hdcen
  have hTG' := hTG G A E U c L hpair hL d hdA hd1 hdcen
  constructor
  · intro hX
    exact hD.eq_of_normalizes hYD hY3 (hX (mem_normalizer_of_inv hD.ℓc hD.ℓd))
  · rintro (rfl | rfl)
    · rintro x ⟨hxD, hxd⟩
      exact mem_normalizer_zpowers (hD.conj_mem_of_twoGroup hTG' hxD hxd)
    · exact inf_le_right

theorem item2112ND_of (h211 : Item211) (h45 : Sec4.Item4_5) (hTG : Item2112TwoGroup)
    (hReal : KF2112HJReal) (hNF : Item2112NoFusion) : Item2112ND := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen x hxD
  obtain ⟨ℓ, -, hD⟩ := exists_dData h211 h45 hReal hpair hL hdA hd1 hdcen
  have hTG' := hTG G A E U c L hpair hL d hdA hd1 hdcen
  have hdinv : IsCentral218 L d⁻¹ :=
    Item2113Proof.isCentral218_of_zpowers_eq hdcen zpowers_inv
  have hNF₀ : ∀ y : G, y * c * y⁻¹ ≠ d := hNF G A E U c L E U c L hpair hL hpair hL d hdA hd1 hdcen
  have hNF₀' : ∀ y : G, y * c * y⁻¹ ≠ d⁻¹ := hNF G A E U c L E U c L hpair hL hpair hL d⁻¹
    (inv_mem hdA) (inv_ne_one.mpr hd1) hdinv
  have hNF₁ : ∀ y : G, y * c * y⁻¹ ∉ zpowers d := by
    intro y hy
    rcases mem_zpowers_cube hD.d3 hy with h1 | h1 | h1
    · apply hD.c1
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    · exact hNF₀ y h1
    · exact hNF₀' y (h1.trans (sq_eq_inv_of_cube hD.d3))
  have hNF₂ : ∀ y : G, y * d * y⁻¹ ∉ zpowers c := by
    intro y hy
    rcases mem_zpowers_cube hD.c3 hy with h1 | h1 | h1
    · apply hD.d1
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    · apply hNF₀ y⁻¹
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simp only [inv_inv]
      simpa [mul_assoc] using this.symm
    · apply hNF₀' y⁻¹
      rw [sq_eq_inv_of_cube hD.c3] at h1
      have h2 : y * d⁻¹ * y⁻¹ = c := by
        rw [show y * d⁻¹ * y⁻¹ = (y * d * y⁻¹)⁻¹ by group, h1, inv_inv]
      have := congrArg (fun z => y⁻¹ * z * y) h2
      simp only [inv_inv]
      simpa [mul_assoc] using this.symm
  exact mem_normalizer_zpowers (hD.conj_mem_of_noFusion
    (fun x hx hxd => hD.conj_mem_of_twoGroup hTG' hx hxd) hNF₁ hNF₂ hxD)

end Pairs

theorem item218FinalD_of (hNF : Item2112NoFusion) : Item218FinalD := by
  intro G _ _ A E U c L U₀ b K hpair hL _ _ hpair' hK _ _ _ _ _ _ _ hccen _ _
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  exact hNF G A E U c L E U₀ b K hpair hL hpair' hK c (hpair.mem_E.2 hpairs.1.1) hpairs.2.1
    hccen 1 (by group)

theorem item2112TwoGroup_of_mem_W (h2 : Item2110Two) {G : Type} [Group G] [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdcen : IsCentral218 L d) (hdc : d ∉ zpowers c) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxd : x * d * x⁻¹ = d) : x * c * x⁻¹ ≠ c * d := by
  intro hxc
  have hAe := hpair.mem_S.1.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  obtain ⟨k, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3
    (by norm_num)
  have hxC : x ∈ centralizer ({d} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [hxd]
  have hxm : x ^ m ∈ normalizer (A : Set G) ⊓ centralizer ({d} : Set G) :=
    ⟨pow_mem hxA m, pow_mem hxC m⟩
  have hxO : x ^ m ∈ CFSG.GH74.GLS.oPrimeResidualOf 3
      (normalizer (A : Set G) ⊓ centralizer ({d} : Set G)) := by
    refine ⟨⟨x ^ m, hxm⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
    apply Subtype.ext
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hH := h2 G A E U c L hpair hL d hdA hd1 hdcen hxO
  have hpow : ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = c * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * c * x⁻¹ * (x * d * x⁻¹) ^ n := by rw [ih, conj_pow]; group
        _ = c * d ^ (n + 1) := by rw [hxc, hxd, pow_succ', mul_assoc]
  have hmem : x ^ m * c * (x ^ m)⁻¹ ∈ zpowers c :=
    (mem_normalizer_iff.mp hH c).mp (mem_zpowers c)
  rw [hpow m] at hmem
  have hdm : d ^ m ∈ zpowers c := by
    have := mul_mem (inv_mem (mem_zpowers c)) hmem
    rwa [inv_mul_cancel_left] at this
  apply hdc
  have h' := Item2113Proof.mem_zpowers_pow hd3 hm3
  exact (zpowers_le.mpr hdm) h'

end Item2113Res2Proof

end CFSG.RankThree.PartTwo.Sec21
