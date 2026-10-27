module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48Gen
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BComm
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

open IsoAux
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem two_three_one {w : G} {k : ℕ} (h2 : w ^ 2 ^ k = 1) (h3 : w ^ 3 = 1) : w = 1 := by
  have hd1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have : orderOf w ∣ 1 := hcop ▸ Nat.dvd_gcd hd1 hd2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem E_cen_2sub {b c : G} (hE3 : ∀ w ∈ Subgroup.closure ({b, c} : Set G), w ^ 3 = 1)
    (hD : Cen (b * c) ≤ Nor (Subgroup.closure ({b, c} : Set G))) {V : Subgroup G}
    (hV : IsPGroup 2 V) (hVD : V ≤ Cen (b * c)) (hb : b ∈ Nor V) : V ≤ Cen b ⊓ Cen c := by
  have hbE : b ∈ Subgroup.closure ({b, c} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ V, x * b = b * x := by
    intro x hx
    have hxN : x ∈ Nor (Subgroup.closure ({b, c} : Set G)) := hD (hVD hx)
    have h1 : x * b * x⁻¹ ∈ Subgroup.closure ({b, c} : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hxN b).1 hbE
    have hE : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.closure ({b, c} : Set G) :=
      mul_mem h1 (inv_mem hbE)
    have h2 : b * x⁻¹ * b⁻¹ ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 hb x⁻¹).1 (inv_mem hx)
      simpa using this
    have hV' : x * b * x⁻¹ * b⁻¹ ∈ V := by
      have := mul_mem hx h2
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hV ⟨_, hV'⟩
    have hw3 := hE3 _ hE
    have h1' : x * b * x⁻¹ * b⁻¹ = 1 := two_three_one (congrArg Subtype.val hk) hw3
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h1', one_mul]
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx), ?_⟩
  have hxD : x * (b * c) = (b * c) * x := Subgroup.mem_centralizer_singleton_iff.1 (hVD hx)
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have hxb := hcomm x hx
  have : b * (x * c) = b * (c * x) := by
    calc b * (x * c) = x * b * c := by rw [← mul_assoc, ← hxb, mul_assoc]
      _ = x * (b * c) := by rw [mul_assoc]
      _ = (b * c) * x := hxD
      _ = b * (c * x) := by rw [mul_assoc]
  exact mul_left_cancel this

theorem hD_conj {x y m : G} (hD : Cen (x * y) ≤ Nor (Subgroup.closure ({x, y} : Set G))) :
    Cen ((m * x * m⁻¹) * (m * y * m⁻¹)) ≤
      Nor (Subgroup.closure ({m * x * m⁻¹, m * y * m⁻¹} : Set G)) := by
  intro g hg
  rw [← conjBy_closure_pair, mem_nor_conjBy]
  apply hD
  have e : (m * x * m⁻¹) * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := by group
  rw [e, ← conjBy_cen, mem_conjBy_iff] at hg
  exact hg

theorem mem_closure_pair_comm {b c a : G} (hbc : b * c = c * b)
    (ha : a ∈ Subgroup.closure ({b, c} : Set G)) : ∃ i j : ℤ, a = b ^ i * c ^ j := by
  have hcomm : ∀ i j : ℤ, c ^ j * b ^ i = b ^ i * c ^ j := fun i j =>
    ((Commute.zpow_zpow (show Commute b c from hbc) i j).eq).symm
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff.1 hx]; exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨i', j', rfl⟩ := ihy
    refine ⟨i + i', j + j', ?_⟩
    rw [zpow_add, zpow_add]
    calc b ^ i * c ^ j * (b ^ i' * c ^ j') = b ^ i * (c ^ j * b ^ i') * c ^ j' := by group
      _ = b ^ i * (b ^ i' * c ^ j) * c ^ j' := by rw [hcomm]
      _ = b ^ i * b ^ i' * (c ^ j * c ^ j') := by group
  | inv x _ ih =>
    obtain ⟨i, j, rfl⟩ := ih
    refine ⟨-i, -j, ?_⟩
    rw [zpow_neg, zpow_neg, mul_inv_rev]
    have := hcomm (-i) (-j)
    rw [zpow_neg, zpow_neg] at this
    exact this

theorem zpow_emod3 {c : G} (hc : c ^ 3 = 1) (k : ℤ) : c ^ k = c ^ (k % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
  have : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc
  rw [this, one_zpow, mul_one]

theorem zpow_eq_of_mod {c : G} (hc : c ^ 3 = 1) {i j : ℤ} (h : j % 3 = i % 3) : c ^ j = c ^ i := by
  rw [zpow_emod3 hc j, zpow_emod3 hc i, h]

theorem comm_of_comm_zpow {z x : G} (hz : z ^ 3 = 1) {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k)
    (h : x * z ^ k = z ^ k * x) : x * z = z * x := by
  have h1 : z ^ k ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 h.symm
  have h2 : z ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [zpow_emod3 hz k] at h1
    have h3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h3 | h3
    · rw [h3, zpow_one] at h1; exact h1
    · rw [h3] at h1
      have h4 : z = (z ^ (2 : ℤ)) ^ 2 := by
        rw [← zpow_natCast, ← zpow_mul]
        have h5 : z ^ ((4 : ℕ) : ℤ) = z * z ^ 3 := by
          rw [zpow_natCast, ← pow_succ']
        rw [hz, mul_one] at h5
        rw [show (2 : ℤ) * ((2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, h5]
      rw [h4]; exact Subgroup.pow_mem _ h1 2
  exact (Subgroup.mem_centralizer_singleton_iff.1 h2).symm

theorem cen_inv (c : G) : Cen c⁻¹ = Cen c := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := (Commute.inv_right (show Commute x c⁻¹ from h)).eq
    simpa using this
  · intro h
    exact (Commute.inv_right (show Commute x c from h)).eq

theorem nor_inf {H K : Subgroup G} {g : G} (hH : g ∈ Nor H) (hK : g ∈ Nor K) : g ∈ Nor (H ⊓ K) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH x, hK x]

theorem isEA_of (p : ℕ) {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hp : ∀ x ∈ E, x ^ p = 1) : IsElementaryAbelian p E := by
  have hH : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hp a a.2)
  have hc : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  exact
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hH }

structure CoreData (b c n : G) (B X U : Subgroup G) : Prop where
  hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  hB3 : ∀ x ∈ B, x ^ 3 = 1
  hbB : b ∈ B
  hcB : c ∈ B
  hb : orderOf b = 3
  hc : orderOf c = 3
  hcb : c ∉ Subgroup.zpowers b
  hX : IsPGroup 2 X
  hBX : B ≤ Nor X
  hXb : X ⊓ Cen b = U
  hUEA : EA2 U
  hD1 : Cen (b * c) ≤ Nor (Subgroup.closure ({b, c} : Set G))
  hD2 : Cen (b * c⁻¹) ≤ Nor (Subgroup.closure ({b, c⁻¹} : Set G))
  hn : n ∈ Nor B
  hnc : n * c * n⁻¹ = b
  hPi : ∀ Y : Subgroup G, Y ≤ Cen b → IsPGroup 2 Y → B ≤ Nor Y → EA2 Y ∧ Nat.card Y ≤ 16
  hU16 : Nat.card U = 16
  hUc4 : Nat.card ↥(U ⊓ Cen c) = 4

namespace CoreData

variable {b c n : G} {B X U : Subgroup G} (d : CoreData b c n B X U)

include d

theorem hUX : U ≤ X := d.hXb ▸ inf_le_left

theorem hUb : U ≤ Cen b := d.hXb ▸ inf_le_right

theorem hbN : b ∈ Nor X := d.hBX d.hbB

theorem hcN : c ∈ Nor X := d.hBX d.hcB

theorem c3 : c ^ 3 = 1 := d.hB3 c d.hcB

theorem b3 : b ^ 3 = 1 := d.hB3 b d.hbB

theorem bcomm : b * c = c * b := d.hBcomm b d.hbB c d.hcB

theorem nor_inf_cen {x : G} (hx : x ∈ B) : B ≤ Nor (X ⊓ Cen x) := by
  intro g hg
  refine nor_inf (d.hBX hg) ?_
  exact Subgroup.le_normalizer
    (Subgroup.mem_centralizer_singleton_iff.2 (d.hBcomm g hg x hx))

theorem hBU : B ≤ Nor U := d.hXb ▸ d.nor_inf_cen d.hbB

theorem cbb_gen {c' : G} (hc'B : c' ∈ B) (hD : Cen (b * c') ≤ Nor (Subgroup.closure ({b, c'} : Set G))) :
    X ⊓ Cen (b * c') = U ⊓ Cen c' := by
  apply le_antisymm
  · have hE3 : ∀ w ∈ Subgroup.closure ({b, c'} : Set G), w ^ 3 = 1 := by
      intro w hw
      refine d.hB3 w ?_
      refine (Subgroup.closure_le B).2 ?_ hw
      intro z hz
      rcases hz with rfl | hz
      · exact d.hbB
      · rw [Set.mem_singleton_iff.1 hz]; exact hc'B
    have hbV : b ∈ Nor (X ⊓ Cen (b * c')) := by
      refine nor_inf d.hbN (Subgroup.le_normalizer ?_)
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have hbc' := d.hBcomm b d.hbB c' hc'B
      calc b * (b * c') = b * (c' * b) := by rw [hbc']
        _ = b * c' * b := by rw [mul_assoc]
    have := E_cen_2sub hE3 hD (d.hX.to_le inf_le_left) inf_le_right hbV
    intro x hx
    have hx1 := this hx
    exact ⟨d.hXb ▸ ⟨hx.1, hx1.1⟩, hx1.2⟩
  · intro x hx
    refine ⟨d.hUX hx.1, ?_⟩
    have hb' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (d.hUb hx.1)
    have hc'' : x * c' = c' * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * (b * c') = b * (x * c') := by rw [← mul_assoc, hb', mul_assoc]
      _ = b * (c' * x) := by rw [hc'']
      _ = b * c' * x := by rw [mul_assoc]

theorem cbb1 : X ⊓ Cen (b * c) = U ⊓ Cen c :=
  d.cbb_gen d.hcB d.hD1

theorem cbb2 : X ⊓ Cen (b * c⁻¹) = U ⊓ Cen c := by
  have := d.cbb_gen (c' := c⁻¹) (inv_mem d.hcB) d.hD2
  rwa [cen_inv] at this

theorem hW : EA2 (X ⊓ Cen c) ∧ Nat.card ↥(X ⊓ Cen c) ≤ 16 := by
  set W := X ⊓ Cen c with hWdef
  have hnB : ∀ g ∈ B, n⁻¹ * g * n ∈ B := fun g hg => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem d.hn) g).1 hg
    simpa using this
  have hY1 : conjBy n W ≤ Cen b := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have hw : n⁻¹ * y * n ∈ Cen c := hy.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    rw [← d.hnc]
    calc y * (n * c * n⁻¹) = n * ((n⁻¹ * y * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * y * n)) * n⁻¹ := by rw [hw]
      _ = n * c * n⁻¹ * y := by group
  have hY2 : IsPGroup 2 (conjBy n W) := (d.hX.to_le inf_le_left).map _
  have hY3 : B ≤ Nor (conjBy n W) := by
    intro g hg
    rw [mem_nor_conjBy]
    exact d.nor_inf_cen d.hcB (hnB g hg)
  obtain ⟨hEA, hcard⟩ := d.hPi _ hY1 hY2 hY3
  refine ⟨?_, ?_⟩
  · have := hEA.conj n⁻¹
    rwa [conjBy_inv_conjBy] at this
  · rwa [card_conjBy] at hcard

theorem sup_bound : X ≤ U ⊔ (X ⊓ Cen c) := by
  set E := Subgroup.closure ({b, c} : Set G) with hE
  have hEB : E ≤ B := by
    refine (Subgroup.closure_le B).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact d.hbB
    · rw [Set.mem_singleton_iff.1 hz]; exact d.hcB
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    d.hBcomm x (hEB hx) y (hEB hy)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => d.hB3 x (hEB hx)
  haveI : IsElementaryAbelian 3 E := isEA_of 3 hEcomm hE3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hcE : c ∈ E := Subgroup.subset_closure (by simp)
  have h9 : 9 ≤ Nat.card E := by
    have hpg : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    by_contra hlt
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.2 hbE
    have hcz : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, d.hb]
    have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers b) := by
      rw [hk, hcz]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    exact d.hcb (Subgroup.eq_of_le_of_card_ge hle hcard ▸ hcE)
  have hEX : E ≤ Nor X := hEB.trans d.hBX
  have hgen := B_gen_centralizers (E := E) (X := X) h9 d.hX hEX
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  obtain ⟨i, j, rfl⟩ := mem_closure_pair_comm d.bcomm ha
  have hb3 := d.b3
  have hc3 := d.c3
  have hbi := zpow_emod3 hb3 i
  have hcj := zpow_emod3 hc3 j
  have hcc : Commute b c := d.bcomm
  intro x hx
  have hxX : x ∈ X := hx.1
  have hxa : x * (b ^ i * c ^ j) = (b ^ i * c ^ j) * x :=
    Subgroup.mem_centralizer_singleton_iff.1 hx.2
  have hz3 : ∀ {z : G}, z ^ 3 = 1 → ∀ {k : ℤ}, ¬ (3 : ℤ) ∣ k → ∀ {y : G},
      y * z ^ k = z ^ k * y → y * z = z * y := fun hz _ hk _ h => comm_of_comm_zpow hz hk h
  by_cases hi : i % 3 = 0
  ·
    have hbi1 : b ^ i = 1 := by rw [hbi, hi]; simp
    rw [hbi1, one_mul] at hxa ha1
    have hj : ¬ (3 : ℤ) ∣ j := by
      intro hdj
      apply ha1
      have : j % 3 = 0 := by omega
      rw [hcj, this]; simp
    have := hz3 hc3 hj hxa
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hxX, Subgroup.mem_centralizer_singleton_iff.2 this⟩)
  by_cases hj : j % 3 = 0
  · have hcj1 : c ^ j = 1 := by rw [hcj, hj]; simp
    rw [hcj1, mul_one] at hxa ha1
    have hi' : ¬ (3 : ℤ) ∣ i := by intro hdj; apply hi; omega
    have := hz3 hb3 hi' hxa
    exact Subgroup.mem_sup_left (d.hXb ▸ Subgroup.mem_inf.2
      ⟨hxX, Subgroup.mem_centralizer_singleton_iff.2 this⟩)
  have hi' : ¬ (3 : ℤ) ∣ i := by intro hdj; apply hi; omega
  have hcases : j % 3 = i % 3 ∨ j % 3 = (-i) % 3 := by omega
  rcases hcases with hij | hij
  ·
    have hz : (b * c) ^ 3 = 1 := by rw [hcc.mul_pow, hb3, hc3, one_mul]
    have e : b ^ i * c ^ j = (b * c) ^ i := by
      rw [hcc.mul_zpow, zpow_eq_of_mod hc3 hij]
    rw [e] at hxa
    have := hz3 hz hi' hxa
    have hx2 : x ∈ X ⊓ Cen (b * c) := Subgroup.mem_inf.2 ⟨hxX, Subgroup.mem_centralizer_singleton_iff.2 this⟩
    rw [d.cbb1] at hx2
    exact Subgroup.mem_sup_left hx2.1
  · have hcc' : Commute b c⁻¹ := hcc.inv_right
    have hz : (b * c⁻¹) ^ 3 = 1 := by rw [hcc'.mul_pow, hb3, inv_pow, hc3]; simp
    have e : b ^ i * c ^ j = (b * c⁻¹) ^ i := by
      rw [hcc'.mul_zpow, inv_zpow', zpow_eq_of_mod hc3 hij]
    rw [e] at hxa
    have := hz3 hz hi' hxa
    have hx2 : x ∈ X ⊓ Cen (b * c⁻¹) := Subgroup.mem_inf.2 ⟨hxX, Subgroup.mem_centralizer_singleton_iff.2 this⟩
    rw [d.cbb2] at hx2
    exact Subgroup.mem_sup_left hx2.1

theorem comm_UW : ∀ u ∈ U, ∀ w ∈ X ⊓ Cen c, u * w = w * u := by
  set W := X ⊓ Cen c with hWdef
  have hUEA := d.hUEA
  have hWEA := d.hW.1
  have hbU : b ∈ Nor U := d.hBU d.hbB
  have hcU : c ∈ Nor U := d.hBU d.hcB
  have hbW : b ∈ Nor W := d.nor_inf_cen d.hcB d.hbB
  have hA : ⁅U, Subgroup.zpowers c⁆ ≤ X ⊓ Cen b := by
    rw [d.hXb]; exact W_le_S hUEA.1 hUEA.2 hcU d.c3
  have hA' : ⁅W, Subgroup.zpowers b⁆ ≤ X ⊓ Cen c := W_le_S hWEA.1 hWEA.2 hbW d.b3
  have hAv := comm_comm hUEA.1 hUEA.2 hcU d.c3
  have hA'u := comm_comm hWEA.1 hWEA.2 hbW d.b3
  have hfix₁ : X ⊓ Cen (b * c) ≤ Cen b := by
    rw [d.cbb1]; exact inf_le_left.trans d.hUb
  have hfix₂ : X ⊓ Cen (b * c ^ 2) ≤ Cen b := by
    have : c ^ 2 = c⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right (show c * c ^ 2 = 1 by rw [← pow_succ']; exact d.c3)).symm
    rw [this, d.cbb2]; exact inf_le_left.trans d.hUb
  have hcomm := B_comm_of_fixed d.hX d.hb d.hc d.bcomm d.hbN d.hcN hA hA' hAv hA'u hfix₁ hfix₂
  have hAA' : ∀ a ∈ ⁅U, Subgroup.zpowers c⁆, ∀ a' ∈ ⁅W, Subgroup.zpowers b⁆, a * a' = a' * a := by
    intro a ha a' ha'
    have h1 := Subgroup.commutator_mem_commutator ha ha'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h1
    have : Commute a a' := by
      have h2 : a * a' = a' * a := by
        calc a * a' = (a * a' * a⁻¹ * a'⁻¹) * (a' * a) := by group
          _ = a' * a := by rw [h1, one_mul]
      exact h2
    exact this.eq
  intro u hu w hw
  obtain ⟨f, hf, d1, hd1, rfl⟩ := decomp hUEA.1 hUEA.2 hcU d.c3 hu
  obtain ⟨f', hf', d2, hd2, rfl⟩ := decomp hWEA.1 hWEA.2 hbW d.b3 hw
  have hfU : f ∈ U := hf.1
  have hfW : f ∈ W := ⟨d.hUX hf.1, hf.2⟩
  have hf'W : f' ∈ W := hf'.1
  have hf'U : f' ∈ U := by
    rw [← d.hXb]
    exact ⟨hf'.1.1, hf'.2⟩
  have hd1U : d1 ∈ U := W_le_S hUEA.1 hUEA.2 hcU d.c3 hd1
  have hd2W : d2 ∈ W := W_le_S hWEA.1 hWEA.2 hbW d.b3 hd2
  have c1 : Commute f f' := (hUEA.1 f hfU f' hf'U)
  have c2 : Commute f d2 := hWEA.1 f hfW d2 hd2W
  have c3 : Commute d1 f' := hUEA.1 d1 hd1U f' hf'U
  have c4 : Commute d1 d2 := hAA' d1 hd1 d2 hd2
  exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq

theorem core : EA2 X ∧ X = U ⊔ (X ⊓ Cen c) ∧ Nat.card X = 4 * Nat.card ↥(X ⊓ Cen c) ∧
    Nat.card ↥(X ⊓ Cen c) ≤ 16 := by
  set W := X ⊓ Cen c with hWdef
  have hUEA := d.hUEA
  have hWEA := d.hW.1
  have hXeq : X = U ⊔ W := le_antisymm d.sup_bound (sup_le d.hUX inf_le_left)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U W d.comm_UW
  have hUW : U ⊓ W = U ⊓ Cen c := by
    ext x
    constructor
    · rintro ⟨hxU, hxW⟩; exact ⟨hxU, hxW.2⟩
    · rintro ⟨hxU, hxc⟩; exact ⟨hxU, d.hUX hxU, hxc⟩
  rw [← hXeq, hUW, d.hUc4, d.hU16] at hcard
  have hX4 : Nat.card X = 4 * Nat.card W := by omega
  refine ⟨?_, hXeq, hX4, d.hW.2⟩
  constructor
  · intro x hx y hy
    rw [hXeq] at hx hy
    have hx' : x ∈ (U : Set G) * (W : Set G) := by rw [← hset]; exact hx
    have hy' : y ∈ (U : Set G) * (W : Set G) := by rw [← hset]; exact hy
    obtain ⟨u, hu, w, hw, rfl⟩ := hx'
    obtain ⟨u', hu', w', hw', rfl⟩ := hy'
    have c1 : Commute u u' := hUEA.1 u hu u' hu'
    have c2 : Commute u w' := d.comm_UW u hu w' hw'
    have c3 : Commute w u' := (d.comm_UW u' hu' w hw).symm
    have c4 : Commute w w' := hWEA.1 w hw w' hw'
    exact (((c1.mul_right c2).mul_left (c3.mul_right c4)).eq)
  · intro x hx
    rw [hXeq] at hx
    have hx' : x ∈ (U : Set G) * (W : Set G) := by rw [← hset]; exact hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx'
    have c := d.comm_UW u hu w hw
    calc u * w * (u * w) = u * (w * u) * w := by group
      _ = u * (u * w) * w := by rw [← c]
      _ = (u * u) * (w * w) := by group
      _ = 1 := by rw [hUEA.2 u hu, hWEA.2 w hw, mul_one]

end CoreData

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
