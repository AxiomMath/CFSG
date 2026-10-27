module

public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Basic

public section

namespace CFSG.Quasithin.H13

namespace End1222

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

@[expose] def fixAut (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    show g (a * b) = a * b
    rw [map_mul, (ha : g a = a), (hb : g b = b)]
  inv_mem' := fun {a} ha => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, (ha : g a = a)]

theorem fixV_le_fixAut {Γ : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Γ) :
    fixV Γ ≤ fixAut g := fun _ hw => hw g hg

theorem eq_one_of_fixAut_eq_top {g : MulAut W} (h : fixAut g = ⊤) : g = 1 := by
  ext w
  have : w ∈ fixAut g := by rw [h]; trivial
  exact this

theorem card_fixAut_modEq [Finite W] {p : ℕ} [Fact p.Prime] {g : MulAut W} (hg : orderOf g = p) :
    Nat.card W ≡ Nat.card (fixAut g) [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := hP.card_modEq_card_fixedPoints W
  have hset : MulAction.fixedPoints (Subgroup.zpowers g) W = (fixAut g : Set W) := by
    ext w
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h x
      have hst : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut W) w :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
      exact MulAction.mem_stabilizer_iff.1 (hst x.2)
  rw [hset] at h
  exact h

theorem exists_move_of_card_fixAut [Finite W] {Γ : Subgroup (MulAut W)} {c g : MulAut W}
    (hc : ∀ x ∈ Γ, c * x = x * c) (hg : g ∈ Γ)
    (hcard : Nat.card (fixAut g) = 2 * Nat.card (fixV Γ)) :
    ∃ v : W, v ∉ fixV Γ ∧ c v * v⁻¹ ∈ fixV Γ := by
  set F := fixAut g with hF
  set Z := fixV Γ with hZ
  have hZF : Z ≤ F := fixV_le_fixAut hg
  set N : Subgroup ↥F := Z.subgroupOf F with hN
  have hNcard : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv
  have hindex : N.index = 2 := by
    have h := N.index_mul_card
    rw [hNcard, hcard] at h
    have hpos : 0 < Nat.card Z := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hindex
  have haN : a ∉ N := by
    rcases ha 1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd N.one_mem h2
    · rwa [one_mul] at h2
  have haa : a * a ∈ N := by
    rcases ha a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 haN
  have haZ : (a : W) ∉ Z := fun h => haN (Subgroup.mem_subgroupOf.2 h)
  have hcaF : c (a : W) ∈ F := by
    show g (c (a : W)) = c (a : W)
    rw [← comm_apply hc hg, (a.2 : g (a : W) = a)]
  have hcaZ : c (a : W) ∉ Z := fun h => haZ ((apply_mem_fixV_iff hc).1 h)
  set b : ↥F := ⟨c (a : W), hcaF⟩ with hb
  have hbN : b ∉ N := fun h => hcaZ (Subgroup.mem_subgroupOf.1 h)
  have hba : b * a ∈ N := by
    rcases ha b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 hbN
  have h1 : c (a : W) * (a : W) ∈ Z := Subgroup.mem_subgroupOf.1 hba
  have h2 : (a : W) * (a : W) ∈ Z := Subgroup.mem_subgroupOf.1 haa
  refine ⟨a, haZ, ?_⟩
  have e : c (a : W) * (a : W)⁻¹ = (c (a : W) * (a : W)) * ((a : W) * (a : W))⁻¹ := by group
  rw [e]
  exact Z.mul_mem h1 (Z.inv_mem h2)

theorem card_fixAut_dvd [Finite W] (g : MulAut W) : Nat.card (fixAut g) ∣ Nat.card W :=
  Subgroup.card_subgroup_dvd_card _

theorem card_fixAut_lt [Finite W] {g : MulAut W} (hg : g ≠ 1) :
    Nat.card (fixAut g) < Nat.card W := by
  have hle : Nat.card (fixAut g) ≤ Nat.card W :=
    Nat.le_of_dvd Nat.card_pos (card_fixAut_dvd g)
  exact lt_of_le_of_ne hle fun h =>
    hg (eq_one_of_fixAut_eq_top (Subgroup.eq_top_of_card_eq _ h))

theorem dvd_sixteen {k : ℕ} (h : k ∣ 16) : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 := by
  have hk : k ≤ 16 := Nat.le_of_dvd (by norm_num) h
  interval_cases k <;> omega

theorem exists_move_of_card_sixteen [Finite W] (hcard : Nat.card W = 16)
    {Γ : Subgroup (MulAut W)} (h7 : 7 ∣ Nat.card Γ) (h3 : 3 ∣ Nat.card Γ) {c : MulAut W}
    (hc : ∀ x ∈ Γ, c * x = x * c) : ∃ v : W, v ∉ fixV Γ ∧ c v * v⁻¹ ∈ fixV Γ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g7, hg7⟩ := exists_prime_orderOf_dvd_card' 7 h7
  obtain ⟨g3, hg3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hg7' : orderOf (g7 : MulAut W) = 7 := by rw [Subgroup.orderOf_coe]; exact hg7
  have hg3' : orderOf (g3 : MulAut W) = 3 := by rw [Subgroup.orderOf_coe]; exact hg3
  have hne7 : (g7 : MulAut W) ≠ 1 := fun h => by rw [h, orderOf_one] at hg7'; omega
  have hne3 : (g3 : MulAut W) ≠ 1 := fun h => by rw [h, orderOf_one] at hg3'; omega
  have h7card : Nat.card (fixAut (g7 : MulAut W)) = 2 := by
    have hd := dvd_sixteen (hcard ▸ card_fixAut_dvd (g7 : MulAut W))
    have hm := card_fixAut_modEq hg7'
    have hlt := card_fixAut_lt hne7
    rw [hcard] at hm hlt
    unfold Nat.ModEq at hm
    omega
  have hZ7 : Nat.card (fixV Γ) ∣ 2 :=
    h7card ▸ Subgroup.card_dvd_of_le (fixV_le_fixAut g7.2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hZ7 with hZ | hZ
  · exact exists_move_of_card_fixAut hc g7.2 (by rw [h7card, hZ])
  · have hZ3 : Nat.card (fixV Γ) ∣ Nat.card (fixAut (g3 : MulAut W)) :=
      Subgroup.card_dvd_of_le (fixV_le_fixAut g3.2)
    have h3card : Nat.card (fixAut (g3 : MulAut W)) = 4 := by
      have hd := dvd_sixteen (hcard ▸ card_fixAut_dvd (g3 : MulAut W))
      have hm := card_fixAut_modEq hg3'
      have hlt := card_fixAut_lt hne3
      rw [hcard] at hm hlt
      unfold Nat.ModEq at hm
      rw [hZ] at hZ3
      omega
    exact exists_move_of_card_fixAut hc g3.2 (by rw [h3card, hZ])

theorem dvd_sixtyfour {k : ℕ} (h : k ∣ 64) :
    k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 64 := by
  have hk : k ≤ 64 := Nat.le_of_dvd (by norm_num) h
  interval_cases k <;> omega

theorem mem_of_card_sixtyfour [Finite W] (hcard : Nat.card W = 64) {Γ : Subgroup (MulAut W)}
    (hfix : ∀ a ∈ Subgroup.centralizer (Γ : Set (MulAut W)), ∀ v : W, v ≠ 1 → a v = v → a = 1)
    (h5 : 5 ∣ Nat.card Γ) {z : MulAut W} (hzΓ : z ∈ Γ) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzC : z ∈ Subgroup.centralizer (Γ : Set (MulAut W))) {c : MulAut W}
    (hcC : c ∈ Subgroup.centralizer (Γ : Set (MulAut W))) : c ∈ Γ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g5, hg5⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hg5' : orderOf (g5 : MulAut W) = 5 := by rw [Subgroup.orderOf_coe]; exact hg5
  set g : MulAut W := (g5 : MulAut W) with hg
  have hne : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg5'; omega
  have hFcard : Nat.card (fixAut g) = 4 := by
    have hd := dvd_sixtyfour (hcard ▸ card_fixAut_dvd g)
    have hm := card_fixAut_modEq hg5'
    have hlt := card_fixAut_lt hne
    rw [hcard] at hm hlt
    unfold Nat.ModEq at hm
    omega
  set C := Subgroup.centralizer (Γ : Set (MulAut W)) with hC
  have hpres : ∀ a ∈ C, ∀ v ∈ fixAut g, a v ∈ fixAut g := by
    intro a ha v hv
    have h1 : g * a = a * g := Subgroup.mem_centralizer_iff.1 ha g g5.2
    have h2 := congrArg (fun φ : MulAut W => φ v) h1
    simp only [MulAut.mul_apply] at h2
    show g (a v) = a v
    rw [h2, (hv : g v = v)]
  have hFne : fixAut g ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨⟨w, hwF⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hzw : z w ≠ w := fun h => hz1 (hfix z hzC w hw1' h)
  have hzzw : z (z w) ≠ w := by
    intro h
    have h2 : z * z = 1 := hfix (z * z) (C.mul_mem hzC hzC) w hw1' h
    apply hz1
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, h2]; simp
  have hzzw' : z (z w) ≠ z w := fun h => hzw (z.injective h)
  have hone : ∀ a : MulAut W, ∀ v : W, a v = 1 → v = 1 := fun a v h =>
    a.injective (h.trans (map_one a).symm)
  have h1zw : z w ≠ 1 := fun h => hw1' (hone z w h)
  have h1zzw : z (z w) ≠ 1 := fun h => h1zw (hone z _ h)
  let _ : Fintype ↥(fixAut g) := Fintype.ofFinite _
  let a₁ : ↥(fixAut g) := ⟨w, hwF⟩
  let a₂ : ↥(fixAut g) := ⟨z w, hpres z hzC w hwF⟩
  let a₃ : ↥(fixAut g) := ⟨z (z w), hpres z hzC _ (hpres z hzC w hwF)⟩
  have hS : ({1, a₁, a₂, a₃} : Finset ↥(fixAut g)).card = 4 := by
    have n1 : (1 : ↥(fixAut g)) ≠ a₁ := fun h => hw1' (congrArg Subtype.val h).symm
    have n2 : (1 : ↥(fixAut g)) ≠ a₂ := fun h => h1zw (congrArg Subtype.val h).symm
    have n3 : (1 : ↥(fixAut g)) ≠ a₃ := fun h => h1zzw (congrArg Subtype.val h).symm
    have n4 : a₁ ≠ a₂ := fun h => hzw (congrArg Subtype.val h).symm
    have n5 : a₁ ≠ a₃ := fun h => hzzw (congrArg Subtype.val h).symm
    have n6 : a₂ ≠ a₃ := fun h => hzzw' (congrArg Subtype.val h).symm
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair n6]
    · simp [n4, n5]
    · simp [n1, n2, n3]
  have huniv : ({1, a₁, a₂, a₃} : Finset ↥(fixAut g)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hS, Fintype.card_eq_nat_card]
    exact hFcard.symm
  set b : ↥(fixAut g) := ⟨c w, hpres c hcC w hwF⟩ with hb
  have hbmem : b ∈ ({1, a₁, a₂, a₃} : Finset ↥(fixAut g)) := by rw [huniv]; exact Finset.mem_univ b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
  rcases hbmem with h | h | h | h
  · exfalso
    exact hw1' (hone c w (congrArg Subtype.val h))
  · have hcw : c w = w := congrArg Subtype.val h
    rw [hfix c hcC w hw1' hcw]
    exact Γ.one_mem
  · have hcw : c w = z w := congrArg Subtype.val h
    have h2 : z⁻¹ * c = 1 := by
      refine hfix (z⁻¹ * c) (C.mul_mem (C.inv_mem hzC) hcC) w hw1' ?_
      rw [MulAut.mul_apply, hcw, MulAut.inv_apply_self]
    have : c = z := (inv_mul_eq_one.1 h2).symm
    rw [this]
    exact hzΓ
  · have hcw : c w = z (z w) := congrArg Subtype.val h
    have h2 : (z * z)⁻¹ * c = 1 := by
      refine hfix ((z * z)⁻¹ * c) (C.mul_mem (C.inv_mem (C.mul_mem hzC hzC)) hcC) w hw1' ?_
      rw [MulAut.mul_apply, hcw]
      show (z * z)⁻¹ ((z * z) w) = w
      exact MulAut.inv_apply_self W (z * z) w
    have : c = z * z := (inv_mul_eq_one.1 h2).symm
    rw [this]
    exact Γ.mul_mem hzΓ hzΓ

end End1222

end CFSG.Quasithin.H13
