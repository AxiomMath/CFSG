module

public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152Y04
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {A : Type} [Group A] [Finite A]

theorem exists_conj_mem_sylow {L P : Subgroup A} (hP : IsSylowTwoOf P L) {x : A} (hxL : x ∈ L)
    (hx : ∃ m : ℕ, x ^ 2 ^ m = 1) : ∃ g ∈ L, g⁻¹ * x * g ∈ P := by
  obtain ⟨m, hm⟩ := hx
  have hord : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hcard : Nat.card (Subgroup.zpowers x) = 2 ^ j := by rw [Nat.card_zpowers, hj]
  have h2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card hcard
  obtain ⟨S, hS, hxS⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hxL) h2
  obtain ⟨h, hh, hSh⟩ := A4.exists_conj_of_isSylowTwoOf hP hS
  exact ⟨h, hh, (hSh x).mp (hxS (Subgroup.mem_zpowers x))⟩

omit [Finite A] in
theorem eq_one_of_odd_orderOf_of_isPGroup {P : Subgroup A} (hP : IsPGroup 2 P) {z : A}
    (hz : z ∈ P) (ho : Odd (orderOf z)) : z = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hi] at ho
  have hi0 : i = 0 := by
    by_contra hne
    exact absurd ho (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hne⟩))
  exact orderOf_eq_one_iff.mp (by rw [hi, hi0]; rfl)

theorem le_commutator_sylow {L Y P : Subgroup A} (hP : IsSylowTwoOf P L) (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set A)) (hY : Y = oTwoUpper L)
    (hodd : Odd (Nat.card Y))
    (hgen : L ≤ Subgroup.closure {x : A | x ∈ L ∧ ∃ m : ℕ, x ^ 2 ^ m = 1}) :
    Y ≤ ⁅Y, P⁆ := by
  have hPL : P ≤ L := hP.1
  have hPY : P ≤ Subgroup.normalizer (Y : Set A) := hPL.trans hn
  have hPc : P ≤ Subgroup.normalizer ((⁅Y, P⁆ : Subgroup A) : Set A) :=
    le_normalizer_commutator_of_le hPY Subgroup.le_normalizer
  have hmulP : ((⁅Y, P⁆ ⊔ P : Subgroup A) : Set A) = ((⁅Y, P⁆ : Subgroup A) : Set A) * (P : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left ⁅Y, P⁆ P hPc
  have hLeq : L = Y ⊔ P := by
    have := eq_oTwoUpper_sup_of_isSylowTwoOf hP
    rwa [← hY] at this
  have hmulY : ((Y ⊔ P : Subgroup A) : Set A) = (Y : Set A) * (P : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y P hPY
  have h2 : ∀ x ∈ L, (∃ m : ℕ, x ^ 2 ^ m = 1) → x ∈ ⁅Y, P⁆ ⊔ P := by
    intro x hxL hx
    obtain ⟨g, hg, hgx⟩ := exists_conj_mem_sylow hP hxL hx
    have hg' : g ∈ (Y : Set A) * (P : Set A) := by rw [← hmulY, ← hLeq]; exact hg
    obtain ⟨y, hy, p, hp, rfl⟩ := hg'
    set x' := (y * p)⁻¹ * x * (y * p) with hx'def
    have hx' : x' ∈ P := hgx
    have hq : p * x' * p⁻¹ ∈ P := P.mul_mem (P.mul_mem hp hx') (P.inv_mem hp)
    have hxeq : x = ⁅y, p * x' * p⁻¹⁆ * (p * x' * p⁻¹) := by
      simp only [hx'def, commutatorElement_def]; group
    rw [hxeq]
    exact Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hy hq) hq
  have hLS : L ≤ ⁅Y, P⁆ ⊔ P :=
    hgen.trans ((Subgroup.closure_le _).mpr fun x hx => h2 x hx.1 hx.2)
  intro y hy
  have hyS : y ∈ ((⁅Y, P⁆ : Subgroup A) : Set A) * (P : Set A) := by
    rw [← hmulP]; exact hLS (hYL hy)
  obtain ⟨n, hn1, p, hp, hnp⟩ := hyS
  have hyeq : y = n * p := hnp.symm
  subst hyeq
  have hnY : n ∈ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hPY hn1
  have hpY : p ∈ Y := by
    have := Y.mul_mem (Y.inv_mem hnY) hy
    simpa using this
  have hp1 : p = 1 := eq_one_of_odd_orderOf_of_isPGroup hP.2.1 hp
    (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Y hpY))
  rw [hp1, mul_one]
  exact hn1

theorem eq_bot_of_central_of_abelian {L Y K : Subgroup A} (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set A)) (hY : Y = oTwoUpper L) (hodd : Odd (Nat.card Y))
    (hgen : L ≤ Subgroup.closure {x : A | x ∈ L ∧ ∃ m : ℕ, x ^ 2 ^ m = 1})
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hKY : K ≤ Y)
    (hKz : ∀ k ∈ K, ∀ x ∈ L, x * k = k * x) : K = ⊥ := by
  obtain ⟨P, hP, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup A) ≤ L)
    (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup A))
  have hle := le_commutator_sylow hP hYL hn hY hodd hgen
  have hPY : P ≤ Subgroup.normalizer (Y : Set A) := hP.1.trans hn
  rw [eq_bot_iff]
  intro k hk
  have hkc : k ∈ ⁅Y, P⁆ := hle (hKY hk)
  have hfix : ∀ ρ ∈ P, ρ * k * ρ⁻¹ = k := fun ρ hρ => by
    rw [hKz k hk ρ (hP.1 hρ), mul_assoc, mul_inv_cancel, mul_one]
  have hpow := pow_card_eq_one_of_mem_commutator (D := Y) (R := P) hab hPY hkc hfix
  obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
  rw [ha] at hpow
  have hodd' : Odd (orderOf k) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Y (hKY hk))
  have h1 : orderOf k ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hi] at hodd'
  have hi0 : i = 0 := by
    by_contra hne
    exact absurd hodd' (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hne⟩))
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (by rw [hi, hi0]; rfl)

theorem le_commutator_of_central {L Y K : Subgroup A} (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set A)) (hY : Y = oTwoUpper L) (hodd : Odd (Nat.card Y))
    (hgen : L ≤ Subgroup.closure {x : A | x ∈ L ∧ ∃ m : ℕ, x ^ 2 ^ m = 1})
    (hKY : K ≤ Y) (hKz : ∀ k ∈ K, ∀ x ∈ L, x * k = k * x) : K ≤ ⁅Y, Y⁆ := by
  have hYY : ⁅Y, Y⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer
  have hYYL : ⁅Y, Y⁆ ≤ L := hYY.trans hYL
  have hLN : L ≤ Subgroup.normalizer ((⁅Y, Y⁆ : Subgroup A) : Set A) :=
    le_normalizer_commutator_of_le hn hn
  set N₀ : Subgroup ↥L := (⁅Y, Y⁆).subgroupOf L with hN₀
  have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYYL).mpr hLN
  let π₀ : ↥L →* ↥L ⧸ N₀ := QuotientGroup.mk' N₀
  have hπ₀ : Function.Surjective π₀ := QuotientGroup.mk'_surjective N₀
  have hYn : (Y.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYL).mpr hn
  set Yq : Subgroup (↥L ⧸ N₀) := (Y.subgroupOf L).map π₀ with hYq
  set Kq : Subgroup (↥L ⧸ N₀) := (K.subgroupOf L).map π₀ with hKq
  have hYqn : Yq.Normal := hYn.map π₀ hπ₀
  have hn' : (⊤ : Subgroup (↥L ⧸ N₀)) ≤ Subgroup.normalizer (Yq : Set (↥L ⧸ N₀)) := by
    intro x _
    have := Subgroup.normalizer_eq_top_iff.mpr hYqn
    rw [this]
    exact Subgroup.mem_top x
  have hY' : Yq = oTwoUpper (⊤ : Subgroup (↥L ⧸ N₀)) := by
    have e1 : oTwoUpper ((⊤ : Subgroup ↥L).map π₀) = (oTwoUpper (⊤ : Subgroup ↥L)).map π₀ :=
      oTwoUpper_map π₀ ⊤
    have e2 : (⊤ : Subgroup ↥L).map π₀ = ⊤ := Subgroup.map_top_of_surjective π₀ hπ₀
    have e3 : oTwoUpper (⊤ : Subgroup ↥L) = Y.subgroupOf L := by
      have := A4.oTwoUpper_subgroupOf (H := L) (N := L) le_rfl
      rw [Subgroup.subgroupOf_self, ← hY] at this
      exact this
    calc Yq = (oTwoUpper (⊤ : Subgroup ↥L)).map π₀ := by rw [e3]
      _ = oTwoUpper ((⊤ : Subgroup ↥L).map π₀) := e1.symm
      _ = oTwoUpper (⊤ : Subgroup (↥L ⧸ N₀)) := by rw [e2]
  have hodd' : Odd (Nat.card Yq) := by
    refine Odd.of_dvd_nat hodd ?_
    refine (Subgroup.card_map_dvd (Y.subgroupOf L) π₀).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv]
  have hab' : ∀ a ∈ Yq, ∀ b ∈ Yq, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hcomm : (⁅x, y⁆ : ↥L) ∈ N₀ := by
      rw [hN₀, Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hy)
    have h1 : π₀ ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hKYq : Kq ≤ Yq := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hKY (Subgroup.mem_subgroupOf.mp hx))
  have hKzq : ∀ k ∈ Kq, ∀ x ∈ (⊤ : Subgroup (↥L ⧸ N₀)), x * k = k * x := by
    intro k hk x _
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨x', rfl⟩ := hπ₀ x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKz k' (Subgroup.mem_subgroupOf.mp hk') x'.1 x'.2)
  have key : ∀ x : A, x ∈ Subgroup.closure {x : A | x ∈ L ∧ ∃ m : ℕ, x ^ 2 ^ m = 1} →
      ∃ hxL : x ∈ L, (⟨x, hxL⟩ : ↥L) ∈ Subgroup.closure {z : ↥L | ∃ m : ℕ, z ^ 2 ^ m = 1} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := hx.2
      exact ⟨hx.1, Subgroup.subset_closure ⟨m, Subtype.ext (by simpa using hm)⟩⟩
    | one => exact ⟨L.one_mem, Subgroup.one_mem _⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxL, hx'⟩ := ihx
      obtain ⟨hyL, hy'⟩ := ihy
      exact ⟨L.mul_mem hxL hyL, Subgroup.mul_mem _ hx' hy'⟩
    | inv x _ ihx =>
      obtain ⟨hxL, hx'⟩ := ihx
      exact ⟨L.inv_mem hxL, Subgroup.inv_mem _ hx'⟩
  have h1 : (⊤ : Subgroup ↥L) ≤ Subgroup.closure {z : ↥L | ∃ m : ℕ, z ^ 2 ^ m = 1} := by
    intro z _
    exact (key z.1 (hgen z.2)).2
  have hgenq : (⊤ : Subgroup (↥L ⧸ N₀)) ≤
      Subgroup.closure {x : ↥L ⧸ N₀ | x ∈ (⊤ : Subgroup (↥L ⧸ N₀)) ∧ ∃ m : ℕ, x ^ 2 ^ m = 1} := by
    calc (⊤ : Subgroup (↥L ⧸ N₀)) = (⊤ : Subgroup ↥L).map π₀ :=
          (Subgroup.map_top_of_surjective π₀ hπ₀).symm
      _ ≤ (Subgroup.closure {z : ↥L | ∃ m : ℕ, z ^ 2 ^ m = 1}).map π₀ := Subgroup.map_mono h1
      _ = Subgroup.closure (π₀ '' {z : ↥L | ∃ m : ℕ, z ^ 2 ^ m = 1}) := MonoidHom.map_closure π₀ _
      _ ≤ _ := Subgroup.closure_mono (by
          rintro _ ⟨z, ⟨m, hm⟩, rfl⟩
          exact ⟨Subgroup.mem_top _, m, by rw [← map_pow, hm, map_one]⟩)
  have hKq0 := eq_bot_of_central_of_abelian (L := ⊤) (Y := Yq) (K := Kq) le_top hn' hY' hodd'
    hgenq hab' hKYq hKzq
  intro k hk
  have hkL : k ∈ L := hYL (hKY hk)
  have hmem : π₀ ⟨k, hkL⟩ ∈ Kq :=
    Subgroup.mem_map.mpr ⟨⟨k, hkL⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  rw [hKq0] at hmem
  have hk1 : π₀ ⟨k, hkL⟩ = 1 := Subgroup.mem_bot.mp hmem
  have hk2 : (⟨k, hkL⟩ : ↥L) ∈ N₀ := (QuotientGroup.eq_one_iff (⟨k, hkL⟩ : ↥L)).mp hk1
  exact Subgroup.mem_subgroupOf.mp hk2

end CFSG.Quasithin
