module

public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec12.Item123

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure Sec11Data (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) (d x s r g : G) : Prop extends Sec11Std G A c L a R Y where
  inf_eq : A ⊓ L = Subgroup.zpowers d
  closure_eq : A = Subgroup.closure {c, a, d}
  inf_L_eq : R ⊓ L = Subgroup.zpowers x
  inf_centralizer_eq : R ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers s
  R_eq : R = Subgroup.closure {r, x, s}
  a_mem_closure : a ∈ Subgroup.closure {r, s}
  pow_eq_one : ∃ k : ℕ, g ^ 3 ^ k = 1
  g_mem : g ∈ Y ⊓ Subgroup.normalizer (A : Set G)
  g_mem_normalizer : g ∈ Subgroup.normalizer (R : Set G)
  g_not_mem : g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  conj_mem : g * c * g⁻¹ ∈ Subgroup.closure {c, d}

theorem rank3II_11_10 {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hs : s = c) : r * a = a * r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 R := h.isSylowOf.isPGroup
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hrR : r ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨k, hk⟩ := hR3 ⟨r, hrR⟩
  have hrk : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc3 : orderOf c = 3 :=
    orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hrc : r * c = c * r := Sec12.commute_of_conj_mem_zpowers hc3
    ((Subgroup.mem_normalizer_iff.mp (hRH hrR) c).mp (Subgroup.mem_zpowers c)) hrk
  have hle : Subgroup.closure ({r, s} : Set G) ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [hs]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hrc.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle h.a_mem_closure)).symm

variable {G : Type*} [Group G]

theorem conj_zpow_eq_of_conj_eq {a c s : G} (hac : a * c = c * a) (hsc : s * c = c * s) {j : ℤ}
    (hj : s * a * s⁻¹ = a * c ^ j) (n : ℕ) : s ^ n * a * (s ^ n)⁻¹ = a * c ^ ((n : ℤ) * j) := by
  have hsc' : Commute s c := hsc
  have hac' : Commute a c := hac
  induction n with
  | zero => simp
  | succ n ih =>
    have e : s ^ (n + 1) * a * (s ^ (n + 1))⁻¹ = s * (s ^ n * a * (s ^ n)⁻¹) * s⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    have e2 : s * (a * c ^ ((n : ℤ) * j)) * s⁻¹ =
        (s * a * s⁻¹) * (s * c ^ ((n : ℤ) * j) * s⁻¹) := by group
    rw [e, ih, e2, hj, (hsc'.zpow_right _).eq, mul_inv_cancel_right, mul_assoc, ← zpow_add]
    congr 2
    push_cast
    ring

theorem exists_pow_inv_mul_mem_centralizer {X : Subgroup G} {a c s : G}
    (hX3 : IsPGroup 3 X) (hsX : s ∈ X) (hac : a * c = c * a) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hac' : a ∉ Subgroup.zpowers c)
    (hXN : X ≤ Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G))
    (hXc : X ≤ Subgroup.centralizer ({c} : Set G)) (hsa : s * a ≠ a * s) :
    ∀ x ∈ X, ∃ n : ℕ, (s ^ n)⁻¹ * x ∈ Subgroup.centralizer ({a} : Set G) := by
  have hca : c * a = a * c := hac.symm
  have hca' : Commute c a := hca
  have hc3' : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
  have key : ∀ x ∈ X, ∃ i : ℤ, x * a * x⁻¹ = a * c ^ i := by
    intro x hx
    obtain ⟨k, hk⟩ := hX3 ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hXc hx)
    have hz : x * a * x⁻¹ ∈ Subgroup.closure ({c, a} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hXN hx) a).mp
        (Subgroup.subset_closure (Set.mem_insert_of_mem c rfl))
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (Sec12.conj_mul_inv_mem_zpowers_of_mem_closure hca hc3 ha3 hac' hxc hxk hz)
    refine ⟨i, ?_⟩
    have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e, ← hi, (hca'.zpow_left i).eq]
  obtain ⟨j, hj⟩ := key s hsX
  have hsc : s * c = c * s := Subgroup.mem_centralizer_singleton_iff.mp (hXc hsX)
  have hj3 : j % 3 ≠ 0 := by
    intro h0
    apply hsa
    obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h0
    have hcj : c ^ j = 1 := by rw [ht, zpow_mul, hc3', one_zpow]
    calc s * a = (s * a * s⁻¹) * s := by group
      _ = a * s := by rw [hj, hcj, mul_one]
  intro x hx
  obtain ⟨i, hi⟩ := key x hx
  set n : ℕ := ((i * j) % 3).toNat with hndef
  have hn : (n : ℤ) = (i * j) % 3 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hsn := conj_zpow_eq_of_conj_eq hac hsc hj n
  have hcn : c ^ ((n : ℤ) * j) = c ^ i := by
    have hj2 : (j * j) % 3 = 1 := by
      have : j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases this with h | h <;> rw [Int.mul_emod, h] <;> norm_num
    have hmod : ((n : ℤ) * j) % 3 = i % 3 := by
      rw [hn, Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl 3), ← Int.mul_emod, mul_assoc,
        Int.mul_emod, hj2, mul_one, Int.emod_emod_of_dvd _ (dvd_refl 3)]
    rw [zpow_eq_zpow_emod _ hc3', hmod, ← zpow_eq_zpow_emod _ hc3']
  refine ⟨n, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : (s ^ n)⁻¹ * x * a = (s ^ n)⁻¹ * (x * a * x⁻¹) * x := by group
  rw [e1, hi, ← hcn, ← hsn]
  group

theorem card_closure_pair_le_nine [Finite G] {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) : Nat.card (Subgroup.closure ({c, d} : Set G)) ≤ 9 := by
  have hcK : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdK : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 → Subgroup.closure ({c, d} : Set G) := fun p =>
    ⟨c ^ p.1.val * d ^ p.2.val, Subgroup.mul_mem _ (Subgroup.pow_mem _ hcK _)
      (Subgroup.pow_mem _ hdK _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hz
    have hc3' : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
    have hd3' : d ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
    have hm0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
    have hn0 : 0 ≤ n % 3 := Int.emod_nonneg _ (by norm_num)
    refine ⟨(⟨(m % 3).toNat, by omega⟩, ⟨(n % 3).toNat, by omega⟩), Subtype.ext ?_⟩
    simp only [f]
    rw [zpow_eq_zpow_emod m hc3', zpow_eq_zpow_emod n hd3', ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0]
  calc Nat.card (Subgroup.closure ({c, d} : Set G)) ≤ Nat.card (Fin 3 × Fin 3) :=
        Nat.card_le_card_of_surjective f hf
    _ = 9 := by simp

theorem Sec11Data.a_not_mem_zpowers {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) : a ∉ Subgroup.zpowers c := by
  intro hac
  have hexpA : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hcommA : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdA : d ∈ A := by
    have hd : d ∈ A ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.mem_inf.mp hd).1
  have hle : A ≤ Subgroup.closure ({c, d} : Set G) := by
    have hA := h.closure_eq
    intro y hy
    rw [hA] at hy
    refine (Subgroup.closure_le _).mpr ?_ hy
    rintro z (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert z {d})
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c {d}))) hac
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have h9 := card_closure_pair_le_nine (hcommA c h.mem_A d hdA) (hexpA c h.mem_A) (hexpA d hdA)
  have h27 : Nat.card A = 27 := h.card_eq
  have hcard := Subgroup.card_le_of_le hle
  rw [h27] at hcard
  exact absurd (hcard.trans h9) (by norm_num)

theorem rank3II_11_11 {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hN : Subgroup.closure ({r, s} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G))
    (hsa : s * a ≠ a * s) :
    ∀ y ∈ Subgroup.closure ({r, s} : Set G), ∃ n : ℕ,
      (s ^ n)⁻¹ * y ∈ Subgroup.closure ({r, s} : Set G) ⊓ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le
  have hrR : r ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hsR : s ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hXR : Subgroup.closure ({r, s} : Set G) ≤ R := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [hrR, hsR]
  have hX3 : IsPGroup 3 (Subgroup.closure ({r, s} : Set G)) :=
    h.isSylowOf.isPGroup.to_le hXR
  have hcA := h.mem_A
  have hexpA : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c hcA) h.ne_one
  have hcommA : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := by
    intro y hy
    obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec12.commute_of_conj_mem_zpowers hc3
        ((Subgroup.mem_normalizer_iff.mp (hRH hy) c).mp (Subgroup.mem_zpowers c)) hyk)
  have hac' : a ∉ Subgroup.zpowers c := h.a_not_mem_zpowers
  intro y hy
  have hsX : s ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (by simp)
  obtain ⟨n, hn⟩ := exists_pow_inv_mul_mem_centralizer hX3 hsX (hcommA a h.a_mem c hcA)
    (hexpA a h.a_mem) (hexpA c hcA) hac' hN (hXR.trans hRc) hsa y hy
  exact ⟨n, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hsX n)) hy, hn⟩

theorem rank3II_11_11_choose {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hN : Subgroup.closure ({r, s} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G))
    (hsa : s * a ≠ a * s) :
    ∃ r' : G, Sec11Data G A c L a R Y d x s r' g ∧ r' * a = a * r' := by
  have hr : r ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (Set.mem_insert r _)
  obtain ⟨n, hn⟩ := rank3II_11_11 h hN hsa r hr
  set r' := (s ^ n)⁻¹ * r with hr'
  have hrr' : r = s ^ n * r' := by rw [hr']; group
  have hsub1 : ∀ T : Set G, s ∈ T →
      Subgroup.closure (insert r' T) = Subgroup.closure (insert r T) := by
    intro T hsT
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
          (Subgroup.subset_closure (Set.mem_insert_of_mem r hsT)) n))
          (Subgroup.subset_closure (Set.mem_insert r T))
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem r hy)
    · rw [Subgroup.closure_le]
      rintro y (rfl | hy)
      · rw [hrr']
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _
          (Subgroup.subset_closure (Set.mem_insert_of_mem r' hsT)) n)
          (Subgroup.subset_closure (Set.mem_insert r' T))
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem r' hy)
  refine ⟨r', { h with R_eq := ?_, a_mem_closure := ?_ }, ?_⟩
  · rw [h.R_eq]
    exact (hsub1 {x, s} (Set.mem_insert_of_mem x rfl)).symm
  · rw [hsub1 {s} rfl]
    exact h.a_mem_closure
  · exact Subgroup.mem_centralizer_singleton_iff.mp hn.2

end CFSG.RankThree.PartTwo.Sec11
