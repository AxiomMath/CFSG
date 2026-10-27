module

public import CFSG.Quasithin.Vol2.F134Basic

public section

namespace CFSG.Quasithin.R3c

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem charP_two_of_natCard_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem exists_cube_root_of_card_two_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Even n)
    (hK : Nat.card K = 2 ^ n) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hn
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · intro h
    rw [h, orderOf_one] at hω
    omega

theorem not_three_dvd_card_of_isPGroup_two {Y : Type*} [Group Y] [Finite Y] (h : IsPGroup 2 Y) :
    ¬ 3 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
  rw [hk]
  intro h3
  have := Nat.prime_three.dvd_of_dvd_pow h3
  omega

theorem pRank_three_top_eq_center_quotient {X : Type*} [Group X] [Finite X]
    (hZ : IsPGroup 2 ↥(Subgroup.center X)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center X)
    (not_three_dvd_card_of_isPGroup_two hZ)).symm

theorem pRank_three_eq_pCore_quotient {G : Type*} [Group G] [Finite G] (L : Subgroup G) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  exact (CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L)
    (not_three_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup)).symm

theorem pRank_three_le_one_of_noElemNine {Y : Type*} [Group Y] [Finite Y]
    (h : CFSG.Quasithin.F134.NoElemNine Y) : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  by_contra hlt
  push Not at hlt
  have hP : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 (x : Y) x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hk2 : 2 ≤ k := by
    by_contra hk1
    have : k ≤ 1 := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) this
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2) (by
    rw [hk]
    exact pow_dvd_pow 3 hk2)
  refine h (K.map E.subtype) ?_ ?_
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 _ x.2

theorem pRank_three_le_two_of_not_dvd {Y : Type*} [Group Y] [Finite Y] (h : ¬ 27 ∣ Nat.card Y) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hP : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 (x : Y) x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hk3
  apply h
  have h1 : 3 ^ 3 ∣ Nat.card E := by
    rw [hk]
    exact pow_dvd_pow 3 (by omega)
  exact h1.trans (Subgroup.card_subgroup_dvd_card E)

theorem one_le_pRank_three_of_dvd {Y : Type*} [Group Y] [Finite Y] (h : 3 ∣ Nat.card Y) :
    1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine CFSG.SectionRank.le_pRank (by norm_num) (le_top : Subgroup.zpowers x ≤ ⊤)
    ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩ (k := 1) ?_
  · obtain ⟨_, m, rfl⟩ := a
    obtain ⟨_, n, rfl⟩ := b
    exact Subtype.ext (Commute.zpow_zpow_self x m n).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  · rw [Nat.card_zpowers, hx, pow_one]

theorem pow_three_eq_one_of_mem_zpowers {Y : Type*} [Group Y] {a : Y} (ha : a ^ 3 = 1) {y : Y}
    (hy : y ∈ Subgroup.zpowers a) : y ^ 3 = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem two_le_pRank_three_of_commuting {Y : Type*} [Group Y] [Finite Y] {a b : Y}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b) (ha1 : a ≠ 1)
    (hnot : ∀ k : ℤ, a ^ k ≠ b) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := fun h => hnot 0 (by simpa using h.symm)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hdisj : ∀ z, z ∈ Subgroup.zpowers a → z ∈ Subgroup.zpowers b → z = 1 := by
    intro z hza hzb
    by_contra hz1
    have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_mem_zpowers ha hza
    have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have h1 : Subgroup.zpowers z = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hza) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hoz])
    have h2 : Subgroup.zpowers z = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzb) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hob, hoz])
    have hbm : b ∈ Subgroup.zpowers a := by
      rw [← h1, h2]
      exact Subgroup.mem_zpowers b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbm
    exact hnot k hk
  have hcomm : ∀ (x : Subgroup.zpowers a) (y : Subgroup.zpowers b),
      Commute ((Subgroup.zpowers a).subtype x) ((Subgroup.zpowers b).subtype y) := by
    rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  let f : (Subgroup.zpowers a) × (Subgroup.zpowers b) →* Y :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm
  have hf : ∀ (x : Subgroup.zpowers a) (y : Subgroup.zpowers b), f (x, y) = (x : Y) * y :=
    fun x y => by simp [f]
  have hcz : ∀ (c : Y) (x y : Subgroup.zpowers c), x * y = y * x := by
    rintro c ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Subtype.ext (Commute.zpow_zpow_self c m n).eq
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ (k := 2) ?_ f ?_ le_top
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    exact Prod.ext (hcz a x₁ x₂) (hcz b y₁ y₂)
  · rintro ⟨x, y⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact pow_three_eq_one_of_mem_zpowers ha x.2
    · exact pow_three_eq_one_of_mem_zpowers hb y.2
  · rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hoa, hob]
    norm_num
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hf] at hxy
    have hxy' : (x : Y) = ((y : Y))⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hx1 : (x : Y) = 1 := hdisj _ x.2 (hxy' ▸ Subgroup.inv_mem _ y.2)
    have hy1 : (y : Y) = 1 := by rw [hx1] at hxy; simpa using hxy
    refine Subgroup.mem_bot.2 (Prod.ext (Subtype.ext hx1) (Subtype.ext hy1))

section Stab

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

def stabVec (v : ι → K) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).mulVec v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have : ((g⁻¹ : GL ι K) : Matrix ι ι K).mulVec ((g : Matrix ι ι K).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rwa [hg] at this

theorem mem_stabVec {v : ι → K} {g : GL ι K} :
    g ∈ stabVec v ↔ (g : Matrix ι ι K).mulVec v = v := Iff.rfl

theorem zpow_ne_of_stabVec (H : Subgroup (GL ι K)) {v : ι → K} {a b : ↥H}
    (ha : (a : GL ι K) ∈ stabVec v) (hb : (b : GL ι K) ∉ stabVec v) (k : ℤ) : a ^ k ≠ b := by
  intro h
  apply hb
  rw [← h]
  exact (stabVec v).zpow_mem ha k

end Stab

end CFSG.Quasithin.R3c
