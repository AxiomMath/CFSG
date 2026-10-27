module

public import CFSG.Quasithin.EmptyFaithful.S153E57A
public import CFSG.Quasithin.EmptyFaithful.S153E58In

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153E58

open S153E57

section MinNormal

variable {Γ : Type*} [Group Γ]

theorem exists_isMinNormalIn [Finite Γ] (H : Subgroup Γ) (hH : H ≠ ⊥) : ∃ K, IsMinNormalIn H K := by
  classical
  obtain ⟨K, ⟨hKH, hKn, hK1⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup Γ))
    {K : Subgroup Γ | K ≤ H ∧ (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) ∧ K ≠ ⊥}
    ⟨H, le_rfl, fun h hh k hk => H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh), hH⟩
  refine ⟨K, hKH, hKn, hK1, fun K' hK'K hK'n => ?_⟩
  by_cases hK'1 : K' = ⊥
  · exact Or.inl hK'1
  · right
    by_contra hne
    exact hmin K' ⟨hK'K.trans hKH, hK'n, hK'1⟩ (lt_of_le_of_ne hK'K hne)

theorem commutator_normalized {H K : Subgroup Γ} (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    ∀ h ∈ H, ∀ n ∈ ⁅K, K⁆, h * n * h⁻¹ ∈ ⁅K, K⁆ := by
  intro h hh n hn
  rw [Subgroup.commutator_def] at hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hK h hh a ha) (hK h hh b hb)
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa [mul_assoc] using (⁅K, K⁆).mul_mem ihx ihy
  | inv x _ ih =>
    simpa [mul_assoc] using (⁅K, K⁆).inv_mem ih

theorem IsMinNormalIn.commutator_eq {H K : Subgroup Γ} (h : IsMinNormalIn H K) :
    ⁅K, K⁆ = ⊥ ∨ ⁅K, K⁆ = K := by
  have hle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx y hy => by
    have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
    rw [this]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  exact h.2.2.2 _ hle (commutator_normalized h.2.1)

theorem IsMinNormalIn.exists_isPGroup [Finite Γ] {H K : Subgroup Γ} (h : IsMinNormalIn H K)
    (hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) : ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥K := by
  obtain ⟨hKH, hKn, hK1, hmin⟩ := h
  have hcard : Nat.card ↥K ≠ 1 := fun h1 => hK1 (Subgroup.card_eq_one.1 h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  let P : Subgroup Γ :=
    { carrier := {y | y ∈ K ∧ ∃ n : ℕ, y ^ p ^ n = 1}
      one_mem' := ⟨K.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, n, hn⟩ ⟨hb, m, hm⟩
        refine ⟨K.mul_mem ha hb, n + m, ?_⟩
        rw [(Commute.mul_pow (hab a ha b hb) _)]
        have h1 : a ^ p ^ (n + m) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
        have h2 : b ^ p ^ (n + m) = 1 := by rw [add_comm, pow_add, pow_mul, hm, one_pow]
        rw [h1, h2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨K.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩ }
  have hPK : P ≤ K := fun y hy => hy.1
  have hPn : ∀ h ∈ H, ∀ k ∈ P, h * k * h⁻¹ ∈ P := by
    rintro h hh k ⟨hk, n, hn⟩
    refine ⟨hKn h hh k hk, n, ?_⟩
    rw [conj_pow, hn]
    simp
  have hxne : (x : Γ) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hxP : (x : Γ) ∈ P := ⟨x.2, 1, by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this⟩
    rw [hbot, Subgroup.mem_bot] at hxP
    exact hxne hxP
  have hPeq : P = K := (hmin P hPK hPn).resolve_left hP1
  refine ⟨p, hp, fun g => ?_⟩
  have hg : (g : Γ) ∈ P := by
    rw [hPeq]
    exact g.2
  obtain ⟨n, hn⟩ := hg.2
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

end MinNormal

theorem mem_normalizer_of_forall' {M' : Type*} [Group M'] [Finite M'] {H : Subgroup M'} {y : M'}
    (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set M') := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]


section OTwo

variable {Γ : Type*} [Group Γ]

theorem oTwoUpper_eq_of_odd {K : Subgroup Γ} (hodd : ∀ x ∈ K, Odd (orderOf x)) : oTwoUpper K = K :=
  le_antisymm (oTwoUpper_le K) fun x hx => mem_oTwoUpper_of_odd hx (hodd x hx)

theorem oTwoUpper_eq_of_perfect [Finite Γ] {K : Subgroup Γ} (hK : ⁅K, K⁆ = K) : oTwoUpper K = K := by
  refine le_antisymm (oTwoUpper_le K) ?_
  let N : Subgroup ↥K := (oTwoUpper K).subgroupOf K
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_oTwoUpper (X := K) (g := (g : Γ)) (Subgroup.le_normalizer g.2) hn
    simpa using this⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have hP : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Finite (↥K ⧸ N) := inferInstance
  have : Group.IsNilpotent (↥K ⧸ N) := hP.isNilpotent
  have : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) ‹_›
  intro g hg
  have : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

end OTwo

section SmallIrr

variable {W : Type} [CommGroup W]

theorem eq_one_of_perfect_perm {K : Subgroup (MulAut W)} (hK : ⁅K, K⁆ = K)
    (α : Type) [Fintype α] (hα : Fintype.card α ≤ 4) (f : ↥K →* Equiv.Perm α) : f = 1 := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have : Group.IsSolvable (Equiv.Perm α) := Equiv.Perm.isSolvable (by simpa using hα)
  have : Group.IsSolvable ↥f.range := inferInstance
  have : Subsingleton ↥f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥f.range ‹_›
  refine MonoidHom.ext fun k => ?_
  have hk : f k ∈ f.range := ⟨k, rfl⟩
  have h1 : (⟨f k, hk⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
  rw [MonoidHom.one_apply]
  exact congrArg Subtype.val h1

theorem eq_one_of_isPGroup_perm {K : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : IsPGroup p ↥K) (α : Type) [Fintype α] (hα : Fintype.card α ≤ 4) (f : ↥K →* Equiv.Perm α) :
    f = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hR : IsPGroup p ↥f.range := hK.of_surjective f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
  obtain ⟨j, hj⟩ := hR.exists_card_eq
  have hdvd : Nat.card ↥f.range ∣ Nat.card (Equiv.Perm α) := Subgroup.card_subgroup_dvd_card _
  have hfac : Nat.card (Equiv.Perm α) ∣ 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    exact (Nat.factorial_dvd_factorial hα).trans (by decide)
  have hj0 : j = 0 := by
    by_contra hne
    have h1 : p ∣ 24 := (dvd_pow_self p hne).trans (hj ▸ hdvd.trans hfac)
    have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24] at h1
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  rw [hj0, pow_zero] at hj
  have : Subsingleton ↥f.range := (Nat.card_eq_one_iff_unique.1 hj).1
  refine MonoidHom.ext fun k => ?_
  have hk : f k ∈ f.range := ⟨k, rfl⟩
  have h1 : (⟨f k, hk⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
  rw [MonoidHom.one_apply]
  exact congrArg Subtype.val h1

theorem eight_le_card_of_irr [Finite W] (hW : ∀ w : W, w * w = 1) {K : Subgroup (MulAut W)}
    (hK : ∀ (α : Type) [Fintype α], Fintype.card α ≤ 4 → ∀ f : ↥K →* Equiv.Perm α, f = 1)
    (hfix : ∀ x : W, (∀ k ∈ K, k x = x) → x = 1) {W₀ : Subgroup W} (h : IsIrrOn153 K W₀) :
    8 ≤ Nat.card ↥W₀ := by
  by_contra hlt
  push Not at hlt
  have hP2 : IsPGroup 2 ↥W₀ := isPGroup_two_of_mul_self hW W₀
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hn3 : n ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle4 : Nat.card ↥W₀ ≤ 4 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 4 := by norm_num
  have : Fintype ↥W₀ := Fintype.ofFinite _
  let act : MulAction ↥K ↥W₀ :=
    { smul := fun s u => ⟨(s : MulAut W) u, h.2.1 s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have h1 := hK ↥W₀ (by simpa [Nat.card_eq_fintype_card] using hle4) (MulAction.toPermHom ↥K ↥W₀)
  apply h.1
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  apply hfix u
  intro k hk
  have h2 := congrArg (fun φ : Equiv.Perm ↥W₀ => (φ ⟨u, hu⟩ : ↥W₀).1) (DFunLike.congr_fun h1 ⟨k, hk⟩)
  exact h2

end SmallIrr

end S153E58

end CFSG.Quasithin
