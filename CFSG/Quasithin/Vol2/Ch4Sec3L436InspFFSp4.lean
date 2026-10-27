module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFL3
public import CFSG.Quasithin.EmptyFaithful.A38c4Main
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.Quasithin.H13.Ch4.FFSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem dvd_two_pow_sub_one_of_sp4 {p n m : ℕ} (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1)
    (hp : p.Prime) (hpL : p ∣ (2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))
    (hr : n = 3 ∨ ∃ r : ℕ, r ∣ 2 ^ (2 * n) - 1 ∧ (∀ k, 0 < k → k < 2 * n → ¬ r ∣ 2 ^ k - 1) ∧
      (r ∣ 2 ^ (2 * m) - 1 ∨ r ∣ 2 ^ (4 * m) - 1)) : p ∣ 2 ^ (2 * m) - 1 := by
  rw [FFL3.dvd_two_pow_sub_one_iff] at hpn ⊢
  rcases hr with rfl | ⟨r, hr1, hprim, hr2⟩
  ·
    rcases (Nat.dvd_prime Nat.prime_three).mp hpn with hd | hd
    · rw [hd]
      exact one_dvd _
    · rw [hd]
      rcases (Nat.Prime.dvd_mul hp).mp hpL with h | h
      · rw [FFL3.dvd_two_pow_sub_one_iff, hd] at h
        exact h
      · rw [FFL3.dvd_two_pow_sub_one_iff, hd] at h
        have h3 : 3 ∣ m := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h
        exact h3.mul_left 2
  ·
    have hord : ∀ k, r ∣ 2 ^ k - 1 → 2 * n ∣ k := by
      intro k hk
      rw [FFL3.dvd_two_pow_sub_one_iff] at hk
      have hr1' := (FFL3.dvd_two_pow_sub_one_iff (p := r) (2 * n)).mp hr1
      have hpos : 0 < orderOf (2 : ZMod r) := Nat.pos_of_dvd_of_pos hr1' (by omega)
      have hle : orderOf (2 : ZMod r) ≤ 2 * n := Nat.le_of_dvd (by omega) hr1'
      have he : orderOf (2 : ZMod r) = 2 * n := by
        refine le_antisymm hle (not_lt.mp fun hlt => hprim _ hpos hlt ?_)
        exact (FFL3.dvd_two_pow_sub_one_iff _).mpr dvd_rfl
      rwa [he] at hk
    have hn2m : n ∣ 2 * m := by
      rcases hr2 with h | h
      · exact (Nat.dvd_of_mul_dvd_mul_left (by norm_num) (hord _ h)).trans (dvd_mul_left m 2)
      · have h4 := hord _ h
        rw [show 4 * m = 2 * (2 * m) by ring] at h4
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    exact hpn.trans hn2m

section Rank

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_one_of_lam_mul_lam_eq_one {A B : SpecialLinearGroup (Fin 2) F}
    (h : lam (0 : Fin 2) A * lam (1 : Fin 2) B = 1) : A = 1 := by
  have h' : lam (0 : Fin 2) A = lam (1 : Fin 2) B⁻¹ := by
    rw [map_inv, eq_inv_iff_mul_eq_one, h]
  have hmat := congrArg (fun g : StatedSp 2 F =>
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h'
  simp only [coe_lam] at hmat
  apply Subtype.ext
  ext i j
  have e := congrFun₂ hmat
  fin_cases i <;> fin_cases j
  · have := e (Sum.inl 0) (Sum.inl 0)
    simpa [pairMat] using this
  · have := e (Sum.inl 0) (Sum.inr 0)
    simpa [pairMat] using this
  · have := e (Sum.inr 0) (Sum.inl 0)
    simpa [pairMat] using this
  · have := e (Sum.inr 0) (Sum.inr 0)
    simpa [pairMat] using this

omit [Finite F] in
theorem eq_one_of_lam_eq_one {i : Fin 2} {B : SpecialLinearGroup (Fin 2) F}
    (h : lam i B = 1) : B = 1 := by
  have hmat := congrArg (fun g : StatedSp 2 F =>
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [coe_lam] at hmat
  apply Subtype.ext
  ext a b
  have e := congrFun₂ hmat
  fin_cases a <;> fin_cases b
  · have := e (Sum.inl i) (Sum.inl i)
    simpa [pairMat] using this
  · have := e (Sum.inl i) (Sum.inr i)
    simpa [pairMat] using this
  · have := e (Sum.inr i) (Sum.inl i)
    simpa [pairMat] using this
  · have := e (Sum.inr i) (Sum.inr i)
    simpa [pairMat] using this

theorem two_le_pRank_sp4 {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F ^ 2 - 1) :
    2 ≤ CFSG.pRank p ↥(StatedSp 2 F) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpF _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hyp : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  refine CFSG.RankThree.PartOne.two_le_pRank_of_two_elements hp (e₁ := lam (0 : Fin 2) y)
    (e₂ := lam (1 : Fin 2) y) (commute_lam_lam (by decide) y y) ?_ ?_ ?_
  · rw [← map_pow, hyp, map_one]
  · rw [← map_pow, hyp, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow] at hij
    have h1 : y ^ i = 1 := eq_one_of_lam_mul_lam_eq_one hij
    rw [h1, map_one, one_mul] at hij
    have h2 : y ^ j = 1 := eq_one_of_lam_eq_one hij
    have h1' := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h2' := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hy] at h1' h2'
    exact ⟨h1', h2'⟩

end Rank

theorem false_of_sp4 {G : Type} [Group G] [Finite G] {L K : Subgroup G} {n m p : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (e : ↥L ≃* ↥(StatedSp 2 F)) (hLq : CFSG.IsQuasisimple ↥L)
    (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hm1 : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    by_contra h0
    have : m = 0 := by omega
    subst this
    norm_num at h2
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm : m = 1 := by omega
    subst hm
    exact CFSG.Quasithin.R3c2.not_isQuasisimple_statedSp_two (by rw [hF]; norm_num) e hLq
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  have hcardL : Nat.card ↥L =
      (2 ^ m) ^ 4 * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), ← pow_mul,
      ← pow_mul, ← pow_mul]
    ring_nf
  have hKL' : 2 ^ n * (4 ^ n - 1) ∣ (2 ^ m) ^ 4 * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
    rw [← hcardK, ← hcardL]
    exact Subgroup.card_dvd_of_le hKL
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n * (4 ^ n - 1) →
      r ∣ (2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1) := by
    intro r hr hr2 hrK
    have hcop : Nat.Coprime r ((2 ^ m) ^ 4) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _
        ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
    exact hcop.dvd_of_dvd_mul_left (hrK.trans hKL')
  have h2n4 : 2 ^ n - 1 ∣ 4 ^ n - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    rwa [one_pow, ← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] at this
  have hpL := hodd p hp hp2 ((hpn.trans h2n4).mul_left _)
  have hpq : p ∣ 2 ^ (2 * m) - 1 := by
    refine dvd_two_pow_sub_one_of_sp4 (by omega) hpn hp hpL ?_
    by_cases hn3 : n = 3
    · exact Or.inl hn3
    right
    obtain ⟨r, hr, hrdvd, hprim⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * n) (by omega) (by omega)
    refine ⟨r, hrdvd, hprim, ?_⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
      have h2 := Nat.dvd_sub h1 hrdvd
      rw [Nat.sub_sub_self Nat.one_le_two_pow] at h2
      omega
    have hrK : r ∣ 2 ^ n * (4 ^ n - 1) := Dvd.dvd.mul_left (by rwa [h4]) _
    exact (Nat.Prime.dvd_mul hr).mp (hodd r hr hr2 hrK)
  have hrank : 2 ≤ CFSG.Open.pRank p L := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine two_le_pRank_sp4 hp ?_
    rwa [hF, ← pow_mul, mul_comm]
  rcases hcase with h | ⟨rfl, S, _, φ, hφ, hker, s, q', -, hS⟩
  · omega
  obtain ⟨hcen, -, hnot⟩ := CFSG.Quasithin.factA318Excl_holds.1 F m hm2 hF
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e x ∈ Subgroup.center ↥(StatedSp 2 F) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [hcen, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hx'
    rw [Subgroup.mem_bot]
    exact hx'
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
  have : Nontrivial ↥L := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim a' b'])
  have hLs : IsSimpleGroup ↥L := by
    let ι : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact IsSimpleGroup.isSimpleGroup_of_surjective ι.toMonoidHom ι.surjective
  have : IsSimpleGroup S := L436.isSimpleGroup_of_isPSLEps3q hS
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : S)
      obtain ⟨x, rfl⟩ := hφ y
      exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
  obtain ⟨r', e', -, -, -, hS'⟩ := hS
  let ψ : S ≃* ↥L := (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
  exact (hnot S s r' e' hS').1 (e.toMonoidHom.comp ψ.toMonoidHom) (e.surjective.comp ψ.surjective)

end CFSG.Quasithin.H13.Ch4.FFSp4
