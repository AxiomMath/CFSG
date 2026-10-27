module

public import CFSG.Quasithin.Vol2.Ch10SecB3CBor
public import CFSG.Quasithin.Vol2.Ch10SecB3CFld
public import CFSG.Quasithin.Vol2.Ch10SecAT1Fix
public import CFSG.Quasithin.Vol2.Ch10SecB3A5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem orderOf_dvd_of_forall_primePow {M : Type*} [Monoid M] {b : M} (hb : IsOfFinOrder b)
    {K : ℕ} (hK : K ≠ 0) (h : ∀ k : ℕ, IsPrimePow (orderOf (b ^ k)) → orderOf (b ^ k) ∣ K) :
    orderOf b ∣ K := by
  have hN : orderOf b ≠ 0 := hb.orderOf_pos.ne'
  refine (Nat.factorization_prime_le_iff_dvd hN hK).mp fun p hp => ?_
  rcases Nat.eq_zero_or_pos ((orderOf b).factorization p) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hd : p ^ (orderOf b).factorization p ∣ orderOf b := Nat.ordProj_dvd _ _
    have ho : orderOf (b ^ (orderOf b / p ^ (orderOf b).factorization p)) =
        p ^ (orderOf b).factorization p := orderOf_pow_orderOf_div hN hd
    have hpp : IsPrimePow (p ^ (orderOf b).factorization p) := ⟨p, _, hp.prime, hpos, rfl⟩
    have := h _ (ho ▸ hpp)
    rw [ho] at this
    exact (hp.pow_dvd_iff_le_factorization hK).mp this

theorem pow_zmod_eq_one (N : ℕ) (x : Multiplicative (ZMod N × ZMod N)) : x ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext <;> simp [nsmul_eq_mul]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_fsuL0_of_kill (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I) {X : Subgroup G}
    (hXM : X ≤ fsuM T L)
    (hkill : ∀ y ∈ X, ∀ r : ℕ, r.Prime → r ≠ 2 → y ^ r = 1 →
      ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) → y = 1)
    {z : G} (hz : z ∈ X) (hzo : Odd (orderOf z)) : z ∈ fsuL0 T L := by
  refine mem_of_forall_primePow (isOfFinOrder_of_finite z) fun k hk => ?_
  obtain ⟨r, j, hr, hj, hrj⟩ := hk
  have hr' : r.Prime := Nat.prime_iff.mpr hr
  have hzk : z ^ k ∈ X := X.pow_mem hz k
  have hok : Odd (orderOf (z ^ k)) := hzo.of_dvd_nat (orderOf_pow_dvd k)
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [← hrj] at hok
    exact (Nat.not_even_iff_odd.mpr hok) (Nat.even_pow.mpr ⟨even_two, hj.ne'⟩)
  by_cases hrL : r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)
  · rw [← h1013 G T L I hyp r hr' hr2 hrL]
    exact Subgroup.subset_closure ⟨hXM hzk, j, hrj.symm⟩
  · exfalso
    have hrj' : r ^ j = r ^ (j - 1) * r := by rw [← pow_succ]; congr 1; omega
    have hyo : orderOf ((z ^ k) ^ r ^ (j - 1)) = r := by
      rw [orderOf_pow_of_dvd (pow_pos hr'.pos _).ne'
          (by rw [← hrj, hrj']; exact dvd_mul_right _ _),
        ← hrj, hrj', Nat.mul_div_cancel_left _ (pow_pos hr'.pos _)]
    have hyr : ((z ^ k) ^ r ^ (j - 1)) ^ r = 1 := by
      have := pow_orderOf_eq_one ((z ^ k) ^ r ^ (j - 1))
      rwa [hyo] at this
    have hy1 := hkill _ (X.pow_mem hzk _) r hr' hr2 hyr hrL
    rw [hy1, orderOf_one] at hyo
    exact hr'.one_lt.ne' hyo.symm

theorem inf_le_normalizer_T0
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (hK : BenderHyp (↥L ⧸ CFSG.pCore 2 ↥L)) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    (H ⊓ fsuM T L) ⊓ fsuL0 T L ≤ Subgroup.normalizer (T0 T L : Set G) := by
  obtain ⟨hsimp, h2⟩ := simple_even_of_bender hK
  have hD1 := D1_ne_bot hyp h2
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, α, -, hΨk, hΨL, hΨt⟩ := exists_coordQ h37 h38 hyp (MulEquiv.refl _) ht htn
  have c : CoordL T L t Ψ α := ⟨hΨk, hΨL, hΨt⟩
  set Y := (H ⊓ fsuM T L) ⊓ fsuL0 T L with hYdef
  have hTX : T ≤ H ⊓ fsuM T L := le_inf hH.1.1 (SecA.le_fsuM T L)
  have hT0Y : T0 T L ≤ Y := inf_le_inf_right _ hTX
  have htX := hTX ht
  have htY : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y := fun y hy =>
    ⟨(H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).inv_mem htX) hy.1) htX,
      conj_mem_fsuL0 ht hy.2⟩
  set A₁ := (imgIn Ψ Y).map (MonoidHom.fst (↥L ⧸ CFSG.pCore 2 ↥L) (↥L ⧸ CFSG.pCore 2 ↥L))
  have hDA : D1 T L ≤ A₁ := by
    rintro _ ⟨⟨d, hdL⟩, hdT, rfl⟩
    have hd := Subgroup.mem_subgroupOf.mp hdT
    exact ⟨_, mem_imgIn.mpr ⟨d, SecA.le_fsuL0 T L hdL,
      hT0Y ⟨hd.1, SecA.le_fsuL0 T L hdL⟩, c.onL d _ hdL⟩, rfl⟩
  have hA₁ : A₁ ≤ Subgroup.normalizer (D1 T L : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rcases hF6 _ hK (D1 T L) A₁ (isSylowTwoOf_D1 hyp) hDA with h | h
    · exact h
    · exact absurd ((c.le_of_fst_eq_top hyp hD1 hT0Y h).trans
        (inf_le_left.trans inf_le_left)) (not_le_of_isHStar h331 hyp hH)
  have hαD := c.map_D1 hyp ht
  have hT0 := c.T0_eq hyp ht
  have hcoord : ∀ (y : G) (hy0 : y ∈ fsuL0 T L), y ∈ Y →
      (Ψ ⟨y, hy0⟩).1 ∈ Subgroup.normalizer (D1 T L : Set (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
        (Ψ ⟨y, hy0⟩).2 ∈ Subgroup.normalizer (D1 T L : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro y hy0 hyY
    refine ⟨hA₁ ⟨_, mem_imgIn.mpr ⟨y, hy0, hyY, rfl⟩, rfl⟩, mem_normalizer_of_map_eq hαD ?_⟩
    have hm := conj_mem_fsuL0 ht hy0
    have hs : Ψ ⟨t⁻¹ * y * t, hm⟩ = (α (Ψ ⟨y, hy0⟩).2, (Ψ ⟨y, hy0⟩).1) :=
      c.swap ⟨y, hy0⟩ hm
    have h3 : (Ψ ⟨t⁻¹ * y * t, hm⟩).1 ∈
        Subgroup.normalizer (D1 T L : Set (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      hA₁ ⟨_, mem_imgIn.mpr ⟨_, hm, htY y hyY, rfl⟩, rfl⟩
    rw [hs] at h3
    exact h3
  have hfwd : ∀ y ∈ Y, ∀ s ∈ T0 T L, y * s * y⁻¹ ∈ T0 T L := by
    intro y hy s hs
    have hs' := hs
    rw [hT0] at hs'
    obtain ⟨hs0, hsD⟩ := mem_preIn.mp hs'
    have hy0 := hy.2
    have hm : y * s * y⁻¹ ∈ fsuL0 T L :=
      (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hy0 hs0) ((fsuL0 T L).inv_mem hy0)
    rw [hT0]
    refine mem_preIn.mpr ⟨hm, ?_⟩
    have e1 : (⟨y * s * y⁻¹, hm⟩ : ↥(fsuL0 T L)) = ⟨y, hy0⟩ * ⟨s, hs0⟩ * ⟨y, hy0⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
    obtain ⟨h1, h2⟩ := hcoord y hy0 hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 _).mp hsD.1,
      (Subgroup.mem_normalizer_iff.mp h2 _).mp hsD.2⟩
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨hfwd y hy s, fun h => ?_⟩
  have := hfwd y⁻¹ (Y.inv_mem hy) _ h
  simpa [mul_assoc] using this

theorem oTwoUpper_le_B0
    (hF5 : FactCommField) (hF6 : FactBenderOver)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h1013 : Stmt10_1_3) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥)
    (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) :
    oTwoUpper (H ⊓ fsuM T L) ≤ B0 T L := by
  have hkill : ∀ y ∈ H ⊓ fsuM T L, ∀ r : ℕ, r.Prime → r ≠ 2 → y ^ r = 1 →
      ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) → y = 1 :=
    fun y hy r hr hr2 hyr hrL => eq_one_of_mem_cenL0 hfaith hB hy hr hr2 hyr
      (mem_cenL0_of_field hF5 h37 h38 h1011 h331 hyp hc hH hZH hy.1 hy.2 hr hr2 hyr hrL)
  have hN := inf_le_normalizer_T0 hF6 h37 h38 h331 hyp (bender_of_cases hc).1 hH
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hx0 := mem_fsuL0_of_kill h1013 hyp inf_le_right hkill hx.1 hx.2
  exact mem_oTwoUpper_of_odd ⟨hx0, hN ⟨hx.1, hx0⟩⟩ hx.2

theorem exists_hall_mem (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) (hle : oTwoUpper (H ⊓ fsuM T L) ≤ B0 T L)
    {c : G} (hc : c ∈ H ⊓ fsuM T L) (hpp : IsPrimePow (orderOf c)) (hodd : Odd (orderOf c)) :
    ∃ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D (B0 T L) ∧
      c ∈ D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨r, j, hr, hj, hrj⟩ := hpp
  have hr' : r.Prime := Nat.prime_iff.mpr hr
  have : Fact r.Prime := ⟨hr'⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [← hrj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj.ne'⟩)
  have hcB := hle (mem_oTwoUpper_of_odd hc hodd)
  have hP : IsPGroup r (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hrj])
  obtain ⟨D₀, hD₀⟩ := SecA.exists_isHallTwoPrimeOf_B0 hyp
  obtain ⟨x, hx, hxle⟩ :=
    Ch11.SecB.exists_conj_le_hall hr2 hD₀ (Subgroup.zpowers_le.mpr hcB) hP
  refine ⟨conjSub x D₀, isHallTwoPrimeOf_conjSub hx hD₀, hxle (Subgroup.mem_zpowers c), ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun z hz => (Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH) hz) c hc.1).symm

theorem false_of_case17 (h1012 : Stmt10_1_2) (hyp : Hyp10 G T L I) (hnL : ¬ LBarL32 L)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Seven T L I) {H : Subgroup G}
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) (hle : oTwoUpper (H ⊓ fsuM T L) ≤ B0 T L)
    {B : Subgroup G} (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {b₀ : G}
    (hb₀ : b₀ ∈ B) (hb1 : b₀ ≠ 1) : False := by
  have hbo : Odd (orderOf b₀) := hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hb₀)
  refine hb1 (Subgroup.mem_bot.mp
    (mem_of_forall_primePow (isOfFinOrder_of_finite b₀) fun k hk => ?_))
  obtain ⟨D, hD, hcD⟩ := exists_hall_mem hyp hZH hle (Subgroup.pow_mem _ (hB.1 hb₀) k) hk
    (hbo.of_dvd_nat (orderOf_pow_dvd k))
  rwa [((h1012 G T L I hyp).2.2.2.2.2.2.2.1 hnL D hD).1 hc] at hcD

theorem eq_two_of_case4 (h1012 : Stmt10_1_2) (hyp : Hyp10 G T L I) (hnL : ¬ LBarL32 L) {n : ℕ}
    (h4 : Case10_1_1Four T L I n) {H : Subgroup G} (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥)
    (hle : oTwoUpper (H ⊓ fsuM T L) ≤ B0 T L) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {m : ℕ} (hm : 2 ≤ m)
    {b₀ : G} (hb₀ : b₀ ∈ B) (ho : orderOf b₀ = 2 ^ m - 1) : m = 2 := by
  have hbo : Odd (orderOf b₀) := hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hb₀)
  have hd : orderOf b₀ ∣ 2 ^ n + 1 :=
    orderOf_dvd_of_forall_primePow (isOfFinOrder_of_finite b₀) (by positivity) fun k hk => by
      obtain ⟨D, hD, hcD⟩ := exists_hall_mem hyp hZH hle (Subgroup.pow_mem _ (hB.1 hb₀) k) hk
        (hbo.of_dvd_nat (orderOf_pow_dvd k))
      obtain ⟨f, hf⟩ := ((h1012 G T L I hyp).2.2.2.2.2.2.2.1 hnL D hD).2 n h4
      rw [← Subgroup.orderOf_mk _ hcD, ← orderOf_injective f hf ⟨b₀ ^ k, hcD⟩]
      exact orderOf_dvd_of_pow_eq_one (pow_zmod_eq_one _ _)
  rw [ho] at hd
  exact eq_two_of_dvd hm hd

theorem stmt10_2_3_comm
    (hF5 : FactCommField) (hF6 : FactBenderOver)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥)
    (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {m : ℕ} (hm : 2 ≤ m)
    {b₀ : G} (hb₀ : b₀ ∈ B) (ho : orderOf b₀ = 2 ^ m - 1) :
    m = 2 ∧ (∀ n, ¬ Case10_1_1One T L I n) ∧ ¬ Case10_1_1Seven T L I := by
  have hnL := (bender_of_cases hc).2
  have hle := oTwoUpper_le_B0 hF5 hF6 h37 h38 h1011 h1013 h331 hyp hc hH hZH hfaith hB
  have hb1 : b₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ho
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have h17 : ¬ ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Seven T L I) := fun h =>
    false_of_case17 h1012 hyp hnL h hZH hle hB hb₀ hb1
  refine ⟨?_, fun n h1 => h17 (Or.inl ⟨n, h1⟩), fun h7 => h17 (Or.inr h7)⟩
  rcases hc with h1 | ⟨n, h4⟩ | h7
  · exact absurd (Or.inl h1) h17
  · exact eq_two_of_case4 h1012 hyp hnL h4 hZH hle hB hm hb₀ ho
  · exact absurd (Or.inr h7) h17

end CFSG.Quasithin.Vol2.Ch10.SecB
