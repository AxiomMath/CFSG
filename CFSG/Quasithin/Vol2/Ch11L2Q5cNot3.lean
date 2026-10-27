module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical
public import CFSG.Quasithin.Vol2.Ch11SecBL2OQ
public import CFSG.Quasithin.Vol2.Ch11SecBL2UA312
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem three_dvd_two_pow_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 n

theorem ordA_one_two_pow_eq {n : ℕ} (hn : 1 ≤ n) : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, show (1 + 1 : ℕ) = 2 by rfl, h, Nat.div_one]

theorem three_dvd_ordG2 (n : ℕ) : 3 ∣ ordG2 (2 ^ n) := by
  unfold ordG2
  exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one n) _

theorem three_dvd_card_psl {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) := by
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.exists_orderOf_eq_three_statedProj_statedSL
    (K := K) hm
  rw [Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K).toEquiv, ← hy]
  have : Finite (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL m K)) :=
    Finite.of_equiv _
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K).toEquiv
  exact orderOf_dvd_natCard y

theorem three_dvd_card_statedProj_statedSp {K : Type} [Field K]
    [Finite (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))] :
    3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) := by
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.exists_orderOf_eq_three_statedProj_statedSp
    (K := K) (n := 2) le_rfl
  rw [← hy]
  exact orderOf_dvd_natCard y

section Leaves

variable {K Y : Type} [Group K] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect K]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y) (hψ : Function.Surjective ψ)
  (hY3 : ¬ 3 ∣ Nat.card Y) (hYc : 20160 < Nat.card Y)
include hY hN hQ hψ hY3 hYc

omit hY3 in
theorem false_of_card_le_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h2 : Nat.card X ≤ 20160) : False := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  have h := card_le_of_surjective hY hN hQ ψ hψ f hf
  omega

omit hYc in
theorem false_of_simple_of_three_dvd {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (f : K →* X) (hf : Function.Surjective f) (h3 : 3 ∣ Nat.card X) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact hY3 (by rw [Nat.card_congr e.toEquiv]; exact h3)

omit hY3 in
theorem false_of_alt_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (e : X ≃* alternatingGroup (Fin n)) : False := by
  have hc : Nat.card X = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alt (by omega)]
  refine false_of_card_le_of_not_three hY hN hQ ψ hψ hYc f hf ?_ ?_ <;> rw [hc]
  · interval_cases n <;> decide
  · interval_cases n <;> decide

omit hY3 in
theorem false_of_hatAlt_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (h : IsHat X (alternatingGroup (Fin n))) : False := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact false_of_alt_of_not_three hY hN hQ ψ hψ hYc
    ((QuotientGroup.mk' (Subgroup.center X)).comp f) ((QuotientGroup.mk'_surjective _).comp hf)
    hn5 hn8 e

omit hY3 in
theorem false_of_card_eq_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {c : ℕ} (hc : Nat.card X = c) (h1 : 1 < c) (h2 : c ≤ 20160) :
    False :=
  false_of_card_le_of_not_three hY hN hQ ψ hψ hYc f hf (hc ▸ h1) (hc ▸ h2)

omit hYc in
theorem false_of_sl2_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : IsSL2 p X) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    isSimpleGroup_psl2 hp5
  refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3
    (((QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))).comp e.toMonoidHom).comp f)
    (((QuotientGroup.mk'_surjective _).comp e.surjective).comp hf) ?_
  exact three_dvd_card_psl (le_refl 2)

omit hYc in
theorem false_of_psl2_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {p : ℕ} (hp3 : 3 < p) (h : IsPSL 2 p 1 X) :
    False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 f hf ?_
  have h2 := two_mul_card_isPSL_two (by omega) h
  have h3 : 3 ∣ p * (p ^ 2 - 1) := by
    have e : p * (p ^ 2 - 1) = (p - 1) * p * (p + 1) := by
      have h1 : 1 ≤ p := by omega
      have h1' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h1']
      ring
    rw [e]
    have : (p - 1) % 3 = 0 ∨ p % 3 = 0 ∨ (p + 1) % 3 = 0 := by omega
    rcases this with h | h | h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) _) _
    · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) _
  rw [← h2] at h3
  exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 2)).mp h3

omit hYc in
theorem false_of_psl22_of_not_three {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (h : IsPSL 2 2 n X) : False := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h).2
  refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 f hf ?_
  have hn : 1 ≤ n := by
    obtain ⟨⟨-, h1, -⟩, -⟩ := h
    exact h1
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
    ordA_one_two_pow_eq hn]
  exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one n) _

omit hYc in
theorem false_of_m22_of_not_three (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f) (h : IsSporadic .M22 X) : False := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := h
  have := hM.1
  have : IsSimpleGroup X := e.isSimpleGroup
  refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 f hf ?_
  rw [Nat.card_congr e.toEquiv, hM.2.1]
  norm_num

omit hYc in
theorem false_of_m24_of_not_three (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f) (h : IsSporadic .M24 X) : False := by
  obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
  have := hM.2.2.1
  have : IsSimpleGroup X := e.isSimpleGroup
  refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 f hf ?_
  rw [Nat.card_congr e.toEquiv, hM.2.2.2]
  norm_num

omit hYc in
theorem false_of_hatM22_of_not_three (hM : FactMathieuOrders) {X : Type} [Group X] [Finite X]
    (f : K →* X) (hf : Function.Surjective f)
    (h : IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : False := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := Finite.of_equiv _ e.toEquiv
  exact false_of_m22_of_not_three hY hN hQ ψ hψ hY3 hM
    ((e.toMonoidHom.comp (QuotientGroup.mk' _)).comp f)
    ((e.surjective.comp (QuotientGroup.mk'_surjective _)).comp hf) ⟨MulEquiv.refl _⟩

theorem a312C3_of_case_of_not_three (hM : FactMathieuOrders) {Γ : Type} [Group Γ] [Finite Γ]
    {B L : Subgroup Γ} (σ : K →* ↥B) (hσ : Function.Surjective σ) (hcase : A312Case B L) :
    A312C3 B L := by
  set σ2 := (QuotientGroup.mk' (CFSG.pCore 2 ↥B)).comp σ with hσ2def
  have hσ2 : Function.Surjective σ2 := (QuotientGroup.mk'_surjective _).comp hσ
  have hcard : ∀ {X : Type} [Group X] [Finite X] {c : ℕ} (f : K →* X), Function.Surjective f →
      Nat.card X = c → 1 < c → c ≤ 20160 → False :=
    fun f hf hc h1 h2 => false_of_card_eq_of_not_three hY hN hQ ψ hψ hYc f hf hc h1 h2
  have halt : ∀ {X : Type} [Group X] [Finite X] {n : ℕ} (f : K →* X), Function.Surjective f →
      5 ≤ n → n ≤ 8 → (X ≃* alternatingGroup (Fin n)) → False :=
    fun f hf hn5 hn8 e => false_of_alt_of_not_three hY hN hQ ψ hψ hYc f hf hn5 hn8 e
  have hhat : ∀ {X : Type} [Group X] [Finite X] {n : ℕ} (f : K →* X), Function.Surjective f →
      5 ≤ n → n ≤ 8 → IsHat X (alternatingGroup (Fin n)) → False :=
    fun f hf hn5 hn8 h => false_of_hatAlt_of_not_three hY hN hQ ψ hψ hYc f hf hn5 hn8 h
  unfold A312Case A312C2 A312C3 A312C4 A312C5 A312C6 A312C7 A312C8 A312C9 A312C10 A312C11
    A312C12 A312C13 A312C14 A312C15 A312C16 A312C17 A312C18 A312C19 A312C20 at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨⟨n, hn⟩, -, -⟩ := h
    exact (false_of_psl22_of_not_three hY hN hQ ψ hψ hY3 σ2 hσ2 hn).elim
  · exact h
  all_goals exfalso
  · obtain ⟨hB, -, -⟩ := h
    exact hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · obtain ⟨hB, -, -⟩ := h
    exact hcard σ2 hσ2 (card_isPSL_four_two_one hB) (by norm_num) (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hcard σ hσ (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hhat σ hσ (by norm_num) (by norm_num) hB
  · rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · exact false_of_psl2_of_not_three hY hN hQ ψ hψ hY3 σ hσ hp3 hB
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
  · rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · exact false_of_sl2_of_not_three hY hN hQ ψ hψ hY3 σ hσ hp hp3 hB
    · obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
      exact halt σ hσ (by norm_num) (by norm_num) e
    · exact hhat σ hσ (by norm_num) (by norm_num) hB
  · obtain ⟨p, hp, hp3, hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
      false_of_sl2_of_not_three hY hN hQ ψ hψ hY3 g' hg' hp hp3 hZ
  · obtain ⟨hB, -⟩ := h
    obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 6)) := hB
    exact halt σ hσ (by norm_num) (by norm_num) e
  · rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 6)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, -⟩ := h
    · exact false_of_m22_of_not_three hY hN hQ ψ hψ hY3 hM σ hσ hB
    · exact hcard σ hσ (card_isPSL_three_two_two hB) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 7)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 6)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
  · obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_four_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB, -⟩ := h
    obtain ⟨e⟩ : Nonempty (↥B ≃* alternatingGroup (Fin 5)) := hB
    exact halt σ hσ (by norm_num) (by norm_num) e
  · obtain ⟨hB, -⟩ := h
    exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
      obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
      exact halt g' hg' (by norm_num) (by norm_num) e
  · obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        false_of_hatM22_of_not_three hY hN hQ ψ hψ hY3 hM g' hg' hZ
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        false_of_m24_of_not_three hY hN hQ ψ hψ hY3 hM g' hg' hZ
    · obtain ⟨e⟩ : Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ2 hσ2 (by norm_num) (by norm_num) e
    · exact hhat σ2 hσ2 (by norm_num) (by norm_num) hB
    · exact hcard σ2 hσ2 (card_isPSL_four_two_one hB) (by norm_num) (by norm_num)
    · exact hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => by
        obtain ⟨e⟩ : Nonempty (Z ≃* alternatingGroup (Fin 5)) := hZ
        exact halt g' hg' (by norm_num) (by norm_num) e
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
  · obtain ⟨hB | hB, -⟩ := h
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' =>
        hcard g' hg' (card_isPSL_three_two_one hZ) (by norm_num) (by norm_num)
    · exact out_ext σ hσ hB fun Z _ _ hZ g' hg' => hhat g' hg' (by norm_num) (by norm_num) hZ
  · obtain ⟨hB | hB, -, -⟩ := h
    · obtain ⟨e⟩ : Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) := hB
      exact halt σ2 hσ2 (by norm_num) (by norm_num) e
    · exact hcard σ2 hσ2 (card_isPSL_three_two_one hB) (by norm_num) (by norm_num)

end Leaves

variable {G : Type} [Group G] [Finite G]

theorem overgroup_iso_or_c3_of_not_three
    (hM : FactMathieuOrders) {T K Kp : Subgroup G} {Y : Type}
    [Group Y] [Finite Y] {k : ℕ} (hk : 2 ≤ k) (hY : L2BadType k Y) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hYc : 20160 < Nat.card Y)
    (hKl : quasithinIsLocal T K) (hKpl : quasithinIsLocal T Kp) (hKKp : K ≤ Kp)
    (hKq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) (ψ : ↥K →* Y)
    (hψ : Function.Surjective ψ)
    (h312 : A312Refined (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) ∨
      A312C3 (modO2Image (Kp ⊔ T) K) (modO2Image (Kp ⊔ T) Kp) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Kp ⊔ T with hHdef
  have hS : IsSylowTwoOf T H := ⟨le_sup_right, hKpl.1, hKpl.2.2.1⟩
  have hBH : K ≤ H := hKKp.trans le_sup_left
  have hL : Kp ∈ cComp H := hKpl.2.1
  have hB : K ∈ lFamily T := hKl.2.1
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hYs : IsSimpleGroup Y := hY.isSimpleGroup hk
  have hYab : ∃ a b : Y, a * b ≠ b * a := nonabelian_of_perfect_surjective ψ hψ
  set σ : ↥K →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom with hσ
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  have hBL : modO2Image H K ≤ modO2Image H Kp := Subgroup.map_mono fun x hx => hKKp hx
  have hN : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := by
    exact CFSG.pCore_isPGroup
  have hNn : (CFSG.Open.pCore 2 ↥K).Normal := by
    exact CFSG.pCore_normal
  rcases lemma_1_2_4_refined h312 hS hBH hB hL hKKp with heq | ⟨-, hcase⟩ | ⟨-, hnon⟩
  · exact Or.inl (nonempty_mulEquiv_modO2_of_eq hBH hL heq)
  · exact Or.inr (a312C3_of_case_of_not_three hYab hN hKq ψ hψ hY3 hYc hM σ hσs hcase)
  · exact (false_of_a312Nonquasi hk hY hKq ψ hψ hBL σ hσs hnon).elim

end CFSG.Quasithin.Vol2.Ch11.SecB
