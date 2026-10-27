module

public import CFSG.RankThree.PartOne.F106.QD32Class
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.PartOne.F106.FiveG2
public import CFSG.RankThree.PartOne.F106.FiveRee
public import CFSG.RankThree.PartOne.F106.FiveTri

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.GroupTheory CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.LIT CFSG.Open
  CFSG.RankThree.PartOne.BRANCH CFSG.RankThree.PartOne.N143

theorem card_ge_pow_four_of_induces {T : Type} [Group T] [Finite T] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {E R : Subgroup T} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) :
    q ^ 4 ≤ Nat.card E := by
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  exact card_ge_pow_four_of_normalizer_qd32 hq hq2 hE h.normalizes ψ hψs hψc

theorem pow_four_dvd_card_of_card {T : Type} [Group T] [Finite T] {q : ℕ} (hq : q.Prime)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1) (h4 : q ^ 4 ≤ Nat.card Y) :
    q ^ 4 ∣ Nat.card Y := by
  have : Fact q.Prime := ⟨hq⟩
  have hY : IsPGroup q Y := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hY
  rw [hk] at h4 ⊢
  exact pow_dvd_pow q ((Nat.pow_le_pow_iff_right hq.one_lt).mp h4)

theorem pow_four_dvd_card_group_of_card {T : Type} [Group T] [Finite T] {q : ℕ} (hq : q.Prime)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1) (h4 : q ^ 4 ≤ Nat.card Y) :
    q ^ 4 ∣ Nat.card T :=
  (pow_four_dvd_card_of_card hq hexp h4).trans (Subgroup.card_subgroup_dvd_card Y)

theorem exists_sub_card_pow_three_of_card {T : Type} [Group T] [Finite T] {q : ℕ} (hq : q.Prime)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1) (h4 : q ^ 4 ≤ Nat.card Y) :
    ∃ E' : Subgroup T, (∀ x ∈ E', x ^ q = 1) ∧ Nat.card E' = q ^ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  have hdvd : q ^ 3 ∣ Nat.card Y :=
    (pow_dvd_pow q (by norm_num : 3 ≤ 4)).trans (pow_four_dvd_card_of_card hq hexp h4)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  refine ⟨H.map Y.subtype, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩
    exact hexp d d.2
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hH]

theorem exp_of_isElementaryAbelian {T : Type} [Group T] {q : ℕ} {E : Subgroup T}
    (hE : IsElementaryAbelian q E) : ∀ x ∈ E, x ^ q = 1 :=
  fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := q) (A := E) x hx

theorem five_le_of_prime_ne {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) : 5 ≤ q := by
  have h2 := hq.two_le
  by_contra hlt
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

theorem false_G2_of_card
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Subgroup X} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (h4 : q ^ 4 ≤ Nat.card Y) : False := by
  by_cases hq3 : q = 3
  · subst hq3
    have hb := card_le_G2_three hmod hexp
    omega
  · obtain ⟨E', hE', hcard'⟩ := exists_sub_card_pow_three_of_card hq hexp h4
    exact false_G2_prime hmod hq (five_le_of_prime_ne hq hq2 hq3) hE' hcard'

theorem false_triality_of_card
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .trialityD4 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Subgroup X} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (h4 : q ^ 4 ≤ Nat.card Y) : False := by
  by_cases hq3 : q = 3
  · subst hq3
    have hb := card_le_triality_three hmod hexp
    omega
  · obtain ⟨E', hE', hcard'⟩ := exists_sub_card_pow_three_of_card hq hexp h4
    exact Q1327C.false_of_pow_three_triality_five hmod hq (five_le_of_prime_ne hq hq2 hq3) hE'
      hcard'

theorem false_ree_of_card
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ReeTitsModel X .twistedF4 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Subgroup X} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (h4 : q ^ 4 ≤ Nat.card Y) : False := by
  by_cases hq3 : q = 3
  · subst hq3
    have hb := card_le_ree_three hmod hexp
    omega
  · obtain ⟨E', hE', hcard'⟩ := exists_sub_card_pow_three_of_card hq hexp h4
    exact Q1327C.false_of_pow_three_ree_five hmod hq (five_le_of_prime_ne hq hq2 hq3) hE' hcard'

theorem false_G2_qd32
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E R : Subgroup X} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False :=
  false_G2_of_card hmod hq hq2 (exp_of_isElementaryAbelian hE)
    (card_ge_pow_four_of_induces hq hq2 hE h)

theorem false_triality_qd32
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .trialityD4 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E R : Subgroup X} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False :=
  false_triality_of_card hmod hq hq2 (exp_of_isElementaryAbelian hE)
    (card_ge_pow_four_of_induces hq hq2 hE h)

theorem false_ree_qd32
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ReeTitsModel X .twistedF4 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E R : Subgroup X} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False :=
  false_ree_of_card hmod hq hq2 (exp_of_isElementaryAbelian hE)
    (card_ge_pow_four_of_induces hq hq2 hE h)

theorem false_suzuki_qd32 {T : Type} [Group T] {f : ℕ} (hmod : SuzukiModel T 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_card hK
  let ψ : T →* GL (Fin 4) K := (suzukiGroup a K).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  obtain ⟨φ, hφs, hφc⟩ := h.hom
  exact false_of_qd32_embedding_gl ψ hψ hq (natCast_ne_zero_of_prime_ne_two hq hq2)
    (by simp) hE h.normalizes φ hφs hφc

theorem prime_mem_of_dvd_tits {q : ℕ} (hq : q.Prime) (h : q ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 13 := by
  have e : ∀ {p k : ℕ}, p.Prime → q ∣ p ^ k → q = p := fun hp hk =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · exact Or.inl (e Nat.prime_two h)
      · exact Or.inr (Or.inl (e Nat.prime_three h))
    · exact Or.inr (Or.inr (Or.inl (e Nat.prime_five h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))

theorem not_pow_four_dvd_tits {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 4 ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by
  intro h
  have h' : q ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := (dvd_pow_self q (by norm_num)).trans h
  rcases prime_mem_of_dvd_tits hq h' with rfl | rfl | rfl | rfl
  · exact hq2 rfl
  · revert h; decide
  · revert h; decide
  · revert h; decide

theorem false_tits_of_card
    {T : Type} [Group T] {f : ℕ} (hmod : ReeTitsModel T .Tits 2 f) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1) (h4 : q ^ 4 ≤ Nat.card Y) :
    False := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 f hmod
  have hT : Nat.card T = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have hdvd := pow_four_dvd_card_group_of_card hq hexp h4
  rw [hT] at hdvd
  exact not_pow_four_dvd_tits hq hq2 (by norm_num at hdvd ⊢; exact hdvd)

theorem false_tits_qd32
    {T : Type} [Group T] [Finite T] {f : ℕ} (hmod : ReeTitsModel T .Tits 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False :=
  false_tits_of_card hmod hq hq2 (exp_of_isElementaryAbelian hE)
    (card_ge_pow_four_of_induces hq hq2 hE h)

theorem prime_mem_of_dvd_ordF4 {q : ℕ} (hq : q.Prime)
    (h : q ∣ 2 ^ 24 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 17 := by
  have e : ∀ {p k : ℕ}, p.Prime → q ∣ p ^ k → q = p := fun hp hk =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · exact Or.inl (e Nat.prime_two h)
          · exact Or.inr (Or.inl (e Nat.prime_three h))
        · exact Or.inr (Or.inr (Or.inl (e Nat.prime_five h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (e (by norm_num) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))))

theorem not_pow_four_dvd_ordF4 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    ¬ q ^ 4 ∣ 2 ^ 24 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 := by
  intro h
  have h' : q ∣ 2 ^ 24 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 :=
    (dvd_pow_self q (by norm_num)).trans h
  rcases prime_mem_of_dvd_ordF4 hq h' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hq2 rfl
  · exact hq3 rfl
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide

theorem false_F4_of_card
    {T : Type} [Group T] (hmod : UntwistedChevalleyModel T .F4 2) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (h4 : q ^ 4 ≤ Nat.card Y) : False := by
  have hT := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmod
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; decide)
  have hdvd := pow_four_dvd_card_group_of_card hq hexp h4
  rw [hT] at hdvd
  exact not_pow_four_dvd_ordF4 hq hq2 hq3 (by simpa [ordF4] using hdvd)

theorem false_F4_qd32
    {T : Type} [Group T] (hmod : UntwistedChevalleyModel T .F4 2) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False := by
  have hT := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmod
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; decide)
  exact false_F4_of_card hmod hq hq2 hq3 (exp_of_isElementaryAbelian hE)
    (card_ge_pow_four_of_induces hq hq2 hE h)

end CFSG.RankThree.PartOne.F106
