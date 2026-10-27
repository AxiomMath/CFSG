module

public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.Quasithin.H13.FiveQuotientOddIndex

open Equiv

theorem sign_eq_neg_one_of_orderOf_eq_eight {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 9) {σ : Perm α} (hσ : orderOf σ = 8) : Perm.sign σ = -1 := by
  have hdvd : ∀ n ∈ σ.cycleType, n ∣ 8 := fun n hn => hσ ▸ Perm.dvd_of_mem_cycleType hn
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => Perm.two_le_of_mem_cycleType hn
  have hsum : σ.cycleType.sum ≤ 9 := by
    rw [Perm.sum_cycleType, ← hα]
    exact Finset.card_le_univ _
  have hlcm : σ.cycleType.lcm = 8 := by rw [Perm.lcm_cycleType, hσ]
  have h8 : 8 ∈ σ.cycleType := by
    by_contra h8
    have h4 : ∀ n ∈ σ.cycleType, n ∣ 4 := by
      intro n hn
      have hn8 := hdvd n hn
      have hn2 := h2 n hn
      have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) hn8
      interval_cases n <;> first | (norm_num at hn8; done) | (norm_num; done) | exact absurd hn h8
    have : σ.cycleType.lcm ∣ 4 := Multiset.lcm_dvd.2 h4
    rw [hlcm] at this
    norm_num at this
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem h8
  have hs0 : s = 0 := by
    by_contra hs0
    obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero hs0
    have hm2 := h2 m (hs ▸ Multiset.mem_cons_of_mem hm)
    have : 8 + m ≤ σ.cycleType.sum := by
      rw [hs, Multiset.sum_cons]
      have := Multiset.le_sum_of_mem hm
      omega
    omega
  rw [Perm.sign_of_cycleType, hs, hs0]
  decide

variable {Q : Type*} [Group Q]

theorem eq_top_of_toPermHom_eq_one {X : Subgroup Q}
    (h : ∀ g : Q, MulAction.toPermHom Q (Q ⧸ X) g = 1) : X = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg := congrArg (fun σ : Perm (Q ⧸ X) => σ (QuotientGroup.mk 1)) (h g⁻¹)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.coe_one, id] at hg
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, inv_inv, mul_one] at hg
  exact hg

theorem eq_top_of_index_le_four [Finite Q] [Group.IsPerfect Q] {X : Subgroup Q}
    (hX : X.index ≤ 4) : X = ⊤ := by
  classical
  let φ := MulAction.toPermHom Q (Q ⧸ X)
  have hsolv : Group.IsSolvable (Perm (Q ⧸ X)) :=
    Perm.isSolvable (by rw [← Subgroup.index_eq_card]; exact hX)
  have hrange : Group.IsSolvable φ.range := inferInstance
  have hperf : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range hrange
  apply eq_top_of_toPermHom_eq_one
  intro g
  have := Subsingleton.elim (φ.rangeRestrict g) 1
  exact congrArg Subtype.val this

theorem isPerfect_of_simple [IsSimpleGroup Q] (hnonab : ∃ a b : Q, a * b ≠ b * a) :
    Group.IsPerfect Q := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have h' : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by rw [← commutator_def]; exact h
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h'
    exact hab (Subgroup.mem_centralizer_iff.1 (hc (Subgroup.mem_top b)) a (Subgroup.mem_top a))
  · exact h

theorem nonabelian_of_simple_of_orderOf_eq_eight [Finite Q] [IsSimpleGroup Q] {g : Q}
    (hg : orderOf g = 8) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have hp := IsSimpleGroup.prime_card (α := Q)
  have h8 : 8 ∣ Nat.card Q := hg ▸ orderOf_dvd_natCard g
  have h2 : 2 ∣ Nat.card Q := Nat.dvd_trans (by norm_num) h8
  have h4 : 4 ∣ Nat.card Q := Nat.dvd_trans (by norm_num) h8
  rcases (Nat.dvd_prime hp).1 h2 with h | h
  · norm_num at h
  · rw [← h] at h4
    norm_num at h4

theorem index_ne_nine_of_simple [Finite Q] [IsSimpleGroup Q] {g : Q} (hg : orderOf g = 8)
    (X : Subgroup Q) : X.index ≠ 9 := by
  classical
  intro h9
  let φ := MulAction.toPermHom Q (Q ⧸ X)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hX : X = ⊤ :=
        eq_top_of_toPermHom_eq_one fun x => (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x)
      rw [hX, Subgroup.index_top] at h9
      norm_num at h9
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hord : orderOf (φ g) = 8 := by rw [orderOf_injective φ hinj, hg]
  have hperf := isPerfect_of_simple (nonabelian_of_simple_of_orderOf_eq_eight hg)
  let _ : Fintype (Q ⧸ X) := Fintype.ofFinite _
  have hsign : Perm.sign (φ g) = 1 := by
    have hle : commutator Q ≤ (Perm.sign.comp φ).ker := Abelianization.commutator_subset_ker _
    rw [Group.IsPerfect.commutator_eq_top] at hle
    exact (MonoidHom.mem_ker).1 (hle (Subgroup.mem_top g))
  have hcard : Fintype.card (Q ⧸ X) = 9 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, h9]
  rw [sign_eq_neg_one_of_orderOf_eq_eight hcard hord] at hsign
  exact absurd hsign (by decide)

theorem isSolvable_of_card {X : Type*} [Group X] [Finite X] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card X = p ^ a * q ^ b) : Group.IsSolvable X := by
  let _ := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

end CFSG.Quasithin.H13.FiveQuotientOddIndex

namespace CFSG.Quasithin.H13.FiveQuotientOddIndex

variable {Q : Type*} [Group Q]

theorem nonabelian_of_simple_of_not_prime [Finite Q] [IsSimpleGroup Q]
    (hn : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  exact hn (IsSimpleGroup.prime_card (α := Q))

theorem dvd_of_odd_dvd {i k m : ℕ} (hi : ¬ 2 ∣ i) (h : i ∣ 2 ^ k * m) : i ∣ m :=
  (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hi).symm).dvd_of_dvd_mul_left h

private instance : DecidableEq (CFSG.Open.WreathedTwoGroup 2) := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

theorem psu33_simple_and_order_eight
    {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSU 3 3 1) :
    IsSimpleGroup Q ∧ ∃ g : Q, orderOf g = 8 := by
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
  obtain ⟨e2⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  let e : Q ≃* CFSG.Quasithin.U33G := e1.trans e2.symm
  have : IsSimpleGroup CFSG.Quasithin.U33G := CFSG.Quasithin.isSimpleGroup_u33Pres
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨w⟩ := CFSG.Quasithin.u33_T_mulEquiv_wreathed
  let x : CFSG.Open.WreathedTwoGroup 2 := CFSG.Quasithin.wrImg 0 * CFSG.Quasithin.wrImg 2
  have hx : orderOf x = 8 := by
    have h1 : ¬ x ^ 2 ^ 2 = 1 := by decide +kernel
    have h2 : x ^ 2 ^ (2 + 1) = 1 := by decide +kernel
    exact orderOf_eq_prime_pow h1 h2
  refine ⟨e.symm (w.symm x : CFSG.Quasithin.u33Data.T), ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]

end CFSG.Quasithin.H13.FiveQuotientOddIndex

namespace CFSG.Quasithin.H13

open FiveQuotientOddIndex

theorem fiveQuotientOddIndexSolvable_holds :
    FiveQuotientOddIndexSolvable := by
  intro Q _ _ hQ X hodd hne
  have hidx1 : X.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hmul : Nat.card X * X.index = Nat.card Q := Subgroup.card_mul_index X
  have hdvdQ : X.index ∣ Nat.card Q := Subgroup.index_dvd_card X
  have p2 := Nat.prime_two
  have p3 := Nat.prime_three
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  rcases hQ with ⟨⟨e⟩⟩ | hL | ⟨⟨e⟩⟩ | ⟨hperf, hZ, ⟨e⟩⟩ | hU
  ·
    have h : Nat.card Q = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin 5 (by norm_num)]
      decide
    rw [h, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num] at hdvdQ
    have hi := Nat.mem_divisors.2 ⟨dvd_of_odd_dvd hodd hdvdQ, by norm_num⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [h] at hmul
    rcases hi with hi | hi | hi | hi <;> rw [hi] at hmul
    · exact absurd hi hidx1
    · exact isSolvable_of_card p2 p5 (by norm_num) (a := 2) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 2) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 2) (b := 0) (by omega)
  ·
    have h : Nat.card Q = 168 := by
      obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel hL
      rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two]
    rw [h, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num] at hdvdQ
    have hi := Nat.mem_divisors.2 ⟨dvd_of_odd_dvd hodd hdvdQ, by norm_num⟩
    rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [h] at hmul
    rcases hi with hi | hi | hi | hi <;> rw [hi] at hmul
    · exact absurd hi hidx1
    · exact isSolvable_of_card p2 p7 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 0) (by omega)
  ·
    have h : Nat.card Q = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin 6 (by norm_num)]
      decide
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Q := e.isSimpleGroup
    have : Group.IsPerfect Q :=
      isPerfect_of_simple (nonabelian_of_simple_of_not_prime (by rw [h]; norm_num))
    rw [h, show (360 : ℕ) = 2 ^ 3 * 45 by norm_num] at hdvdQ
    have hi := Nat.mem_divisors.2 ⟨dvd_of_odd_dvd hodd hdvdQ, by norm_num⟩
    rw [show Nat.divisors 45 = {1, 3, 5, 9, 15, 45} by decide] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [h] at hmul
    rcases hi with hi | hi | hi | hi | hi | hi
    · exact absurd hi hidx1
    · exact absurd (eq_top_of_index_le_four (by omega)) hne
    all_goals rw [hi] at hmul
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 2) (by omega)
    · exact isSolvable_of_card p2 p5 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 0) (by omega)
  ·
    have h : Nat.card Q = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q),
        Nat.card_congr e.toEquiv, card_alternatingGroup_fin 6 (by norm_num), hZ]
      decide
    rw [h, show (1080 : ℕ) = 2 ^ 3 * 135 by norm_num] at hdvdQ
    have hi := Nat.mem_divisors.2 ⟨dvd_of_odd_dvd hodd hdvdQ, by norm_num⟩
    rw [show Nat.divisors 135 = {1, 3, 5, 9, 15, 27, 45, 135} by decide] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [h] at hmul
    rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
    · exact absurd hi hidx1
    · exact absurd (eq_top_of_index_le_four (by omega)) hne
    · rw [hi] at hmul
      exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 3) (by omega)
    ·
      have hX120 : Nat.card X = 120 := by rw [hi] at hmul; omega
      by_cases hZX : Subgroup.center Q ≤ X
      ·
        let ZX : Subgroup X := (Subgroup.center Q).subgroupOf X
        have : ZX.Normal := Subgroup.Normal.subgroupOf inferInstance X
        have hZX3 : Nat.card ZX = 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv, hZ]
        have hq : Nat.card (X ⧸ ZX) = 40 := by
          have := Subgroup.card_eq_card_quotient_mul_card_subgroup ZX
          rw [hX120, hZX3] at this
          omega
        have : Group.IsSolvable (X ⧸ ZX) :=
          isSolvable_of_card p2 p5 (by norm_num) (a := 3) (b := 1) (by rw [hq]; norm_num)
        have : Group.IsSolvable ZX := Group.isSolvable_of_comm fun a b => by
          have ha : ((a : X) : Q) ∈ Subgroup.center Q := Subgroup.mem_subgroupOf.1 a.2
          exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 ha _).symm)
        exact Group.isSolvable_of_subgroup_quotient ZX
      ·
        exfalso
        set Y := X ⊔ Subgroup.center Q with hY
        have hXY : X ≤ Y := le_sup_left
        have hrel := Subgroup.relIndex_mul_index hXY
        rw [hi] at hrel
        have hrel1 : X.relIndex Y ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          exact fun h => hZX (le_sup_right.trans h)
        have hYdvd : Y.index ∣ 9 := ⟨X.relIndex Y, by rw [← hrel, mul_comm]⟩
        have hYi : Y.index ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hYdvd, by norm_num⟩
        rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hYi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hYi
        rcases hYi with hY1 | hY3 | hY9
        ·
          have hYtop : Y = ⊤ := Subgroup.index_eq_one.1 hY1
          have hXn : X.Normal := by
            rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hYtop]
            refine sup_le Subgroup.le_normalizer fun z hz => ?_
            rw [Subgroup.mem_normalizer_iff]
            intro x
            rw [(Subgroup.mem_center_iff.1 hz x).symm, mul_inv_cancel_right]
          have hQX : Nat.card (Q ⧸ X) = 3 ^ 2 := by
            rw [← Subgroup.index_eq_card, hi]
            norm_num
          have hle : commutator Q ≤ X :=
            (Subgroup.Normal.quotient_commutative_iff_commutator_le).1
              (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQX)
          rw [Group.IsPerfect.commutator_eq_top] at hle
          exact hne (top_le_iff.1 hle)
        · have hYt := eq_top_of_index_le_four (X := Y) (by omega)
          rw [hYt, Subgroup.index_top] at hY3
          omega
        · rw [hY9] at hrel
          exact hrel1 (by omega)
    all_goals rw [hi] at hmul
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 2) (by omega)
    · exact isSolvable_of_card p2 p5 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 3) (b := 0) (by omega)
  ·
    have h : Nat.card Q = 6048 := card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU)
    obtain ⟨hsimple, g, hg⟩ := psu33_simple_and_order_eight hU
    have : Group.IsPerfect Q := isPerfect_of_simple (nonabelian_of_simple_of_orderOf_eq_eight hg)
    rw [h, show (6048 : ℕ) = 2 ^ 5 * 189 by norm_num] at hdvdQ
    have hi := Nat.mem_divisors.2 ⟨dvd_of_odd_dvd hodd hdvdQ, by norm_num⟩
    rw [show Nat.divisors 189 = {1, 3, 7, 9, 21, 27, 63, 189} by decide] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [h] at hmul
    rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
    · exact absurd hi hidx1
    · exact absurd (eq_top_of_index_le_four (by omega)) hne
    · rw [hi] at hmul
      exact isSolvable_of_card p2 p3 (by norm_num) (a := 5) (b := 3) (by omega)
    · exact absurd hi (index_ne_nine_of_simple hg X)
    all_goals rw [hi] at hmul
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 5) (b := 2) (by omega)
    · exact isSolvable_of_card p2 p7 (by norm_num) (a := 5) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 5) (b := 1) (by omega)
    · exact isSolvable_of_card p2 p3 (by norm_num) (a := 5) (b := 0) (by omega)

end CFSG.Quasithin.H13
