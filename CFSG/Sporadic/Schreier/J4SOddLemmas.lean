module

public import CFSG.Sporadic.Schreier.J4SPointwise
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalSplitAbelian
public import CFSG.Sporadic.Schreier.J4SOddCore
public import CFSG.Sporadic.FischerOddCore.AlmostSimple
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Sporadic.FischerOddCore.Basic

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

@[expose] def conjOn {S B : Subgroup G} (h : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) :
    S →* MulAut B where
  toFun s :=
    { toFun := fun b => ⟨(s : G) * b * (s : G)⁻¹, h s s.2 b b.2⟩
      invFun := fun b => ⟨(s : G)⁻¹ * b * s, by
        have := h _ (S.inv_mem s.2) b b.2
        rwa [inv_inv] at this⟩
      left_inv := fun b => Subtype.ext (by dsimp only; group)
      right_inv := fun b => Subtype.ext (by dsimp only; group)
      map_mul' := fun b b' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show ((1 : S) : G) * b * ((1 : S) : G)⁻¹ = b
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  map_mul' s s' := MulEquiv.ext fun b => Subtype.ext (by
    show ((s * s' : S) : G) * b * ((s * s' : S) : G)⁻¹ = s * (s' * b * (s' : G)⁻¹) * (s : G)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem conjOn_apply {S B : Subgroup G} (h : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) (s : S) (b : B) :
    ((conjOn h s b : B) : G) = s * b * (s : G)⁻¹ :=
  rfl

theorem inf_eq_bot_of_odd [Finite G] {N H R : Subgroup G}
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hC : Subgroup.centralizer (N : Set G) ⊓ H ≤ N) (hN : IsPGroup 2 N)
    (hR : Odd (Nat.card R)) (hRN : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R) : R ⊓ H = ⊥ := by
  have hRN' : R ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hR)
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨hrR, hrH⟩ := Subgroup.mem_inf.1 hr
  have hcomm : ∀ n ∈ N, n * r = r * n := by
    intro n hn
    have h1 : r * n * r⁻¹ * n⁻¹ ∈ N := N.mul_mem (hnorm r hrH n hn) (N.inv_mem hn)
    have h2 : r * n * r⁻¹ * n⁻¹ ∈ R := by
      have e : r * n * r⁻¹ * n⁻¹ = r * (n * r⁻¹ * n⁻¹) := by group
      rw [e]
      exact R.mul_mem hrR (hRN n hn _ (R.inv_mem hrR))
    have h3 : r * n * r⁻¹ * n⁻¹ = 1 := by
      have h4 : r * n * r⁻¹ * n⁻¹ ∈ R ⊓ N := Subgroup.mem_inf.2 ⟨h2, h1⟩
      rw [hRN'] at h4
      exact h4
    calc n * r = (r * n * r⁻¹ * n⁻¹)⁻¹ * (r * n) := by group
      _ = r * n := by rw [h3, inv_one, one_mul]
  have hrN : r ∈ N :=
    hC (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun n hn => hcomm n hn, hrH⟩)
  have h5 : r ∈ R ⊓ N := Subgroup.mem_inf.2 ⟨hrR, hrN⟩
  rw [hRN'] at h5
  exact h5

theorem exists_invariant_sylow [Finite G] {S R : Subgroup G} (hS : IsPGroup 2 S)
    (hR : Odd (Nat.card R)) (hSR : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (q : ℕ) [Fact q.Prime] :
    ∃ P : Subgroup G, P ≤ R ∧ IsPGroup q P ∧ Nat.card P = q ^ (Nat.card R).factorization q ∧
      ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
  classical
  let _ : MulAction S (Sylow q R) := MulAction.compHom _ (conjOn hSR)
  have h2 : ¬ 2 ∣ Nat.card (Sylow q R) := by
    obtain ⟨P⟩ : Nonempty (Sylow q R) := inferInstance
    intro h
    have h1 := (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card (P : Subgroup R))
    exact (Nat.not_even_iff_odd.2 hR) (even_iff_two_dvd.2 (h.trans h1))
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q R) h2
  refine ⟨(P : Subgroup R).map R.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map R.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective, Sylow.card_eq_multiplicity]
  · rintro s hs _ ⟨y, hy, rfl⟩
    have hfix : (⟨s, hs⟩ : S) • P = P := hP ⟨s, hs⟩
    have hmem : conjOn hSR ⟨s, hs⟩ y ∈ (((⟨s, hs⟩ : S) • P : Sylow q R) : Subgroup R) := by
      show conjOn hSR ⟨s, hs⟩ y ∈ conjOn hSR ⟨s, hs⟩ • (P : Subgroup R)
      exact Subgroup.smul_mem_pointwise_smul y _ _ hy
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩

theorem card_le_two_pow_mul_card_centralizer [Finite G] {N P : Subgroup G}
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1) {q : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) (hP : IsPGroup q P) (hNP : ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P) {m : ℕ}
    (hm : Nat.card P ≤ q ^ m) :
    Nat.card N ≤ 2 ^ m * Nat.card (N ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
  classical
  set ψ := conjOn hNP with hψ
  set A := ψ.range with hA
  have hAc : IsMulCommutative A := ⟨⟨by
    rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
    apply Subtype.ext
    show ψ a * ψ b = ψ b * ψ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hNc a a.2 b b.2)⟩⟩
  have hA2 : ∀ x : A, x ^ 2 = 1 := by
    rintro ⟨_, ⟨a, rfl⟩⟩
    apply Subtype.ext
    show ψ a ^ 2 = 1
    rw [← map_pow, sq]
    have : a * a = 1 := Subtype.ext (hN2 a a.2)
    rw [this, map_one]
  have hexp2 : Monoid.exponent A ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hA2
  have hexp : Monoid.exponent A ∣ q - 1 := by
    refine hexp2.trans ?_
    rcases (Fact.out : q.Prime).eq_two_or_odd' with h | h
    · exact absurd h hq
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
  have hAel : IsElementaryAbelian 2 A := { hAc with exponent_dvd_p := hexp2 }
  have hAp : IsPGroup 2 A := fun x => ⟨1, by rw [pow_one]; exact hA2 x⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hAp
  have hPel : ∀ X : Subgroup P, IsElementaryAbelian q X → Nat.card X ≤ q ^ m := fun X _ =>
    (Subgroup.card_le_card_group X).trans hm
  obtain ⟨_, -, -, -, -, _, _, -, -, -, -, hm'⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.split_abelian_coprime_automorphism_rank_bound
      hP A hAc hexp
  have hkm := (hm' m hPel).2.2 hq hAel k hk
  have hker : ψ.ker.map N.subtype = N ⊓ Subgroup.centralizer (P : Set G) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine Subgroup.mem_inf.2 ⟨n.2, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
      have h1 := congrArg (fun φ : MulAut P => ((φ ⟨p, hp⟩ : P) : G)) (MonoidHom.mem_ker.1 hn)
      change (n : G) * p * (n : G)⁻¹ = p at h1
      calc p * n = n * p * (n : G)⁻¹ * n := by rw [h1]
        _ = n * p := by group
    · intro hx
      obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxN⟩, MonoidHom.mem_ker.2 (MulEquiv.ext fun p => Subtype.ext ?_), rfl⟩
      change x * p * x⁻¹ = p
      rw [← Subgroup.mem_centralizer_iff.1 hxC p p.2]
      group
  have hcard : Nat.card ψ.ker = Nat.card (N ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective N.subtype_injective]
  have hN := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hcard, hk] at hN
  rw [← hN, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hkm)

theorem card_le_two_pow_mul_card_centralizer_odd [Finite G] {N R : Subgroup G}
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1)
    (hR : Odd (Nat.card R)) (hNR : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R) {M : ℕ} (hM : M ≠ 0)
    (hRM : Nat.card R ∣ M) :
    Nat.card N ≤ 2 ^ M.primeFactorsList.length *
      Nat.card (N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) := by
  classical
  have hN : IsPGroup 2 N := fun x => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hN2 x x.2)⟩
  have hsyl : ∀ q : ℕ, q.Prime → ∃ P : Subgroup G, P ≤ R ∧ IsPGroup q P ∧
      Nat.card P = q ^ (Nat.card R).factorization q ∧ ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P :=
    fun q hq => by
      have := Fact.mk hq
      exact exists_invariant_sylow hN hR hNR q
  choose! P hPR hPp hPc hPN using hsyl
  have key : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime ∧ q ≠ 2) →
      Nat.card N ≤ 2 ^ (∑ q ∈ s, (Nat.card R).factorization q) *
        Nat.card (N ⊓ ⨅ q ∈ s, Subgroup.centralizer (P q : Set G) : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert q s hqs ih =>
      intro hs
      have h1 := ih fun q' hq' => hs q' (Finset.mem_insert_of_mem hq')
      obtain ⟨hq, hq2⟩ := hs q (Finset.mem_insert_self q s)
      have := Fact.mk hq
      set D := N ⊓ ⨅ q' ∈ s, Subgroup.centralizer (P q' : Set G) with hD
      have hDN : D ≤ N := inf_le_left
      have h2 := card_le_two_pow_mul_card_centralizer (N := D) (P := P q)
        (fun a ha b hb => hNc a (hDN ha) b (hDN hb)) (fun a ha => hN2 a (hDN ha)) hq2 (hPp q hq)
        (fun n hn x hx => hPN q hq n (hDN hn) x hx) (m := (Nat.card R).factorization q)
        (le_of_eq (hPc q hq))
      have e : (N ⊓ ⨅ q' ∈ insert q s, Subgroup.centralizer (P q' : Set G) : Subgroup G) =
          D ⊓ Subgroup.centralizer (P q : Set G) := by
        rw [Finset.iInf_insert, hD, inf_assoc,
          inf_comm (⨅ q' ∈ s, Subgroup.centralizer (P q' : Set G))]
      rw [e, Finset.sum_insert hqs, pow_add]
      calc Nat.card N ≤ 2 ^ (∑ q ∈ s, (Nat.card R).factorization q) * Nat.card D := h1
        _ ≤ 2 ^ (∑ q ∈ s, (Nat.card R).factorization q) * (2 ^ (Nat.card R).factorization q *
            Nat.card (D ⊓ Subgroup.centralizer (P q : Set G) : Subgroup G)) :=
          Nat.mul_le_mul_left _ h2
        _ = _ := by ring
  have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  have hk := key (Nat.card R).primeFactors fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hR) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hq))⟩
  have hsum : ∑ q ∈ (Nat.card R).primeFactors, (Nat.card R).factorization q =
      (Nat.card R).primeFactorsList.length := by
    rw [← List.sum_toFinset_count_eq_length]
    refine Finset.sum_congr rfl fun q _ => Nat.primeFactorsList_count_eq.symm
  have hle : (N ⊓ ⨅ q ∈ (Nat.card R).primeFactors, Subgroup.centralizer (P q : Set G) :
      Subgroup G) ≤ N ⊓ Subgroup.centralizer (R : Set G) := by
    intro d hd
    obtain ⟨hdN, hdI⟩ := Subgroup.mem_inf.1 hd
    refine Subgroup.mem_inf.2 ⟨hdN, ?_⟩
    have hPd : ∀ q ∈ (Nat.card R).primeFactors, P q ≤ R ⊓ Subgroup.centralizer {d} := by
      intro q hq x hx
      have hdq : d ∈ Subgroup.centralizer (P q : Set G) := by
        have := (Subgroup.mem_iInf.1 hdI) q
        exact (Subgroup.mem_iInf.1 this) hq
      exact Subgroup.mem_inf.2 ⟨hPR q (Nat.prime_of_mem_primeFactors hq) hx,
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hdq x hx)⟩
    have hC0 : Nat.card (R ⊓ Subgroup.centralizer {d} : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    have hdvd : Nat.card R ∣ Nat.card (R ⊓ Subgroup.centralizer {d} : Subgroup G) := by
      rw [← Nat.factorization_le_iff_dvd hR0 hC0]
      intro q
      by_cases hq : q ∈ (Nat.card R).primeFactors
      · have hq' := Nat.prime_of_mem_primeFactors hq
        have h1 := Subgroup.card_dvd_of_le (hPd q hq)
        rw [hPc q hq'] at h1
        exact (hq'.pow_dvd_iff_le_factorization hC0).1 h1
      · have h0 : (Nat.card R).factorization q = 0 :=
          Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
        rw [h0]
        exact Nat.zero_le _
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : R ⊓ Subgroup.centralizer {d} ≤ R)
      (Nat.le_of_dvd Nat.card_pos hdvd)
    refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    have hr' : r ∈ R ⊓ Subgroup.centralizer {d} := by rw [heq]; exact hr
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr').2
  rw [hsum] at hk
  refine hk.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num)
    (Nat.primeFactorsList_sublist_of_dvd hRM hM).length_le) (Subgroup.card_le_of_le hle))

theorem card_le_two_pow_length_mul_card_centralizer [Finite G] {N R : Subgroup G}
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1)
    (hR : Odd (Nat.card R)) (hNR : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R) {L : List ℕ}
    (hL : ∀ p ∈ L, p.Prime) (hRL : Nat.card R ∣ L.prod) :
    Nat.card N ≤ 2 ^ L.length *
      Nat.card (N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) := by
  have hperm := Nat.primeFactorsList_unique rfl hL
  have h0 : L.prod ≠ 0 := List.prod_ne_zero fun h => (Nat.not_prime_zero (hL 0 h))
  rw [hperm.length_eq]
  exact card_le_two_pow_mul_card_centralizer_odd hNc hN2 hR hNR h0 hRL

theorem card_modEq_two_of_fixed [Finite G] {B : Subgroup G} {a t : G} {p : ℕ} [Fact p.Prime]
    (ha : a ^ p = 1) (hB : ∀ z ∈ Subgroup.zpowers a, ∀ b ∈ B, z * b * z⁻¹ ∈ B) (ht : t ∈ B)
    (ht1 : t ≠ 1) (hta : a * t * a⁻¹ = t) (hfix : ∀ b ∈ B, a * b * a⁻¹ = b → b = 1 ∨ b = t) :
    Nat.card B ≡ 2 [MOD p] := by
  classical
  let _ : MulAction (Subgroup.zpowers a) B := MulAction.compHom _ (conjOn hB)
  have hP : IsPGroup p (Subgroup.zpowers a) := by
    have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one ha
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints B
  have hfixed : MulAction.fixedPoints (Subgroup.zpowers a) B = {⟨1, B.one_mem⟩, ⟨t, ht⟩} := by
    ext b
    rw [MulAction.mem_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hb
      have h1 := congrArg Subtype.val (hb ⟨a, Subgroup.mem_zpowers a⟩)
      change a * b * a⁻¹ = b at h1
      rcases hfix b b.2 h1 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · have hcomm : ∀ x : G, a * x * a⁻¹ = x → ∀ z ∈ Subgroup.zpowers a, z * x * z⁻¹ = x := by
        intro x hx z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        have hc : Commute a x := by
          show a * x = x * a
          calc a * x = a * x * a⁻¹ * a := by group
            _ = x * a := by rw [hx]
        rw [((hc.zpow_left k).eq), mul_inv_cancel_right]
      rintro (rfl | rfl) ⟨z, hz⟩
      · exact Subtype.ext (by
          change z * 1 * z⁻¹ = 1
          group)
      · exact Subtype.ext (hcomm t hta z hz)
  rw [hfixed, Nat.card_coe_set_eq, Set.ncard_pair (fun h => ht1 (congrArg Subtype.val h).symm)]
    at hmod
  exact hmod

theorem exists_mem_inf_ne_one [Finite G] {N B W : Subgroup G} (hBN : B ≤ N) (hWN : W ≤ N)
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (h : Nat.card N < Nat.card B * Nat.card W) :
    ∃ w ∈ W, w ∈ B ∧ w ≠ 1 := by
  have hdvd := card_mul_card_dvd hBN hWN fun x hx n hn => by
    rw [hNc x hx n (hBN hn), mul_inv_cancel_right]
    exact hn
  by_contra hne
  push Not at hne
  have hbot : (B ⊓ W : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwB, hwW⟩ := Subgroup.mem_inf.1 hw
    exact Subgroup.mem_bot.2 (hne w hwW hwB)
  rw [hbot, Subgroup.card_bot, one_mul] at hdvd
  exact absurd (Nat.le_of_dvd Nat.card_pos hdvd) (not_le.2 h)

theorem mul_mem_of_index_le_two [Finite G] {N E : Subgroup G} (hEN : E ≤ N)
    (hcard : Nat.card N ≤ 2 * Nat.card E) {a b : G} (ha : a ∈ N) (hb : b ∈ N) (haE : a ∉ E)
    (hbE : b ∉ E) : a * b ∈ E := by
  have hc : Nat.card (E.subgroupOf N) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have h1 := Subgroup.card_mul_index (E.subgroupOf N)
  rw [hc] at h1
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hidx : (E.subgroupOf N).index = 2 := by
    have hle : (E.subgroupOf N).index ≤ 2 := by
      by_contra hlt
      have : Nat.card E * 3 ≤ Nat.card E * (E.subgroupOf N).index :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hne1 : (E.subgroupOf N).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      have hmem : (⟨a, ha⟩ : N) ∈ E.subgroupOf N := by
        rw [h]
        exact Subgroup.mem_top _
      exact haE (Subgroup.mem_subgroupOf.1 hmem)
    have hne0 : (E.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have h2 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
    ⟨fun h => absurd (Subgroup.mem_subgroupOf.1 h) haE,
      fun h => absurd (Subgroup.mem_subgroupOf.1 h) hbE⟩
  exact Subgroup.mem_subgroupOf.1 h2

theorem smul_eq_of_ncard_le_three {X : Type*} [MulAction G X] {r : G} {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) (hr : r ^ q = 1) {T : Set X} (hTf : T.Finite) (hT : T.ncard ≤ 3)
    (hrT : ∀ x ∈ T, r • x ∈ T) {v : X} (hv : v ∈ T) : r • v = v := by
  have hfo : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.2 ⟨q, (Fact.out : q.Prime).pos, hr⟩
  have hpow : ∀ n : ℕ, r ^ n • v ∈ T := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact hv
    | succ n ih => rw [pow_succ', mul_smul]; exact hrT _ ih
  have hsub : MulAction.orbit (Subgroup.zpowers r) v ⊆ T := by
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfo.mem_powers_iff_mem_zpowers.2 hz)
    exact hpow n
  have : Finite (MulAction.orbit (Subgroup.zpowers r) v) := (hTf.subset hsub).to_subtype
  have hP : IsPGroup q (Subgroup.zpowers r) := by
    have h1 : orderOf r ∣ q := orderOf_dvd_of_pow_eq_one hr
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨n, hn⟩ := hP.card_orbit v
  have hle : Nat.card (MulAction.orbit (Subgroup.zpowers r) v) ≤ 3 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub hTf).trans hT
  have hn0 : n = 0 := by
    by_contra h0
    have : q ≤ q ^ n := Nat.le_self_pow h0 q
    omega
  rw [hn0, pow_zero] at hn
  have hsing := Nat.card_eq_one_iff_unique.1 hn
  have h1 : (⟨r • v, ⟨r, Subgroup.mem_zpowers r⟩, rfl⟩ :
      MulAction.orbit (Subgroup.zpowers r) v) = ⟨v, MulAction.mem_orbit_self v⟩ :=
    hsing.1.elim _ _
  exact congrArg Subtype.val h1

theorem oddCore_centralizer_eq_bot_of_pointwise {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    [F.Normal] (hC : Subgroup.centralizer (F : Set X) = ⊥) {Q : Type*} [Group Q]
    (θ : F ≃* Q) (M : Subgroup Q) (hM : IsPGroup 2 (pointwiseFixingAut M)) (t : F)
    (hMt : ∀ m ∈ M, m * θ t = θ t * m)
    (hQ : CFSG.oddCore (Subgroup.centralizer ({θ t} : Set Q)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  classical
  set C := Subgroup.centralizer ({(t : X)} : Set X) with hCdef
  let e : ↥(C ⊓ F) ≃* ↥(Subgroup.centralizer ({t} : Set F)) :=
    { toFun := fun x => ⟨⟨x, (Subgroup.mem_inf.1 x.2).2⟩, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).1
        exact Subtype.ext h1⟩
      invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2), y.1.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl }
  have hN : CFSG.oddCore ↥(C ⊓ F) = ⊥ := by
    have h := FischerOddCore.oddCore_centralizer_eq_bot_of_mulEquiv θ.symm hQ
    rw [MulEquiv.symm_apply_apply] at h
    exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      e.symm h
  refine oddCore_eq_bot_of_normal inf_le_left (fun x hx n hn => Subgroup.mem_inf.2
    ⟨C.mul_mem (C.mul_mem hx (Subgroup.mem_inf.1 hn).1) (C.inv_mem hx),
      (inferInstance : F.Normal).conj_mem n (Subgroup.mem_inf.1 hn).2 x⟩) hN ?_
  intro x hx hcomm
  have hfix : FischerOddCore.conjTransport θ x ∈ pointwiseFixingAut M := by
    intro m hm
    rw [FischerOddCore.conjTransport_apply]
    have hmF : ((θ.symm m : F) : X) ∈ C ⊓ F := by
      refine Subgroup.mem_inf.2 ⟨?_, (θ.symm m).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : θ.symm m * t = t * θ.symm m := by
        apply θ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hMt m hm
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h3
    have h2 : MulAut.conjNormal x (θ.symm m) = θ.symm m := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hcomm _ hmF, mul_inv_cancel_right]
    rw [h2, MulEquiv.apply_symm_apply]
  obtain ⟨k, hk⟩ := hM ⟨_, hfix⟩
  refine ⟨k, FischerOddCore.conjTransport_injective θ hC ?_⟩
  rw [map_pow, map_one]
  exact congrArg Subtype.val hk

theorem centralizer_generalizedFitting_eq_bot' {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) :
    Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊥ := by
  refine FischerOddCore.centralizer_generalizedFitting_eq_bot_of_center ?_
  rcases hF.eq_bot_or_eq_top_of_normal (Subgroup.center (CFSG.generalizedFitting X)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center (CFSG.generalizedFitting X) := h ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.1 hb a))

theorem oddCore_centralizer_of_conj {X Q : Type*} [Group X] [Finite X] [Group Q]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* Q) (M : Subgroup Q)
    (hM : IsPGroup 2 (pointwiseFixingAut M)) (hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (t : CFSG.generalizedFitting X) {c s : Q} (hcs : c * ψ t * c⁻¹ = s) (hs : s ∈ M)
    (hQ : CFSG.oddCore (Subgroup.centralizer ({s} : Set Q)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hθ : (ψ.trans (MulAut.conj c)) t = s := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, hcs]
  refine oddCore_centralizer_eq_bot_of_pointwise (centralizer_generalizedFitting_eq_bot' hF hnab)
    (ψ.trans (MulAut.conj c)) M hM t (fun m hm => by rw [hθ]; exact hMc m hm s hs) ?_
  rw [hθ]
  exact hQ

theorem full_group_of_local_conj {X Q : Type*} [Group X] [Finite X] [Group Q]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* Q) (M : Subgroup Q)
    (hM : IsPGroup 2 (pointwiseFixingAut M)) (hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (L : Subgroup Q) (e : Q) (heM : ∀ k ∈ L, k⁻¹ * e * k ∈ M)
    (hloc : ∀ q : Q, (∃ g : Q, ∃ k ∈ L, q = g⁻¹ * (k⁻¹ * e * k) * g) →
      orderOf q = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({q} : Set Q)) = ⊥)
    (t : CFSG.generalizedFitting X) (ht : ∃ g : Q, ∃ k ∈ L, ψ t = g⁻¹ * (k⁻¹ * e * k) * g) :
    orderOf (t : X) = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  obtain ⟨g, k, hk, hψ⟩ := ht
  have hc : g * ψ t * g⁻¹ = k⁻¹ * e * k := by rw [hψ]; group
  refine ⟨?_, oddCore_centralizer_of_conj hF hnab ψ M hM hMc t hc (heM k hk)
    (hloc _ ⟨1, k, hk, by group⟩).2⟩
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ]
  exact (hloc _ ⟨g, k, hk, hψ⟩).1

theorem conj_mem_inf_centralizer {N P : Subgroup G} {s : G} (hsN : ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hsP : ∀ x ∈ P, s⁻¹ * x * s ∈ P) {b : G}
    (hb : b ∈ N ⊓ Subgroup.centralizer (P : Set G)) :
    s * b * s⁻¹ ∈ N ⊓ Subgroup.centralizer (P : Set G) := by
  obtain ⟨hbN, hbP⟩ := Subgroup.mem_inf.1 hb
  refine Subgroup.mem_inf.2 ⟨hsN b hbN, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hbP _ (hsP x hx)
  calc x * (s * b * s⁻¹) = s * ((s⁻¹ * x * s) * b) * s⁻¹ := by group
    _ = s * (b * (s⁻¹ * x * s)) * s⁻¹ := by rw [h1]
    _ = s * b * s⁻¹ * x := by group

theorem eq_conj_form {a b g : G} (h : g * a * g⁻¹ = b) : a = g⁻¹ * (1⁻¹ * b * 1) * g := by
  rw [← h]
  group

end Generic

end CFSG.Sporadic.J4Schreier
