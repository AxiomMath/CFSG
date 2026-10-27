module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Embedding
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.QAbelian
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G : Type} [Group G] [Finite G]

theorem exists_pCore_not_comm {R : Subgroup G} [hRn : R.Normal] (hRodd : Odd (Nat.card R))
    {d : Fin 3 → G} (hd : ∀ i, d i * d i = 1) (hRT : ∃ y ∈ R, ∃ i, d i * y ≠ y * d i) :
    ∃ q : ℕ, q.Prime ∧ ∃ i, ∃ f ∈ (CFSG.pCore q R).map R.subtype, d i * f ≠ f * d i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy, i, hne⟩ := hRT
  have hsol : IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
  have hT : IsPGroup 2 (zpowers (d i)) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (d i ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hd i, one_zpow]
  have hTX : zpowers (d i) ≤ normalizer (R : Set G) := fun g _ =>
    mem_normalizer_iff.mpr fun h => ⟨fun hh => hRn.conj_mem h hh g, fun hh => by
      simpa [mul_assoc] using hRn.conj_mem _ hh g⁻¹⟩
  have hF : ∀ f ∈ (CFSG.fittingSubgroup R).map R.subtype, d i * f = f * d i := by
    rw [CFSG.Quasithin.A36B.fitting_eq_iSup_primes, Subgroup.map_iSup]
    intro f hf
    have hle : (⨆ q : Nat.Primes, (CFSG.pCore (q : ℕ) R).map R.subtype) ≤ centralizer {d i} :=
      iSup_le fun q f hf => mem_centralizer_singleton_iff.mpr (hcon q q.2 i f hf).symm
    exact (mem_centralizer_singleton_iff.mp (hle hf)).symm
  have := commute_of_commute_fitting hRodd hsol hT hTX (fun t ht f hf => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
    exact Commute.zpow_left (hF f hf) k) (d i) (mem_zpowers _) y hy
  exact hne this.eq

theorem exists_min_moved {P : Subgroup G} [hPn : P.Normal] {d : Fin 3 → G}
    (hP : ∃ i, ∃ f ∈ P, d i * f ≠ f * d i) :
    ∃ Q : Subgroup G, Q.Normal ∧ Q ≤ P ∧ (∃ i, ∃ x ∈ Q, d i * x ≠ x * d i) ∧
      ∀ N : Subgroup G, N.Normal → N < Q → ∀ i, ∀ x ∈ N, d i * x = x * d i := by
  classical
  let S : Set (Subgroup G) := {N | N.Normal ∧ N ≤ P ∧ ∃ i, ∃ x ∈ N, d i * x ≠ x * d i}
  have hS : S.Nonempty := ⟨P, hPn, le_rfl, hP⟩
  obtain ⟨Q, ⟨hQn, hQP, hQm⟩, hmin⟩ :=
    WellFounded.has_min (InvImage.wf (fun N : Subgroup G => Nat.card N) wellFounded_lt) S hS
  refine ⟨Q, hQn, hQP, hQm, fun N hN hNQ i x hx => ?_⟩
  by_contra hne
  exact hmin N ⟨hN, hNQ.le.trans hQP, i, x, hx, hne⟩ (Subgroup.card_lt_of_lt hNQ)

theorem quot_comm_iff {Q Q₀ : Subgroup G} [hQ₀n : Q₀.Normal] (a b : Q) :
    (QuotientGroup.mk a * QuotientGroup.mk b : Q ⧸ Q₀.subgroupOf Q) =
      QuotientGroup.mk b * QuotientGroup.mk a ↔ (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ Q₀ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro h
    have := hQ₀n.conj_mem _ (Q₀.inv_mem h) ((a : G) * b)
    convert this using 1
    group
  · intro h
    have := hQ₀n.conj_mem _ (Q₀.inv_mem h) ((b : G)⁻¹ * (a : G)⁻¹)
    convert this using 1
    group

theorem quot_pow_eq_one_iff {Q Q₀ : Subgroup G} [Q₀.Normal] (a : Q) (n : ℕ) :
    (QuotientGroup.mk a : Q ⧸ Q₀.subgroupOf Q) ^ n = 1 ↔ (a : G) ^ n ∈ Q₀ := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow]

theorem exists_S1 {M : Type*} [AddCommGroup M] [Finite M] [DistribMulAction G M]
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {R : Subgroup G} [hRn : R.Normal] (hRodd : Odd (Nat.card R))
    {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1) (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hgen : normalClosure ({d 0} : Set G) = ⊤) (hRT : ∃ y ∈ R, ∃ i, d i * y ≠ y * d i) :
    ∃ r : ℕ, r.Prime ∧ ¬ r ∣ Nat.card M ∧ ∃ Q Q₀ : Subgroup G, Q.Normal ∧ Q ≤ R ∧ Q₀ ≤ Q ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀) ∧ Q₀ ≤ center G ∧ IsPGroup r Q₀ ∧
      (∀ x ∈ Q, x ^ r ∈ Q₀) ∧
      (∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q) ∧
      ∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀ := by
  classical
  obtain ⟨q, hq, hP⟩ := exists_pCore_not_comm hRodd hd hRT
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hPn : ((CFSG.pCore q R).map R.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hPp : IsPGroup q ((CFSG.pCore q R).map R.subtype) := (CFSG.pCore_isPGroup).map R.subtype
  have hPR : (CFSG.pCore q R).map R.subtype ≤ R := map_subtype_le _
  obtain ⟨Q, hQn, hQP, hQm, hmin⟩ := exists_min_moved hP
  have hQp : IsPGroup q Q := hPp.to_le hQP
  have hQR : Q ≤ R := hQP.trans hPR
  have hQodd : Odd (Nat.card Q) := Odd.of_dvd_nat hRodd (card_dvd_of_le hQR)
  have hcentral : ∀ N : Subgroup G, N.Normal → N < Q → N ≤ center G := by
    intro N hN hNQ
    haveI := hN
    have hle : normalClosure ({d 0} : Set G) ≤ centralizer (N : Set G) :=
      normalClosure_le_normal (by
        rw [Set.singleton_subset_iff]
        exact mem_centralizer_iff.mpr fun x hx => (hmin N hN hNQ 0 x hx).symm)
    rw [hgen] at hle
    intro x hx
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (hle (mem_top g)) x hx).symm
  let Q₀ : Subgroup G := sSup {N | N.Normal ∧ N < Q}
  have hQ₀Q : Q₀ ≤ Q := sSup_le fun N hN => hN.2.le
  have hQ₀Z : Q₀ ≤ center G := sSup_le fun N hN => hcentral N hN.1 hN.2
  haveI hQ₀n : Q₀.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hQ₀Z hn) g, mul_inv_cancel_right]; exact hn⟩
  have hQ₀c : ∀ x ∈ Q₀, ∀ g : G, g * x * g⁻¹ = x := fun x hx g => by
    rw [mem_center_iff.mp (hQ₀Z hx) g, mul_inv_cancel_right]
  have hQ₀ne : Q₀ ≠ Q := by
    intro h
    obtain ⟨i, x, hx, hne⟩ := hQm
    rw [← h] at hx
    exact hne (mem_center_iff.mp (hQ₀Z hx) (d i))
  have hchief : ∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q := by
    intro N hN h1 h2
    by_cases hNQ : N = Q
    · exact Or.inr hNQ
    · exact Or.inl (le_antisymm (le_sSup ⟨hN, lt_of_le_of_ne h2 hNQ⟩) h1)
  have hQ₀p : IsPGroup q Q₀ := hQp.to_le hQ₀Q
  have hconjQ : ∀ g : G, ∀ x ∈ Q, g⁻¹ * x * g ∈ Q := fun g x hx => by
    simpa using hQn.conj_mem x hx g⁻¹
  have hQb : IsPGroup q (Q ⧸ Q₀.subgroupOf Q) := hQp.to_quotient _
  obtain ⟨x₀, hx₀Q, hx₀⟩ : ∃ x ∈ Q, x ∉ Q₀ := by
    by_contra h; push_neg at h; exact hQ₀ne (le_antisymm hQ₀Q h)
  have hmk1 : ∀ (a : Q), (QuotientGroup.mk a : Q ⧸ Q₀.subgroupOf Q) = 1 ↔ (a : G) ∈ Q₀ :=
    fun a => by rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  haveI hQbnt : Nontrivial (Q ⧸ Q₀.subgroupOf Q) :=
    ⟨⟨QuotientGroup.mk ⟨x₀, hx₀Q⟩, 1, fun h => hx₀ ((hmk1 _).mp h)⟩⟩
  have hQ' : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀ := by
    let K : Subgroup G :=
      { carrier := {y | y ∈ Q ∧ ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀}
        mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, fun x hx => by
          have h1 := hb.2 x hx
          have h2 := ha.2 x hx
          rw [show a * b * x * (a * b)⁻¹ * x⁻¹ =
            a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) by group, hQ₀c _ h1 a]
          exact Q₀.mul_mem h1 h2⟩
        one_mem' := ⟨Q.one_mem, fun x _ => by simp⟩
        inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, fun x hx => by
          have h := Q₀.inv_mem (ha.2 _ (hconjQ a x hx))
          convert h using 1
          group⟩ }
    have hKn : K.Normal := ⟨fun y hy g => ⟨hQn.conj_mem y hy.1 g, fun x hx => by
      have := hQ₀n.conj_mem _ (hy.2 _ (hconjQ g x hx)) g
      convert this using 1
      group⟩⟩
    have hQ₀K : Q₀ ≤ K := fun y hy => ⟨hQ₀Q hy, fun x _ => by
      rw [← mem_center_iff.mp (hQ₀Z hy) x, mul_inv_cancel_right, mul_inv_cancel]
      exact Q₀.one_mem⟩
    have hKQ : K ≤ Q := fun y hy => hy.1
    haveI := hQb.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : center (Q ⧸ Q₀.subgroupOf Q))
    obtain ⟨⟨x, hxQ⟩, hxz⟩ := QuotientGroup.mk_surjective (z : Q ⧸ Q₀.subgroupOf Q)
    have hxK : x ∈ K := ⟨hxQ, fun y hy => by
      have := mem_center_iff.mp z.2 (QuotientGroup.mk ⟨y, hy⟩)
      rw [← hxz] at this
      exact (quot_comm_iff (Q₀ := Q₀) ⟨x, hxQ⟩ ⟨y, hy⟩).mp this.symm⟩
    have hxQ₀ : x ∉ Q₀ := fun h => hz1 (Subtype.ext (by
      rw [← hxz]; exact (hmk1 ⟨x, hxQ⟩).mpr h))
    rcases hchief K hKn hQ₀K hKQ with h | h
    · exact absurd (h ▸ hxK) hxQ₀
    · intro x hx y hy
      rw [← h] at hx
      exact hx.2 y hy
  have hQr : ∀ x ∈ Q, x ^ q ∈ Q₀ := by
    let N : Subgroup G :=
      { carrier := {y | y ∈ Q ∧ y ^ q ∈ Q₀}
        mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
          have hc : Commute (QuotientGroup.mk ⟨a, ha.1⟩ : Q ⧸ Q₀.subgroupOf Q)
              (QuotientGroup.mk ⟨b, hb.1⟩) :=
            (quot_comm_iff (Q₀ := Q₀) ⟨a, ha.1⟩ ⟨b, hb.1⟩).mpr (hQ' a ha.1 b hb.1)
          have := (quot_pow_eq_one_iff (Q₀ := Q₀) (⟨a * b, Q.mul_mem ha.1 hb.1⟩ : Q) q).mp (by
            rw [show (⟨a * b, Q.mul_mem ha.1 hb.1⟩ : Q) = ⟨a, ha.1⟩ * ⟨b, hb.1⟩ from rfl,
              QuotientGroup.mk_mul, hc.mul_pow,
              (quot_pow_eq_one_iff (Q₀ := Q₀) ⟨a, ha.1⟩ q).mpr ha.2,
              (quot_pow_eq_one_iff (Q₀ := Q₀) ⟨b, hb.1⟩ q).mpr hb.2, one_mul])
          exact this⟩
        one_mem' := ⟨Q.one_mem, by rw [one_pow]; exact Q₀.one_mem⟩
        inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [inv_pow]; exact Q₀.inv_mem ha.2⟩ }
    have hNn : N.Normal := ⟨fun y hy g => ⟨hQn.conj_mem y hy.1 g, by
      rw [conj_pow]; exact hQ₀n.conj_mem _ hy.2 g⟩⟩
    have hQ₀N : Q₀ ≤ N := fun y hy => ⟨hQ₀Q hy, pow_mem hy q⟩
    have hNQ : N ≤ Q := fun y hy => hy.1
    haveI : Fintype (Q ⧸ Q₀.subgroupOf Q) := Fintype.ofFinite _
    have hdvd : q ∣ Fintype.card (Q ⧸ Q₀.subgroupOf Q) := by
      obtain ⟨n, hn⟩ := hQb.exists_card_eq
      rw [← Nat.card_eq_fintype_card, hn]
      rcases n with _ | n
      · exfalso
        have h1 := Finite.one_lt_card_iff_nontrivial.mpr hQbnt
        rw [hn, pow_zero] at h1
        exact lt_irrefl _ h1
      · exact dvd_pow_self q (Nat.succ_ne_zero n)
    obtain ⟨z, hzq⟩ := exists_prime_orderOf_dvd_card q hdvd
    obtain ⟨⟨x, hxQ⟩, hxz⟩ := QuotientGroup.mk_surjective z
    have hxN : x ∈ N := ⟨hxQ, (quot_pow_eq_one_iff (Q₀ := Q₀) ⟨x, hxQ⟩ q).mp (by
      rw [hxz, ← hzq]; exact pow_orderOf_eq_one z)⟩
    have hxQ₀ : x ∉ Q₀ := fun h => by
      have : z = 1 := by rw [← hxz]; exact (hmk1 ⟨x, hxQ⟩).mpr h
      rw [this, orderOf_one] at hzq
      exact hq.one_lt.ne hzq
    rcases hchief N hNn hQ₀N hNQ with h | h
    · exact absurd (h ▸ hxN) hxQ₀
    · intro x hx
      rw [← h] at hx
      exact hx.2
  have hrM : ¬ q ∣ Nat.card M := by
    intro hqM
    have hmod := hQp.card_modEq_card_fixedPoints M
    have hfix : q ∣ Nat.card (MulAction.fixedPoints Q M) :=
      (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hqM)))
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q M) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, fun g => smul_zero (g : G)⟩⟩, inferInstance⟩
    have h1 : 1 < Nat.card (MulAction.fixedPoints Q M) :=
      lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd hpos hfix)
    haveI := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨m, hm⟩, hm0⟩ := exists_ne (⟨0, fun g => smul_zero (g : G)⟩ : MulAction.fixedPoints Q M)
    have hm0' : m ≠ 0 := fun h => hm0 (Subtype.ext h)
    let C : AddSubgroup M :=
      { carrier := {m | ∀ g ∈ Q, g • m = m}
        add_mem' := fun {a b} ha hb g hg => by rw [smul_add, ha g hg, hb g hg]
        zero_mem' := fun g _ => smul_zero g
        neg_mem' := fun {a} ha g hg => by rw [smul_neg, ha g hg] }
    have hinv : ∀ g : G, ∀ m ∈ C, g • m ∈ C := by
      intro g m hm v hv
      have := hm _ (hconjQ g v hv)
      calc v • g • m = g • ((g⁻¹ * v * g) • m) := by
            rw [← mul_smul, ← mul_smul]; congr 1; group
        _ = g • m := by rw [this]
    rcases hirr C hinv with h | h
    · have : m ∈ C := fun g hg => hm ⟨g, hg⟩
      rw [h] at this
      exact hm0' ((AddSubgroup.mem_bot).mp this)
    · obtain ⟨i, x, hx, hne⟩ := hQm
      apply hne
      rw [hfaith x fun m' => by
        have : m' ∈ C := by rw [h]; exact AddSubgroup.mem_top m'
        exact this x hx]
      group
  have hmove : ∃ i, ∃ x ∈ Q, d i * x * (d i)⁻¹ * x⁻¹ ∉ Q₀ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, x, hx, hne⟩ := hQm
    have hk := hcon i x hx
    have hkk : (d i * x * (d i)⁻¹ * x⁻¹) * (d i * x * (d i)⁻¹ * x⁻¹) = 1 := by
      calc (d i * x * (d i)⁻¹ * x⁻¹) * (d i * x * (d i)⁻¹ * x⁻¹)
          = (d i * (d i * x * (d i)⁻¹ * x⁻¹) * (d i)⁻¹) * (d i * x * (d i)⁻¹ * x⁻¹) := by
            rw [hQ₀c _ hk (d i)]
        _ = (d i * d i) * x * (d i * d i)⁻¹ * x⁻¹ := by group
        _ = 1 := by rw [hd i]; group
    have h1 := eq_one_of_mul_self hQodd (hQ₀Q hk) hkk
    apply hne
    calc d i * x = (d i * x * (d i)⁻¹ * x⁻¹) * x * d i := by group
      _ = x * d i := by rw [h1, one_mul]
  have hrot : ∀ a : Fin 3, (∃ x ∈ Q, d a * x * (d a)⁻¹ * x⁻¹ ∉ Q₀) →
      ∃ x ∈ Q, d (a + 1) * x * (d (a + 1))⁻¹ * x⁻¹ ∉ Q₀ := by
    rintro a ⟨x, hx, hnot⟩
    refine ⟨t * x * t⁻¹, hQn.conj_mem x hx t, fun h => hnot ?_⟩
    rw [← ht a] at h
    have := hQ₀n.conj_mem _ h t⁻¹
    convert this using 1
    group
  obtain ⟨i, hi⟩ := hmove
  have hS1 : ∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀ := by
    have key : ∀ a : Fin 3, 0 = a ∨ 0 = a + 1 ∨ 0 = a + 1 + 1 := by decide
    rcases key i with h | h | h
    · rw [h]; exact hi
    · rw [h]; exact hrot i hi
    · rw [h]; exact hrot _ (hrot i hi)
  exact ⟨q, hq, hrM, Q, Q₀, hQn, hQR, hQ₀Q, hQ', hQ₀Z, hQ₀p, hQr, hchief, hS1⟩

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

