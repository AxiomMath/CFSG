module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG CFSG.LocalCores
open scoped IsMulCommutative

variable {H : Type*} [Group H]

theorem exists_elemAbelian_of_component_family [Finite H] {ι : Type*} [Fintype ι] {q : ℕ}
    (hq : q.Prime) (K : ι → Subgroup H) (hK : ∀ i, IsComponent (K i))
    (hinj : Function.Injective K) (y : ι → H) (hy : ∀ i, y i ∈ K i)
    (hyq : ∀ i, orderOf (((⟨y i, hy i⟩ : K i) : K i ⧸ center (K i))) = q) :
    ∃ V : Subgroup H, V ≤ closure (Set.range y) ∧ CFSG.Assembly.IsElemAbelian q V ∧
      Nat.card V = q ^ Fintype.card ι := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcent : ∀ i j, i ≠ j → y j ∈ centralizer (K i : Set H) := by
    intro i j hij
    rcases distinct_components_commute (hK i) (hK j) with h | h
    · exact absurd (hinj h) hij
    · exact commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact h) (hy j)
  have hcomm : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact mem_centralizer_iff.mp (hcent i j hij) (y i) (hy i)
  set B := closure (Set.range y) with hB
  have : IsMulCommutative B := isMulCommutative_closure hcomm
  let y' : ι → B := fun i => ⟨y i, subset_closure ⟨i, rfl⟩⟩
  have hgen : ∀ b : B, ∃ n : ι → ℤ, b = ∏ i, y' i ^ n i := by
    intro b
    refine (mem_closure_range_iff_of_fintype).mp ?_
    have h : closure (Set.range y') = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨b, hb⟩ -
      induction hb using closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact subset_closure ⟨i, rfl⟩
      | one => exact one_mem _
      | mul x y _ _ hx hy => exact mul_mem hx hy
      | inv x _ hx => exact inv_mem hx
    rw [h]
    exact mem_top b
  have hind : ∀ n : ι → ℤ, ∏ i, y' i ^ n i = 1 → ∀ j, (q : ℤ) ∣ n j := by
    intro n hn j
    rw [← Finset.mul_prod_erase Finset.univ (fun i => y' i ^ n i) (Finset.mem_univ j)] at hn
    have hrest : (∏ i ∈ Finset.univ.erase j, y' i ^ n i : B) ∈
        (centralizer (K j : Set H)).comap B.subtype :=
      Subgroup.prod_mem _ fun i hi => by
        rw [mem_comap]
        exact zpow_mem (hcent j i (Finset.ne_of_mem_erase hi).symm) _
    have hyj : y' j ^ n j = (∏ i ∈ Finset.univ.erase j, y' i ^ n i)⁻¹ :=
      eq_inv_of_mul_eq_one_left hn
    have h1 : y j ^ n j ∈ centralizer (K j : Set H) := by
      have h2 : ((y' j ^ n j : B) : H) ∈ centralizer (K j : Set H) := by
        rw [hyj]
        exact inv_mem hrest
      simpa [y'] using h2
    have hc : (⟨y j, hy j⟩ : K j) ^ n j ∈ center (K j) := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      simpa using mem_centralizer_iff.mp h1 k k.2
    rw [← hyq j]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (by
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
      exact hc)
  let ψ : B →* B := powMonoidHom q
  let φ : (ι → Fin q) → B ⧸ ψ.range := fun c =>
    QuotientGroup.mk (∏ i, y' i ^ (((c i : ℕ) : ℤ)))
  have hφ : Function.Injective φ := by
    intro c c' h
    obtain ⟨b, hb⟩ := QuotientGroup.eq.mp h
    obtain ⟨n, rfl⟩ := hgen b
    have e1 : ψ (∏ i, y' i ^ n i) = ∏ i, y' i ^ ((q : ℤ) * n i) := by
      simp only [ψ, powMonoidHom_apply, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    have e2 : ∀ a b : ι → ℤ, (∏ i, y' i ^ a i)⁻¹ * ∏ i, y' i ^ b i = ∏ i, y' i ^ (b i - a i) := by
      intro a b
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_neg, ← zpow_add]
      ring_nf
    have h2 : ∏ i, y' i ^ ((((c' i : ℕ) : ℤ) - (c i : ℕ)) - q * n i) = 1 := by
      have := e2 (fun i => (q : ℤ) * n i) (fun i => ((c' i : ℕ) : ℤ) - (c i : ℕ))
      rw [← this, ← e1, hb, e2, inv_mul_cancel]
    funext j
    obtain ⟨t, ht⟩ : (q : ℤ) ∣ ((c' j : ℕ) : ℤ) - (c j : ℕ) := by
      have := dvd_add (hind _ h2 j) (dvd_mul_right (q : ℤ) (n j))
      simpa using this
    have hlt1 := (c j).isLt
    have hlt2 := (c' j).isLt
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h0 | h0 | h0
      · nlinarith
      · exact h0
      · nlinarith
    apply Fin.ext
    rw [ht0, mul_zero, sub_eq_zero] at ht
    exact_mod_cast ht.symm
  have hcard1 : q ^ Fintype.card ι ≤ Nat.card (B ⧸ ψ.range) := by
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin q), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := ι)] at this
  have hΩ : Nat.card ψ.ker = Nat.card (B ⧸ ψ.range) := by
    have h1 : Nat.card B = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, mul_comm,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have h2 : Nat.card B = Nat.card (B ⧸ ψ.range) * Nat.card ψ.range :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans h2)
  have hΩp : IsPGroup q ψ.ker := fun w => ⟨1, by
    rw [pow_one]
    exact Subtype.ext w.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩp
  have hle : Fintype.card ι ≤ k := by
    have : q ^ Fintype.card ι ≤ q ^ k := by
      rw [← hk, hΩ]
      exact hcard1
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp this
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime q
    (show q ^ Fintype.card ι ∣ Nat.card ψ.ker from hk ▸ pow_dvd_pow q hle)
  refine ⟨(V'.map ψ.ker.subtype).map B.subtype, map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨wa, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨wb, -, rfl⟩⟩ := b
    apply Subtype.ext
    change (wa : H) * wb = wb * wa
    exact congrArg Subtype.val (mul_comm wa wb)
  · rintro _ ⟨w, ⟨ω, -, rfl⟩, rfl⟩
    exact congrArg Subtype.val ω.2
  · rw [card_map_of_injective B.subtype_injective, card_map_of_injective ψ.ker.subtype_injective,
      hV']

open scoped Pointwise in
theorem component_orbit_ambient_local_rank_witness [Finite H] {r : ℕ} (hr : r.Prime) {x : H}
    (hx : ∃ k : ℕ, orderOf x = r ^ k) {L : Subgroup H} (hL : IsComponent L)
    (hmove : L.map (MulAut.conj x).toMonoidHom ≠ L) {q : ℕ} (hq : q.Prime)
    (hqL : 2 * q ∣ Nat.card (L ⧸ center L)) {d : ℕ}
    (hd : (Set.range fun n : ℤ => L.map (MulAut.conj (x ^ n)).toMonoidHom).ncard = d) :
    (∃ i : ℕ, 1 ≤ i ∧ d = r ^ i) ∧ r ≤ d ∧
      ∃ u : H, orderOf u = 2 ∧ ∃ V : Subgroup H, V ≤ centralizer {u} ∧
        CFSG.Assembly.IsElemAbelian q V ∧ Nat.card V = q ^ (d - 1) ∧
        d - 1 ≤ CFSG.Assembly.RankThreeEven.localRank q H ∧ r - 1 ≤ d - 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  set O := Set.range fun n : ℤ => L.map (MulAut.conj (x ^ n)).toMonoidHom with hO
  have hOorb : O = MulAction.orbit (zpowers (MulAut.conj x)) L := by
    ext K
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨⟨MulAut.conj x ^ n, n, rfl⟩, ?_⟩
      change (MulAut.conj x ^ n) • L = _
      rw [← map_zpow, CFSG.GroupActions.mulAut_smul_subgroup_eq_map]
    · rintro ⟨⟨g, n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      change _ = (MulAut.conj x ^ n) • L
      rw [← map_zpow, CFSG.GroupActions.mulAut_smul_subgroup_eq_map]
  obtain ⟨k, hk⟩ := hx
  have hdvd : d ∣ r ^ k := by
    rw [← hd, hOorb, ← MulAction.index_stabilizer, ← hk]
    refine (Subgroup.index_dvd_card _).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_map_dvd _ x
  have hL0 : L ∈ O := ⟨0, Subgroup.ext fun y => by simp⟩
  have hL1 : L.map (MulAut.conj x).toMonoidHom ∈ O := ⟨1, by simp⟩
  have hd1 : d ≠ 1 := by
    intro h
    rw [← hd, Set.ncard_eq_one] at h
    obtain ⟨K, hK⟩ := h
    rw [hK, Set.mem_singleton_iff] at hL0 hL1
    exact hmove (hL1.trans hL0.symm)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  have hi1 : i ≠ 0 := by
    rintro rfl
    exact hd1 (by rw [hi, pow_zero])
  have hrd : r ≤ d := hi ▸ Nat.le_self_pow hi1 r
  have hOcomp : ∀ K ∈ O, IsComponent K ∧ Nat.card (K ⧸ center K) = Nat.card (L ⧸ center L) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨isComponent_map_mulEquiv (MulAut.conj (x ^ n)) hL, ?_⟩
    let e := L.equivMapOfInjective (MulAut.conj (x ^ n)).toMonoidHom (MulAut.conj (x ^ n)).injective
    have hc := Subgroup.map_center_eq e
    exact (Nat.card_congr (QuotientGroup.congr _ _ e hc).toEquiv).symm
  have h2L : 2 ∣ Nat.card L :=
    (dvd_mul_right 2 q).trans (hqL.trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 h2L
  set ι := ↥(O \ {L}) with hι
  have hex : ∀ K : ι, ∃ z : (K : Subgroup H),
      orderOf ((z : (K : Subgroup H)) : (K : Subgroup H) ⧸ center (K : Subgroup H)) = q := by
    intro K
    have hqK : q ∣ Nat.card ((K : Subgroup H) ⧸ center (K : Subgroup H)) := by
      rw [(hOcomp K K.2.1).2]
      exact (dvd_mul_left q 2).trans hqL
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' q hqK
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨z, hs⟩
  choose z hz using hex
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨V, hVB, hVab, hVcard⟩ := exists_elemAbelian_of_component_family hq
    (fun K : ι => (K : Subgroup H)) (fun K => (hOcomp K K.2.1).1) Subtype.val_injective
    (fun K => (z K : H)) (fun K => (z K).2) hz
  have hcardι : Fintype.card ι = d - 1 := by
    rw [← Nat.card_eq_fintype_card, hι, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hL0,
      hd]
  have hVu : V ≤ centralizer {(u : H)} := by
    refine hVB.trans ((closure_le _).mpr ?_)
    rintro _ ⟨K, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases distinct_components_commute (hOcomp K K.2.1).1 hL with h | h
    · exact absurd h K.2.2
    · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h (z K).2) u u.2).symm
  have hu2 : orderOf (u : H) = 2 := by rw [Subgroup.orderOf_coe, hu]
  rw [hcardι] at hVcard
  refine ⟨⟨i, Nat.one_le_iff_ne_zero.mpr hi1, hi⟩, hrd, u, hu2, V, hVu, hVab, hVcard,
    CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hq hu2 hVu hVab hVcard,
    Nat.sub_le_sub_right hrd 1⟩

end CFSG.RankThree.GroupTheory.SteinbergBK
