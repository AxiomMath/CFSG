module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3A9Data
public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiHyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A7

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup
open CFSG
open CFSG.RankThree.PartTwo.Sec21.FF84 (tab comp sqT tab_mul tab_inj tab_pow_eight)

theorem cycleType_m₂ : m₂.cycleType = {3, 3} := by
  have h1 : (List.formPerm [0, 1, 2] : P8).IsThreeCycle := isThreeCycle_c
  have h2 : (List.formPerm [3, 5, 4] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  have hd : Equiv.Perm.Disjoint (List.formPerm [0, 1, 2] : P8) (List.formPerm [3, 5, 4]) :=
    fun z => by revert z; decide
  show (List.formPerm [0, 1, 2] * List.formPerm [3, 5, 4] : P8).cycleType = {3, 3}
  rw [hd.cycleType_mul, h1.cycleType, h2.cycleType]
  rfl

theorem card_of_list (S : Subgroup P8) (L : List P8) (hnd : L.Nodup) (hiff : ∀ x, x ∈ S ↔ x ∈ L) :
    Nat.card S = L.length := by
  classical
  have hset : (S : Set P8) = ↑L.toFinset := by
    ext x
    simp [hiff]
  calc Nat.card S = (S : Set P8).ncard := Nat.card_coe_set_eq (S : Set P8)
    _ = (↑L.toFinset : Set P8).ncard := by rw [hset]
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ = L.length := List.toFinset_card_of_nodup hnd

theorem mem_iff_of_list {H : Subgroup P8} {L : List P8} (hnd : L.Nodup)
    (hlen : L.length = Nat.card H) (hsub : ∀ x ∈ L, x ∈ H) (x : P8) : x ∈ H ↔ x ∈ L := by
  classical
  have hfin : (H : Set P8).Finite := Set.toFinite _
  have hs : ((L.toFinset : Finset P8) : Set P8) ⊆ (H : Set P8) := fun y hy =>
    hsub y (List.mem_toFinset.1 hy)
  have hc : (H : Set P8).ncard ≤ ((L.toFinset : Finset P8) : Set P8).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
    exact (Nat.card_coe_set_eq (H : Set P8)).ge
  have heq := Set.eq_of_subset_of_ncard_le hs hc hfin
  constructor
  · intro hx
    have hx' : x ∈ ((L.toFinset : Finset P8) : Set P8) := by
      rw [heq]
      exact hx
    exact List.mem_toFinset.1 hx'
  · exact hsub x

def listSub (L : List P8) (h1 : (1 : P8) ∈ L) (hm : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L)
    (hi : ∀ a ∈ L, a⁻¹ ∈ L) : Subgroup P8 where
  carrier := {x | x ∈ L}
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  one_mem' := h1
  inv_mem' := fun {a} ha => hi a ha

theorem mem_listSub (L : List P8) (h1 : (1 : P8) ∈ L) (hm : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L)
    (hi : ∀ a ∈ L, a⁻¹ ∈ L) (x : P8) : x ∈ listSub L h1 hm hi ↔ x ∈ L := Iff.rfl

theorem two_group_pow8 {R : Subgroup P8} (hR : IsPGroup 2 R) {y : P8} (hy : y ∈ R) :
    y ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact (two_pow_order_iff y).1 ⟨j, hj⟩

theorem conj_mem_of_normal {H R : Subgroup P8} (hN : (R.subgroupOf H).Normal) {a x : P8}
    (ha : a ∈ H) (hxH : x ∈ H) (hx : x ∈ R) : a * x * a⁻¹ ∈ R := by
  have h : (⟨a, ha⟩ * ⟨x, hxH⟩ * ⟨a, ha⟩⁻¹ : H) ∈ R.subgroupOf H :=
    hN.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨a, ha⟩
  simpa using Subgroup.mem_subgroupOf.1 h

theorem mem_zpowers_iff_of_sq {s : P8} (hs : s * s = 1) (x : P8) :
    x ∈ Subgroup.zpowers s ↔ x = 1 ∨ x = s := by
  have hsq : s ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, hsq, one_zpow]
    · right
      rw [hm, zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem isElemAb_two_three (A : Subgroup P8) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card A = 8) : IsElemAb 2 3 A := by
  unfold IsElemAb
  have hc : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hexp : Monoid.exponent ↥A ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hsq x x.2)
  refine ⟨{ toIsMulCommutative := hc, exponent_dvd_p := hexp }, ?_⟩
  rw [hcard]
  norm_num

theorem A9_cycleType_four {p q r u : P8} (hp : p.IsSwap) (hq : q.IsSwap) (hr : r.IsSwap)
    (hu : u.IsSwap) (h1 : Disjoint p q) (h2 : Disjoint p r) (h3 : Disjoint p u)
    (h4 : Disjoint q r) (h5 : Disjoint q u) (h6 : Disjoint r u) :
    (p * q * r * u).cycleType = {2, 2, 2, 2} := by
  have hd1 : Disjoint (p * q) r := Disjoint.mul_left h2 h4
  have hd2 : Disjoint (p * q * r) u := Disjoint.mul_left (Disjoint.mul_left h3 h5) h6
  rw [Disjoint.cycleType_mul hd2, Disjoint.cycleType_mul hd1, Disjoint.cycleType_mul h1,
    isSwap_iff_cycleType.mp hp, isSwap_iff_cycleType.mp hq, isSwap_iff_cycleType.mp hr,
    isSwap_iff_cycleType.mp hu]
  rfl

theorem A9s0_cycleType : A9s0.cycleType = {2, 2, 2, 2} :=
  A9_cycleType_four (p := (List.formPerm [0, 3] : P8)) (q := (List.formPerm [1, 5] : P8)) (r := (List.formPerm [2, 4] : P8)) (u := (List.formPerm [6, 7] : P8))
    ⟨0, 3, by decide, by decide⟩ ⟨1, 5, by decide, by decide⟩
    ⟨2, 4, by decide, by decide⟩ ⟨6, 7, by decide, by decide⟩
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)

theorem A9s1_cycleType : A9s1.cycleType = {2, 2, 2, 2} :=
  A9_cycleType_four (p := (List.formPerm [0, 4] : P8)) (q := (List.formPerm [1, 3] : P8)) (r := (List.formPerm [2, 5] : P8)) (u := (List.formPerm [6, 7] : P8))
    ⟨0, 4, by decide, by decide⟩ ⟨1, 3, by decide, by decide⟩
    ⟨2, 5, by decide, by decide⟩ ⟨6, 7, by decide, by decide⟩
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)

theorem A9s2_cycleType : A9s2.cycleType = {2, 2, 2, 2} :=
  A9_cycleType_four (p := (List.formPerm [0, 5] : P8)) (q := (List.formPerm [1, 4] : P8)) (r := (List.formPerm [2, 3] : P8)) (u := (List.formPerm [6, 7] : P8))
    ⟨0, 5, by decide, by decide⟩ ⟨1, 4, by decide, by decide⟩
    ⟨2, 3, by decide, by decide⟩ ⟨6, 7, by decide, by decide⟩
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)
    (fun z => by revert z; decide) (fun z => by revert z; decide)

abbrev A9Good (s t : P8) (Hl Ql El G2 : List P8) : Prop :=
  s * s = 1 ∧ t * s = s * t ∧ Equiv.Perm.sign t = -1 ∧
  (∀ x ∈ Hl, x * s = s * x ∧ Equiv.Perm.sign x = 1) ∧ Hl.Nodup ∧ Hl.length = 192 ∧
  (∀ x ∈ Ql, x ∈ Hl) ∧ Ql.Nodup ∧ Ql.length = 32 ∧ (1 : P8) ∈ Ql ∧
  (∀ a ∈ Ql, ∀ b ∈ Ql, a * b ∈ Ql) ∧ (∀ a ∈ Ql, a⁻¹ ∈ Ql) ∧
  (∀ h ∈ Hl, ∀ x ∈ Ql, h * x * h⁻¹ ∈ Ql) ∧ (∀ x ∈ Ql, x ^ 8 = 1) ∧ s ∈ Ql ∧
  (∀ g ∈ Ql, (∀ h ∈ Ql, h * g = g * h) → g = 1 ∨ g = s) ∧
  (∀ a ∈ Ql, ∀ b ∈ Ql, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = s) ∧
  (∃ a ∈ Ql, ∃ b ∈ Ql, a * b * a⁻¹ * b⁻¹ = s) ∧ (∀ x ∈ Ql, x ^ 2 = 1 ∨ x ^ 2 = s) ∧
  (∀ h ∈ Ql, h * s = s * h) ∧
  El.Nodup ∧ El.length = 8 ∧ (∀ x ∈ El, x ∈ Ql) ∧ (1 : P8) ∈ El ∧
  (∀ a ∈ El, ∀ b ∈ El, a * b ∈ El) ∧ (∀ a ∈ El, a⁻¹ ∈ El) ∧
  (∀ a ∈ El, ∀ b ∈ El, a * b = b * a) ∧ (∀ a ∈ El, a ^ 2 = 1) ∧
  (∀ a ∈ G2, a ∈ Hl) ∧
  (∀ x ∈ Hl, x ^ 8 = 1 → x ∈ Ql ∨
      ∃ a ∈ G2, ∃ b ∈ G2, ((a * x * a⁻¹) * (b * x * b⁻¹)) ^ 8 ≠ 1)

theorem A9_list (s t : P8) (Hl Ql El G2 : List P8) (hcyc : s.cycleType = {2, 2, 2, 2})
    (hG : A9Good s t Hl Ql El G2) :
    s.cycleType = {2, 2, 2, 2} ∧ ∃ Q : Subgroup P8, Q ≤ A8s ∧
      Q ≤ Subgroup.centralizer ({s} : Set P8) ∧
      (Q.subgroupOf (Subgroup.centralizer ({s} : Set P8) ⊓ A8s)).Normal ∧ IsPGroup 2 Q ∧
      Nat.card Q = 32 ∧ s ∈ Q ∧ Subgroup.center ↥Q = (Subgroup.zpowers s).subgroupOf Q ∧
      IsExtraspecialPGroup 2 ↥Q ∧ (∃ A : Subgroup P8, A ≤ Q ∧ IsElemAb 2 3 A) ∧
      ∀ R : Subgroup P8, R ≤ Subgroup.centralizer ({s} : Set P8) ⊓ A8s → IsPGroup 2 R →
        (R.subgroupOf (Subgroup.centralizer ({s} : Set P8) ⊓ A8s)).Normal → R ≤ Q := by
  obtain ⟨hss, ht, hto, hHsub, hHnd, hHlen, hQH, hQnd, hQlen, hQone, hQmul, hQinv,
    hQnorm, hQ2, hsQ, hQcent, hQcomm, hQcomm', hQsq, hQs, hEnd, hElen, hEQ, hEone, hEmul,
    hEinv, hEcomm, hE2, hG2H, hO2⟩ := hG
  refine ⟨hcyc, ?_⟩
  have hs1 : s ≠ 1 := by
    rintro rfl
    have := congrArg Multiset.card hcyc
    simp at this
  set H := Subgroup.centralizer ({s} : Set P8) ⊓ A8s with hHdef
  have hHcard : Nat.card H = 192 := by
    have h1 := card_inf_alt_mul_two s t ht hto
    have h2 := card_centralizer_eq_of_cycleType hcyc
    have h3 : Nat.card (Subgroup.centralizer ({s} : Set P8)) = 384 := by
      rw [h2]
      decide
    rw [hHdef]
    omega
  have hHiff : ∀ x, x ∈ H ↔ x ∈ Hl := fun x =>
    mem_iff_of_list hHnd (by rw [hHlen, hHcard]) (fun x hx => by
      obtain ⟨h1, h2⟩ := hHsub x hx
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 h1,
        Equiv.Perm.mem_alternatingGroup.2 h2⟩) x
  have hQiff : ∀ x, x ∈ listSub Ql hQone hQmul hQinv ↔ x ∈ Ql := fun x =>
    mem_listSub Ql hQone hQmul hQinv x
  set Q := listSub Ql hQone hQmul hQinv with hQdef
  have hQH' : ∀ x ∈ Q, x ∈ H := fun x hx => (hHiff x).2 (hQH x ((hQiff x).1 hx))
  have hQA8 : Q ≤ A8s := fun x hx => (Subgroup.mem_inf.1 (hQH' x hx)).2
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set P8) := fun x hx =>
    (Subgroup.mem_inf.1 (hQH' x hx)).1
  have hNorm : (Q.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hQiff _).2 (hQnorm _ ((hHiff _).1 g.2) _ ((hQiff _).1 hn))
  have hP : IsPGroup 2 Q := by
    intro g
    refine ⟨3, ?_⟩
    apply Subtype.ext
    have := hQ2 _ ((hQiff _).1 g.2)
    simpa using this
  have hcardQ : Nat.card Q = 32 := by
    rw [card_of_list Q Ql hQnd (hQiff), hQlen]
  have hsQ' : s ∈ Q := (hQiff s).2 hsQ
  have hcentQ : ∀ g : Q, g ∈ Subgroup.center Q ↔ (g : P8) = 1 ∨ (g : P8) = s := by
    intro g
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hc
      refine hQcent g.1 ((hQiff _).1 g.2) (fun h hh => ?_)
      have := congrArg Subtype.val (hc ⟨h, (hQiff h).2 hh⟩)
      simpa using this
    · rintro (hg | hg) h
      · apply Subtype.ext
        simp [hg]
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, hg]
        exact hQs _ ((hQiff _).1 h.2)
  have hcenter : Subgroup.center Q = (Subgroup.zpowers s).subgroupOf Q := by
    ext g
    rw [Subgroup.mem_subgroupOf, hcentQ, mem_zpowers_iff_of_sq hss]
  have hcomm : commutator Q = Subgroup.center Q := by
    apply le_antisymm
    · show ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [hcentQ, commutatorElement_def]
      have := hQcomm x.1 ((hQiff _).1 x.2) y.1 ((hQiff _).1 y.2)
      simpa using this
    · intro g hg
      rw [hcentQ] at hg
      rcases hg with hg | hg
      · obtain rfl : g = 1 := Subtype.ext (by simpa using hg)
        exact one_mem _
      · obtain ⟨a, ha, b, hb, hab⟩ := hQcomm'
        let x : Q := ⟨a, (hQiff a).2 ha⟩
        let y : Q := ⟨b, (hQiff b).2 hb⟩
        have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [commutatorElement_def] at hmem
        have hval : x * y * x⁻¹ * y⁻¹ = g := Subtype.ext (by simp [x, y, hab, hg])
        rw [hval] at hmem
        exact hmem
  have hfrat : frattini Q = Subgroup.center Q := by
    haveI : Fact (IsPGroup 2 Q) := ⟨hP⟩
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), hcomm]
    apply le_antisymm
    · apply (Subgroup.closure_le _).2
      rintro g (hg | ⟨x, rfl⟩)
      · exact hg
      · rw [SetLike.mem_coe, hcentQ]
        simp only [Subgroup.coe_pow]
        exact hQsq _ ((hQiff _).1 x.2)
    · intro g hg
      exact Subgroup.subset_closure (Set.mem_union_left _ hg)
  have hcard2 : Nat.card (Subgroup.center Q) = 2 := by
    have hmap : (Subgroup.center Q).map Q.subtype = Subgroup.zpowers s := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        rcases (hcentQ g).1 hg with hg' | hg' <;> simp [hg']
      · intro hx
        rcases (mem_zpowers_iff_of_sq hss x).1 hx with h1 | h1
        · exact ⟨1, Subgroup.one_mem _, by simp [h1]⟩
        · exact ⟨⟨s, hsQ'⟩, (hcentQ _).2 (Or.inr rfl), h1.symm⟩
    have h2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
    rw [← Subgroup.card_map_of_injective (f := Q.subtype) Subtype.val_injective, hmap,
      Nat.card_zpowers, h2]
  refine ⟨Q, hQA8, hQC, hNorm, hP, hcardQ, hsQ', hcenter, ?_, ?_, ?_⟩
  · unfold IsExtraspecialPGroup
    exact ⟨hP, hcomm, hfrat, hcard2⟩
  ·
    have hAiff : ∀ x, x ∈ listSub El hEone hEmul hEinv ↔ x ∈ El := fun x =>
      mem_listSub El hEone hEmul hEinv x
    refine ⟨listSub El hEone hEmul hEinv, fun x hx => (hQiff x).2 (hEQ x ((hAiff x).1 hx)), ?_⟩
    apply isElemAb_two_three
    · intro a ha b hb
      exact hEcomm a ((hAiff a).1 ha) b ((hAiff b).1 hb)
    · intro a ha
      exact hE2 a ((hAiff a).1 ha)
    · rw [card_of_list _ El hEnd hAiff, hElen]
  ·
    intro R hR hPR hNR x hx
    have hxH : x ∈ H := hR hx
    have hx8 : x ^ 8 = 1 := two_group_pow8 hPR hx
    rcases hO2 x ((hHiff x).1 hxH) hx8 with h | ⟨a, ha, b, hb, hne⟩
    · exact (hQiff x).2 h
    · exfalso
      apply hne
      have haH : a ∈ H := (hHiff a).2 (hG2H a ha)
      have hbH : b ∈ H := (hHiff b).2 (hG2H b hb)
      have hA := conj_mem_of_normal hNR haH hxH hx
      have hB := conj_mem_of_normal hNR hbH hxH hx
      exact two_group_pow8 hPR (R.mul_mem hA hB)

theorem A9_mem_tab {L : List P8} {x : P8} : x ∈ L ↔ tab x ∈ L.map tab := by
  constructor
  · intro hx
    exact List.mem_map_of_mem hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hx
    obtain rfl := tab_inj hyx
    exact hy

theorem inv_mem_of_tab {L : List P8} {T : List (List (Fin 8))} (hT : L.map tab = T)
    (hinv : ∀ a ∈ T, ∃ b ∈ T, comp a b = tab 1) {a : P8} (ha : a ∈ L) : a⁻¹ ∈ L := by
  obtain ⟨b, hb, hab⟩ := hinv (tab a) (by rw [← hT]; exact A9_mem_tab.1 ha)
  have hb' : b ∈ L.map tab := by rw [hT]; exact hb
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb'
  have hay : a * y = 1 := tab_inj (by rw [tab_mul]; exact hab)
  rw [inv_eq_of_mul_eq_one_right hay]
  exact hy

theorem A9_commutator_of_tab (a b c : P8) (h : a * b = c * (b * a)) :
    a * b * a⁻¹ * b⁻¹ = c := by
  rw [h]
  group

theorem A9_good_of_tab (s t : P8) (HL QL EL GP : List P8) (HT QT ET : List (List (Fin 8)))
    (GT : List (List (Fin 8) × List (Fin 8))) (hs : s * s = 1)
    (hHsign : ∀ x ∈ HL, Equiv.Perm.sign x = 1) (hto : Equiv.Perm.sign t = -1)
    (h : A9Tab s t HL QL EL GP HT QT ET GT) : A9Good s t HL QL EL GP := by
  unfold A9Tab at h
  obtain ⟨htst, hHlen, hQlen, hELlen, hHT, hHTnd, hHcomm, hQT, hQTnd, hQH,
    hQone, hQs', hQmul, hQinv, hQnorm, hQ2, hQcent, hQcomm, hQcomm', hQsq, hQs,
    hEL, hETnd, hEQ, hE1, hEmul, hEinv, hEcomm, hEsq, hGT, hGH, hO2⟩ := h
  have hHmem : ∀ x, x ∈ HL ↔ tab x ∈ HT := fun x => by rw [← hHT]; exact A9_mem_tab
  have hQmem : ∀ x, x ∈ QL ↔ tab x ∈ QT := fun x => by rw [← hQT]; exact A9_mem_tab
  have hEmem : ∀ x, x ∈ EL ↔ tab x ∈ ET := fun x => by rw [← hEL]; exact A9_mem_tab
  refine ⟨hs, htst, hto, ?_, ?_, hHlen, ?_, ?_, hQlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hELlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    exact ⟨tab_inj (by rw [tab_mul, tab_mul]; exact hHcomm _ ((hHmem x).1 hx)), hHsign x hx⟩
  · exact List.Nodup.of_map tab (by rw [hHT]; exact hHTnd)
  · intro x hx
    exact (hHmem x).2 (hQH _ ((hQmem x).1 hx))
  · exact List.Nodup.of_map tab (by rw [hQT]; exact hQTnd)
  · exact (hQmem 1).2 hQone
  · intro a ha b hb
    rw [hQmem, tab_mul]
    exact hQmul _ ((hQmem a).1 ha) _ ((hQmem b).1 hb)
  · intro a ha
    exact inv_mem_of_tab hQT hQinv ha
  ·
    intro h hh x hx
    obtain ⟨y, hy, hyeq⟩ := hQnorm _ ((hHmem h).1 hh) _ ((hQmem x).1 hx)
    have hy' : y ∈ QL.map tab := by rw [hQT]; exact hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy'
    have hEq : h * x = w * h := tab_inj (by rw [tab_mul, tab_mul]; exact hyeq)
    have hconj : h * x * h⁻¹ = w := by rw [hEq, mul_inv_cancel_right]
    rw [hconj]
    exact hw
  · intro x hx
    exact tab_inj (by rw [tab_pow_eight]; exact hQ2 _ ((hQmem x).1 hx))
  · exact (hQmem s).2 hQs'
  ·
    intro g hg hc
    have hcT : ∀ h ∈ QT, comp h (tab g) = comp (tab g) h := by
      intro h hh
      have hh' : h ∈ QL.map tab := by rw [hQT]; exact hh
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hh'
      have := hc w hw
      rw [← tab_mul, ← tab_mul, this]
    rcases hQcent _ ((hQmem g).1 hg) hcT with h | h
    · exact Or.inl (tab_inj h)
    · exact Or.inr (tab_inj h)
  ·
    intro a ha b hb
    obtain ⟨c, hc, heq⟩ := hQcomm _ ((hQmem a).1 ha) _ ((hQmem b).1 hb)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl (A9_commutator_of_tab a b 1 (tab_inj (by simp only [tab_mul]; exact heq)))
    · exact Or.inr (A9_commutator_of_tab a b s (tab_inj (by simp only [tab_mul]; exact heq)))
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := hQcomm'
    have ha' : a ∈ QL.map tab := by rw [hQT]; exact ha
    have hb' : b ∈ QL.map tab := by rw [hQT]; exact hb
    obtain ⟨a', ha'', rfl⟩ := List.mem_map.1 ha'
    obtain ⟨b', hb'', rfl⟩ := List.mem_map.1 hb'
    exact ⟨a', (hQmem a').2 ha, b', (hQmem b').2 hb,
      A9_commutator_of_tab a' b' s (tab_inj (by simp only [tab_mul]; exact hab))⟩
  · intro x hx
    rw [pow_two]
    rcases hQsq _ ((hQmem x).1 hx) with h | h
    · exact Or.inl (tab_inj (by rw [tab_mul]; exact h))
    · exact Or.inr (tab_inj (by rw [tab_mul]; exact h))
  · intro h hh
    exact tab_inj (by rw [tab_mul, tab_mul]; exact hQs _ ((hQmem h).1 hh))
  · exact List.Nodup.of_map tab (by rw [hEL]; exact hETnd)
  · intro x hx
    have := (hEmem x).1 hx
    exact (hQmem x).2 (hEQ _ this)
  · exact (hEmem 1).2 hE1
  · intro a ha b hb
    rw [hEmem, tab_mul]
    exact hEmul _ ((hEmem a).1 ha) _ ((hEmem b).1 hb)
  · intro a ha
    exact inv_mem_of_tab hEL hEinv ha
  · intro a ha b hb
    exact tab_inj (by rw [tab_mul, tab_mul]; exact hEcomm _ ((hEmem a).1 ha) _ ((hEmem b).1 hb))
  · intro a ha
    exact tab_inj (by rw [pow_two, tab_mul]; exact hEsq _ ((hEmem a).1 ha))
  · intro a ha
    have hmem : (tab a, tab a⁻¹) ∈ GT := by
      rw [← hGT]
      exact List.mem_map_of_mem ha
    exact (hHmem a).2 (hGH _ hmem)
  · intro x hx h8
    have hT8 : sqT (sqT (sqT (tab x))) = tab 1 := by
      have := tab_pow_eight x
      rw [h8] at this
      exact this.symm
    rcases hO2 _ ((hHmem x).1 hx) hT8 with hq | ⟨a', ha', b', hb', hne⟩
    · exact Or.inl ((hQmem x).2 hq)
    · have ha'' : a' ∈ GT := ha'
      have hb'' : b' ∈ GT := hb'
      rw [← hGT] at ha'' hb''
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha''
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb''
      refine Or.inr ⟨g, hg, k, hk, ?_⟩
      intro heq
      have key := tab_pow_eight ((g * x * g⁻¹) * (k * x * k⁻¹))
      rw [heq] at key
      simp only [tab_mul] at key
      exact hne key.symm

theorem A9_centralizer : A9CentralizerStmt := by
  intro s hs h2 h₁ h₂
  have hc2 : s * m₂ = m₂ * s := mul_inv_eq_iff_eq_mul.1 h₂
  have hcard : Nat.card ↥(Subgroup.centralizer ({m₂} : Set P8)) = 36 :=
    card_centralizer_cycle33 cycleType_m₂
  have hmem : s ∈ A9Cl := by
    have hsub : ∀ x ∈ A9Cl, x ∈ Subgroup.centralizer ({m₂} : Set P8) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (A9Cl_centr x hx)
    exact (mem_iff_of_list (H := Subgroup.centralizer ({m₂} : Set P8)) A9Cl_good.1
      (by rw [A9Cl_good.2, hcard]) hsub s).1 (Subgroup.mem_centralizer_singleton_iff.2 hc2)
  have hcl := A9_class s hmem h2 (Equiv.Perm.mem_alternatingGroup.1 hs) h₁
  rcases hcl with rfl | rfl | rfl
  · exact A9_list _ _ _ _ _ _ A9s0_cycleType
      (A9_good_of_tab _ _ _ _ _ _ _ _ _ _ h2 A9Hsign0 A9tsign0 A9Tab0)
  · exact A9_list _ _ _ _ _ _ A9s1_cycleType
      (A9_good_of_tab _ _ _ _ _ _ _ _ _ _ h2 A9Hsign1 A9tsign1 A9Tab1)
  · exact A9_list _ _ _ _ _ _ A9s2_cycleType
      (A9_good_of_tab _ _ _ _ _ _ _ _ _ _ h2 A9Hsign2 A9tsign2 A9Tab2)

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
