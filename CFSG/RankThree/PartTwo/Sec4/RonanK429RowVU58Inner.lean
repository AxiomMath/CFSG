module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Blk
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Ord
public import CFSG.Models.PGLSimple
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

namespace RowV

theorem eq_one_of_mk_eq_one_of_pow_odd {S : Type} [Group S] {Q : Subgroup S} (x : Q) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) (hx : (QuotientGroup.mk x : Q ⧸ CFSG.pCore 2 Q) = 1) :
    x = 1 := by
  rw [QuotientGroup.eq_one_iff] at hx
  have h2 : IsPGroup 2 (CFSG.pCore 2 Q) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg (fun y : CFSG.pCore 2 Q => (y : Q)) hk
    simpa using this
  have hd : orderOf x ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hxm)
  have hg : Nat.gcd (2 ^ k) m = 1 := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem nontrivial_of_isType429 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (h : IsType429 X) : Nontrivial X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  exact not_isType429_of_dvd (N := 1) (B := 2) one_pos
    (by rw [Nat.card_eq_one_iff_unique.mpr ⟨hX, ⟨1⟩⟩]) (by norm_num) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem dvd_of_dvd_mul_of_forall_pow {G : Type} [Group G] [Finite G] {p N : ℕ} (hp : p.Prime)
    (hd : Nat.card G ∣ p * N) (hno : ∀ g : G, g ^ p = 1 → g = 1) : Nat.card G ∣ N := by
  have hnd : ¬ p ∣ Nat.card G := by
    intro h
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p h
    have h1 := hno g (by rw [← hg]; exact pow_orderOf_eq_one g)
    rw [h1, orderOf_one] at hg
    exact hp.one_lt.ne hg
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)).dvd_of_dvd_mul_left hd

theorem isSubnormal_subgroupOf_of_le {S : Type} [Group S] {C H Q : Subgroup S} (hHC : H ≤ C)
    (hsn : (Q.subgroupOf C).IsSubnormal) : (Q.subgroupOf H).IsSubnormal := by
  have h := hsn.comap (Subgroup.inclusion hHC)
  have heq : (Q.subgroupOf C).comap (Subgroup.inclusion hHC) = Q.subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rwa [heq] at h

theorem false_of_u38 {S : Type} [Group S] [Finite S] {C H Q : Subgroup S} (hHC : H ≤ C)
    (hCH : C ≤ Subgroup.normalizer (H : Set S)) (hq : CFSG.IsQuasisimple H) {z : S} (hzH : z ∈ H)
    (hzC : ∀ c ∈ C, c * z = z * c) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (h19 : ∀ t ∈ C, t ^ 19 = 1 → t ∈ H) (hQC : Q ≤ C) (hsn : (Q.subgroupOf C).IsSubnormal)
    [Group.IsPerfect Q] (hX : Nonempty (Q ⧸ CFSG.pCore 2 Q ≃* projSU 3 2 3)) : False := by
  obtain ⟨φ⟩ := hX
  have hXcard : Nat.card (Q ⧸ CFSG.pCore 2 Q) = 5515776 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.PGLModel.card_projSU_three_eight
  haveI : Nontrivial (Q ⧸ CFSG.pCore 2 Q) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : IsSimpleGroup (projSU 3 2 3) :=
    CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩
  haveI hsimp : IsSimpleGroup (Q ⧸ CFSG.pCore 2 Q) := φ.isSimpleGroup
  have hZX : Subgroup.center (Q ⧸ CFSG.pCore 2 Q) = ⊥ :=
    center_eq_bot_of_isoLThreePi (p := 2) (e := 3) (by norm_num) (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
  rcases Res429.eq_top_or_le_center_of_isSubnormal hq (isSubnormal_subgroupOf_of_le hHC hsn) with
    htop | hcen
  ·
    have hzQ : z ∈ Q := by
      have h1 : (⟨z, hzH⟩ : H) ∈ Q.subgroupOf H := by
        rw [htop]
        exact Subgroup.mem_top _
      exact h1
    have hzc : (QuotientGroup.mk (⟨z, hzQ⟩ : Q) : Q ⧸ CFSG.pCore 2 Q) ∈
        Subgroup.center (Q ⧸ CFSG.pCore 2 Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact hzC y (hQC y.2)
    rw [hZX, Subgroup.mem_bot] at hzc
    have h1 := eq_one_of_mk_eq_one_of_pow_odd ⟨z, hzQ⟩ (m := 3) ⟨1, rfl⟩
      (Subtype.ext (by simpa using hz3)) hzc
    exact hz1 (congrArg Subtype.val h1)
  ·
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have h19Q : 19 ∣ Nat.card Q :=
      (show 19 ∣ Nat.card (Q ⧸ CFSG.pCore 2 Q) by rw [hXcard]; norm_num).trans
        (Subgroup.card_quotient_dvd_card _)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 19 h19Q
    have ht19 : (t : S) ^ 19 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, OneMemClass.coe_one]
    have htH : (t : S) ∈ H := h19 t (hQC t.2) ht19
    set N : Subgroup Q := H.subgroupOf Q with hN
    have hNn : N.Normal := by
      constructor
      intro n hn g
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hCH (hQC g.2)) (n : S)).mp hn
      simpa using h1
    have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
      intro x hx y hy
      rw [hN, Subgroup.mem_subgroupOf] at hx hy
      have hxc : (⟨(x : S), hx⟩ : H) ∈ Subgroup.center H :=
        hcen (by rw [Subgroup.mem_subgroupOf]; exact x.2)
      have h1 := Subgroup.mem_center_iff.mp hxc ⟨(y : S), hy⟩
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2 ⊢
      exact h2.symm
    set Nb := N.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) with hNb
    have hNbn : Nb.Normal := Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
    haveI := hNbn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nb with hbot | htop'
    ·
      have htN : t ∈ N := htH
      have h1 : (QuotientGroup.mk t : Q ⧸ CFSG.pCore 2 Q) = 1 := by
        have h2 : QuotientGroup.mk' (CFSG.pCore 2 Q) t ∈ Nb := Subgroup.mem_map_of_mem _ htN
        rw [hbot, Subgroup.mem_bot] at h2
        exact h2
      have h3 := eq_one_of_mk_eq_one_of_pow_odd t (m := 19) ⟨9, rfl⟩
        (by rw [← ht]; exact pow_orderOf_eq_one t) h1
      rw [h3, orderOf_one] at ht
      norm_num at ht
    ·
      obtain ⟨a, ha⟩ := exists_ne (1 : Q ⧸ CFSG.pCore 2 Q)
      have hcomm : ∀ x y : Q ⧸ CFSG.pCore 2 Q, x * y = y * x := by
        intro x y
        have hx : x ∈ Nb := by
          rw [htop']
          exact Subgroup.mem_top x
        have hy : y ∈ Nb := by
          rw [htop']
          exact Subgroup.mem_top y
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        rw [← map_mul, ← map_mul, hNcomm x' hx' y' hy']
      have hac : a ∈ Subgroup.center (Q ⧸ CFSG.pCore 2 Q) :=
        Subgroup.mem_center_iff.mpr fun g => hcomm g a
      rw [hZX, Subgroup.mem_bot] at hac
      exact ha hac

section Reps

open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesU58
open CFSG.RankThree.PartTwo.KFacts.KS21.U58

theorem card_centralizer_dvd (s : SUI) :
    Nat.card (Subgroup.centralizer ({s} : Set SUI)) ∣ 4656663745464977326080 := by
  have h := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({s} : Set SUI))
  rw [card_SUI] at h
  norm_num at h
  exact h

theorem fib0_lt : ∀ κ : ZMod 9, Fintype.card {i // ext9 (us 0) i = κ} < 4 := by decide

theorem fib0_small : ∀ κ : ZMod 9, κ ≠ 0 → Fintype.card {i // ext9 (us 0) i = κ} < 3 := by
  decide

theorem fib1_lt : ∀ κ : ZMod 9, Fintype.card {i // ext9 (us 1) i = κ} < 4 := by decide

theorem fib1_small : ∀ κ : ZMod 9, κ ≠ 3 → Fintype.card {i // ext9 (us 1) i = κ} < 3 := by
  decide

theorem fib2_lt : ∀ κ : ZMod 9, Fintype.card {i // ext9 (us 2) i = κ} < 3 := by decide

theorem fib3_single : ∀ k : Fin 5, ext9 (us 3) k = ext9 (us 3) 4 → k = 4 := by decide

theorem fib3_const : ∀ k : Fin 5, k ≠ 4 → ext9 (us 3) k = 3 := by decide

theorem idOutsideSU_le_centralizer {u : Fin 4 → ZMod 9} (κ : ZMod 9) :
    idOutsideSU {i | ext9 u i = κ} ≤
      Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) :=
  fun _ hx => mem_centralizer_of_isBlockDiag (IsIdOutside.isBlockDiag hx)

theorem centralizer_le_normalizer_fibre {u : Fin 4 → ZMod 9} (κ : ZMod 9) :
    Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) ≤
      Subgroup.normalizer (idOutsideSU {i | ext9 u i = κ} : Set SUI) :=
  centralizer_le_normalizer_idOutsideSU fun i j e => by simp only [Set.mem_ofPred_eq, e]

theorem card_centralizer_dvd_of_pow {u : Fin 4 → ZMod 9} {p N : ℕ} (hp : p.Prime)
    (hd : Nat.card (Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) ∣ p * N)
    (h : (p = 5 ∧ ∀ κ, Fintype.card {i // ext9 u i = κ} < 4) ∨
      (p = 19 ∧ ∀ κ, Fintype.card {i // ext9 u i = κ} < 3)) :
    Nat.card (Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) ∣ N :=
  dvd_of_dvd_mul_of_forall_pow hp hd fun g hg =>
    Subtype.ext (eq_one_of_mem_centralizer_of_pow g.2 h (by simpa using congrArg Subtype.val hg))

theorem false_of_bs2 {Q : Subgroup SUI} (hQ : Q ≤ Subgroup.centralizer ({bs 2} : Set SUI))
    [Group.IsPerfect Q] (hT : IsType429 (Q ⧸ CFSG.pCore 2 Q)) : False := by
  have h5 : Nat.card (Subgroup.centralizer ({bs 2} : Set SUI)) ∣ 931332749092995465216 :=
    card_centralizer_dvd_of_pow (u := us 2) (by decide)
      (by rw [show 5 * 931332749092995465216 = 4656663745464977326080 by norm_num]
          exact card_centralizer_dvd _)
      (Or.inl ⟨rfl, fun κ => (fib2_lt κ).trans (by norm_num)⟩)
  have h95 : Nat.card (Subgroup.centralizer ({bs 2} : Set SUI)) ∣ 49017513110157656064 :=
    card_centralizer_dvd_of_pow (u := us 2) (by decide)
      (by rw [show 19 * 49017513110157656064 = 931332749092995465216 by norm_num]; exact h5)
      (Or.inr ⟨rfl, fib2_lt⟩)
  exact not_isType429_of_dvd (N := 49017513110157656064) (B := 332) (by norm_num)
    ((Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_dvd_of_le hQ).trans h95))
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT

theorem false_of_bs0 {Q : Subgroup SUI} (hQ : Q ≤ Subgroup.centralizer ({bs 0} : Set SUI))
    (hsn : (Q.subgroupOf (Subgroup.centralizer ({bs 0} : Set SUI))).IsSubnormal)
    [Group.IsPerfect Q] (hT : IsType429 (Q ⧸ CFSG.pCore 2 Q)) : False := by
  have hCd : Nat.card (Subgroup.centralizer ({bs 0} : Set SUI)) ∣ 931332749092995465216 :=
    card_centralizer_dvd_of_pow (u := us 0) (by decide)
      (by rw [show 5 * 931332749092995465216 = 4656663745464977326080 by norm_num]
          exact card_centralizer_dvd _)
      (Or.inl ⟨rfl, fib0_lt⟩)
  have hX := isType429_u38_of_dvd (N := 931332749092995465216) (B := 480) (by norm_num)
    ((Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_dvd_of_le hQ).trans hCd))
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT
  have hf : Function.Injective (![2, 3, 4] : Fin 3 → Fin 5) := by decide
  have hfib : Set.range (![2, 3, 4] : Fin 3 → Fin 5) = {i | ext9 (us 0) i = 0} :=
    range_eq_setOf (by decide)
  refine false_of_u38 (idOutsideSU_le_centralizer (u := us 0) 0)
    (centralizer_le_normalizer_fibre (u := us 0) 0)
    (isQuasisimple_idOutsideSU _ hf hfib (by norm_num))
    (z := τ (Multiplicative.ofAdd ![0, 0, 3, 3])) (τ_mem_idOutsideSU (by decide))
    (Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_constant (u := us 0) (by decide)))
    ?_ ?_ (fun t ht h19 => mem_idOutsideSU_of_pow_nineteen (u := us 0) ht 0 fib0_small h19)
    hQ hsn hX
  · intro h
    have h1 := τ_injective (h.trans (map_one τ).symm)
    have h2 := congrArg (fun v : Multiplicative (Fin 4 → ZMod 9) => Multiplicative.toAdd v 2) h1
    exact absurd h2 (by decide)
  · rw [← map_pow]
    have h3 : (Multiplicative.ofAdd (![0, 0, 3, 3] : Fin 4 → ZMod 9)) ^ 3 = 1 := by decide
    rw [h3, map_one]

theorem false_of_bs1 {Q : Subgroup SUI} (hQ : Q ≤ Subgroup.centralizer ({bs 1} : Set SUI))
    (hsn : (Q.subgroupOf (Subgroup.centralizer ({bs 1} : Set SUI))).IsSubnormal)
    [Group.IsPerfect Q] (hT : IsType429 (Q ⧸ CFSG.pCore 2 Q)) : False := by
  have hCd : Nat.card (Subgroup.centralizer ({bs 1} : Set SUI)) ∣ 931332749092995465216 :=
    card_centralizer_dvd_of_pow (u := us 1) (by decide)
      (by rw [show 5 * 931332749092995465216 = 4656663745464977326080 by norm_num]
          exact card_centralizer_dvd _)
      (Or.inl ⟨rfl, fib1_lt⟩)
  have hX := isType429_u38_of_dvd (N := 931332749092995465216) (B := 480) (by norm_num)
    ((Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_dvd_of_le hQ).trans hCd))
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT
  have hf : Function.Injective (![0, 1, 2] : Fin 3 → Fin 5) := by decide
  have hfib : Set.range (![0, 1, 2] : Fin 3 → Fin 5) = {i | ext9 (us 1) i = 3} :=
    range_eq_setOf (by decide)
  refine false_of_u38 (idOutsideSU_le_centralizer (u := us 1) 3)
    (centralizer_le_normalizer_fibre (u := us 1) 3)
    (isQuasisimple_idOutsideSU _ hf hfib (by norm_num)) (z := bs 1)
    (τ_mem_idOutsideSU (u := us 1) (w := us 1) (by decide))
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) ?_ (δ_pow_three _)
    (fun t ht h19 => mem_idOutsideSU_of_pow_nineteen (u := us 1) ht 3 fib1_small h19) hQ hsn hX
  intro h
  have h1 := δ_injective (h.trans (map_one δ).symm)
  have h2 := congrArg (fun v : Multiplicative (Fin 4 → ZMod 3) => Multiplicative.toAdd v 0) h1
  exact absurd h2 (by decide)

theorem false_of_bs3 {Q : Subgroup SUI} (hQ : Q ≤ Subgroup.centralizer ({bs 3} : Set SUI))
    (hsn : (Q.subgroupOf (Subgroup.centralizer ({bs 3} : Set SUI))).IsSubnormal)
    [hQp : Group.IsPerfect Q] (hT : IsType429 (Q ⧸ CFSG.pCore 2 Q)) : False := by
  have hf : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 5) := by decide
  have hfib : Set.range (![0, 1, 2, 3] : Fin 4 → Fin 5) = {i | ext9 (us 3) i = 3} :=
    range_eq_setOf (by decide)
  have hq := isQuasisimple_idOutsideSU _ hf hfib (by norm_num)
  have hQH : Q ≤ idOutsideSU {i | ext9 (us 3) i = 3} := by
    rw [← Subgroup.commutator_eq_self (H := Q)]
    exact Subgroup.commutator_le.mpr fun a ha b hb =>
      commutator_mem_idOutsideSU (u := us 3) fib3_single fib3_const (hQ ha) (hQ hb)
  haveI := nontrivial_of_isType429 hT
  have hQ1 : Nontrivial Q := by
    obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ CFSG.pCore 2 Q)
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    exact nontrivial_of_ne q 1 (fun h => hx (by rw [h]; rfl))
  have hQeq : Q = idOutsideSU {i | ext9 (us 3) i = 3} :=
    Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hQH hq hQp hQ1
      (isSubnormal_subgroupOf_of_le (idOutsideSU_le_centralizer (u := us 3) 3) hsn)
  have h13Q : 13 ∣ Nat.card Q := by
    rw [hQeq, card_idOutsideSU _ hf hfib (by norm_num)]
    exact thirteen_dvd_card_SU4
  have h13X : 13 ∣ Nat.card (Q ⧸ CFSG.pCore 2 Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 Q))
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Q), hk] at h13Q
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 13 2)).dvd_of_dvd_mul_right h13Q
  exact not_isType429_of_dvd_of_dvd (N := 4656663745464977326080) (M := 13) (B := 587)
    (by norm_num)
    ((Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_dvd_of_le hQ).trans
      (card_centralizer_dvd _)))
    h13X (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT

end Reps

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
