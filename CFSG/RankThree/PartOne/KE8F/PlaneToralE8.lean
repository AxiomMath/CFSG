module

public import CFSG.RankThree.PartOne.KE.PlaneToral

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE
open scoped Pointwise commutatorElement IsMulCommutative


theorem fixes_two_power_of_card_le_sixteen {X : Type*} [Group X] [Finite X]
    (hcomm : ∀ a b : X, a * b = b * a) (hX : Nat.card {x : X // x ^ 2 = 1} ≤ 16)
    {p : ℕ} [Fact p.Prime] (hp : 10 < p) {τ : MulAut X} {n : ℕ} (hn : τ ^ (p ^ n) = 1) :
    ∀ (k : ℕ) (x : X), x ^ (2 ^ k) = 1 → τ x = x := by
  classical
  have hfix2 : ∀ z : X, z ^ 2 = 1 → τ z = z := by
    let T := {x : X // x ^ 2 = 1}
    have : Fintype T := Fintype.ofFinite T
    let σ : Equiv.Perm T :=
      { toFun := fun t => ⟨τ t, by rw [← map_pow, t.2, map_one]⟩
        invFun := fun t => ⟨τ.symm t, by rw [← map_pow, t.2, map_one]⟩
        left_inv := fun t => Subtype.ext (τ.symm_apply_apply t)
        right_inv := fun t => Subtype.ext (τ.apply_symm_apply t) }
    have hσpow : ∀ (m : ℕ) (t : T), ((σ ^ m) t : X) = (τ ^ m) t := by
      intro m t
      induction m generalizing t with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
        rfl
    have hσ : σ ^ (p ^ n) = 1 := by
      ext t
      rw [hσpow, hn]
      rfl
    have hcard := Equiv.Perm.card_compl_support_modEq hσ
    have hTcard : Fintype.card T ≤ 16 := by rw [← Nat.card_eq_fintype_card]; exact hX
    have hsum : σ.supportᶜ.card + σ.support.card = Fintype.card T := Finset.card_compl_add_card _
    have hmod : σ.support.card ≡ 0 [MOD p] := by
      have h1 : σ.supportᶜ.card + σ.support.card ≡ Fintype.card T + σ.support.card [MOD p] :=
        Nat.ModEq.add_right _ hcard
      rw [hsum] at h1
      have h2 : Fintype.card T + 0 ≡ Fintype.card T + σ.support.card [MOD p] := by
        simpa using h1
      exact (Nat.ModEq.add_left_cancel' _ h2).symm
    let Tall : Subgroup X :=
      { carrier := {x | x ^ 2 = 1}
        mul_mem' := fun {a b} ha hb => by
          change a ^ 2 = 1 at ha
          change b ^ 2 = 1 at hb
          change (a * b) ^ 2 = 1
          rw [Commute.mul_pow (hcomm a b) 2, ha, hb, one_mul]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          change a ^ 2 = 1 at ha
          change a⁻¹ ^ 2 = 1
          rw [inv_pow, ha, inv_one] }
    let Tfix : Subgroup X := Tall ⊓ (τ.toMonoidHom.eqLocus (MonoidHom.id X))
    have h2all : IsPGroup 2 Tall := fun x => ⟨1, Subtype.ext (by
      show (x : X) ^ 2 ^ 1 = 1
      rw [pow_one]
      exact x.2)⟩
    have h2fix : IsPGroup 2 Tfix := fun x => ⟨1, Subtype.ext (by
      show (x : X) ^ 2 ^ 1 = 1
      rw [pow_one]
      exact x.2.1)⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := Tall)).1 h2all
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2) (G := Tfix)).1 h2fix
    have hTeq : Fintype.card T = 2 ^ m := by
      rw [← hm, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
    have hfixeq : σ.supportᶜ.card = 2 ^ j := by
      have h1 : σ.supportᶜ.card = Nat.card {t : T // σ t = t} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext t
        simp [Equiv.Perm.mem_support]
      rw [h1, ← hj]
      refine Nat.card_congr
        { toFun := fun t => ⟨(t.1 : T).1, ⟨(t.1 : T).2, congrArg Subtype.val t.2⟩⟩
          invFun := fun t => ⟨⟨t.1, t.2.1⟩, Subtype.ext t.2.2⟩
          left_inv := fun t => Subtype.ext (Subtype.ext rfl)
          right_inv := fun t => Subtype.ext rfl }
    have h16 : 2 ^ m ≤ 16 := hTeq ▸ hTcard
    have hm4 : m ≤ 4 := by
      by_contra h
      have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hsupp : σ.support.card = 2 ^ m - 2 ^ j := by omega
    have hj4 : j ≤ m := by
      have : 2 ^ j ≤ 2 ^ m := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have hjpos : 0 < σ.supportᶜ.card := by
      rw [hfixeq]
      positivity
    have hs15 : σ.support.card ≤ 15 := by omega
    have h0 : σ.support.card = 0 := by
      have hdvd := Nat.modEq_zero_iff_dvd.1 hmod
      rcases Nat.eq_zero_or_pos σ.support.card with h | h
      · exact h
      · exfalso
        have hpk : σ.support.card = p := by
          obtain ⟨k, hk⟩ := hdvd
          rcases k with _ | _ | k
          · omega
          · simpa using hk
          · nlinarith
        have hpp : p.Prime := Fact.out
        have hp15 : p ≤ 15 := by omega
        have hp1113 : p = 11 ∨ p = 13 := by
          interval_cases p <;> first | omega | (exfalso; norm_num at hpp)
        rcases hp1113 with rfl | rfl <;>
          interval_cases m <;> interval_cases j <;> simp at hsupp <;> omega
    have hσ1 : σ = 1 := Equiv.Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 h0)
    intro z hz
    have := congrArg (fun s : Equiv.Perm T => (s ⟨z, hz⟩ : X)) hσ1
    exact this
  have hpodd : Odd (p ^ n) := by
    have : Odd p := by
      rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
      · omega
      · exact h
    exact this.pow
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, pow_one] at hx
    subst hx
    exact map_one τ
  | succ k ih =>
    intro x hx
    have hy : (x ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
      exact hx
    have h1 : τ (x ^ 2) = x ^ 2 := ih _ hy
    set z := x⁻¹ * τ x with hz
    have hc : Commute x⁻¹ (τ x) := hcomm _ _
    have hz2 : z ^ 2 = 1 := by
      rw [hz, hc.mul_pow, ← map_pow, h1, inv_pow, inv_mul_cancel]
    have hτz : τ z = z := hfix2 z hz2
    have hτx : τ x = x * z := by rw [hz]; group
    have hiter : ∀ m : ℕ, (τ ^ m) x = x * z ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, hτx, map_pow, hτz, pow_succ', mul_assoc]
    have h2 : x = x * z ^ (p ^ n) := by
      have := hiter (p ^ n)
      rwa [hn, show (1 : MulAut X) x = x from rfl] at this
    have h3 : z ^ (p ^ n) = 1 := by
      have := congrArg (fun w => x⁻¹ * w) h2
      simpa using this.symm
    have h4 : z = 1 := by
      obtain ⟨j, hj⟩ := hpodd
      rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul] at h3
      exact h3
    rw [hτx, h4, mul_one]

theorem odd_card_commutator_of_toral16 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp10 : 10 < p) {S A Q : Subgroup G} (hA : IsPGroup p A) (hSp : ¬ p ∣ Nat.card S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQ2 : Nat.card {x : Q // x ^ 2 = 1} ≤ 16)
    (hodd : Odd (Q.relIndex (⁅S, A⁆ : Subgroup G))) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set U : Subgroup G := ⁅S, A⁆ with hU
  have hUS : U ≤ S := by
    rw [hU]
    refine Subgroup.commutator_le.2 fun s hs a ha => ?_
    have h1 : a * s⁻¹ * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hAS ha) s⁻¹).1 (inv_mem hs)
    have e : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hs h1
  have hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
    intro a ha u hu
    induction hu using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨s, hs, a', ha', rfl⟩ := hz
      have hs' : a * s * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hAS ha) s).1 hs
      have e : a * ⁅s, a'⁆ * a⁻¹ = ⁅a * s * a⁻¹, a * a' * a⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator hs' (mul_mem (mul_mem ha ha') (inv_mem ha))
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
      exact inv_mem hx
  have hUQ : ∀ u ∈ U, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := fun u hu q hq =>
    (Subgroup.mem_normalizer_iff.1 (hSQ (hUS hu)) q).1 hq
  have hidem : (⁅U, A⁆ : Subgroup G) = U :=
    CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent hp A S hA hSp
      hAS
  have hQ' : ∀ u ∈ U, ∀ k : ℕ, u ^ (2 ^ k) = 1 → u ∈ Q := by
    intro u hu k hk
    let N : Subgroup U := Q.subgroupOf U
    have hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hUQ g g.2 n hn⟩
    have hm : Odd N.index := hodd
    have h1 : ((⟨u, hu⟩ : U) ^ N.index : U) ∈ N := Subgroup.pow_index_mem N ⟨u, hu⟩
    have h2 : u ^ N.index ∈ Q := by
      have := Subgroup.mem_subgroupOf.1 h1
      simpa using this
    have hcop : IsCoprime ((N.index : ℕ) : ℤ) ((2 ^ k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm))
    obtain ⟨c, d, hcd⟩ := hcop
    have e2 : u ^ (c * ((N.index : ℕ) : ℤ) + d * ((2 ^ k : ℕ) : ℤ)) = (u ^ N.index) ^ c := by
      rw [zpow_add, mul_comm c, zpow_mul, mul_comm d, zpow_mul, zpow_natCast, zpow_natCast, hk,
        one_zpow, mul_one]
    have e : u = (u ^ N.index) ^ c := by
      rw [← e2, hcd, zpow_one]
    rw [e]
    exact zpow_mem h2 c
  have hAfix : ∀ a ∈ A, ∀ q ∈ Q, ∀ k : ℕ, q ^ (2 ^ k) = 1 → a * q * a⁻¹ = q := by
    intro a ha q hq k hk
    have hcomm : ∀ x y : Q, x * y = y * x := fun x y => Subtype.ext (hQab x x.2 y y.2)
    have hQ2' : Nat.card {x : Q // x ^ 2 = 1} ≤ 16 := hQ2
    have hAQ' : ∀ b ∈ A, ∀ x ∈ Q, b * x * b⁻¹ ∈ Q := fun b hb x hx =>
      (Subgroup.mem_normalizer_iff.1 (hAQ hb) x).1 hx
    let τ : MulAut Q :=
      { toFun := fun x => ⟨a * x * a⁻¹, hAQ' a ha x x.2⟩
        invFun := fun x => ⟨a⁻¹ * x * a, by
          simpa using hAQ' a⁻¹ (inv_mem ha) x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    have hτpow : ∀ (m : ℕ) (x : Q), ((τ ^ m) x : G) = a ^ m * x * (a ^ m)⁻¹ := by
      intro m x
      induction m generalizing x with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', MulAut.mul_apply]
        change a * ((τ ^ m) x : G) * a⁻¹ = _
        rw [ih, pow_succ']
        group
    obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
    have hn' : a ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hτ : τ ^ (p ^ n) = 1 := by
      ext x
      rw [hτpow, hn']
      simp
    have := fixes_two_power_of_card_le_sixteen hcomm hQ2' (p := p) hp10 hτ k ⟨q, hq⟩
      (Subtype.ext (by simpa using hk))
    exact congrArg Subtype.val this
  let Y : Subgroup G :=
    { carrier := {u | u ∈ U ∧ ∃ k : ℕ, u ^ (2 ^ k) = 1}
      mul_mem' := by
        rintro u v ⟨hu, i, hi⟩ ⟨hv, j, hj⟩
        refine ⟨mul_mem hu hv, i + j, ?_⟩
        have hc : Commute u v := hQab u (hQ' u hu i hi) v (hQ' v hv j hj)
        rw [hc.mul_pow, pow_add, pow_mul, hi, one_pow, one_mul, pow_mul', ← pow_mul', mul_comm,
          pow_mul, hj, one_pow]
      one_mem' := ⟨one_mem U, 0, by simp⟩
      inv_mem' := by
        rintro u ⟨hu, k, hk⟩
        exact ⟨inv_mem hu, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hYU : Y ≤ U := fun y hy => hy.1
  have hYQ : ∀ y ∈ Y, y ∈ Q := fun y hy => hQ' y hy.1 hy.2.choose hy.2.choose_spec
  have hYfix : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ = y := fun a ha y hy =>
    hAfix a ha y (hYQ y hy) hy.2.choose hy.2.choose_spec
  have hYnorm : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y := by
    rintro u hu y ⟨hy, k, hk⟩
    exact ⟨mul_mem (mul_mem hu hy) (inv_mem hu), k, by rw [conj_pow, hk]; group⟩
  have hYcent : ∀ u ∈ U, ∀ y ∈ Y, u * y = y * u := by
    have hle : (⁅U, A⁆ : Subgroup G) ≤ Subgroup.centralizer (Y : Set G) := by
      refine Subgroup.commutator_le.2 fun u hu a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hw : a * u * a⁻¹ ∈ U := hAU a ha u hu
      have hcw : ∀ y' ∈ Y, (a * u * a⁻¹) * y' * (a * u * a⁻¹)⁻¹ = u * y' * u⁻¹ := by
        intro y' hy'
        have h1 : a⁻¹ * y' * a = y' := by
          have := hYfix a⁻¹ (inv_mem ha) y' hy'
          simpa using this
        have h2 : u * y' * u⁻¹ ∈ Y := hYnorm u hu y' hy'
        calc (a * u * a⁻¹) * y' * (a * u * a⁻¹)⁻¹ = a * u * (a⁻¹ * y' * a) * u⁻¹ * a⁻¹ := by group
          _ = a * (u * y' * u⁻¹) * a⁻¹ := by rw [h1]; group
          _ = u * y' * u⁻¹ := hYfix a ha _ h2
      have e : ⁅u, a⁆ = u * (a * u * a⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      generalize a * u * a⁻¹ = w at hw hcw e
      have hy'' : w⁻¹ * y * w ∈ Y := by
        have := hYnorm w⁻¹ (inv_mem hw) y hy
        simpa using this
      have hc1 := hcw _ hy''
      have hlhs : w * (w⁻¹ * y * w) * w⁻¹ = y := by group
      rw [hlhs] at hc1
      have h3 : y * u = u * (w⁻¹ * y * w) := by
        calc y * u = (u * (w⁻¹ * y * w) * u⁻¹) * u := by rw [← hc1]
          _ = u * (w⁻¹ * y * w) := by group
      rw [e]
      calc y * (u * w⁻¹) = (y * u) * w⁻¹ := by group
        _ = (u * (w⁻¹ * y * w)) * w⁻¹ := by rw [h3]
        _ = (u * w⁻¹) * y := by group
    rw [hidem] at hle
    intro u hu y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hle hu) y hy)).symm
  have hYodd : Odd (Y.relIndex U) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 U) := inferInstance
    have hle : (P : Subgroup U) ≤ Y.subgroupOf U := by
      intro g hg
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨g.2, k, by simpa using congrArg Subtype.val (congrArg Subtype.val hk)⟩
    have h1 := Subgroup.index_dvd_of_le hle
    have h2 : ¬ 2 ∣ (P : Subgroup U).index := P.not_dvd_index
    have h3 : ¬ 2 ∣ (Y.subgroupOf U).index := fun h => h2 (h.trans h1)
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h3)
  have hYbot : Y = ⊥ :=
    central_two_part_eq_bot hYU hYcent hYfix hAU hidem hYodd (fun y hy => hy.2)
  by_contra hne
  have h2 : 2 ∣ Nat.card U := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu1 : ((u : U) : G) ∈ Y := by
    refine ⟨u.2, 1, ?_⟩
    have : (u : U) ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    simpa using congrArg Subtype.val this
  rw [hYbot] at hu1
  have : (u : U) = 1 := Subtype.ext (Subgroup.mem_bot.1 hu1)
  rw [this, orderOf_one] at hu
  omega

theorem inner_core_abelian_two_of_solvable16 {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hV : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
      ¬ p ∣ Nat.card V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 16) :
    (∀ q ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range,
      ∀ r ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range, q * r = r * q) ∧
    Nat.card {q : ↥(inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range) // q ^ 2 = 1} ≤ 16 := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    rw [hD] at hd
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hYSD : S.comap Int ≤ D := by
    intro y hy
    have hyM : Int y ∈ M := hSM hy
    rw [hM] at hyM
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyM).2 (Int x) rfl
    rw [hD]
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hinj (by rw [map_mul, map_mul]; exact h1.symm))
  have hVnormal : ((S.comap Int).subgroupOf D).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    change Int ((d : C) * (v : C) * (d : C)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnorm _ (hIntD d d.2) _ hv⟩
  let f : ((S.comap Int).subgroupOf D) →* S :=
    ((Int.comp D.subtype).comp ((S.comap Int).subgroupOf D).subtype).codRestrict S
      fun v => Subgroup.mem_subgroupOf.1 v.2
  have hfi : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab)))
  have hVsol : Group.IsSolvable ((S.comap Int).subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective (f := f) hfi
  have hSp : ¬ p ∣ Nat.card S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).2.2.1
    rw [hS, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact h
  have hVp : ¬ p ∣ Nat.card ((S.comap Int).subgroupOf D) :=
    fun h => hSp (h.trans (Subgroup.card_dvd_of_injective f hfi))
  have hV' : (∀ v ∈ (S.comap Int).subgroupOf D, ∀ w ∈ (S.comap Int).subgroupOf D, v * w = w * v) ∧
      Nat.card {v : ((S.comap Int).subgroupOf D) // v ^ 2 = 1} ≤ 16 := by
    rw [hD] at hVnormal hVsol hVp ⊢
    exact hV _ hVnormal hVsol hVp
  obtain ⟨hVab, hV4⟩ := hV'
  have hlift : ∀ q ∈ S ⊓ Int.range, ∃ v : (S.comap Int).subgroupOf D, Int (v : D) = q := by
    intro q hq
    obtain ⟨hqS, y, hy⟩ := Subgroup.mem_inf.1 hq
    have hyS : y ∈ S.comap Int := by
      rw [Subgroup.mem_comap, hy]
      exact hqS
    exact ⟨⟨⟨y, hYSD hyS⟩, Subgroup.mem_subgroupOf.2 hyS⟩, hy⟩
  refine ⟨fun q hq r hr => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hlift q hq
    obtain ⟨w, rfl⟩ := hlift r hr
    have := congrArg (fun z : D => (z : C)) (hVab (v : D) v.2 (w : D) w.2)
    simp only [Subgroup.coe_mul] at this
    rw [← map_mul, ← map_mul]
    exact congrArg Int this
  · choose g hg using fun q : ↥(S ⊓ Int.range) => hlift q.1 q.2
    let φ : ↥(S ⊓ Int.range) → ((S.comap Int).subgroupOf D) := g
    have hφinj : Function.Injective φ := fun a b hab => Subtype.ext (by
      rw [← hg a, ← hg b]
      exact congrArg (fun v : (S.comap Int).subgroupOf D => Int (v : D)) hab)
    let ψ : {q : ↥(S ⊓ Int.range) // q ^ 2 = 1} →
        {v : ((S.comap Int).subgroupOf D) // v ^ 2 = 1} := fun q => ⟨φ q.1, by
      have h1 : Int ((φ q.1 : D) : C) ^ 2 = 1 := by
        rw [hg q.1]
        have := congrArg Subtype.val q.2
        simpa using this
      have h2 : (((φ q.1 : D) : C)) ^ 2 = 1 := by
        apply hinj
        rw [map_pow, map_one]
        exact h1
      exact Subtype.ext (Subtype.ext h2)⟩
    have hψinj : Function.Injective ψ := fun a b hab =>
      Subtype.ext (hφinj (congrArg Subtype.val hab))
    exact (Nat.card_le_card_of_injective ψ hψinj).trans hV4


theorem native_plane16 {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hp10 : 10 < p) (hC : Subgroup.center C = ⊥)
    (hV : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → ¬ p ∣ Nat.card V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 16)
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range)
    (hI : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : C →* MulAut C).range → Odd (Nat.card ↥(autThetaT p B A))) :
    ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : C →* MulAut C).range →
            inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) = ⊥ ∧
              autPlaneProduct p B A t = ⊥) := by
  intro B hB A hAB hA hcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have htp : orderOf t = p := orderOf_eq_prime (hpow t htA) ht1
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
    obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
        B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
      ⟨_, rfl⟩
    have hAM : A ≤ M := by
      intro a ha
      rw [hM]
      refine Subgroup.mem_inf.2 ⟨hAB ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (mul_comm' (⟨_, htA⟩ : A) ⟨a, ha⟩)
    have hSM : S ≤ M := by
      rw [hS]
      exact Subgroup.map_subtype_le _
    have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
      intro m hm s hs
      rw [hS] at hs ⊢
      obtain ⟨s', hs', rfl⟩ := hs
      refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
      exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
    have hSnormalizer : ∀ m ∈ M, m ∈ Subgroup.normalizer (S : Set (MulAut C)) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro s
      refine ⟨fun hs => hSnorm m hm s hs, fun hs => ?_⟩
      have := hSnorm m⁻¹ (inv_mem hm) _ hs
      simpa [mul_assoc] using this
    have hSp : ¬ p ∣ Nat.card S := by
      have h := (solvable_prime_complement_core_characterization (H := M) hp).2.2.1
      rw [hS, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
      exact h
    obtain ⟨hQab, hQ2⟩ := inner_core_abelian_two_of_solvable16 (B := B) hp hC hB (hV x hxp)
    rw [← hM, ← hS] at hQab hQ2
    have hconj : ∀ m ∈ M, ∀ q ∈ S ⊓ (MulAut.conj : C →* MulAut C).range,
        m * q * m⁻¹ ∈ S ⊓ (MulAut.conj : C →* MulAut C).range := by
      intro m hm q hq
      obtain ⟨hqS, hqr⟩ := Subgroup.mem_inf.1 hq
      exact Subgroup.mem_inf.2 ⟨hSnorm m hm q hqS, (innerNormal C).conj_mem q hqr m⟩
    have hQnormalizer : ∀ m ∈ M, m ∈ Subgroup.normalizer
        ((S ⊓ (MulAut.conj : C →* MulAut C).range : Subgroup (MulAut C)) : Set (MulAut C)) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro q
      refine ⟨fun hq => hconj m hm q hq, fun hq => ?_⟩
      have := hconj m⁻¹ (inv_mem hm) _ hq
      simpa [mul_assoc] using this
    have hSA : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs => hSnorm a (hAM ha) s hs
    have hodd := odd_relIndex_inner_commutator hout hSA
    have hN : Odd (Nat.card ↥(⁅S, A⁆ : Subgroup (MulAut C))) :=
      odd_card_commutator_of_toral16 hp hp10 (IsPGroup.of_card hcard) hSp
        (fun a ha => hSnormalizer a (hAM ha)) (fun s hs => hQnormalizer s (hSM hs))
        (fun a ha => hQnormalizer a (hAM ha)) hQab hQ2 hodd
    have hIS : autThetaT p B A ≤ S := by
      have := hthetaT_le (MulAut.conj x) htA ht1
      rwa [← hM, ← hS] at this
    have hI' : Odd (Nat.card ↥(autThetaT p B A)) := by
      by_cases hnon : ∃ b ∈ A, b ∉ (MulAut.conj : C →* MulAut C).range
      · obtain ⟨b, hbA, hbn⟩ := hnon
        have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
        have hbp : orderOf b = p := orderOf_eq_prime (hpow b hbA) hb1
        have hθb := hcore B hB b (hAB hbA) hbn hbp
        have hle := hthetaT_le b hbA hb1
        rw [hθb] at hle
        have hbot : autThetaT p B A = ⊥ := le_bot_iff.1 hle
        rw [hbot, Subgroup.card_bot]
        exact odd_one
      · push Not at hnon
        exact hI B hB A hAB hA hcard hnon
    have hplane : autPlaneProduct p B A (MulAut.conj x) = ⁅S, A⁆ ⊔ autThetaT p B A := by
      rw [autPlaneProduct, ← hM, ← hS]
    have hodd' := odd_card_sup_of_odd ((hIS.trans (le_normalizer_commutator_left S A))) hN hI'
    rw [hplane]
    exact ⟨hodd'.not_two_dvd_nat, fun h => absurd ⟨x, rfl⟩ h⟩
  · have hθt := hcore B hB t (hAB htA) htn htp
    have hT : autThetaT p B A = ⊥ :=
      le_bot_iff.1 ((hthetaT_le t htA ht1).trans hθt.le)
    have hplane : autPlaneProduct p B A t = ⊥ := by
      rw [autPlaneProduct, hθt, Subgroup.commutator_bot_left, hT, sup_bot_eq]
    refine ⟨?_, fun _ => ⟨hθt, hplane⟩⟩
    rw [hplane, Subgroup.card_bot]
    omega

theorem planeLocalCoreOdd16 {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hp10 : 10 < p) (hC : Subgroup.center C = ⊥)
    (hV : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → ¬ p ∣ Nat.card V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 16)
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range)
    (hI : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : C →* MulAut C).range → Odd (Nat.card ↥(autThetaT p B A))) :
    PlaneLocalCoreOdd p C := fun B hB A hAB hA hcard t htA ht1 =>
  (native_plane16 hp hp10 hC hV hout hcore hI B hB A hAB hA hcard t
    htA ht1).1

end CFSG.RankThree.PartOne.KE8F
