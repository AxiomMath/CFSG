module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C1
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.N588

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_comm {x y c : G} (hc : y * x = c * x * y) (hcy : c * y = y * c) (n : ℕ) :
    y ^ n * x = c ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcy' : y * c ^ n = c ^ n * y := ((Commute.pow_left hcy n).eq).symm
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (c ^ n * x * y ^ n) := by rw [ih]
      _ = (y * c ^ n) * x * y ^ n := by group
      _ = c ^ n * (y * x) * y ^ n := by rw [hcy']; group
      _ = c ^ n * (c * x * y) * y ^ n := by rw [hc]
      _ = c ^ (n + 1) * x * y ^ (n + 1) := by rw [pow_succ, pow_succ']; group

theorem mul_pow_eq_of_comm {x y c : G} (hc : y * x = c * x * y) (hcx : c * x = x * c)
    (hcy : c * y = y * c) (n : ℕ) :
    (x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcx' : x ^ n * c ^ n = c ^ n * x ^ n := ((Commute.pow_pow hcx n n).eq).symm
    have hch : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = c ^ (n.choose 2) * x ^ n * (y ^ n * x) * y := by rw [ih]; group
      _ = c ^ (n.choose 2) * (x ^ n * c ^ n) * x * y ^ n * y := by
          rw [pow_mul_eq_of_comm hc hcy n]; group
      _ = c ^ (n.choose 2) * (c ^ n * x ^ n) * x * y ^ n * y := by rw [hcx']
      _ = c ^ ((n + 1).choose 2) * x ^ (n + 1) * y ^ (n + 1) := by
          rw [hch, pow_add, pow_succ, pow_succ]; group

theorem mul_pow_prime_eq {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x y c : G} (hc : y * x = c * x * y)
    (hcx : c * x = x * c) (hcy : c * y = y * c) (hcq : c ^ q = 1) :
    (x * y) ^ q = x ^ q * y ^ q := by
  have h2 : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm hq2)
  obtain ⟨k, hk⟩ := hq.dvd_choose_self (k := 2) (by norm_num) h2
  rw [mul_pow_eq_of_comm hc hcx hcy, hk, pow_mul, hcq, one_pow, one_mul]

theorem conj_eq_of_coprime [Finite G] {q : ℕ} {ℓ x : G}
    (hω : ℓ * (x⁻¹ * (ℓ * x * ℓ⁻¹)) * ℓ⁻¹ = x⁻¹ * (ℓ * x * ℓ⁻¹))
    (hωq : (x⁻¹ * (ℓ * x * ℓ⁻¹)) ^ q = 1) (hcop : Nat.Coprime (orderOf ℓ) q) :
    ℓ * x * ℓ⁻¹ = x := by
  set ω := x⁻¹ * (ℓ * x * ℓ⁻¹) with hωdef
  have hlx : ℓ * x = x * ω * ℓ := by rw [hωdef]; group
  have hωl : ℓ * ω = ω * ℓ := by
    calc ℓ * ω = (ℓ * ω * ℓ⁻¹) * ℓ := by group
      _ = ω * ℓ := by rw [hω]
  have key : ∀ n : ℕ, ℓ ^ n * x = x * ω ^ n * ℓ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hωl' : ℓ * ω ^ n = ω ^ n * ℓ := (Commute.pow_right hωl n).eq
      calc ℓ ^ (n + 1) * x = ℓ * (ℓ ^ n * x) := by rw [pow_succ', mul_assoc]
        _ = ℓ * (x * ω ^ n * ℓ ^ n) := by rw [ih]
        _ = (ℓ * x) * ω ^ n * ℓ ^ n := by group
        _ = x * ω * (ℓ * ω ^ n) * ℓ ^ n := by rw [hlx]; group
        _ = x * ω * (ω ^ n * ℓ) * ℓ ^ n := by rw [hωl']
        _ = x * ω ^ (n + 1) * ℓ ^ (n + 1) := by rw [pow_succ', pow_succ']; group
  have h1 := key (orderOf ℓ)
  rw [pow_orderOf_eq_one, one_mul, mul_one] at h1
  have h2 : ω ^ orderOf ℓ = 1 := by
    have := congrArg (fun t => x⁻¹ * t) h1
    simpa using this.symm
  have h3 : orderOf ω ∣ Nat.gcd (orderOf ℓ) q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hωq)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have : x⁻¹ * (ℓ * x * ℓ⁻¹) = 1 := h3
  calc ℓ * x * ℓ⁻¹ = x * (x⁻¹ * (ℓ * x * ℓ⁻¹)) := by group
    _ = x := by rw [this, mul_one]


variable [Finite G]

theorem exists_index_prime_le {q : ℕ} [hq : Fact q.Prime] {P : Subgroup G} (hP : IsPGroup q P)
    (hP1 : P ≠ ⊥) : ∃ N₀ : Subgroup G, N₀ ≤ P ∧ N₀ ≠ P ∧ (∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ N₀) ∧
      ∀ x ∈ P, x ^ q ∈ N₀ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hP1 (Subgroup.card_eq_one.1 hn)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime q (G := ↥P) (n := n - 1)
    (by rw [hn]; exact pow_dvd_pow q (Nat.sub_le n 1))
  have hidx : K.index = q := by
    have h := K.card_mul_index
    rw [hK, hn] at h
    have h2 : q ^ n = q ^ (n - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)]
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.out.pos _) h
  have hKn : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, hn, Nat.pow_minFac hn0, hq.out.minFac_eq])
  have hQ : Nat.card (↥P ⧸ K) = q := by rw [← Subgroup.index_eq_card, hidx]
  haveI : IsCyclic (↥P ⧸ K) := isCyclic_of_prime_card hQ
  letI : CommGroup (↥P ⧸ K) := IsCyclic.commGroup
  refine ⟨K.map P.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · intro h
    have h1 : Nat.card (K.map P.subtype) = Nat.card P := by rw [h]
    rw [Subgroup.card_map_of_injective P.subtype_injective, hK, hn] at h1
    have := Nat.pow_right_injective hq.out.two_le h1
    omega
  · intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆, ?_, rfl⟩
    have h1 : ((⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ : ↥P) : ↥P ⧸ K) = 1 := by
      rw [show ((⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ : ↥P) : ↥P ⧸ K) =
        QuotientGroup.mk' K ⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ from rfl, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  · intro x hx
    refine ⟨(⟨x, hx⟩ : ↥P) ^ q, ?_, rfl⟩
    have h1 : (((⟨x, hx⟩ : ↥P) ^ q : ↥P) : ↥P ⧸ K) = 1 := by
      rw [QuotientGroup.mk_pow, ← hQ, pow_card_eq_one']
    exact (QuotientGroup.eq_one_iff _).1 h1

@[expose] def fratOf (q : ℕ) (P : Subgroup G) : Subgroup G :=
  ⁅P, P⁆ ⊔ closure ((fun x => x ^ q) '' (P : Set G))

theorem commutator_mem_fratOf {q : ℕ} {P : Subgroup G} {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    ⁅x, y⁆ ∈ fratOf q P :=
  mem_sup_left (commutator_mem_commutator hx hy)

theorem pow_mem_fratOf {q : ℕ} {P : Subgroup G} {x : G} (hx : x ∈ P) : x ^ q ∈ fratOf q P :=
  mem_sup_right (subset_closure ⟨x, hx, rfl⟩)

theorem fratOf_le {q : ℕ} {P N : Subgroup G} (hc : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ N)
    (hp : ∀ x ∈ P, x ^ q ∈ N) : fratOf q P ≤ N := by
  refine sup_le (Subgroup.commutator_le.2 hc) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact hp x hx

theorem fratOf_le_self (q : ℕ) (P : Subgroup G) : fratOf q P ≤ P :=
  fratOf_le (fun _ hx _ hy => P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx))
    (P.inv_mem hy)) fun _ hx => P.pow_mem hx q

theorem mem_normalizer_fratOf {q : ℕ} {P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (P : Set G)) : g ∈ normalizer ((fratOf q P : Subgroup G) : Set G) := by
  have hP : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx => (mem_normalizer_iff.1 hg x).1 hx
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hle : fratOf q P ≤ (fratOf q P).comap (MulAut.conj g).toMonoidHom := by
    refine fratOf_le (fun x hx z hz => ?_) fun x hx => ?_
    · show (MulAut.conj g) ⁅x, z⁆ ∈ fratOf q P
      rw [map_commutatorElement]
      exact commutator_mem_fratOf (hP x hx) (hP z hz)
    · show (MulAut.conj g) (x ^ q) ∈ fratOf q P
      rw [map_pow]
      exact pow_mem_fratOf (hP x hx)
  exact hle hy


theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

theorem commutator_le_of_le_normalizer {P L : Subgroup G} (hLP : L ≤ normalizer (P : Set G)) :
    ⁅P, L⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro p hp ℓ hℓ
  have h1 : ℓ * p⁻¹ * ℓ⁻¹ ∈ P := (mem_normalizer_iff.1 (hLP hℓ) _).1 (P.inv_mem hp)
  rw [commutatorElement_def, show p * ℓ * p⁻¹ * ℓ⁻¹ = p * (ℓ * p⁻¹ * ℓ⁻¹) by group]
  exact P.mul_mem hp h1

theorem commutator_eq_bot_of_perfect {P L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : ⁅⁅P, L⁆, L⁆ = ⊥) : ⁅P, L⁆ = ⊥ := by
  have h2 : ⁅⁅L, P⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L P]; exact h
  have h3 : ⁅⁅L, L⁆, P⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h
  rw [hL, Subgroup.commutator_comm] at h3
  exact h3

theorem mul_pow_of_fratOf_central {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {P : Subgroup G}
    (hΦc : ∀ a ∈ fratOf q P, ∀ x ∈ P, a * x = x * a) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    (x * y) ^ q = x ^ q * y ^ q := by
  set c := ⁅y, x⁆ with hcdef
  have hcΦ : c ∈ fratOf q P := commutator_mem_fratOf hy hx
  have hc : y * x = c * x * y := by rw [hcdef, commutatorElement_def]; group
  have hcx : c * x = x * c := hΦc c hcΦ x hx
  have hcy : c * y = y * c := hΦc c hcΦ y hy
  have hcq : c ^ q = 1 := by
    have h1 := pow_mul_eq_of_comm hc hcy q
    have h2 : y ^ q * x = x * y ^ q := hΦc _ (pow_mem_fratOf hy) x hx
    rw [h2] at h1
    have h3 : x = c ^ q * x := mul_right_cancel h1
    have h4 := congrArg (fun t => t * x⁻¹) h3
    simpa using h4.symm
  exact mul_pow_prime_eq hq hq2 hc hcx hcy hcq

@[expose] def omegaOf (q : ℕ) (P : Subgroup G) : Subgroup G :=
  closure {x | x ∈ P ∧ x ^ q = 1}

theorem omegaOf_le (q : ℕ) (P : Subgroup G) : omegaOf q P ≤ P :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem pow_eq_one_of_mem_omegaOf {q : ℕ} {P : Subgroup G}
    (hpow : ∀ x ∈ P, ∀ y ∈ P, (x * y) ^ q = x ^ q * y ^ q) {y : G} (hy : y ∈ omegaOf q P) :
    y ^ q = 1 := by
  have key : y ∈ P ∧ y ^ q = 1 := by
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨P.one_mem, one_pow q⟩
    | mul a b _ _ ha hb => exact ⟨P.mul_mem ha.1 hb.1, by rw [hpow a ha.1 b hb.1, ha.2, hb.2,
        one_mul]⟩
    | inv a _ ha => exact ⟨P.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩
  exact key.2

theorem mem_normalizer_omegaOf {q : ℕ} {P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (P : Set G)) : g ∈ normalizer ((omegaOf q P : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hle : omegaOf q P ≤ (omegaOf q P).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    refine subset_closure ⟨(mem_normalizer_iff.1 hg x).1 hx.1, ?_⟩
    show (g * x * g⁻¹) ^ q = 1
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  exact hle hy


theorem card_le_pow_six {q : ℕ} [hq : Fact q.Prime] {P : Subgroup G} (hP : IsPGroup q P)
    (hexp : ∀ x ∈ P, x ^ q = 1) (hcl : ∀ a ∈ ⁅P, P⁆, ∀ x ∈ P, a * x = x * a)
    (hrank : CFSG.Open.pRank q P ≤ 3) : Nat.card P ≤ q ^ 6 := by
  classical
  set Z : Subgroup G := P ⊓ centralizer (P : Set G) with hZ
  let S : Set (Subgroup G) := {B | Z ≤ B ∧ B ≤ P ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a}
  have hZS : Z ∈ S :=
    ⟨le_rfl, inf_le_left, fun a ha b hb => (mem_centralizer_iff.1 hb.2 a ha.1)⟩
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : Nonempty S := ⟨⟨Z, hZS⟩⟩
  obtain ⟨⟨A, hAS⟩, hAmax⟩ := Finite.exists_max (fun B : S => Nat.card (B : Subgroup G))
  obtain ⟨hZA, hAP, hAc⟩ := hAS
  have hself : ∀ x ∈ P, (∀ a ∈ A, a * x = x * a) → x ∈ A := by
    intro x hx hxA
    have hx' : x ∈ centralizer (A : Set G) := mem_centralizer_iff.2 hxA
    have hAcen : A ≤ centralizer (A : Set G) := fun a ha =>
      mem_centralizer_iff.2 fun b hb => hAc b hb a ha
    have hxx : x ∈ centralizer ((zpowers x : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (Commute.refl x) k).eq
    have h1 : A ⊔ zpowers x ≤ centralizer (A : Set G) := sup_le hAcen ((zpowers_le).2 hx')
    have h2 : A ⊔ zpowers x ≤ centralizer ((zpowers x : Subgroup G) : Set G) :=
      sup_le (Subgroup.le_centralizer_iff.1 ((zpowers_le).2 hx')) ((zpowers_le).2 hxx)
    have hBc : A ⊔ zpowers x ≤ centralizer ((A ⊔ zpowers x : Subgroup G) : Set G) :=
      sup_le (Subgroup.le_centralizer_iff.1 h1) (Subgroup.le_centralizer_iff.1 h2)
    have hBS : A ⊔ zpowers x ∈ S :=
      ⟨hZA.trans le_sup_left, sup_le hAP ((zpowers_le).2 hx), fun a ha b hb =>
        mem_centralizer_iff.1 (hBc hb) a ha⟩
    have hcard := hAmax ⟨A ⊔ zpowers x, hBS⟩
    have hAB : A = A ⊔ zpowers x := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    rw [hAB]
    exact mem_sup_right (mem_zpowers x)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (hP.to_le hAP)
  have hael : CFSG.Open.IsElemAbelian q A :=
    ⟨⟨⟨fun x y => Subtype.ext (hAc x x.2 y y.2)⟩⟩, fun x hx => hexp x (hAP hx)⟩
  have ha3 : a ≤ 3 :=
    (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove q hq.out P)
      ⟨A, hAP, hael, ha⟩).trans hrank
  have hPN : P ≤ normalizer (A : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hc : ⁅x, y⁆ ∈ ⁅P, P⁆ := commutator_mem_commutator hx (hAP hy)
    have hcA : ⁅x, y⁆ ∈ A := hZA ⟨Subgroup.commutator_le_self P hc,
      mem_centralizer_iff.2 fun z hz => (hcl _ hc z hz).symm⟩
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem hcA hy
  let φ : ↥P →* MulAut ↥A := A.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have hker : φ.ker ≤ A.subgroupOf P := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [mem_subgroupOf]
    refine hself x x.2 fun b hb => ?_
    have h1 := congrArg (fun e : MulAut ↥A => ((e ⟨b, hb⟩ : ↥A) : G)) hx
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulAut.one_apply] at h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    have h2 : (x : G) * b * (x : G)⁻¹ = b := h1
    calc b * (x : G) = ((x : G) * b * (x : G)⁻¹) * (x : G) := by rw [h2]
      _ = (x : G) * b := by group
  have hcardP : Nat.card ↥P = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hkerc : Nat.card φ.ker ≤ q ^ a := by
    calc Nat.card φ.ker ≤ Nat.card (A.subgroupOf P) := Subgroup.card_le_of_le hker
      _ = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
      _ = q ^ a := ha
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hrd : Nat.card φ.range ∣ q ^ n := hn ▸ Dvd.intro_left _ hcardP.symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq.out).1 hrd
  have hAcomm : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (hAc x x.2 y y.2)
  have hAexp : ∀ x : ↥A, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp x (hAP x.2))
  have hGL : q ^ k ∣ Nat.card (GL (Fin a) (ZMod q)) := by
    rw [← hk]
    exact (Subgroup.card_subgroup_dvd_card φ.range).trans
      (card_mulAut_dvd_card_GL hAcomm hAexp ha)
  have hk3 := le_three_of_pow_dvd_card_GL ha3 hGL
  calc Nat.card P = Nat.card φ.ker * Nat.card φ.range := hcardP
    _ ≤ q ^ a * q ^ k := Nat.mul_le_mul hkerc hk.le
    _ ≤ q ^ 3 * q ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_right hq.out.pos ha3)
        (Nat.pow_le_pow_right hq.out.pos hk3)
    _ = q ^ 6 := by ring


theorem mem_commutator_of_forall_GL {q : ℕ} [hq : Fact q.Prime] {L P : Subgroup G}
    (hLP : L ≤ normalizer (P : Set G)) (hP : IsPGroup q P) (hexp : ∀ x ∈ P, x ^ q = 1)
    (hcard : Nat.card P ≤ q ^ 6) (hGL : ∀ d ≤ 6, ∀ f : ↥L →* GL (Fin d) (ZMod q), f = 1) :
    ∀ ℓ ∈ L, ∀ x ∈ P, x⁻¹ * (ℓ * x * ℓ⁻¹) ∈ ⁅P, P⁆ := by
  classical
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hVd : Nat.card (↥P ⧸ commutator ↥P) ∣ q ^ n :=
    hn ▸ Subgroup.card_quotient_dvd_card _
  obtain ⟨d, hdn, hd⟩ := (Nat.dvd_prime_pow hq.out).1 hVd
  have hd6 : d ≤ 6 := by
    have h1 : q ^ d ≤ q ^ 6 :=
      calc q ^ d ≤ q ^ n := Nat.pow_le_pow_right hq.out.pos hdn
        _ = Nat.card P := hn.symm
        _ ≤ q ^ 6 := hcard
    exact (Nat.pow_le_pow_iff_right hq.out.one_lt).1 h1
  have hcomm : ∀ u v : ↥P ⧸ commutator ↥P, u * v = v * u := by
    intro u v
    induction u using QuotientGroup.induction_on with | H u =>
    induction v using QuotientGroup.induction_on with | H v =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : (u * v)⁻¹ * (v * u) = ⁅v⁻¹, u⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [e, commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hexpV : ∀ u : ↥P ⧸ commutator ↥P, u ^ q = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with | H u =>
    rw [← QuotientGroup.mk_pow]
    have h1 : u ^ q = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp u u.2)
    rw [h1, QuotientGroup.mk_one]
  obtain ⟨f, hf⟩ := exists_mulAut_injective_GL
    hcomm hexpV hd
  let ψ : ↥L →* MulAut (↥P ⧸ commutator ↥P) :=
    (autQuot (commutator ↥P)).comp
      (P.normalizerMonoidHom.comp (Subgroup.inclusion hLP))
  have h1 := hGL d hd6 (f.comp ψ)
  intro ℓ hℓ x hx
  have h2 : ψ ⟨ℓ, hℓ⟩ = 1 := hf (by
    have := congrArg (fun φ : ↥L →* GL (Fin d) (ZMod q) => φ ⟨ℓ, hℓ⟩) h1
    simpa using this)
  have h3 := congrArg
    (fun e : MulAut (↥P ⧸ commutator ↥P) => e ((⟨x, hx⟩ : ↥P) : ↥P ⧸ commutator ↥P)) h2
  simp only [ψ, MonoidHom.coe_comp, Function.comp_apply,
    autQuot_mk, MulAut.one_apply] at h3
  rw [QuotientGroup.eq] at h3
  have h4 := Subgroup.mem_map_of_mem P.subtype h3
  rw [Subgroup.map_subtype_commutator] at h4
  have h5 : ((P.normalizerMonoidHom (Subgroup.inclusion hLP ⟨ℓ, hℓ⟩) ⟨x, hx⟩ : ↥P) : G) =
      ℓ * x * ℓ⁻¹ := by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have h6 : P.subtype ((P.normalizerMonoidHom (Subgroup.inclusion hLP ⟨ℓ, hℓ⟩) ⟨x, hx⟩)⁻¹ *
      ⟨x, hx⟩) = (ℓ * x * ℓ⁻¹)⁻¹ * x := by
    rw [map_mul, map_inv, Subgroup.coe_subtype, h5]
  rw [h6] at h4
  have h7 := Subgroup.inv_mem _ h4
  simpa [mul_assoc] using h7

theorem commutator_eq_bot_of_pRank_le_three {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    {L : Subgroup G} (hLperf : ⁅L, L⁆ = L)
    (hLgen : ∀ T : Subgroup G, (∀ ℓ ∈ L, Nat.Coprime (orderOf ℓ) q → ℓ ∈ T) → L ≤ T)
    (hGL : ∀ d ≤ 6, ∀ f : ↥L →* GL (Fin d) (ZMod q), f = 1) :
    ∀ P : Subgroup G, IsPGroup q P → CFSG.Open.pRank q P ≤ 3 →
      L ≤ normalizer (P : Set G) → ⁅P, L⁆ = ⊥ := by
  intro P
  induction hn : Nat.card P using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  intro hP hrank hLP
  have IH : ∀ Q : Subgroup G, Q < P → L ≤ normalizer (Q : Set G) → ⁅Q, L⁆ = ⊥ :=
    fun Q hQP hLQ => ih (Nat.card Q) (hn ▸ Subgroup.card_lt_of_lt hQP) Q rfl (hP.to_le hQP.le)
      ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq.out hQP.le).trans hrank) hLQ
  have hcrit : (∀ ℓ ∈ L, Nat.Coprime (orderOf ℓ) q → ∀ x ∈ P, ℓ * x * ℓ⁻¹ = x) →
      ⁅P, L⁆ = ⊥ := by
    intro h
    have hL : L ≤ centralizer (P : Set G) := hLgen _ fun ℓ hℓ hc =>
      mem_centralizer_iff.2 fun x hx => by
        have e := h ℓ hℓ hc x hx
        calc x * ℓ = (ℓ * x * ℓ⁻¹) * ℓ := by rw [e]
          _ = ℓ * x := by group
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.1 hL)
  by_contra hne
  have hPL : ⁅P, L⁆ = P := by
    by_contra h1
    have hlt : ⁅P, L⁆ < P := lt_of_le_of_ne (commutator_le_of_le_normalizer hLP) h1
    have hLN : L ≤ normalizer ((⁅P, L⁆ : Subgroup G) : Set G) := fun ℓ hℓ =>
      mem_normalizer_commutator (hLP hℓ) (Subgroup.le_normalizer hℓ)
    exact hne (commutator_eq_bot_of_perfect hLperf (IH _ hlt hLN))
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    exact hne (Subgroup.commutator_bot_left L)
  obtain ⟨N₀, hN₀P, hN₀ne, hN₀c, hN₀p⟩ := exists_index_prime_le hP hP1
  have hΦlt : fratOf q P < P := lt_of_le_of_lt (fratOf_le hN₀c hN₀p) (lt_of_le_of_ne hN₀P hN₀ne)
  have hΦL : ⁅fratOf q P, L⁆ = ⊥ := IH _ hΦlt fun ℓ hℓ => mem_normalizer_fratOf (hLP hℓ)
  have hΦP : ⁅fratOf q P, P⁆ = ⊥ := by
    have h1 : ⁅⁅L, fratOf q P⁆, P⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L, hΦL, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅fratOf q P, P⁆, L⁆ = ⊥ := by
      have hle : ⁅fratOf q P, P⁆ ≤ fratOf q P :=
        (Subgroup.commutator_mono (fratOf_le_self q P) le_rfl).trans le_sup_left
      exact eq_bot_iff.2 ((Subgroup.commutator_mono hle le_rfl).trans hΦL.le)
    have h3 : ⁅⁅P, L⁆, fratOf q P⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hPL, Subgroup.commutator_comm] at h3
    exact h3
  have hΦc : ∀ a ∈ fratOf q P, ∀ x ∈ P, a * x = x * a := fun a ha x hx =>
    (mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hΦP ha) x hx).symm
  have hΦl : ∀ ℓ ∈ L, ∀ a ∈ fratOf q P, ℓ * a * ℓ⁻¹ = a := fun ℓ hℓ a ha => by
    have e := mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hΦL ha) ℓ hℓ
    rw [e]; group
  have hpow : ∀ x ∈ P, ∀ y ∈ P, (x * y) ^ q = x ^ q * y ^ q := fun x hx y hy =>
    mul_pow_of_fratOf_central hq.out hq2 hΦc hx hy
  have hexp : ∀ x ∈ P, x ^ q = 1 := by
    by_cases hΩ : omegaOf q P = P
    · intro x hx
      exact pow_eq_one_of_mem_omegaOf hpow (hΩ.symm ▸ hx)
    · exfalso
      have hΩlt : omegaOf q P < P := lt_of_le_of_ne (omegaOf_le q P) hΩ
      have hΩL : ⁅omegaOf q P, L⁆ = ⊥ := IH _ hΩlt fun ℓ hℓ => mem_normalizer_omegaOf (hLP hℓ)
      refine hne (hcrit fun ℓ hℓ hc x hx => ?_)
      have hlx : ℓ * x * ℓ⁻¹ ∈ P := (mem_normalizer_iff.1 (hLP hℓ) x).1 hx
      have hωq : (x⁻¹ * (ℓ * x * ℓ⁻¹)) ^ q = 1 := by
        rw [hpow _ (P.inv_mem hx) _ hlx, inv_pow, conj_pow, hΦl ℓ hℓ _ (pow_mem_fratOf hx),
          inv_mul_cancel]
      have hωΩ : x⁻¹ * (ℓ * x * ℓ⁻¹) ∈ omegaOf q P :=
        subset_closure ⟨P.mul_mem (P.inv_mem hx) hlx, hωq⟩
      have hfix := mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hΩL hωΩ)
        ℓ hℓ
      refine conj_eq_of_coprime ?_ hωq hc
      rw [hfix]; group
  have hcl : ∀ a ∈ ⁅P, P⁆, ∀ x ∈ P, a * x = x * a := fun a ha x hx => hΦc a (mem_sup_left ha) x hx
  have hcard := card_le_pow_six hP hexp hcl hrank
  have hact := mem_commutator_of_forall_GL hLP hP hexp hcard hGL
  refine hne (hcrit fun ℓ hℓ hc x hx => ?_)
  have hlx : ℓ * x * ℓ⁻¹ ∈ P := (mem_normalizer_iff.1 (hLP hℓ) x).1 hx
  have hω := hact ℓ hℓ x hx
  refine conj_eq_of_coprime (hΦl ℓ hℓ _ (mem_sup_left hω)) ?_ hc
  exact hexp _ (P.mul_mem (P.inv_mem hx) hlx)

end CFSG.LocalAnalysis.UniquenessCase.UC6.N588
