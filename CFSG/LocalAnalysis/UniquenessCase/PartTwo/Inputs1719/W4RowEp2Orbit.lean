module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowEp2Count

import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup.X1

@[expose] def ep2Line {G : Type*} [Monoid G] (a b : G) : ℕ → G
  | 0 => b
  | i + 1 => a * b ^ i

variable {W : Type} [CommGroup W] [Finite W] {p : ℕ} [Fact p.Prime] {a b : MulAut W}

private theorem ep2Line_zpowers_le_sup {G : Type*} [Group G] {a b : G} (i : ℕ) :
    Subgroup.zpowers (ep2Line a b i) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Subgroup.zpowers_le]
  cases i with
  | zero => exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  | succ n =>
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) n)

private theorem ep2Line_zpowers_injOn {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {a b : G} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j) :
    ∀ i ≤ p, ∀ j ≤ p, Subgroup.zpowers (ep2Line a b i) =
      Subgroup.zpowers (ep2Line a b j) → i = j := by
  intro i hi j hj hij
  rcases i with _ | n <;> rcases j with _ | m
  · rfl
  · exfalso
    exact zpowers_ne_zpowers_mul_pow ha hb ha1 hab hba m (by simpa [ep2Line] using hij)
  · exfalso
    exact zpowers_ne_zpowers_mul_pow ha hb ha1 hab hba n (by simpa [ep2Line] using hij.symm)
  · have hn : n < p := by omega
    have hm : m < p := by omega
    have h := by simpa [ep2Line] using hij
    have hnm := eq_of_zpowers_mul_pow_eq (i := n) (j := m) ha hb ha1 hab hba hn hm h
    omega

private theorem ep2_setup {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : MulAut W} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < p, b ≠ a ^ j)
    {A : Subgroup (MulAut W)} (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    Nat.card ↥A = p ^ 2 ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ x ∈ A, x ^ p = 1) ∧
      fixV A ⊓ (normHom A).ker = ⊥ ∧
      Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W ∧
      (∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker) ∧
      orderOf b = p := by
  have hao : orderOf a = p := orderOf_eq_prime ha ha1
  have hbo : orderOf b = p := orderOf_eq_prime hb (by
    have := hba 0 (Fact.out : p.Prime).pos
    simpa using this)
  have hcarda : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hao]
  have hcommXA : ∀ x ∈ Subgroup.zpowers a, x * b = b * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left hab n).eq
  obtain ⟨hAea, hAsupcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := p)
      (X := Subgroup.zpowers a) (v := b) hcarda hbo
      (not_mem_zpowers_of_forall_ne_pow_lt (Fact.out : p.Prime).pos ha hba) hcommXA
  have hAcard : Nat.card ↥A = p ^ 2 := by simpa [hA] using hAsupcard
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    rw [hA] at hx hy
    exact congrArg Subtype.val (hAea.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : ∀ x ∈ A, x ^ p = 1 := by
    intro x hx
    rw [hA] at hx
    exact hAea.2 x hx
  have hodd : Odd (Nat.card ↥A) := by
    rw [hAcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact ⟨hAcard, hAc, hAp, fixV_inf_ker_normHom hW hodd,
    card_ker_normHom_mul hW hodd,
    fun x hx k hk => map_ker_normHom (Subgroup.le_normalizer hx) hk, hbo⟩

private theorem ep2_card_ker_eq_prod {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : MulAut W} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < p, b ≠ a ^ j)
    {A : Subgroup (MulAut W)} (hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hfix : fixV A ⊓ (normHom A).ker = ⊥) :
    Nat.card ↥(normHom A).ker =
      ∏ i ∈ Finset.range (p + 1),
        Nat.card ↥(fixV (Subgroup.zpowers (ep2Line a b i)) ⊓ (normHom A).ker) := by
  classical
  obtain ⟨hAcard, hAc, hAp, -, -, hKinv, hbo⟩ :=
    ep2_setup hW hp2 ha hb ha1 hab hba hA
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    insert (Subgroup.zpowers b) ((Finset.range p).image fun i =>
      Subgroup.zpowers (a * b ^ i))
  have h𝒟def : 𝒟 = insert (Subgroup.zpowers b) ((Finset.range p).image fun i =>
      Subgroup.zpowers (a * b ^ i)) := rfl
  obtain ⟨h𝒟, hcard𝒟⟩ := ep2_lines_mem_iff hA ha hb ha1 hab hba hbo hAcard 𝒟 h𝒟def
  let D : ℕ → Subgroup (MulAut W) := fun i => Subgroup.zpowers (ep2Line a b i)
  have hDmem : ∀ i ≤ p, D i ∈ 𝒟 := by
    intro i _
    cases i with
    | zero => exact Finset.mem_insert_self _ _
    | succ n =>
        refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨n, ?_, ?_⟩)
        · exact Finset.mem_range.2 (by omega)
        · rfl
  have hsub : (Finset.range (p + 1)).image D ⊆ 𝒟 := by
    intro E hE
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hE
    exact hDmem i (Nat.lt_succ_iff.1 (Finset.mem_range.1 (by simpa using hi)))
  have hinj : Set.InjOn D ↑(Finset.range (p + 1)) := by
    intro i hi j hj hij
    exact ep2Line_zpowers_injOn ha hb ha1 hab hba i
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 (by simpa using hi)))
      j (Nat.lt_succ_iff.1 (Finset.mem_range.1 (by simpa using hj))) hij
  have hcardimg : ((Finset.range (p + 1)).image D).card = p + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have himg : (Finset.range (p + 1)).image D = 𝒟 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard𝒟, hcardimg])
  have hprod := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hAc hAp hKinv hfix 𝒟 h𝒟
  rw [← himg, Finset.prod_image hinj] at hprod
  simpa [D] using hprod

private theorem ep2_partner_card_eq {p K : ℕ} {c d : ℕ → ℕ}
    (hdc : ∀ i ≤ p, d i * c i = K) (hpos : ∀ i ≤ p, 0 < d i)
    (hpart : ∀ i ≤ p, ∃ j ≤ p, ∃ k ≤ p, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      d j = d i ∧ d k = d i) :
    ∀ i ≤ p, ∃ j ≤ p, ∃ k ≤ p, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ c j = c i ∧ c k = c i := by
  intro i hi
  obtain ⟨j, hj, k, hk, hji, hki, hjk, hdj, hdk⟩ := hpart i hi
  have hcij : c j = c i := by
    have h1 := hdc j hj
    have h2 := hdc i hi
    rw [hdj] at h1
    exact Nat.mul_left_cancel (hpos i hi) (h1.trans h2.symm)
  have hcik : c k = c i := by
    have h1 := hdc k hk
    have h2 := hdc i hi
    rw [hdk] at h1
    exact Nat.mul_left_cancel (hpos i hi) (h1.trans h2.symm)
  exact ⟨j, hj, k, hk, hji, hki, hjk, hcij, hcik⟩

private theorem card_ker_normHom_ne_one_of_ne_one {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {a : MulAut W} (ha1 : a ≠ 1) (haA : a ∈ A)
    (hcard : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W) :
    Nat.card ↥(normHom A).ker ≠ 1 := by
  intro h1
  have hcardA : Nat.card ↥(fixV A) = Nat.card W := by
    rw [h1, mul_one] at hcard
    exact hcard
  have htop : fixV A = ⊤ := Subgroup.eq_top_of_card_eq _ hcardA
  have haeq : ∀ w : W, a w = w := fun w =>
    mem_fixV.1 (by rw [htop]; exact Subgroup.mem_top w) a haA
  exact ha1 (MulEquiv.ext fun w => by simpa using haeq w)

private theorem ep2_prod_three_le {p K : ℕ} {c : ℕ → ℕ}
    (hprod : K = ∏ i ∈ Finset.range (p + 1), c i)
    (hc1 : ∀ i ≤ p, 1 ≤ c i) :
    ∀ i j k, i ≤ p → j ≤ p → k ≤ p → j ≠ i → k ≠ i → j ≠ k →
      c i * c j * c k ≤ K := by
  intro i j k hi hj hk hji hki hjk
  have hsub : ({i, j, k} : Finset ℕ) ⊆ Finset.range (p + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.mem_range.2 (by omega)
  have hle := Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun x hx _ => hc1 x (Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)))
  have hcalc : ∏ x ∈ ({i, j, k} : Finset ℕ), c x = c i * c j * c k := by
    rw [Finset.prod_insert (by simp [hji.symm, hki.symm]), Finset.prod_pair hjk,
      mul_assoc]
  rw [hcalc, ← hprod] at hle
  exact hle

private theorem ep2_partner_numeric {p K f : ℕ} {c d : ℕ → ℕ}
    (hdc : ∀ i ≤ p, d i * c i = K)
    (hprod : K = ∏ i ∈ Finset.range (p + 1), c i)
    (hpart : ∀ i ≤ p, ∃ j ≤ p, ∃ k ≤ p, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      c j = c i ∧ c k = c i)
    (hmin : ∀ i ≤ p, c i ≠ 1 → 2 ^ f ≤ c i)
    (hKne : K ≠ 1) :
    (∀ i ≤ p, 2 ^ (2 * f) ≤ d i) ∧ 2 ^ (3 * f) ≤ K := by
  classical
  have hc1 : ∀ i ≤ p, 1 ≤ c i := by
    intro i hi
    by_cases hci : c i = 1
    · rw [hci]
    · exact Nat.one_le_two_pow.trans (hmin i hi hci)
  have hprod3 := ep2_prod_three_le hprod hc1
  have hex : ∃ i ≤ p, c i ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∏ i ∈ Finset.range (p + 1), c i = 1 := by
      refine Finset.prod_eq_one fun i hi => hcon i ?_
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact hKne (by rw [hprod, h1])
  have hK3 : 2 ^ (3 * f) ≤ K := by
    obtain ⟨i, hi, hci⟩ := hex
    obtain ⟨j, hj, k, hk, hji, hki, hjk, hcj, hck⟩ := hpart i hi
    have hm : 2 ^ f ≤ c i := hmin i hi hci
    have h3 : (2 ^ f) ^ 3 ≤ c i * c j * c k := by
      rw [hcj, hck]
      calc (2 ^ f) ^ 3 = (2 ^ f * 2 ^ f) * 2 ^ f := by rw [pow_succ, pow_two]
        _ ≤ (c i * c i) * c i := Nat.mul_le_mul (Nat.mul_le_mul hm hm) hm
        _ = c i * c i * c i := rfl
    calc 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [mul_comm, pow_mul]
      _ ≤ c i * c j * c k := h3
      _ ≤ K := hprod3 i j k hi hj hk hji hki hjk
  refine ⟨fun i hi => ?_, hK3⟩
  obtain ⟨j, hj, k, hk, hji, hki, hjk, hcj, hck⟩ := hpart i hi
  by_cases hci : c i = 1
  · have hdK : d i = K := by
      have h := hdc i hi
      rwa [hci, mul_one] at h
    rw [hdK]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hK3
  · have hm : 2 ^ f ≤ c i := hmin i hi hci
    have hcpos : 0 < c i := lt_of_lt_of_le (by norm_num) hm
    have hle : c i * c i * c i ≤ d i * c i := by
      have h3 := hprod3 i j k hi hj hk hji hki hjk
      rwa [hcj, hck, ← hdc i hi] at h3
    have hd : c i * c i ≤ d i := Nat.le_of_mul_le_mul_right hle hcpos
    have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [mul_comm, pow_mul]
    rw [h2]
    calc (2 ^ f) ^ 2 ≤ c i ^ 2 := Nat.pow_le_pow_left hm 2
      _ = c i * c i := by rw [pow_two]
      _ ≤ d i := hd

private theorem two_pow_le_card_fixV_inf_of_ne_one {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    {A D : Subgroup (MulAut W)} {K : Subgroup W}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hKinv : ∀ x ∈ A, ∀ k ∈ K, x k ∈ K) (hfix : fixV A ⊓ K = ⊥)
    (hDA : D ≤ A) (hAcard : Nat.card ↥A = p ^ 2)
    (hDcard : Nat.card ↥D = p) (hne : Nat.card ↥(fixV D ⊓ K) ≠ 1) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
  have hrel : D.relIndex A = p := relIndex_eq_prime_of_le_of_card hDA hAcard hDcard
  have hbot : fixV D ⊓ K ≠ ⊥ := by
    intro hbot
    exact hne (by rw [hbot, Subgroup.card_bot])
  exact two_pow_le_card_fixV_inf hW hAc hAp hKinv hfix hDA hrel hbot

theorem two_pow_le_index_of_ep2_partners (hW : ∀ w : W, w * w = 1) (hp2 : p ≠ 2)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j)
    (hpart : ∀ i ≤ p, ∃ j ≤ p, ∃ k ≤ p, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (fixV (Subgroup.zpowers (ep2Line a b j))).index =
        (fixV (Subgroup.zpowers (ep2Line a b i))).index ∧
      (fixV (Subgroup.zpowers (ep2Line a b k))).index =
        (fixV (Subgroup.zpowers (ep2Line a b i))).index) :
    (∀ i ≤ p, 2 ^ (2 * orderOf (2 : ZMod p)) ≤
        (fixV (Subgroup.zpowers (ep2Line a b i))).index) ∧
      2 ^ (3 * orderOf (2 : ZMod p)) ≤
        (fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)).index := by
  classical
  let A : Subgroup (MulAut W) := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  let K : Subgroup W := (normHom A).ker
  let c : ℕ → ℕ := fun i =>
    Nat.card ↥(fixV (Subgroup.zpowers (ep2Line a b i)) ⊓ K)
  let d : ℕ → ℕ := fun i => (fixV (Subgroup.zpowers (ep2Line a b i))).index
  have hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b := rfl
  obtain ⟨hAcard, hAc, hAp, hfix, hcardK, hKinv, hbo⟩ :=
    ep2_setup hW hp2 ha hb ha1 hab hba hA
  have hDmemA : ∀ i, Subgroup.zpowers (ep2Line a b i) ≤ A :=
    fun i => by rw [hA]; exact ep2Line_zpowers_le_sup i
  have hDcard : ∀ i, Nat.card ↥(Subgroup.zpowers (ep2Line a b i)) = p := by
    intro i
    cases i with
    | zero => simp [ep2Line, Nat.card_zpowers, hbo]
    | succ n => exact card_zpowers_mul_pow ha hb ha1 hab hba n
  have hdc : ∀ i ≤ p, d i * c i = Nat.card ↥K := by
    intro i _
    exact index_mul_card_inf_ker_normHom_eq (A := A)
      (D := Subgroup.zpowers (ep2Line a b i)) (hDmemA i) hfix hcardK
  have hprod : Nat.card ↥K = ∏ i ∈ Finset.range (p + 1), c i :=
    ep2_card_ker_eq_prod hW hp2 ha hb ha1 hab hba hA hfix
  have hmin : ∀ i ≤ p, c i ≠ 1 → 2 ^ orderOf (2 : ZMod p) ≤ c i :=
    fun i _ hci => two_pow_le_card_fixV_inf_of_ne_one hW hAc hAp hKinv hfix
      (hDmemA i) hAcard (hDcard i) hci
  have hKne : Nat.card ↥K ≠ 1 :=
    card_ker_normHom_ne_one_of_ne_one ha1
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) hcardK
  have hpartc : ∀ i ≤ p, ∃ j ≤ p, ∃ k ≤ p, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      c j = c i ∧ c k = c i := by
    apply ep2_partner_card_eq hdc
    · intro i _
      change 0 < (fixV (Subgroup.zpowers (ep2Line a b i))).index
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    · intro i hi
      obtain ⟨j, hj, k, hk, hji, hki, hjk, hdj, hdk⟩ := hpart i hi
      exact ⟨j, hj, k, hk, hji, hki, hjk, by simpa [d] using hdj,
        by simpa [d] using hdk⟩
  obtain ⟨hsmall, hbig⟩ := ep2_partner_numeric hdc hprod hpartc hmin hKne
  have hAindex : (fixV A).index = Nat.card ↥K := by
    have h := index_mul_card_inf_ker_normHom_eq (A := A) (D := A) le_rfl hfix hcardK
    rwa [hfix, Subgroup.card_bot, mul_one] at h
  refine ⟨fun i hi => hsmall i hi, ?_⟩
  change 2 ^ (3 * orderOf (2 : ZMod p)) ≤ (fixV A).index
  rw [hAindex]
  exact hbig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
