module

public import CFSG.Sporadic.Th.Recog.MFactsB.Complement
public import CFSG.Sporadic.Th.Recog.MFactsA
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog
open scoped IsMulCommutative

section Basic

@[expose] noncomputable def E₀ : Subgroup ↥Max3.M := Subgroup.closure {zM, e₀, e₁}

private theorem e₁_sq : e₁ * e₁ = 1 := by
  rw [e₁]
  calc uM * e₀ * uM⁻¹ * (uM * e₀ * uM⁻¹)
      = uM * (e₀ * e₀) * uM⁻¹ := by group
    _ = 1 := by rw [e₀_mul_self]; group

private theorem zM_comm_e₀ : zM * e₀ = e₀ * zM :=
  Subtype.ext (Max3.commute_z_of_mem_M e₀.2).eq

private theorem zM_comm_e₁ : zM * e₁ = e₁ * zM :=
  Subtype.ext (Max3.commute_z_of_mem_M e₁.2).eq

private theorem zM_comm_tLetter : zM * tLetter = tLetter * zM :=
  Subtype.ext (Max3.commute_z_of_mem_M tLetter.2).eq

private theorem mem_E₀_z : zM ∈ E₀ := Subgroup.subset_closure (by simp [E₀])
private theorem mem_E₀_e₀ : e₀ ∈ E₀ := Subgroup.subset_closure (by simp [E₀])
private theorem mem_E₀_e₁ : e₁ ∈ E₀ := Subgroup.subset_closure (by simp [E₀])

private theorem e8_mem_E₀ (l : Fin 8) : e8 l ∈ E₀ := by
  rw [e8]
  exact E₀.mul_mem (E₀.mul_mem (Subgroup.pow_mem E₀ mem_E₀_z _)
    (Subgroup.pow_mem E₀ mem_E₀_e₀ _)) (Subgroup.pow_mem E₀ mem_E₀_e₁ _)

private theorem range_e8_subset : Set.range e8 ⊆ (E₀ : Set ↥Max3.M) := by
  rintro x ⟨l, rfl⟩
  exact e8_mem_E₀ l

private theorem elem_ab_z : IsElementaryAbelian 2 (Subgroup.zpowers zM) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (G := ↥Max3.M) (x := zM)
    (by rw [pow_two, zM_mul_self])

private theorem elem_ab_e₀ : IsElementaryAbelian 2 (Subgroup.zpowers e₀) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (G := ↥Max3.M) (x := e₀)
    (by rw [pow_two, e₀_mul_self])

private theorem elem_ab_e₁ : IsElementaryAbelian 2 (Subgroup.zpowers e₁) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (G := ↥Max3.M) (x := e₁)
    (by rw [pow_two, e₁_sq])

private theorem zpowers_le_centralizer_zpowers {x y : ↥Max3.M} (h : x * y = y * x) :
    Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers y : Set ↥Max3.M) := by
  have hzy : (Subgroup.zpowers y : Set ↥Max3.M) = Subgroup.closure {y} := by
    rw [Subgroup.zpowers_eq_closure]
  rw [hzy, Subgroup.centralizer_closure, Subgroup.zpowers_le,
    Subgroup.mem_centralizer_singleton_iff]
  exact h

private theorem elem_ab_sup : IsElementaryAbelian 2
    ↥(Subgroup.zpowers zM ⊔ Subgroup.zpowers e₀) := by
  haveI := elem_ab_z
  haveI := elem_ab_e₀
  exact IsElementaryAbelian.sup_of_le_centralizer (p := 2) (G := ↥Max3.M)
    (E := Subgroup.zpowers zM) (C := Subgroup.zpowers e₀)
    (zpowers_le_centralizer_zpowers (x := e₀) (y := zM) zM_comm_e₀.symm)

private theorem E₀_eq_sup : E₀ = (Subgroup.zpowers zM ⊔ Subgroup.zpowers e₀) ⊔
    Subgroup.zpowers e₁ := by
  rw [E₀, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff, or_assoc]

private theorem elem_ab_sup₂ (hcomm : e₀ * e₁ = e₁ * e₀) : IsElementaryAbelian 2
    ↥((Subgroup.zpowers zM ⊔ Subgroup.zpowers e₀) ⊔ Subgroup.zpowers e₁) := by
  haveI := elem_ab_sup
  haveI := elem_ab_e₁
  refine IsElementaryAbelian.sup_of_le_centralizer (p := 2) (G := ↥Max3.M)
    (E := Subgroup.zpowers zM ⊔ Subgroup.zpowers e₀) (C := Subgroup.zpowers e₁) ?_
  rw [Subgroup.le_centralizer_iff]
  have h1 : Subgroup.zpowers zM ≤
      Subgroup.centralizer (Subgroup.zpowers e₁ : Set ↥Max3.M) :=
    zpowers_le_centralizer_zpowers (x := zM) (y := e₁) zM_comm_e₁
  have h2 : Subgroup.zpowers e₀ ≤
      Subgroup.centralizer (Subgroup.zpowers e₁ : Set ↥Max3.M) :=
    zpowers_le_centralizer_zpowers (x := e₀) (y := e₁) (by rw [hcomm])
  exact sup_le h1 h2

private theorem elem_ab_E₀ (hcomm : e₀ * e₁ = e₁ * e₀) : IsElementaryAbelian 2 ↥E₀ := by
  rw [E₀_eq_sup]
  exact elem_ab_sup₂ hcomm

private theorem e8_zero : e8 0 = 1 := by simp [e8]
private theorem e8_one : e8 1 = zM := by simp [e8]
private theorem e8_two : e8 2 = e₀ := by simp [e8]
private theorem e8_four : e8 4 = e₁ := by simp [e8]

private theorem zM_ne_e₀ (hinj : Function.Injective e8) : zM ≠ e₀ := by
  intro h
  have h' : e8 1 = e8 2 := by rw [e8_one, e8_two, h]
  exact absurd (hinj h') (by decide)

private theorem zM_ne_e₁ (hinj : Function.Injective e8) : zM ≠ e₁ := by
  intro h
  have h' : e8 1 = e8 4 := by rw [e8_one, e8_four, h]
  exact absurd (hinj h') (by decide)

private theorem e₀_ne_e₁ (hinj : Function.Injective e8) : e₀ ≠ e₁ := by
  intro h
  have h' : e8 2 = e8 4 := by rw [e8_two, e8_four, h]
  exact absurd (hinj h') (by decide)

private theorem card_gen_set (hinj : Function.Injective e8) :
    Nat.card ({zM, e₀, e₁} : Set ↥Max3.M) = 3 := by
  have hset : ({zM, e₀, e₁} : Set ↥Max3.M) =
      insert zM (insert e₀ ({e₁} : Set ↥Max3.M)) := rfl
  rw [hset, Nat.card_coe_set_eq]
  simp [Set.ncard_insert_of_notMem, zM_ne_e₀ hinj, zM_ne_e₁ hinj, e₀_ne_e₁ hinj]

private theorem rank_E₀_le (hinj : Function.Injective e8) : generatorRank ↥E₀ ≤ 3 := by
  rw [generatorRank_eq_group_rank]
  have h := Subgroup.rank_closure_finite_le_nat_card ({zM, e₀, e₁} : Set ↥Max3.M)
  rw [card_gen_set hinj] at h
  simpa [E₀] using h

private theorem card_E₀_le (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8) :
    Nat.card E₀ ≤ 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI hAb : IsElementaryAbelian 2 ↥E₀ := elem_ab_E₀ hcomm
  have hcard := elementaryAbelian_card_eq_pow_generatorRank (p := 2) ↥E₀
  have hrank := rank_E₀_le hinj
  calc Nat.card E₀ = 2 ^ generatorRank ↥E₀ := hcard
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrank
    _ = 8 := by norm_num

private theorem card_range_e8 (hinj : Function.Injective e8) :
    Nat.card (Set.range e8) = 8 := by
  rw [Nat.card_coe_set_eq, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  norm_num

private theorem le_card_E₀ (hinj : Function.Injective e8) : 8 ≤ Nat.card E₀ := by
  have hfin : (E₀ : Set ↥Max3.M).Finite := Set.toFinite _
  calc 8 = Nat.card (Set.range e8) := (card_range_e8 hinj).symm
    _ ≤ Nat.card (E₀ : Set ↥Max3.M) := Nat.card_mono hfin range_e8_subset
    _ = Nat.card E₀ := Nat.card_coe_set_eq _

private theorem card_E₀ (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8) :
    Nat.card E₀ = 8 :=
  le_antisymm (card_E₀_le hcomm hinj) (le_card_E₀ hinj)

private theorem E₀_eq_range (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8) :
    (E₀ : Set ↥Max3.M) = Set.range e8 := by
  have hE : (E₀ : Set ↥Max3.M).ncard = 8 := by
    have h := card_E₀ hcomm hinj
    change (E₀ : Set ↥Max3.M).ncard = 8 at h
    exact h
  have hR : (Set.range e8).ncard = 8 := by
    have h := card_range_e8 hinj
    change (Set.range e8).ncard = 8 at h
    exact h
  have hEq : Set.range e8 = (E₀ : Set ↥Max3.M) := by
    refine Set.eq_of_subset_of_ncard_le range_e8_subset ?_
    change (E₀ : Set ↥Max3.M).ncard ≤ (Set.range e8).ncard
    rw [hE, hR]
  exact hEq.symm

private theorem mem_E₀_iff (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8)
    {x : ↥Max3.M} :
    x ∈ E₀ ↔ ∃ l : Fin 8, e8 l = x := by
  constructor
  · intro hx
    have h : x ∈ (E₀ : Set ↥Max3.M) := hx
    rw [E₀_eq_range hcomm hinj] at h
    exact h
  · rintro ⟨l, rfl⟩
    exact e8_mem_E₀ l

private theorem E₀_comm (hcomm : e₀ * e₁ = e₁ * e₀) :
    ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
  haveI : IsMulCommutative ↥E₀ := (elem_ab_E₀ hcomm).toIsMulCommutative
  intro x hx y hy
  simpa using congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥E₀) (⟨y, hy⟩ : ↥E₀))

private theorem E₀_sq (hcomm : e₀ * e₁ = e₁ * e₀) : ∀ x ∈ E₀, x * x = 1 := by
  haveI : IsElementaryAbelian 2 ↥E₀ := elem_ab_E₀ hcomm
  intro x hx
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (G := ↥Max3.M) (A := E₀) x hx
  simpa [pow_two] using h

private theorem E₀_le_centralizer_t :
    E₀ ≤ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) := by
  rw [E₀, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr zM_comm_tLetter
  · exact Subgroup.mem_centralizer_singleton_iff.mpr e₀_comm_tLetter
  · exact Subgroup.mem_centralizer_singleton_iff.mpr e₁_comm_tLetter

private theorem E₀_comm_t : ∀ x ∈ E₀, x * tLetter = tLetter * x := by
  intro x hx
  have h := E₀_le_centralizer_t hx
  rwa [Subgroup.mem_centralizer_singleton_iff] at h

private theorem pow_mul_eq_mul_pow {x y : ↥Max3.M} (h : x * y = y * x) (n : ℕ) :
    x ^ n * y = y * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc x ^ (n + 1) * y = x ^ n * (x * y) := by rw [pow_succ, mul_assoc]
        _ = x ^ n * (y * x) := by rw [h]
        _ = (x ^ n * y) * x := by rw [mul_assoc]
        _ = (y * x ^ n) * x := by rw [ih]
        _ = y * (x ^ n * x) := by rw [mul_assoc]
        _ = y * x ^ (n + 1) := by rw [pow_succ]

private theorem pre_mul_q_comm_e₀ {m : ↥Max3.M} {a : Fin 18} {q : ↥Max3.M} {k : ℕ}
    (hmq : m = tLetter ^ k * pre a * q) (hm : m * e₀ = e₀ * m)
    (ht : tLetter ^ k * e₀ = e₀ * tLetter ^ k) :
    pre a * q * e₀ = e₀ * (pre a * q) := by
  have hmain : tLetter ^ k * ((pre a * q) * e₀) =
      tLetter ^ k * (e₀ * (pre a * q)) := by
    calc tLetter ^ k * ((pre a * q) * e₀)
        = (tLetter ^ k * (pre a * q)) * e₀ := by group
      _ = m * e₀ := by rw [hmq]; group
      _ = e₀ * m := hm
      _ = e₀ * (tLetter ^ k * (pre a * q)) := by rw [hmq]; group
      _ = (e₀ * tLetter ^ k) * (pre a * q) := by group
      _ = (tLetter ^ k * e₀) * (pre a * q) := by rw [ht]
      _ = tLetter ^ k * (e₀ * (pre a * q)) := by group
  exact mul_left_cancel hmain

private theorem pre_mul_q_comm_e₁ {m : ↥Max3.M} {a : Fin 18} {q : ↥Max3.M} {k : ℕ}
    (hmq : m = tLetter ^ k * pre a * q) (hm : m * e₁ = e₁ * m)
    (ht : tLetter ^ k * e₁ = e₁ * tLetter ^ k) :
    pre a * q * e₁ = e₁ * (pre a * q) := by
  have hmain : tLetter ^ k * ((pre a * q) * e₁) =
      tLetter ^ k * (e₁ * (pre a * q)) := by
    calc tLetter ^ k * ((pre a * q) * e₁)
        = (tLetter ^ k * (pre a * q)) * e₁ := by group
      _ = m * e₁ := by rw [hmq]; group
      _ = e₁ * m := hm
      _ = e₁ * (tLetter ^ k * (pre a * q)) := by rw [hmq]; group
      _ = (e₁ * tLetter ^ k) * (pre a * q) := by group
      _ = (tLetter ^ k * e₁) * (pre a * q) := by rw [ht]
      _ = tLetter ^ k * (e₁ * (pre a * q)) := by group
  exact mul_left_cancel hmain

private theorem E₀_cent (hce : ∀ {q : ↥Max3.M}, (q : J) ∈ Max3.Q →
    q * tLetter = tLetter * q → ∀ a : Fin 18,
      pre a * q * e₀ = e₀ * (pre a * q) → pre a * q * e₁ = e₁ * (pre a * q) →
        a = 0 ∧ ∃ l : Fin 8, q = e8 l) :
    ∀ m : ↥Max3.M, m * tLetter = tLetter * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tLetter ^ k := by
  intro m hm hEm
  obtain ⟨k, a, q, hqC, hmq⟩ := exists_rT_mul hm
  have hqQ : (q : J) ∈ Max3.Q := Subgroup.mem_subgroupOf.mp hqC.1
  have hqt : q * tLetter = tLetter * q :=
    (Subgroup.mem_centralizer_iff.mp hqC.2 tLetter (Set.mem_singleton tLetter)).symm
  have htke₀ : tLetter ^ k.val * e₀ = e₀ * tLetter ^ k.val :=
    pow_mul_eq_mul_pow (x := tLetter) (y := e₀) e₀_comm_tLetter.symm k.val
  have htke₁ : tLetter ^ k.val * e₁ = e₁ * tLetter ^ k.val :=
    pow_mul_eq_mul_pow (x := tLetter) (y := e₁) e₁_comm_tLetter.symm k.val
  have hrE₀ : pre a * q * e₀ = e₀ * (pre a * q) :=
    pre_mul_q_comm_e₀ (m := m) (a := a) (q := q) (k := k.val) hmq
      (hEm e₀ mem_E₀_e₀) htke₀
  have hrE₁ : pre a * q * e₁ = e₁ * (pre a * q) :=
    pre_mul_q_comm_e₁ (m := m) (a := a) (q := q) (k := k.val) hmq
      (hEm e₁ mem_E₀_e₁) htke₁
  obtain ⟨ha0, l, hql⟩ := hce hqQ hqt a hrE₀ hrE₁
  refine ⟨q, ?_, k.val, ?_⟩
  · rw [hql]
    exact e8_mem_E₀ l
  · rw [hmq, ha0]
    simp only [pre, Fin.val_zero, Nat.zero_div, Nat.zero_mod, pow_zero, one_mul, mul_one]
    rw [hql]
    have hpow : ∀ n : ℕ, tLetter ^ n * q = q * tLetter ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc tLetter ^ (n + 1) * q = tLetter ^ n * (tLetter * q) := by
                rw [pow_succ, mul_assoc]
            _ = tLetter ^ n * (q * tLetter) := by rw [← hqt]
            _ = (tLetter ^ n * q) * tLetter := by rw [mul_assoc]
            _ = (q * tLetter ^ n) * tLetter := by rw [ih]
            _ = q * (tLetter ^ n * tLetter) := by rw [mul_assoc]
            _ = q * tLetter ^ (n + 1) := by rw [pow_succ]
    rw [hql] at hpow
    exact hpow k.val

private theorem nE_normalizes
    (hn₀ : ∀ i : Fin 5, nE i * e₀ * (nE i)⁻¹ = e8 (![3, 4, 5, 6, 7] i))
    (hn₁ : ∀ i : Fin 5, nE i * e₁ * (nE i)⁻¹ = e8 (![5, 2, 3, 3, 2] i))
    (i : Fin 5) : ∀ x ∈ E₀, nE i * x * (nE i)⁻¹ ∈ E₀ := by
  have hz : nE i * zM * (nE i)⁻¹ = zM := by
    apply Subtype.ext
    change (nE i : J) * Max3.z * (nE i : J)⁻¹ = Max3.z
    rw [← (Max3.commute_z_of_mem_M (nE i).2).eq, mul_assoc, mul_inv_cancel, mul_one]
  have he₀ := hn₀ i
  have he₁ := hn₁ i
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [hz]; exact mem_E₀_z
      · rw [he₀]; exact e8_mem_E₀ _
      · rw [he₁]; exact e8_mem_E₀ _
  | one => simp
  | mul a b ha hb iha ihb =>
      rw [show nE i * (a * b) * (nE i)⁻¹ =
        (nE i * a * (nE i)⁻¹) * (nE i * b * (nE i)⁻¹) by group]
      exact E₀.mul_mem iha ihb
  | inv a ha iha =>
      rw [show nE i * a⁻¹ * (nE i)⁻¹ = (nE i * a * (nE i)⁻¹)⁻¹ by group]
      exact E₀.inv_mem iha

private theorem E₀_trans
    (hnt : ∀ i : Fin 5, nE i * tLetter = tLetter * nE i)
    (hn₀ : ∀ i : Fin 5, nE i * e₀ * (nE i)⁻¹ = e8 (![3, 4, 5, 6, 7] i))
    (hn₁ : ∀ i : Fin 5, nE i * e₁ * (nE i)⁻¹ = e8 (![5, 2, 3, 3, 2] i))
    (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8) :
    ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M,
      n * tLetter = tLetter * n ∧ (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧
        n * e₀ * n⁻¹ = w := by
  intro w hw hw1 hwz
  obtain ⟨l, rfl⟩ := (mem_E₀_iff hcomm hinj).mp hw
  fin_cases l
  · exact absurd e8_zero (by simpa using hw1)
  · have hwz' : (e8 1 : J) ≠ Max3.z := by simpa using hwz
    rw [e8_one] at hwz'
    exact absurd rfl hwz'
  · exact ⟨1, by simp, fun x hx => by simpa using hx, by simp [e8]⟩
  · exact ⟨nE 0, hnt 0, nE_normalizes hn₀ hn₁ 0, by simpa using hn₀ 0⟩
  · exact ⟨nE 1, hnt 1, nE_normalizes hn₀ hn₁ 1, by simpa using hn₀ 1⟩
  · exact ⟨nE 2, hnt 2, nE_normalizes hn₀ hn₁ 2, by simpa using hn₀ 2⟩
  · exact ⟨nE 3, hnt 3, nE_normalizes hn₀ hn₁ 3, by simpa using hn₀ 3⟩
  · exact ⟨nE 4, hnt 4, nE_normalizes hn₀ hn₁ 4, by simpa using hn₀ 4⟩

private theorem e₀_sq_J : (e₀ : J) * (e₀ : J) = 1 := by
  simpa using congrArg (fun z : ↥Max3.M => (z : J)) e₀_mul_self

private theorem e₀_ne_one_J : (e₀ : J) ≠ 1 := by
  intro h
  exact e₀_ne_one (Subtype.ext h)

private theorem z_conj_inv_eq (g : J) (hg : g ∈ Max3.M) :
    g⁻¹ * Max3.z * g = Max3.z := by
  calc g⁻¹ * Max3.z * g = g⁻¹ * (Max3.z * g) := by group
    _ = g⁻¹ * (g * Max3.z) := by rw [(Max3.commute_z_of_mem_M hg).symm.eq]
    _ = Max3.z := by group

private theorem isConj_e₀_q0M : IsConj e₀ q0M := by
  obtain ⟨g, hgM, hg | hg⟩ :=
    Max3.InvRep.exists_conj_of_mem_Q e₀_mem_Q e₀_sq_J e₀_ne_one_J
  · exfalso
    have hz : (e₀ : J) = Max3.z := by
      calc (e₀ : J) = g⁻¹ * (g * (e₀ : J) * g⁻¹) * g := by group
        _ = g⁻¹ * Max3.z * g := by rw [hg]
        _ = Max3.z := z_conj_inv_eq g hgM
    exact coe_e₀_ne_z hz
  · refine isConj_iff.mpr ⟨⟨g, hgM⟩, ?_⟩
    apply Subtype.ext
    simpa using hg

private theorem card_centralizer_e₀ :
    Nat.card (Subgroup.centralizer ({e₀} : Set ↥Max3.M)) = 2 ^ 14 * 21 := by
  have h := Subgroup.card_centralizer_of_isConj (g := e₀) (h := q0M) isConj_e₀_q0M
  rw [card_centralizer_q0M] at h
  exact h

private theorem mem_A_of_lt_four {A : Subgroup ↥Max3.M} (hzA : zM ∈ A) (he₀A : e₀ ∈ A)
    {l : Fin 8} (hl : l.val < 4) : e8 l ∈ A := by
  fin_cases l
  · simpa [e8] using A.one_mem
  · simpa [e8_one] using hzA
  · simpa [e8_two] using he₀A
  · simpa [e8] using A.mul_mem hzA he₀A
  · simp at hl
  · simp at hl
  · simp at hl
  · simp at hl

private theorem card_e8_four (hinj : Function.Injective e8) :
    Nat.card ({e8 0, e8 1, e8 2, e8 3} : Set ↥Max3.M) = 4 := by
  have h01 : e8 0 ≠ e8 1 := fun h => absurd (hinj h) (by decide)
  have h02 : e8 0 ≠ e8 2 := fun h => absurd (hinj h) (by decide)
  have h03 : e8 0 ≠ e8 3 := fun h => absurd (hinj h) (by decide)
  have h12 : e8 1 ≠ e8 2 := fun h => absurd (hinj h) (by decide)
  have h13 : e8 1 ≠ e8 3 := fun h => absurd (hinj h) (by decide)
  have h23 : e8 2 ≠ e8 3 := fun h => absurd (hinj h) (by decide)
  rw [Nat.card_coe_set_eq]
  have hm1 : e8 0 ∉ ({e8 1, e8 2, e8 3} : Set ↥Max3.M) := by
    simp [h01, h02, h03]
  have hm2 : e8 1 ∉ ({e8 2, e8 3} : Set ↥Max3.M) := by simp [h12, h13]
  have hm3 : e8 2 ∉ ({e8 3} : Set ↥Max3.M) := by simp [h23]
  rw [show ({e8 0, e8 1, e8 2, e8 3} : Set ↥Max3.M) =
      insert (e8 0) (insert (e8 1) (insert (e8 2) ({e8 3} : Set ↥Max3.M))) from rfl,
    Set.ncard_insert_of_notMem hm1, Set.ncard_insert_of_notMem hm2,
    Set.ncard_insert_of_notMem hm3, Set.ncard_singleton]

private theorem le_card_four_of_all_lt_four {A : Subgroup ↥Max3.M}
    (hinj : Function.Injective e8) (hzA : zM ∈ A) (he₀A : e₀ ∈ A)
    (hall : ∀ x ∈ A, ∃ l : Fin 8, l.val < 4 ∧ x = e8 l) : 4 ≤ Nat.card A := by
  have hsub : ({e8 0, e8 1, e8 2, e8 3} : Set ↥Max3.M) ⊆ (A : Set ↥Max3.M) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [e8] using A.one_mem
    · simpa [e8_one] using hzA
    · simpa [e8_two] using he₀A
    · simpa [e8] using A.mul_mem hzA he₀A
  calc 4 = Nat.card ({e8 0, e8 1, e8 2, e8 3} : Set ↥Max3.M) :=
        (card_e8_four hinj).symm
    _ ≤ Nat.card (A : Set ↥Max3.M) := Nat.card_mono (Set.toFinite _) hsub
    _ = Nat.card ↥A := Nat.card_coe_set_eq _

private theorem card_four_of_all_lt_four {A : Subgroup ↥Max3.M}
    (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8) (hzA : zM ∈ A)
    (he₀A : e₀ ∈ A)
    (hall : ∀ x ∈ A, ∃ l : Fin 8, l.val < 4 ∧ x = e8 l) : Nat.card A = 4 := by
  have hAE : A ≤ E₀ := by
    intro x hx
    obtain ⟨l, -, rfl⟩ := hall x hx
    exact e8_mem_E₀ l
  have h4 : 4 ≤ Nat.card ↥A := le_card_four_of_all_lt_four hinj hzA he₀A hall
  have hdvd : Nat.card ↥A ∣ 8 := by
    have h := Subgroup.card_dvd_of_le hAE
    rwa [card_E₀ hcomm hinj] at h
  have hdvd' : Nat.card ↥A ∣ 2 ^ 3 := by simpa using hdvd
  obtain ⟨m, hm_le, hm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd'
  have hcases : Nat.card ↥A = 4 ∨ Nat.card ↥A = 8 := by
    have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm_cases with rfl | rfl | rfl | rfl
    · rw [pow_zero] at hm; omega
    · rw [pow_one] at hm; omega
    · left; rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hm; exact hm
    · right; rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at hm; exact hm
  rcases hcases with h4A | h8A
  · exact h4A
  · exfalso
    have hAEq : A = E₀ :=
      Subgroup.eq_of_le_of_card_ge hAE (by rw [h8A, card_E₀ hcomm hinj])
    have he₁A : e₁ ∈ A := by rw [hAEq]; exact mem_E₀_e₁
    obtain ⟨l, hl4, hl⟩ := hall e₁ he₁A
    have hEq : e8 4 = e8 l := by rw [e8_four, hl]
    have h4l : (4 : Fin 8) = l := hinj hEq
    rw [← h4l] at hl4
    simp at hl4

private theorem E₀_abelian
    (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8)
    (hceE : ∀ i : Fin 7, cE i * e₀ = e₀ * cE i)
    (hcN : ∀ j : Fin 6, cN j * e₀ = e₀ * cN j)
    (hA : ∀ {q : ↥Max3.M}, (q : J) ∈ Max3.Q → q * e₀ = e₀ * q →
      (∃ l : Fin 8, l.val < 4 ∧ q = e8 l) ∨
        (∃ j : Fin 6, cN j * q * (cN j)⁻¹ * q ≠ q * (cN j * q * (cN j)⁻¹)) ∨
        ∃ (i : Fin 7) (l : Fin 8), l.val < 4 ∧ cE i * q * (cE i)⁻¹ = e₁ * e8 l) :
    ∀ A : Subgroup ↥Max3.M, (∀ x ∈ A, (x : J) ∈ Max3.Q ∧ x * e₀ = e₀ * x) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    (∀ c : ↥Max3.M, c * e₀ = e₀ * c → ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
    (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ A → e₀ ∈ A → Nat.card A = 4 ∨ E₀ ≤ A := by
  intro A hAQ hAcomm hAnorm hzA he₀A
  by_cases hall : ∀ x ∈ A, ∃ l : Fin 8, l.val < 4 ∧ x = e8 l
  · left
    exact card_four_of_all_lt_four hcomm hinj hzA he₀A hall
  · right
    push Not at hall
    obtain ⟨q, hqA, hqnot⟩ := hall
    have hqQ : (q : J) ∈ Max3.Q := (hAQ q hqA).1
    have hqe₀ : q * e₀ = e₀ * q := (hAQ q hqA).2
    rcases hA hqQ hqe₀ with ⟨l, hl4, hql⟩ | ⟨j, hj⟩ | ⟨i, l, hl4, hil⟩
    · exfalso
      exact hqnot l hl4 hql
    · exfalso
      have hrA : cN j * q * (cN j)⁻¹ ∈ A := hAnorm (cN j) (hcN j) q hqA
      exact hj (hAcomm _ hrA q hqA)
    · have hrA : cE i * q * (cE i)⁻¹ ∈ A := hAnorm (cE i) (hceE i) q hqA
      have hprodA : e₁ * e8 l ∈ A := by rw [← hil]; exact hrA
      have hlA : e8 l ∈ A := mem_A_of_lt_four hzA he₀A hl4
      have he₁A : e₁ ∈ A := by
        have := A.mul_mem hprodA (A.inv_mem hlA)
        simpa [mul_assoc] using this
      rw [E₀, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hzA
      · exact he₀A
      · exact he₁A

private noncomputable def m₁ : ↥Max3.M := dM * uM * dM

private noncomputable def m₂ : ↥Max3.M := dM * tLetter * uM * dM

private theorem dMul_mul (x y : ↥Max3.M) :
    dM * (x * y) * dM = (dM * x * dM) * (dM * y * dM) := by
  have h : (dM * x * dM) * (dM * y * dM) = dM * (x * y) * dM := by
    calc (dM * x * dM) * (dM * y * dM) = dM * x * (dM * dM) * y * dM := by group
      _ = dM * x * y * dM := by rw [dM_mul_self, mul_one]
      _ = dM * (x * y) * dM := by group
  exact h.symm

private theorem dMul_pow (x : ↥Max3.M) (n : ℕ) :
    (dM * x * dM) ^ n = dM * x ^ n * dM := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one]; exact dM_mul_self.symm
  | succ n ih =>
      rw [pow_succ, ih, ← dMul_mul, ← pow_succ]

private theorem m₂_eq_dMul_tu : m₂ = dM * (tLetter * uM) * dM := by
  rw [m₂]; group

private theorem m₁_eq_dMul : m₁ = dM * uM * dM := rfl

private theorem m₁_comm_e₀ : m₁ * e₀ = e₀ * m₁ := by
  rw [m₁_eq_dMul, e₀, ← dMul_mul uM cM, ← dMul_mul cM uM, uM_comm_cM]

private theorem tu_mul_cM : (tLetter * uM) * cM = cM * (tLetter * uM) := by
  rw [mul_assoc, uM_comm_cM, ← mul_assoc, ← cM_comm_tLetter, mul_assoc]

private theorem m₂_comm_e₀ : m₂ * e₀ = e₀ * m₂ := by
  rw [m₂_eq_dMul_tu, e₀, ← dMul_mul (tLetter * uM) cM, ← dMul_mul cM (tLetter * uM),
    tu_mul_cM]

private theorem m₁_pow_four : m₁ ^ 4 = 1 := by
  rw [m₁_eq_dMul, dMul_pow, uM_pow_four, mul_one, dM_mul_self]

private theorem tu_pow_four : (tLetter * uM) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, tLetter_mul_uM_sq]
  calc (uM ^ 2) ^ 2 = uM ^ (2 * 2) := by rw [pow_mul]
    _ = uM ^ 4 := by norm_num
    _ = 1 := uM_pow_four

private theorem m₂_pow_four : m₂ ^ 4 = 1 := by
  rw [m₂_eq_dMul_tu, dMul_pow, tu_pow_four, mul_one, dM_mul_self]

private theorem uM_mul_tu : uM * (tLetter * uM) = tLetter⁻¹ * uM ^ 2 := by
  calc uM * (tLetter * uM) = (uM * tLetter) * uM := by group
    _ = (tLetter⁻¹ * uM) * uM := by rw [uM_mul_tLetter]
    _ = tLetter⁻¹ * uM ^ 2 := by rw [pow_two]; group

private theorem dMul_t_inv : dM * tLetter⁻¹ * dM = tLetter⁻¹ := by
  have h : dM * tLetter * dM = tLetter := by
    rw [dM_comm_tLetter, mul_assoc, dM_mul_self, mul_one]
  calc dM * tLetter⁻¹ * dM = dM⁻¹ * tLetter⁻¹ * dM⁻¹ := by rw [dM_inv]
    _ = (dM * tLetter * dM)⁻¹ := by group
    _ = tLetter⁻¹ := by rw [h]

private theorem zM_comm_dM : zM * dM = dM * zM :=
  Subtype.ext (Max3.commute_z_of_mem_M dM.2).eq

private theorem dMul_z : dM * zM * dM = zM := by
  calc dM * zM * dM = zM * dM * dM := by rw [← zM_comm_dM]
    _ = zM := by rw [mul_assoc, dM_mul_self, mul_one]

private theorem dMul_c : dM * cM * dM = e₀ := rfl

private theorem dMul_u_sq : dM * uM ^ 2 * dM = zM * e₀ := by
  rw [uM_pow_two, dMul_mul, dMul_z, dMul_c]

private theorem m₁_mul_m₂ : m₁ * m₂ = tLetter⁻¹ * (zM * e₀) := by
  rw [m₁_eq_dMul, m₂_eq_dMul_tu, ← dMul_mul uM (tLetter * uM), uM_mul_tu,
    dMul_mul, dMul_t_inv, dMul_u_sq]

private theorem zM_mul_e₀_sq : (zM * e₀) ^ 2 = 1 := by
  rw [pow_two]
  calc (zM * e₀) * (zM * e₀) = zM * (e₀ * zM) * e₀ := by group
    _ = zM * (zM * e₀) * e₀ := by rw [← zM_comm_e₀]
    _ = (zM * zM) * (e₀ * e₀) := by group
    _ = 1 := by rw [zM_mul_self, e₀_mul_self]; group

private theorem zM_mul_e₀_ne_one : zM * e₀ ≠ 1 := by
  intro h
  have hz : zM = e₀ := by
    calc zM = zM * (zM * e₀) := by rw [h, mul_one]
      _ = (zM * zM) * e₀ := by group
      _ = e₀ := by rw [zM_mul_self, one_mul]
  have hJ : (e₀ : J) = Max3.z := by rw [← hz]
  exact coe_e₀_ne_z hJ

private theorem orderOf_zM_mul_e₀ : orderOf (zM * e₀) = 2 :=
  orderOf_eq_prime zM_mul_e₀_sq zM_mul_e₀_ne_one

private theorem orderOf_tLetter_inv : orderOf (tLetter⁻¹) = 3 := by
  rw [orderOf_inv, orderOf_tLetter]

private theorem commute_t_inv_zE : Commute (tLetter⁻¹) (zM * e₀) := by
  have h3 : tLetter * (zM * e₀) = (zM * e₀) * tLetter := by
    calc tLetter * (zM * e₀) = (tLetter * zM) * e₀ := by group
      _ = (zM * tLetter) * e₀ := by rw [← zM_comm_tLetter]
      _ = zM * (tLetter * e₀) := by group
      _ = zM * (e₀ * tLetter) := by rw [e₀_comm_tLetter]
      _ = (zM * e₀) * tLetter := by group
  have h4 : (zM * e₀) * tLetter⁻¹ = tLetter⁻¹ * (zM * e₀) := by
    calc (zM * e₀) * tLetter⁻¹
        = tLetter⁻¹ * (tLetter * (zM * e₀)) * tLetter⁻¹ := by group
      _ = tLetter⁻¹ * ((zM * e₀) * tLetter) * tLetter⁻¹ := by rw [h3]
      _ = tLetter⁻¹ * (zM * e₀) := by group
  exact h4.symm

private theorem m₁_mul_m₂_order : orderOf (m₁ * m₂) = 6 := by
  rw [m₁_mul_m₂]
  have hcop : Nat.Coprime (orderOf (tLetter⁻¹)) (orderOf (zM * e₀)) := by
    rw [orderOf_tLetter_inv, orderOf_zM_mul_e₀]; norm_num
  have h := Commute.orderOf_mul_eq_mul_orderOf_of_coprime
    (x := tLetter⁻¹) (y := zM * e₀) commute_t_inv_zE hcop
  rw [orderOf_tLetter_inv, orderOf_zM_mul_e₀] at h
  exact h

private theorem E₀_three : ∃ m₁ m₂ : ↥Max3.M,
    m₁ * e₀ = e₀ * m₁ ∧ m₂ * e₀ = e₀ * m₂ ∧
      (∃ k : ℕ, m₁ ^ 2 ^ k = 1) ∧ (∃ k : ℕ, m₂ ^ 2 ^ k = 1) ∧
        3 ∣ orderOf (m₁ * m₂) := by
  refine ⟨dM * uM * dM, dM * tLetter * uM * dM, ?_, ?_, ?_, ?_, ?_⟩
  · exact m₁_comm_e₀
  · exact m₂_comm_e₀
  · exact ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact m₁_pow_four⟩
  · exact ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact m₂_pow_four⟩
  · rw [show dM * uM * dM = m₁ from rfl,
      show dM * tLetter * uM * dM = m₂ from rfl, m₁_mul_m₂_order]
    norm_num

theorem e8Facts_of (hcomm : e₀ * e₁ = e₁ * e₀) (hinj : Function.Injective e8)
    (hnt : ∀ i : Fin 5, nE i * tLetter = tLetter * nE i)
    (hn₀ : ∀ i : Fin 5, nE i * e₀ * (nE i)⁻¹ = e8 (![3, 4, 5, 6, 7] i))
    (hn₁ : ∀ i : Fin 5, nE i * e₁ * (nE i)⁻¹ = e8 (![5, 2, 3, 3, 2] i))
    (hce : ∀ {q : ↥Max3.M}, (q : J) ∈ Max3.Q → q * tLetter = tLetter * q → ∀ a : Fin 18,
      pre a * q * e₀ = e₀ * (pre a * q) → pre a * q * e₁ = e₁ * (pre a * q) →
        a = 0 ∧ ∃ l : Fin 8, q = e8 l)
    (hcE : ∀ i : Fin 7, cE i * e₀ = e₀ * cE i) (hcN : ∀ j : Fin 6, cN j * e₀ = e₀ * cN j)
    (hA : ∀ {q : ↥Max3.M}, (q : J) ∈ Max3.Q → q * e₀ = e₀ * q →
      (∃ l : Fin 8, l.val < 4 ∧ q = e8 l) ∨
        (∃ j : Fin 6, cN j * q * (cN j)⁻¹ * q ≠ q * (cN j * q * (cN j)⁻¹)) ∨
        ∃ (i : Fin 7) (l : Fin 8), l.val < 4 ∧ cE i * q * (cE i)⁻¹ = e₁ * e8 l) :
    E8Facts E₀ e₀ where
  mem := mem_E₀_e₀
  ne_one := e₀_ne_one
  ne_z := coe_e₀_ne_z
  comm := E₀_comm hcomm
  sq := E₀_sq hcomm
  card := card_E₀ hcomm hinj
  z_mem := mem_E₀_z
  comm_t := E₀_comm_t
  cent := E₀_cent hce
  trans := E₀_trans hnt hn₀ hn₁ hcomm hinj
  mem_Q := e₀_mem_Q
  card_centralizer := card_centralizer_e₀
  abelian := E₀_abelian hcomm hinj hcE hcN hA
  three := E₀_three

end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
