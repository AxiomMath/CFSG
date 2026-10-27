module

public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open

variable {G : Type} [Group G]

theorem pow_gcd_mem {S : Subgroup G} {g : G} {m n : ℕ} (hm : g ^ m ∈ S) (hn : g ^ n ∈ S) :
    g ^ Nat.gcd m n ∈ S := by
  have h : ((Nat.gcd m n : ℕ) : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n := Nat.gcd_eq_gcd_ab m n
  rw [← zpow_natCast, h, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  exact S.mul_mem (S.zpow_mem hm _) (S.zpow_mem hn _)

@[expose] def quadSet (u v : G) : Set G :=
  Set.range fun p : Fin 2 × Fin 2 => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ)

theorem mem_quadSet_of {u v w₁ w₂ : G} (h₁ : w₁ = 1 ∨ w₁ = u) (h₂ : w₂ = 1 ∨ w₂ = v) :
    w₁ * w₂ ∈ quadSet u v := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact ⟨(0, 0), by simp⟩
  · exact ⟨(0, 1), by simp⟩
  · exact ⟨(1, 0), by simp⟩
  · exact ⟨(1, 1), by simp⟩

theorem mul_mem_quadSet {u v w₁ w₂ : G} (huv : u * v = v * u) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (h₁ : w₁ ∈ quadSet u v) (h₂ : w₂ ∈ quadSet u v) : w₁ * w₂ ∈ quadSet u v := by
  obtain ⟨⟨i, j⟩, rfl⟩ := h₁
  obtain ⟨⟨k, l⟩, rfl⟩ := h₂
  refine ⟨(i + k, j + l), ?_⟩
  have hc : Commute (v ^ (j : ℕ)) (u ^ (k : ℕ)) := ((Commute.symm huv).pow_pow _ _)
  simp only [Fin.val_add]
  rw [← pow_eq_pow_mod _ hu, ← pow_eq_pow_mod _ hv]
  calc u ^ ((i : ℕ) + k) * v ^ ((j : ℕ) + l) = u ^ (i : ℕ) * (u ^ (k : ℕ) * v ^ (j : ℕ)) *
        v ^ (l : ℕ) := by rw [pow_add, pow_add]; group
    _ = u ^ (i : ℕ) * v ^ (j : ℕ) * (u ^ (k : ℕ) * v ^ (l : ℕ)) := by
        rw [← hc.eq]; group

theorem card_quadSet_le (u v : G) : Nat.card ↥(quadSet u v) ≤ 4 := by
  unfold quadSet
  calc Nat.card ↥(Set.range fun p : Fin 2 × Fin 2 => u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ)) ≤
        Nat.card (Fin 2 × Fin 2) := Finite.card_range_le _
    _ = 4 := by simp

instance (u v : G) : Finite ↥(quadSet u v) := Set.finite_range _ |>.to_subtype

theorem conj_mem_centralizer {Y : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (hc : c ∈ Subgroup.centralizer (Y : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (Y : Set G) :=
  (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer Y hg) c).mp hc

theorem conj_mem_of_mem_normalizer {Y : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hy : y ∈ Y) : g * y * g⁻¹ ∈ Y :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

@[expose] noncomputable def commHom {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) : ↥Y →* ↥Y where
  toFun y := ⟨a * y * a⁻¹ * (y : G)⁻¹, Y.mul_mem (conj_mem_of_mem_normalizer ha y.2)
    (Y.inv_mem y.2)⟩
  map_one' := by ext; simp
  map_mul' y₁ y₂ := by
    apply Subtype.ext
    have h₁ := conj_mem_of_mem_normalizer ha y₁.2
    have h₂ := conj_mem_of_mem_normalizer ha y₂.2
    have hc : (y₁ : G)⁻¹ * (a * y₂ * a⁻¹ * (y₂ : G)⁻¹) =
        (a * y₂ * a⁻¹ * (y₂ : G)⁻¹) * (y₁ : G)⁻¹ :=
      F7.isElemAbelian_comm hY (Y.inv_mem y₁.2) (Y.mul_mem h₂ (Y.inv_mem y₂.2))
    simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
    calc a * (y₁ * y₂ : G) * a⁻¹ * ((y₁ : G) * y₂)⁻¹ =
        a * y₁ * a⁻¹ * ((a * y₂ * a⁻¹ * (y₂ : G)⁻¹) * (y₁ : G)⁻¹) := by group
      _ = a * y₁ * a⁻¹ * ((y₁ : G)⁻¹ * (a * y₂ * a⁻¹ * (y₂ : G)⁻¹)) := by rw [hc]
      _ = a * y₁ * a⁻¹ * (y₁ : G)⁻¹ * (a * y₂ * a⁻¹ * (y₂ : G)⁻¹) := by group

theorem commHom_apply_coe {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    ((commHom hY ha y : ↥Y) : G) = a * y * a⁻¹ * (y : G)⁻¹ := rfl

theorem exists_transv_of_mQuot [Finite G] {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G))
    (h : E3.mQuot Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 1) :
    ∃ y₀ ∈ Y, ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀ := by
  classical
  have hker : (commHom hY ha).ker = (Y ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : a * y * a⁻¹ * (y : G)⁻¹ = 1 := by
        have := congrArg Subtype.val h1
        rwa [commHom_apply_coe] at this
      have h3 : a * y * a⁻¹ = y := mul_inv_eq_one.mp h2
      refine ⟨y.2, ?_⟩
      calc (y : G) * a = a * y * a⁻¹ * a := by rw [h3]
        _ = a * y := by group
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      rw [commHom_apply_coe, Subgroup.coe_one, ← h1]
      group
  have hcard : Nat.card (commHom hY ha).range ≤ 2 := by
    rw [← Subgroup.index_ker, hker]
    have h1 := E3.relIndex_eq_two_pow (F7.isPGroup_of_isElemAbelian hY)
      (Y ⊓ Subgroup.centralizer ({a} : Set G))
    rw [Subgroup.relIndex] at h1
    rw [h1]
    calc 2 ^ E3.mQuot Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 2 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) h
      _ = 2 := by norm_num
  by_cases hall : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1
  · exact ⟨1, Y.one_mem, fun y hy => Or.inl (hall y hy)⟩
  push Not at hall
  obtain ⟨y₁, hy₁, hne⟩ := hall
  refine ⟨a * y₁ * a⁻¹ * y₁⁻¹, (commHom hY ha ⟨y₁, hy₁⟩).2, fun y hy => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have : Fintype ↥(commHom hY ha).range := Fintype.ofFinite _
  let w₁ : ↥(commHom hY ha).range := ⟨commHom hY ha ⟨y₁, hy₁⟩, ⟨_, rfl⟩⟩
  let w : ↥(commHom hY ha).range := ⟨commHom hY ha ⟨y, hy⟩, ⟨_, rfl⟩⟩
  have hw₁ : ((w₁ : ↥Y) : G) = a * y₁ * a⁻¹ * y₁⁻¹ := commHom_apply_coe hY ha _
  have hw : ((w : ↥Y) : G) = a * y * a⁻¹ * y⁻¹ := commHom_apply_coe hY ha _
  have h1w : (1 : ↥(commHom hY ha).range) ≠ w := fun h0 => hc1 (by
    rw [← hw, ← h0]
    rfl)
  have h1w₁ : (1 : ↥(commHom hY ha).range) ≠ w₁ := fun h0 => hne (by
    rw [← hw₁, ← h0]
    rfl)
  have hww₁ : w ≠ w₁ := fun h0 => hc2 (by rw [← hw, ← hw₁, h0])
  have h3 : ({1, w, w₁} : Finset ↥(commHom hY ha).range).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1w, h1w₁]), Finset.card_pair hww₁]
  have h4 := Finset.card_le_univ ({1, w, w₁} : Finset ↥(commHom hY ha).range)
  rw [h3, Fintype.card_eq_nat_card] at h4
  omega

theorem mem_centralizer_of_conj_eq {Y : Subgroup G} {g : G} (h : ∀ y ∈ Y, g * y * g⁻¹ = y) :
    g ∈ Subgroup.centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * g = g * y * g⁻¹ * g := by rw [h y hy]
    _ = g * y := by group

theorem conj_eq_of_mem_centralizer {Y : Subgroup G} {c y : G}
    (hc : c ∈ Subgroup.centralizer (Y : Set G)) (hy : y ∈ Y) : c * y * c⁻¹ = y := by
  have h := Subgroup.mem_centralizer_iff.mp hc y hy
  calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [h]
    _ = y := by group

theorem sq_mem_centralizer_of_transv {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) :
    a ^ 2 ∈ Subgroup.centralizer (Y : Set G) := by
  have hsq : y₀ * y₀ = 1 := by
    have h := F7.isElemAbelian_pow_eq_one hY hy₀
    rwa [pow_two] at h
  have hfix : a * y₀ * a⁻¹ = y₀ := by
    rcases htr y₀ hy₀ with h | h
    · exact mul_inv_eq_one.mp h
    · have h1 : a * y₀ * a⁻¹ = 1 := by
        calc a * y₀ * a⁻¹ = (a * y₀ * a⁻¹ * y₀⁻¹) * y₀ := by group
          _ = y₀ * y₀ := by rw [h]
          _ = 1 := hsq
      have h2 : y₀ = 1 := by
        calc y₀ = a⁻¹ * (a * y₀ * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      rw [h1, h2]
  refine mem_centralizer_of_conj_eq fun y hy => ?_
  rcases htr y hy with h | h
  · have h1 : a * y * a⁻¹ = y := mul_inv_eq_one.mp h
    calc a ^ 2 * y * (a ^ 2)⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by rw [pow_two]; group
      _ = y := by rw [h1, h1]
  · have h1 : a * y * a⁻¹ = y₀ * y := by
      calc a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
        _ = y₀ * y := by rw [h]
    calc a ^ 2 * y * (a ^ 2)⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by rw [pow_two]; group
      _ = a * (y₀ * y) * a⁻¹ := by rw [h1]
      _ = (a * y₀ * a⁻¹) * (a * y * a⁻¹) := by group
      _ = y₀ * y₀ * y := by rw [hfix, h1, mul_assoc]
      _ = y := by rw [hsq, one_mul]

theorem inv_transv {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) :
    ∀ y ∈ Y, a⁻¹ * y * a * y⁻¹ = 1 ∨ a⁻¹ * y * a * y⁻¹ = y₀ := by
  intro y hy
  have hz : a⁻¹ * y * a ∈ Y := by
    simpa using conj_mem_of_mem_normalizer (inv_mem ha) hy
  have hinv : y₀⁻¹ = y₀ := by
    have h := F7.isElemAbelian_pow_eq_one hY hy₀
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have e : a⁻¹ * y * a * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by group
  rcases htr _ hz with h | h
  · left
    rw [e, h, inv_one]
  · right
    rw [e, h, hinv]

theorem mem_centralizer_of_inv {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a x y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (hy₀ : y₀ ∈ Y) (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hxr : x ^ r ∈ Subgroup.centralizer (Y : Set G))
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) :
    x ∈ Subgroup.centralizer (Y : Set G) := by
  set C := Subgroup.centralizer (Y : Set G) with hCdef
  have hYsq : ∀ y ∈ Y, y * y = 1 := fun y hy => by
    have h := F7.isElemAbelian_pow_eq_one hY hy
    rwa [pow_two] at h
  set y₁ := x * y₀ * x⁻¹ with hy₁def
  have hy₁ : y₁ ∈ Y := conj_mem_of_mem_normalizer hx hy₀
  have h₀₁ : y₁ * y₀ = y₀ * y₁ := F7.isElemAbelian_comm hY hy₁ hy₀
  have hsq₁ : y₁ ^ 2 = 1 := by rw [pow_two]; exact hYsq _ hy₁
  have hsq₀ : y₀ ^ 2 = 1 := by rw [pow_two]; exact hYsq _ hy₀
  have hQY : quadSet y₁ y₀ ⊆ Y := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Y.mul_mem (Y.pow_mem hy₁ _) (Y.pow_mem hy₀ _)
  have htr' := inv_transv hY ha hy₀ htr
  have key : ∀ y ∈ Y, x ^ 2 * y * (x ^ 2)⁻¹ * y⁻¹ ∈ quadSet y₁ y₀ := by
    intro y hy
    have hc := conj_eq_of_mem_centralizer hinv hy
    have hy' : a⁻¹ * y * a ∈ Y := by simpa using conj_mem_of_mem_normalizer (inv_mem ha) hy
    have hy'' : x⁻¹ * (a⁻¹ * y * a) * x ∈ Y := by
      simpa using conj_mem_of_mem_normalizer (inv_mem hx) hy'
    have e : x ^ 2 * y * (x ^ 2)⁻¹ * y⁻¹ =
        (x * (a * (x⁻¹ * (a⁻¹ * y * a) * x) * a⁻¹ * (x⁻¹ * (a⁻¹ * y * a) * x)⁻¹) * x⁻¹) *
          (a⁻¹ * y * a * y⁻¹) := by
      calc x ^ 2 * y * (x ^ 2)⁻¹ * y⁻¹ = x * a * x⁻¹ * a⁻¹ *
            ((a * x * a⁻¹ * x) * y * (a * x * a⁻¹ * x)⁻¹) * a * x * a⁻¹ * x⁻¹ * y⁻¹ := by
            rw [pow_two]; group
        _ = x * a * x⁻¹ * a⁻¹ * y * a * x * a⁻¹ * x⁻¹ * y⁻¹ := by rw [hc]
        _ = _ := by group
    rw [e]
    refine mem_quadSet_of ?_ (htr' y hy)
    rcases htr _ hy'' with h | h
    · left
      rw [h]
      group
    · right
      rw [h]
  have hstab : ∀ e ∈ quadSet y₁ y₀, x ^ 2 * e * (x ^ 2)⁻¹ ∈ quadSet y₁ y₀ := by
    intro e he
    have h1 := key e (hQY he)
    have e1 : x ^ 2 * e * (x ^ 2)⁻¹ = (x ^ 2 * e * (x ^ 2)⁻¹ * e⁻¹) * e := by group
    rw [e1]
    exact mul_mem_quadSet h₀₁ hsq₁ hsq₀ h1 he
  have hiter : ∀ e ∈ quadSet y₁ y₀, ∀ k : ℕ,
      (x ^ 2) ^ k * e * ((x ^ 2) ^ k)⁻¹ ∈ quadSet y₁ y₀ := by
    intro e he k
    induction k with
    | zero => simpa using he
    | succ k ih =>
      have e1 : (x ^ 2) ^ (k + 1) * e * ((x ^ 2) ^ (k + 1))⁻¹ =
          x ^ 2 * ((x ^ 2) ^ k * e * ((x ^ 2) ^ k)⁻¹) * (x ^ 2)⁻¹ := by
        rw [pow_succ']
        group
      rw [e1]
      exact hstab _ ih
  have hcent : ∀ e ∈ quadSet y₁ y₀, x ^ 2 ∈ Subgroup.centralizer ({e} : Set G) := by
    intro e he
    let f : Fin 5 → ↥(quadSet y₁ y₀) := fun k => ⟨_, hiter e he k⟩
    have : Fintype ↥(quadSet y₁ y₀) := Fintype.ofFinite _
    have hlt : Fintype.card ↥(quadSet y₁ y₀) < Fintype.card (Fin 5) := by
      rw [Fintype.card_fin, Fintype.card_eq_nat_card]
      have := card_quadSet_le y₁ y₀
      omega
    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
    have hfij' := congrArg Subtype.val hfij
    simp only [f] at hfij'
    obtain ⟨d, hd1, hd4, hd⟩ : ∃ d : ℕ, 1 ≤ d ∧ d ≤ 4 ∧
        (x ^ 2) ^ d * e * ((x ^ 2) ^ d)⁻¹ = e := by
      rcases lt_or_gt_of_ne hij with h | h
      · refine ⟨(j : ℕ) - i, by omega, by omega, ?_⟩
        have e1 : (x ^ 2) ^ (j : ℕ) = (x ^ 2) ^ (i : ℕ) * (x ^ 2) ^ ((j : ℕ) - i) := by
          rw [← pow_add]; congr 1; omega
        rw [e1] at hfij'
        have h2 : (x ^ 2) ^ ((j : ℕ) - i) * e * ((x ^ 2) ^ ((j : ℕ) - i))⁻¹ =
            ((x ^ 2) ^ (i : ℕ))⁻¹ * ((x ^ 2) ^ (i : ℕ) * (x ^ 2) ^ ((j : ℕ) - i) * e *
              ((x ^ 2) ^ (i : ℕ) * (x ^ 2) ^ ((j : ℕ) - i))⁻¹) * (x ^ 2) ^ (i : ℕ) := by group
        rw [h2, ← hfij']
        group
      · refine ⟨(i : ℕ) - j, by omega, by omega, ?_⟩
        have e1 : (x ^ 2) ^ (i : ℕ) = (x ^ 2) ^ (j : ℕ) * (x ^ 2) ^ ((i : ℕ) - j) := by
          rw [← pow_add]; congr 1; omega
        rw [e1] at hfij'
        have h2 : (x ^ 2) ^ ((i : ℕ) - j) * e * ((x ^ 2) ^ ((i : ℕ) - j))⁻¹ =
            ((x ^ 2) ^ (j : ℕ))⁻¹ * ((x ^ 2) ^ (j : ℕ) * (x ^ 2) ^ ((i : ℕ) - j) * e *
              ((x ^ 2) ^ (j : ℕ) * (x ^ 2) ^ ((i : ℕ) - j))⁻¹) * (x ^ 2) ^ (j : ℕ) := by group
        rw [h2, hfij']
        group
    have hmem_d : (x ^ 2) ^ d ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x ^ 2) ^ d * e = (x ^ 2) ^ d * e * ((x ^ 2) ^ d)⁻¹ * (x ^ 2) ^ d := by group
        _ = e * (x ^ 2) ^ d := by rw [hd]
    have hmem_r : (x ^ 2) ^ r ∈ Subgroup.centralizer ({e} : Set G) := by
      have h1 : (x ^ 2) ^ r = x ^ r * x ^ r := by rw [← pow_mul, mul_comm, pow_mul, pow_two]
      rw [h1, Subgroup.mem_centralizer_singleton_iff]
      have h2 := Subgroup.mem_centralizer_iff.mp hxr e (hQY he)
      calc x ^ r * x ^ r * e = x ^ r * (x ^ r * e) := by group
        _ = x ^ r * (e * x ^ r) := by rw [h2]
        _ = (x ^ r * e) * x ^ r := by group
        _ = (e * x ^ r) * x ^ r := by rw [h2]
        _ = e * (x ^ r * x ^ r) := by group
    have hg := pow_gcd_mem hmem_d hmem_r
    have hcop : Nat.gcd d r = 1 := by
      have h1 : ¬ r ∣ d := fun h => by
        have := Nat.le_of_dvd (by omega) h
        omega
      exact Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr h1))
    rwa [hcop, pow_one] at hg
  have hx4 : x ^ 4 ∈ C := by
    refine mem_centralizer_of_conj_eq fun y hy => ?_
    have hw := key y hy
    set w := x ^ 2 * y * (x ^ 2)⁻¹ * y⁻¹ with hwdef
    have hwc := Subgroup.mem_centralizer_singleton_iff.mp (hcent w hw)
    have hww : w * w = 1 := hYsq w (hQY hw)
    calc x ^ 4 * y * (x ^ 4)⁻¹ = x ^ 2 * (x ^ 2 * y * (x ^ 2)⁻¹) * (x ^ 2)⁻¹ := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; group
      _ = x ^ 2 * (w * y) * (x ^ 2)⁻¹ := by rw [hwdef]; group
      _ = (x ^ 2 * w * (x ^ 2)⁻¹) * (x ^ 2 * y * (x ^ 2)⁻¹) := by group
      _ = w * (w * y) := by
          rw [show x ^ 2 * w * (x ^ 2)⁻¹ = w by rw [hwc]; group, hwdef]; group
      _ = y := by rw [← mul_assoc, hww, one_mul]
  have hg := pow_gcd_mem hx4 hxr
  have hcop : Nat.gcd 4 r = 1 := by
    have h1 : ¬ r ∣ 4 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr h1))
  rwa [hcop, pow_one] at hg

theorem inv_mem_centralizer_commutator {Y : Subgroup G} {a z : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hz : z ∈ Subgroup.normalizer (Y : Set G))
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) :
    a * (z * a * z⁻¹ * a⁻¹) * a⁻¹ * (z * a * z⁻¹ * a⁻¹) ∈ Subgroup.centralizer (Y : Set G) := by
  have haz : a * z ∈ Subgroup.normalizer (Y : Set G) := mul_mem ha hz
  have hazi : a * z⁻¹ ∈ Subgroup.normalizer (Y : Set G) := mul_mem ha (inv_mem hz)
  have hc₃ := conj_mem_centralizer hazi (inv_mem ha2)
  have e : a * (z * a * z⁻¹ * a⁻¹) * a⁻¹ * (z * a * z⁻¹ * a⁻¹) =
      ((a * z) * ((a * z⁻¹) * (a ^ 2)⁻¹ * (a * z⁻¹)⁻¹) * (a * z)⁻¹) *
        ((a * z) * a ^ 2 * (a * z)⁻¹) := by
    rw [pow_two]; group
  rw [e]
  exact mul_mem (conj_mem_centralizer haz hc₃) (conj_mem_centralizer haz ha2)

end CFSG.Quasithin.Vol2.Ch11.SecG
