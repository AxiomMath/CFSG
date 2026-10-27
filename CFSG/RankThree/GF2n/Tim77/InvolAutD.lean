module

public import CFSG.RankThree.GF2n.Tim77.InvolAut

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open Subgroup

section Helpers

variable {G : Type} [Group G]

theorem invAutD_eq_one_of_sq_odd {x : G} {n : ℕ} (hn : Odd n) (h2 : x ^ 2 = 1)
    (hxn : x ^ n = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hn
  have h1 : x ^ (2 * q + 1) = x := by
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  calc x = x ^ (2 * q + 1) := h1.symm
    _ = 1 := hxn

theorem invAutD_conj_zpow {a r : G} (h : a * r * a⁻¹ = r⁻¹) (s : ℤ) :
    a * r ^ s * a⁻¹ = (r ^ s)⁻¹ := by
  rw [← inv_zpow, ← h, conj_zpow]

theorem invAutD_swap {a r : G} (h : a * r * a⁻¹ = r⁻¹) (s : ℤ) :
    a * r ^ s = (r ^ s)⁻¹ * a := by
  rw [← invAutD_conj_zpow h s]
  group

theorem invAutD_zpow_pow {r : G} {n : ℕ} (hn : r ^ n = 1) (j : ℤ) : (r ^ j) ^ n = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]

theorem invAutD_conj_inj (a X Y : G) : a * X * a⁻¹ = a * Y * a⁻¹ ↔ X = Y := by
  constructor
  · intro h
    calc X = a⁻¹ * (a * X * a⁻¹) * a := by group
      _ = a⁻¹ * (a * Y * a⁻¹) * a := by rw [h]
      _ = Y := by group
  · intro h
    rw [h]

end Helpers

section Sig

variable {G : Type} [Group G]

@[expose] def invAutDSig (r : G) (s : ℤ) (v : G) : G := r ^ s * v * (r ^ s)⁻¹

@[expose] def invAutDD (r : G) (s : ℤ) (v : G) : G :=
  invAutDSig r s v * invAutDSig r (-s) v

theorem invAutDSig_mul (r : G) (s : ℤ) (x y : G) :
    invAutDSig r s (x * y) = invAutDSig r s x * invAutDSig r s y := by
  unfold invAutDSig
  group

theorem invAutDSig_comp (r : G) (s t : ℤ) (v : G) :
    invAutDSig r s (invAutDSig r t v) = invAutDSig r (s + t) v := by
  unfold invAutDSig
  rw [zpow_add]
  group

theorem invAutDSig_zero (r v : G) : invAutDSig r 0 v = v := by
  unfold invAutDSig
  simp

theorem invAutDSig_mem {M : Subgroup G} {r : G}
    (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M) {v : G} (hv : v ∈ M) (s : ℤ) :
    invAutDSig r s v ∈ M :=
  hrM s v hv

theorem invAutDD_mem {M : Subgroup G} {r : G}
    (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M) {v : G} (hv : v ∈ M) (s : ℤ) :
    invAutDD r s v ∈ M :=
  M.mul_mem (invAutDSig_mem hrM hv s) (invAutDSig_mem hrM hv (-s))

theorem invAutDSig_conj_a {a r : G} (hara : a * r * a⁻¹ = r⁻¹) (s : ℤ) (v : G) :
    a * invAutDSig r s v * a⁻¹ = invAutDSig r (-s) (a * v * a⁻¹) := by
  have h1 : a * r ^ s * a⁻¹ = (r ^ s)⁻¹ := invAutD_conj_zpow hara s
  have h2 : a * (r ^ s)⁻¹ * a⁻¹ = r ^ s := by
    have h := invAutD_conj_zpow hara (-s)
    rwa [zpow_neg, inv_inv] at h
  unfold invAutDSig
  rw [zpow_neg]
  calc a * (r ^ s * v * (r ^ s)⁻¹) * a⁻¹
      = (a * r ^ s * a⁻¹) * (a * v * a⁻¹) * (a * (r ^ s)⁻¹ * a⁻¹) := by group
    _ = (r ^ s)⁻¹ * (a * v * a⁻¹) * r ^ s := by rw [h1, h2]
    _ = (r ^ s)⁻¹ * (a * v * a⁻¹) * ((r ^ s)⁻¹)⁻¹ := by rw [inv_inv]

theorem invAutDSig_conj_r (r : G) (s : ℤ) (v : G) :
    r * invAutDSig r s v * r⁻¹ = invAutDSig r s (r * v * r⁻¹) := by
  have hc : Commute r (r ^ s) := Commute.self_zpow r s
  have hc' : Commute r⁻¹ (r ^ s)⁻¹ := hc.inv_inv
  unfold invAutDSig
  calc r * (r ^ s * v * (r ^ s)⁻¹) * r⁻¹
      = (r * r ^ s) * v * ((r ^ s)⁻¹ * r⁻¹) := by group
    _ = (r ^ s * r) * v * (r⁻¹ * (r ^ s)⁻¹) := by rw [hc.eq, hc'.eq]
    _ = r ^ s * (r * v * r⁻¹) * (r ^ s)⁻¹ := by group

theorem invAutDSig_conj (u r : G) (s : ℤ) (v : G) (hv : u * v * u⁻¹ = v) :
    u * invAutDSig r s v * u⁻¹ = invAutDSig (u * r * u⁻¹) s v := by
  have h : (u * r * u⁻¹) ^ s = u * r ^ s * u⁻¹ := conj_zpow
  unfold invAutDSig
  calc u * (r ^ s * v * (r ^ s)⁻¹) * u⁻¹
      = (u * r ^ s * u⁻¹) * (u * v * u⁻¹) * (u * r ^ s * u⁻¹)⁻¹ := by group
    _ = (u * r ^ s * u⁻¹) * v * (u * r ^ s * u⁻¹)⁻¹ := by rw [hv]
    _ = (u * r * u⁻¹) ^ s * v * ((u * r * u⁻¹) ^ s)⁻¹ := by rw [h]

theorem invAutDD_conj (u r : G) (s : ℤ) (v : G) (hv : u * v * u⁻¹ = v) :
    u * invAutDD r s v * u⁻¹ = invAutDD (u * r * u⁻¹) s v := by
  unfold invAutDD
  calc u * (invAutDSig r s v * invAutDSig r (-s) v) * u⁻¹
      = (u * invAutDSig r s v * u⁻¹) * (u * invAutDSig r (-s) v * u⁻¹) := by group
    _ = invAutDSig (u * r * u⁻¹) s v * invAutDSig (u * r * u⁻¹) (-s) v := by
        rw [invAutDSig_conj u r s v hv, invAutDSig_conj u r (-s) v hv]

theorem invAutDD_conj_a {M : Subgroup G} {a r : G} (hara : a * r * a⁻¹ = r⁻¹)
    (haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M) (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (s : ℤ) {v : G} (hv : v ∈ M) :
    invAutDD r s (a * v * a⁻¹) = a * invAutDD r s v * a⁻¹ := by
  have hw : a * v * a⁻¹ ∈ M := haM v hv
  have e : a * invAutDD r s v * a⁻¹
      = (a * invAutDSig r s v * a⁻¹) * (a * invAutDSig r (-s) v * a⁻¹) := by
    unfold invAutDD
    group
  rw [e, invAutDSig_conj_a hara s v, invAutDSig_conj_a hara (-s) v, neg_neg]
  unfold invAutDD
  exact hMc _ (invAutDSig_mem hrM hw s) _ (invAutDSig_mem hrM hw (-s))

theorem invAutDD_conj_r (r : G) (s : ℤ) (v : G) :
    invAutDD r s (r * v * r⁻¹) = r * invAutDD r s v * r⁻¹ := by
  unfold invAutDD
  rw [← invAutDSig_conj_r r s v, ← invAutDSig_conj_r r (-s) v]
  group

theorem invAutDD_mul {M : Subgroup G} {r : G}
    (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (s : ℤ) {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    invAutDD r s (x * y) = invAutDD r s x * invAutDD r s y := by
  have hc : invAutDSig r (-s) x * invAutDSig r s y = invAutDSig r s y * invAutDSig r (-s) x :=
    hMc _ (invAutDSig_mem hrM hx (-s)) _ (invAutDSig_mem hrM hy s)
  unfold invAutDD
  rw [invAutDSig_mul, invAutDSig_mul]
  calc invAutDSig r s x * invAutDSig r s y * (invAutDSig r (-s) x * invAutDSig r (-s) y)
      = invAutDSig r s x * (invAutDSig r s y * invAutDSig r (-s) x) * invAutDSig r (-s) y := by
        group
    _ = invAutDSig r s x * (invAutDSig r (-s) x * invAutDSig r s y) * invAutDSig r (-s) y := by
        rw [hc]
    _ = invAutDSig r s x * invAutDSig r (-s) x * (invAutDSig r s y * invAutDSig r (-s) y) := by
        group

theorem invAutDD_twist {M : Subgroup G} {r : G}
    (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) {k : ℤ} {m₀ v : G} (hm₀ : m₀ ∈ M) (hv : v ∈ M) :
    invAutDD (r ^ k * m₀) 1 v = invAutDD r k v := by
  have hY : (r ^ k)⁻¹ * v * r ^ k ∈ M := by
    have h := hrM (-k) v hv
    rwa [zpow_neg, inv_inv] at h
  have hm0v : m₀ * v * m₀⁻¹ = v := by
    rw [hMc m₀ hm₀ v hv]
    group
  have e1 : (r ^ k * m₀) * v * (r ^ k * m₀)⁻¹ = r ^ k * v * (r ^ k)⁻¹ := by
    rw [mul_inv_rev]
    calc r ^ k * m₀ * v * (m₀⁻¹ * (r ^ k)⁻¹) = r ^ k * (m₀ * v * m₀⁻¹) * (r ^ k)⁻¹ := by
          group
      _ = r ^ k * v * (r ^ k)⁻¹ := by rw [hm0v]
  have e2 : (r ^ k * m₀)⁻¹ * v * (r ^ k * m₀) = (r ^ k)⁻¹ * v * r ^ k := by
    have hYm : (r ^ k)⁻¹ * v * r ^ k * m₀ = m₀ * ((r ^ k)⁻¹ * v * r ^ k) :=
      hMc _ hY m₀ hm₀
    calc (r ^ k * m₀)⁻¹ * v * (r ^ k * m₀)
        = m₀⁻¹ * ((r ^ k)⁻¹ * v * r ^ k) * m₀ := by group
      _ = m₀⁻¹ * (m₀ * ((r ^ k)⁻¹ * v * r ^ k)) := by rw [← hYm]; group
      _ = (r ^ k)⁻¹ * v * r ^ k := by group
  unfold invAutDD invAutDSig
  simp only [zpow_one, zpow_neg, inv_inv]
  rw [e1, e2]

end Sig

section Setup

variable {G : Type} [Group G] {A Ab L Lb M : Subgroup G}

theorem invAutD_mem_or_mem {K H : Subgroup G} (hK : H.relIndex K = 2) {a y : G} (ha : a ∈ K)
    (haH : a ∉ H) (hy : y ∈ K) : y ∈ H ∨ a⁻¹ * y ∈ H := by
  by_cases hyH : y ∈ H
  · exact Or.inl hyH
  refine Or.inr ?_
  have haH' : a⁻¹ ∉ H := fun h' => haH (by simpa using H.inv_mem h')
  have h := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) hK
    (a := ⟨a⁻¹, K.inv_mem ha⟩) (b := ⟨y, hy⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mk] at h
  exact h.mpr (by simp [haH', hyH])

theorem invAutD_closure_pred {T : Set G} {Q : G → Prop} (h1 : Q 1) (hgen : ∀ x ∈ T, Q x)
    (hmul : ∀ x y, x ∈ Subgroup.closure T → y ∈ Subgroup.closure T → Q x → Q y → Q (x * y))
    (hinv : ∀ x, x ∈ Subgroup.closure T → Q x → Q x⁻¹) :
    ∀ x ∈ Subgroup.closure T, Q x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact h1
  | mul x y hx hy ihx ihy => exact hmul x y hx hy ihx ihy
  | inv x hx ih => exact hinv x hx ih

theorem invAutD_conj_mem' {N : Subgroup G} {y z : G} (hy : y ∈ Subgroup.normalizer (N : Set G))
    (hz : z ∈ N) : y * z * y⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp hy z).mp hz

theorem invAutD_conj_inv_mem' {N : Subgroup G} {y z : G}
    (hy : y ∈ Subgroup.normalizer (N : Set G)) (hz : z ∈ N) : y⁻¹ * z * y ∈ N := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) z).mp hz
  simpa using h

theorem invAutD_le_closure [Finite G] (S : Prop24Setup A Ab L Lb M) (hrel : L.relIndex A = 2)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb) :
    A ⊔ Ab ≤ Subgroup.closure ({a, a * b} ∪ (M : Set G)) := by
  have ha' : a ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) :=
    Subgroup.subset_closure (Or.inl (Set.mem_insert _ _))
  have hr' : a * b ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) :=
    Subgroup.subset_closure (Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hbT : b ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) := by
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') hr'
  have hLc : ∀ y ∈ L, y ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) := fun y hy =>
    Subgroup.subset_closure (Or.inr (S.L_le_M hy))
  have hLbc : ∀ y ∈ Lb, y ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) := fun y hy =>
    Subgroup.subset_closure (Or.inr (S.Lb_le_M hy))
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · rcases invAutD_mem_or_mem hrel ha haL hy with h | h
    · exact hLc y h
    · simpa using Subgroup.mul_mem _ ha' (hLc _ h)
  · rcases invAutD_mem_or_mem (S.relIndex_Lb.trans hrel) hb hbL hy with h | h
    · exact hLbc y h
    · simpa using Subgroup.mul_mem _ hbT (hLbc _ h)

theorem invAutD_rM [Finite G] (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A)
    (hb : b ∈ Ab) : ∀ j : ℤ, ∀ m ∈ M, (a * b) ^ j * m * ((a * b) ^ j)⁻¹ ∈ M := by
  have hrN : a * b ∈ Subgroup.normalizer (M : Set G) :=
    S.sup_le_normalizer_M
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))
  intro j m hm
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hrN j) m).mp hm

end Setup

section NormalForm

variable {G : Type} [Group G] {r : G}

theorem invAutD_N_mul {M : Subgroup G} (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    {x y : G} (hx : ∃ i : ℤ, ∃ m ∈ M, x = r ^ i * m) (hy : ∃ i : ℤ, ∃ m ∈ M, y = r ^ i * m) :
    ∃ i : ℤ, ∃ m ∈ M, x * y = r ^ i * m := by
  obtain ⟨i, m, hm, rfl⟩ := hx
  obtain ⟨j, m', hm', rfl⟩ := hy
  refine ⟨i + j, (r ^ j)⁻¹ * m * r ^ j * m', ?_, ?_⟩
  · have h1 : (r ^ j)⁻¹ * m * r ^ j ∈ M := by
      have h := hrM (-j) m hm
      rwa [zpow_neg, inv_inv] at h
    exact M.mul_mem h1 hm'
  · rw [zpow_add]
    group

theorem invAutD_N_inv {M : Subgroup G} (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    {x : G} (hx : ∃ i : ℤ, ∃ m ∈ M, x = r ^ i * m) :
    ∃ i : ℤ, ∃ m ∈ M, x⁻¹ = r ^ i * m := by
  obtain ⟨i, m, hm, rfl⟩ := hx
  refine ⟨-i, r ^ i * m⁻¹ * (r ^ i)⁻¹, hrM i m⁻¹ (M.inv_mem hm), ?_⟩
  rw [zpow_neg]
  group

theorem invAutD_N_conj {a : G} {M : Subgroup G} (hara : a * r * a⁻¹ = r⁻¹)
    (haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M) {x : G} (hx : ∃ i : ℤ, ∃ m ∈ M, x = r ^ i * m) :
    ∃ i : ℤ, ∃ m ∈ M, a * x * a⁻¹ = r ^ i * m := by
  obtain ⟨i, m, hm, rfl⟩ := hx
  refine ⟨-i, a * m * a⁻¹, haM m hm, ?_⟩
  rw [zpow_neg, ← invAutD_conj_zpow hara i]
  group

theorem invAutD_normal_form {a : G} {M : Subgroup G} (ha2 : a * a = 1)
    (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M) (hara : a * r * a⁻¹ = r⁻¹)
    (haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M) :
    ∀ x ∈ Subgroup.closure ({a, r} ∪ (M : Set G)),
      (∃ i : ℤ, ∃ m ∈ M, x = r ^ i * m) ∨ (∃ i : ℤ, ∃ m ∈ M, a * x = r ^ i * m) := by
  have hainv : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha2, inv_one]
  refine invAutD_closure_pred (Q := fun x => (∃ i : ℤ, ∃ m ∈ M, x = r ^ i * m) ∨
    (∃ i : ℤ, ∃ m ∈ M, a * x = r ^ i * m)) ?_ ?_ ?_ ?_
  · exact Or.inl ⟨0, 1, M.one_mem, by simp⟩
  · rintro x ((hx | hx) | hx)
    · refine Or.inr ⟨0, 1, M.one_mem, ?_⟩
      rw [hx, ha2]
      simp
    · refine Or.inl ⟨1, 1, M.one_mem, ?_⟩
      rw [hx, zpow_one, mul_one]
    · exact Or.inl ⟨0, x, hx, by simp⟩
  · intro x y _ _ hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (invAutD_N_mul hrM hx hy)
    ·
      obtain ⟨i, m, hm, hxa⟩ := invAutD_N_conj hara haM hx
      obtain ⟨j, m', hm', hyy⟩ := invAutD_N_mul hrM ⟨i, m, hm, hxa⟩ hy
      refine Or.inr ⟨j, m', hm', ?_⟩
      rw [← hyy]
      group
    ·
      obtain ⟨i, m, hm, h⟩ := invAutD_N_mul hrM hx hy
      refine Or.inr ⟨i, m, hm, ?_⟩
      rw [← mul_assoc]
      exact h
    ·
      obtain ⟨i, m, hm, hxa⟩ := invAutD_N_conj hara haM hx
      have hxy : x * y = (a * (a * x) * a⁻¹) * (a * y) := by
        calc x * y = (a * a) * x * (a⁻¹ * a) * y := by
              rw [ha2, inv_mul_cancel, one_mul, mul_one]
          _ = (a * (a * x) * a⁻¹) * (a * y) := by group
      obtain ⟨j, m', hm', hyy⟩ := invAutD_N_mul hrM ⟨i, m, hm, hxa⟩ hy
      refine Or.inl ⟨j, m', hm', ?_⟩
      rw [hxy]
      exact hyy
  · intro x _ hx
    rcases hx with hx | hx
    · exact Or.inl (invAutD_N_inv hrM hx)
    ·
      obtain ⟨i, m, hm, h⟩ := invAutD_N_inv hrM hx
      obtain ⟨j, m', hm', h'⟩ := invAutD_N_conj hara haM ⟨i, m, hm, h⟩
      refine Or.inr ⟨j, m', hm', ?_⟩
      rw [← h']
      calc a * x⁻¹ = a * x⁻¹ * (a⁻¹ * a⁻¹) := by rw [hainv, mul_one]
        _ = a * (a * x)⁻¹ * a⁻¹ := by rw [mul_inv_rev]; group

theorem invAutD_mem_of_form {M : Subgroup G} {n : ℕ} (hMe : ∀ m ∈ M, m * m = 1)
    (hodd : Odd n) (hrn : r ^ n = 1) (hrM : ∀ j : ℤ, ∀ m ∈ M, r ^ j * m * (r ^ j)⁻¹ ∈ M)
    {i : ℤ} {m : G} (hm : m ∈ M) (hx : (r ^ i * m) * (r ^ i * m) = 1) : r ^ i * m ∈ M := by
  have hE : r ^ i * m * r ^ i = m := by
    calc r ^ i * m * r ^ i = (r ^ i * m * (r ^ i * m)) * m := by
          rw [show (r ^ i * m * (r ^ i * m)) * m = r ^ i * m * r ^ i * (m * m) by group,
            hMe m hm, mul_one]
      _ = m := by rw [hx, one_mul]
  have key : r ^ i * m * (r ^ i)⁻¹ * m = r ^ i * r ^ i := by
    calc r ^ i * m * (r ^ i)⁻¹ * m = r ^ i * m * (r ^ i)⁻¹ * (r ^ i * m * r ^ i) := by
          rw [hE]
      _ = r ^ i * (m * m) * r ^ i := by group
      _ = r ^ i * r ^ i := by rw [hMe m hm, mul_one]
  have hsq : r ^ i * r ^ i ∈ M := by
    rw [← key]
    exact M.mul_mem (hrM i m hm) hm
  have hy1 : r ^ i * r ^ i = 1 := by
    apply invAutD_eq_one_of_sq_odd hodd
    · rw [sq]
      exact hMe _ hsq
    · have h := invAutD_zpow_pow hrn (i + i)
      rwa [zpow_add] at h
  have hi1 : r ^ i = 1 := by
    apply invAutD_eq_one_of_sq_odd hodd
    · rw [sq]
      exact hy1
    · exact invAutD_zpow_pow hrn i
  rw [hi1, one_mul]
  exact hm

end NormalForm

section Rot

variable {G : Type} [Group G] {A Ab L Lb M : Subgroup G}

theorem invAutD_rot_fix [Finite G] (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A)
    (haL : a ∉ L) (hb : b ∈ Ab) {n : ℕ} (hodd : Odd n) (hrn : (a * b) ^ n = 1) {j : ℤ}
    (hj : (a * b) ^ j ≠ 1) {v : G} (hv : v ∈ M) (hvc : (a * b) ^ j * v = v * (a * b) ^ j) :
    v = 1 := by
  obtain ⟨q, hq⟩ := hodd
  have ha2 : a * a = 1 := S.sq_A ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : b * b = 1 := S.sq_Ab hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have haa : a⁻¹ * a⁻¹ = 1 := by rw [hainv, ha2]
  have hara : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, mul_inv_rev, hbinv, hainv, ← mul_assoc, ha2, one_mul]
  have hsw : ∀ s : ℤ, a * (a * b) ^ s = ((a * b) ^ s)⁻¹ * a := fun s => invAutD_swap hara s
  have hca : (a * b) ^ j * a = a * ((a * b) ^ j)⁻¹ := by
    have h := hsw (-j)
    rw [zpow_neg, inv_inv] at h
    exact h.symm
  obtain ⟨i, hi⟩ : ∃ i : ℤ, i = -(j * ((q : ℤ) + 1)) := ⟨_, rfl⟩
  have hexp : -(i + i) = j + j * (n : ℤ) := by
    rw [hi, hq]
    push_cast
    ring
  have hpow : (a * b) ^ (j + j * (n : ℤ)) = (a * b) ^ j := by
    rw [zpow_add, zpow_mul, zpow_natCast, invAutD_zpow_pow hrn j, mul_one]
  have e1 : a * ((a * b) ^ i)⁻¹ = (a * b) ^ i * a := by
    rw [← zpow_neg, hsw (-i), zpow_neg, inv_inv]
  have e2 : (a * b) ^ (i + i) * a = a * (a * b) ^ j := by
    have h := hsw (-(i + i))
    rw [zpow_neg, inv_inv] at h
    rw [← h, ← zpow_neg, hexp, hpow]
  have hgg : (a * b) ^ i * a * ((a * b) ^ i)⁻¹ = a * (a * b) ^ j := by
    rw [mul_assoc, e1, ← mul_assoc, ← zpow_add]
    exact e2
  have hgt : ((a * b) ^ i)⁻¹ * (a * (a * b) ^ j) * (a * b) ^ i = a := by
    rw [← hgg]
    group
  have hra : a * b ∈ A ⊔ Ab :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hgX : (a * b) ^ i ∈ A ⊔ Ab := Subgroup.zpow_mem _ hra i
  have hne : conjSubgroup ((a * b) ^ i) A ≠ A := by
    intro h
    have hmemA : a * (a * b) ^ j ∈ A := by
      rw [← h, mem_conjSubgroup, hgt]
      exact ha
    have hcA : (a * b) ^ j ∈ A := by
      have h' := A.mul_mem (A.inv_mem ha) hmemA
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h'
    have hsq : ((a * b) ^ j) ^ 2 = 1 := by
      rw [sq]
      exact S.sq_A hcA
    exact hj (invAutD_eq_one_of_sq_odd ⟨q, hq⟩ hsq (invAutD_zpow_pow hrn j))
  have S' := S.setup_conj hgX hne
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy => S.comm_M hx hy
  have hconjA : ∀ x, a * (a * x * a⁻¹) * a⁻¹ = x := fun x => by
    calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a⁻¹ * a⁻¹) := by group
      _ = x := by rw [ha2, haa, one_mul, mul_one]
  have hav : a * v * a⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) v).mp hv
  have hw : v * (a * v * a⁻¹) ∈ M := M.mul_mem hv hav
  have hwa : a * (v * (a * v * a⁻¹)) * a⁻¹ = v * (a * v * a⁻¹) := by
    calc a * (v * (a * v * a⁻¹)) * a⁻¹
        = (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) := by group
      _ = (a * v * a⁻¹) * v := by rw [hconjA v]
      _ = v * (a * v * a⁻¹) := S.comm_M hav hv
  have haw : a * (v * (a * v * a⁻¹)) = (v * (a * v * a⁻¹)) * a := by
    calc a * (v * (a * v * a⁻¹)) = a * (v * (a * v * a⁻¹)) * a⁻¹ * a := by group
      _ = (v * (a * v * a⁻¹)) * a := by rw [hwa]
  have hwL : v * (a * v * a⁻¹) ∈ L := S.mem_L_of_commute_M ha haL hw haw
  have hcv : (a * b) ^ j * v * ((a * b) ^ j)⁻¹ = v := by
    rw [hvc]
    group
  have hcinv : ((a * b) ^ j)⁻¹ * v * (a * b) ^ j = v := by
    calc ((a * b) ^ j)⁻¹ * v * (a * b) ^ j = ((a * b) ^ j)⁻¹ * (v * (a * b) ^ j) := by group
      _ = ((a * b) ^ j)⁻¹ * ((a * b) ^ j * v) := by rw [hvc]
      _ = v := by group
  have hcav : (a * b) ^ j * (a * v * a⁻¹) * ((a * b) ^ j)⁻¹ = a * v * a⁻¹ := by
    calc (a * b) ^ j * (a * v * a⁻¹) * ((a * b) ^ j)⁻¹
        = ((a * b) ^ j * a) * v * ((a * b) ^ j * a)⁻¹ := by group
      _ = (a * ((a * b) ^ j)⁻¹) * v * (a * ((a * b) ^ j)⁻¹)⁻¹ := by rw [hca]
      _ = a * (((a * b) ^ j)⁻¹ * v * (a * b) ^ j) * a⁻¹ := by group
      _ = a * v * a⁻¹ := by rw [hcinv]
  have hcw : (a * b) ^ j * (v * (a * v * a⁻¹)) * ((a * b) ^ j)⁻¹ = v * (a * v * a⁻¹) := by
    calc (a * b) ^ j * (v * (a * v * a⁻¹)) * ((a * b) ^ j)⁻¹
        = ((a * b) ^ j * v * ((a * b) ^ j)⁻¹)
          * ((a * b) ^ j * (a * v * a⁻¹) * ((a * b) ^ j)⁻¹) := by
          group
      _ = v * (a * v * a⁻¹) := by rw [hcv, hcav]
  have hcw_comm : (a * b) ^ j * (v * (a * v * a⁻¹)) = (v * (a * v * a⁻¹)) * (a * b) ^ j := by
    calc (a * b) ^ j * (v * (a * v * a⁻¹))
        = (a * b) ^ j * (v * (a * v * a⁻¹)) * ((a * b) ^ j)⁻¹ * (a * b) ^ j := by group
      _ = (v * (a * v * a⁻¹)) * (a * b) ^ j := by rw [hcw]
  have htw : a * (a * b) ^ j * (v * (a * v * a⁻¹))
      = (v * (a * v * a⁻¹)) * (a * (a * b) ^ j) := by
    calc a * (a * b) ^ j * (v * (a * v * a⁻¹))
        = a * ((a * b) ^ j * (v * (a * v * a⁻¹))) := by group
      _ = a * ((v * (a * v * a⁻¹)) * (a * b) ^ j) := by rw [hcw_comm]
      _ = (a * (v * (a * v * a⁻¹))) * (a * b) ^ j := by group
      _ = ((v * (a * v * a⁻¹)) * a) * (a * b) ^ j := by rw [haw]
      _ = (v * (a * v * a⁻¹)) * (a * (a * b) ^ j) := by group
  have htA : a * (a * b) ^ j ∈ conjSubgroup ((a * b) ^ i) A :=
    mem_conjSubgroup.mpr (by rw [hgt]; exact ha)
  have htL : a * (a * b) ^ j ∉ conjSubgroup ((a * b) ^ i) L := fun h => haL (by
    have h' := mem_conjSubgroup.mp h
    rw [hgt] at h'
    exact h')
  have hwg : v * (a * v * a⁻¹) ∈ conjSubgroup ((a * b) ^ i) L :=
    S'.symm.mem_L_of_commute_M htA htL (Subgroup.mem_sup_left hwL) htw
  have hwA : v * (a * v * a⁻¹) ∈ conjSubgroup ((a * b) ^ i) A :=
    mem_conjSubgroup.mpr (S.L_le (mem_conjSubgroup.mp hwg))
  have hw1 : v * (a * v * a⁻¹) = 1 := by
    have hmem : v * (a * v * a⁻¹) ∈ A ⊓ conjSubgroup ((a * b) ^ i) A :=
      Subgroup.mem_inf.mpr ⟨S.L_le hwL, hwA⟩
    rw [S'.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hav2 : a * v * a⁻¹ = v := by
    have h1 : a * v * a⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_right hw1
    have hvv : v * v = 1 := S.mem_M_sq hv
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hvv
  have hav_comm : a * v = v * a := by
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [hav2]
  have hvL : v ∈ L := S.mem_L_of_commute_M ha haL hv hav_comm
  have htv : a * (a * b) ^ j * v = v * (a * (a * b) ^ j) := by
    calc a * (a * b) ^ j * v = a * ((a * b) ^ j * v) := by group
      _ = a * (v * (a * b) ^ j) := by rw [hvc]
      _ = (a * v) * (a * b) ^ j := by group
      _ = (v * a) * (a * b) ^ j := by rw [hav_comm]
      _ = v * (a * (a * b) ^ j) := by group
  have hvg : v ∈ conjSubgroup ((a * b) ^ i) L :=
    S'.symm.mem_L_of_commute_M htA htL (Subgroup.mem_sup_left hvL) htv
  have hvA : v ∈ conjSubgroup ((a * b) ^ i) A :=
    mem_conjSubgroup.mpr (S.L_le (mem_conjSubgroup.mp hvg))
  have hmem : v ∈ A ⊓ conjSubgroup ((a * b) ^ i) A :=
    Subgroup.mem_inf.mpr ⟨S.L_le hvL, hvA⟩
  rw [S'.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact hmem

end Rot

section Main

variable {G : Type} [Group G] {A Ab L Lb M : Subgroup G}

theorem invAutD_conj_rot [Finite G] (S : Prop24Setup A Ab L Lb M) (hrel : L.relIndex A = 2)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb) {n : ℕ} (hodd : Odd n)
    (hrn : (a * b) ^ n = 1) {u : G} (hu : conjSubgroup u (A ⊔ Ab) = A ⊔ Ab)
    (hC : u ∈ centralizer (A : Set G)) (hMu : conjSubgroup u M = M) :
    ∃ k : ℤ, ∃ m₀ ∈ M, u * (a * b) * u⁻¹ = (a * b) ^ k * m₀ := by
  have hrM := invAutD_rM S ha hb
  have ha2 : a * a = 1 := S.sq_A ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : b * b = 1 := S.sq_Ab hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hara : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, mul_inv_rev, hbinv, hainv, ← mul_assoc, ha2, one_mul]
  have haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) m).mp hm
  have hMe : ∀ m ∈ M, m * m = 1 := fun m hm => S.mem_M_sq hm
  have hC' : ∀ x ∈ A, u * x * u⁻¹ = x := fun x hx => by
    rw [(Subgroup.mem_centralizer_iff.mp hC x hx).symm]
    group
  have hua : u * a * u⁻¹ = a := hC' a ha
  have huMi : ∀ m ∈ M, u⁻¹ * m * u ∈ M := fun m hm => invAut_conj_inv_mem hMu hm
  have hXu : ∀ x ∈ A ⊔ Ab, u * x * u⁻¹ ∈ A ⊔ Ab := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_conjSubgroup_eq hu) x).mp hx
  have hbX : b ∈ A ⊔ Ab := Subgroup.mem_sup_right hb
  have hx2 : u * b * u⁻¹ * (u * b * u⁻¹) = 1 := by
    calc u * b * u⁻¹ * (u * b * u⁻¹) = u * (b * b) * u⁻¹ := by group
      _ = 1 := by rw [hb2, mul_one, mul_inv_cancel]
  have hxM : u * b * u⁻¹ ∉ M := by
    intro hxM
    have hbM : b ∈ M := by
      have h := huMi _ hxM
      have e : u⁻¹ * (u * b * u⁻¹) * u = b := by group
      rw [e] at h
      exact h
    have hb' : b ∈ Ab ⊓ M := Subgroup.mem_inf.mpr ⟨hb, hbM⟩
    rw [S.symm.inf_M] at hb'
    exact hbL hb'
  have hcl : u * b * u⁻¹ ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) :=
    invAutD_le_closure S hrel ha haL hb hbL (hXu b hbX)
  rcases invAutD_normal_form ha2 hrM hara haM _ hcl with ⟨i, m, hm, hx⟩ | ⟨i, m, hm, hax⟩
  · have hxm : (a * b) ^ i * m ∈ M := by
      apply invAutD_mem_of_form hMe hodd hrn hrM hm
      rw [← hx]
      exact hx2
    rw [← hx] at hxm
    exact absurd hxm hxM
  · refine ⟨i, m, hm, ?_⟩
    calc u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
      _ = a * (u * b * u⁻¹) := by rw [hua]
      _ = (a * b) ^ i * m := hax

theorem invAutD_defect [Finite G] (S : Prop24Setup A Ab L Lb M) (hrel : L.relIndex A = 2)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    {u : G} (hu : conjSubgroup u (A ⊔ Ab) = A ⊔ Ab) (hC : u ∈ centralizer (A : Set G))
    {k : ℤ} {m₀ : G} (hm₀ : m₀ ∈ M) (hR : u * (a * b) * u⁻¹ = (a * b) ^ k * m₀) :
    ∀ v ∈ M, invAutDD (a * b) k v = invAutDD (a * b) 1 v := by
  have hrM := invAutD_rM S ha hb
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy => S.comm_M hx hy
  have ha2 : a * a = 1 := S.sq_A ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : b * b = 1 := S.sq_Ab hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hara : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, mul_inv_rev, hbinv, hainv, ← mul_assoc, ha2, one_mul]
  have haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) m).mp hm
  have hC' : ∀ x ∈ A, u * x * u⁻¹ = x := fun x hx => by
    rw [(Subgroup.mem_centralizer_iff.mp hC x hx).symm]
    group
  have hcl : Subgroup.closure ({a, a * b} ∪ (M : Set G)) ≤ Subgroup.normalizer (M : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ((hx | hx) | hx)
    · rw [hx]
      exact S.A_le_normalizer_M ha
    · rw [hx]
      exact S.sup_le_normalizer_M
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))
    · exact Subgroup.le_normalizer hx
  have hΨ : ∀ x ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)), ∀ v ∈ M,
      (invAutDD (a * b) k v = invAutDD (a * b) 1 v ↔
        invAutDD (a * b) k (x * v * x⁻¹) = invAutDD (a * b) 1 (x * v * x⁻¹)) := by
    refine invAutD_closure_pred (Q := fun x => ∀ v ∈ M,
      (invAutDD (a * b) k v = invAutDD (a * b) 1 v ↔
        invAutDD (a * b) k (x * v * x⁻¹) = invAutDD (a * b) 1 (x * v * x⁻¹))) ?_ ?_ ?_ ?_
    · intro v _
      simp
    · rintro x ((hx | hx) | hx) v hv
      · rw [hx, invAutDD_conj_a hara haM hrM hMc k hv, invAutDD_conj_a hara haM hrM hMc 1 hv]
        exact (invAutD_conj_inj a _ _).symm
      · rw [hx, invAutDD_conj_r (a * b) k v, invAutDD_conj_r (a * b) 1 v]
        exact (invAutD_conj_inj (a * b) _ _).symm
      · have e : x * v * x⁻¹ = v := by
          rw [hMc x hx v hv]
          group
        rw [e]
    · intro x y hx hy hQx hQy v hv
      have hyv : y * v * y⁻¹ ∈ M := invAutD_conj_mem' (hcl hy) hv
      have hxyv : (x * y) * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ := by group
      rw [hxyv]
      exact (hQy v hv).trans (hQx _ hyv)
    · intro x hx hQx v hv
      have hv' : x⁻¹ * v * x ∈ M := invAutD_conj_inv_mem' (hcl hx) hv
      have e : x * (x⁻¹ * v * x) * x⁻¹ = v := by group
      have h := hQx _ hv'
      rw [e] at h
      rw [inv_inv]
      exact h.symm
  obtain ⟨k₀, hk₀, hLb⟩ := sec34_exists_k S
  have hk₀cl : k₀ ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) :=
    invAutD_le_closure S hrel ha haL hb hbL hk₀
  have hL : ∀ v ∈ L, invAutDD (a * b) k v = invAutDD (a * b) 1 v := by
    intro v hv
    have hvA : v ∈ A := S.L_le hv
    have hvM : v ∈ M := S.L_le_M hv
    have hav : a * v * a⁻¹ = v := by
      rw [S.comm_A ha hvA]
      group
    have hy : invAutDD (a * b) 1 v ∈ M := invAutDD_mem hrM hvM 1
    have hay : a * invAutDD (a * b) 1 v * a⁻¹ = invAutDD (a * b) 1 v := by
      rw [← invAutDD_conj_a hara haM hrM hMc 1 hvM, hav]
    have hyL : invAutDD (a * b) 1 v ∈ L := by
      refine S.mem_L_of_commute_M ha haL hy ?_
      calc a * invAutDD (a * b) 1 v = a * invAutDD (a * b) 1 v * a⁻¹ * a := by group
        _ = invAutDD (a * b) 1 v * a := by rw [hay]
    have huy : u * invAutDD (a * b) 1 v * u⁻¹ = invAutDD (a * b) 1 v :=
      hC' _ (S.L_le hyL)
    rw [invAutDD_conj u (a * b) 1 v (hC' v hvA), hR, invAutDD_twist hrM hMc hm₀ hvM] at huy
    exact huy
  have hLb' : ∀ lb ∈ Lb, invAutDD (a * b) k lb = invAutDD (a * b) 1 lb := by
    intro lb hlb
    have hl : k₀⁻¹ * lb * k₀ ∈ L := by
      have h := hlb
      rw [hLb, mem_conjSubgroup] at h
      exact h
    have h1 := (hΨ k₀ hk₀cl (k₀⁻¹ * lb * k₀) (S.L_le_M hl)).mp (hL _ hl)
    have e : k₀ * (k₀⁻¹ * lb * k₀) * k₀⁻¹ = lb := by group
    rw [e] at h1
    exact h1
  intro v hv
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hv
  rw [invAutDD_mul hrM hMc k (S.L_le_M hl) (S.Lb_le_M hlb),
    invAutDD_mul hrM hMc 1 (S.L_le_M hl) (S.Lb_le_M hlb), hL l hl, hLb' lb hlb]

theorem invAutD_k_cases [Finite G] (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A)
    (haL : a ∉ L) (hb : b ∈ Ab) {n : ℕ} (hodd : Odd n) (hrn : (a * b) ^ n = 1) {k : ℤ}
    (hP : ∀ v ∈ M, invAutDD (a * b) k v = invAutDD (a * b) 1 v) :
    (a * b) ^ (k - 1) = 1 ∨ (a * b) ^ (k + 1) = 1 := by
  have hrM := invAutD_rM S ha hb
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy => S.comm_M hx hy
  have hstar : ∀ v ∈ M, invAutDSig (a * b) (k + k) v * v
      = invAutDSig (a * b) (k + 1) v * invAutDSig (a * b) (k - 1) v := by
    intro v hv
    have h := congrArg (invAutDSig (a * b) k) (hP v hv)
    unfold invAutDD at h
    rw [invAutDSig_mul, invAutDSig_mul, invAutDSig_comp, invAutDSig_comp, invAutDSig_comp,
      invAutDSig_comp, add_neg_cancel, invAutDSig_zero, ← sub_eq_add_neg] at h
    exact h
  have hfix0 : ∀ v ∈ M, invAutDSig (a * b) (k + 1) (invAutDSig (a * b) (k - 1) v * v)
      = invAutDSig (a * b) (k - 1) v * v := by
    intro v hv
    have hα : invAutDSig (a * b) (k + 1) v ∈ M := invAutDSig_mem hrM hv _
    have hβ : invAutDSig (a * b) (k - 1) v ∈ M := invAutDSig_mem hrM hv _
    have hvv : v * v = 1 := S.mem_M_sq hv
    have hαα : invAutDSig (a * b) (k + 1) v * invAutDSig (a * b) (k + 1) v = 1 :=
      S.mem_M_sq hα
    have hst := hstar v hv
    rw [invAutDSig_mul, invAutDSig_comp]
    have e : k + 1 + (k - 1) = k + k := by ring
    rw [e]
    calc invAutDSig (a * b) (k + k) v * invAutDSig (a * b) (k + 1) v
        = invAutDSig (a * b) (k + k) v * (v * v) * invAutDSig (a * b) (k + 1) v := by
          rw [hvv, mul_one]
      _ = (invAutDSig (a * b) (k + k) v * v) * v * invAutDSig (a * b) (k + 1) v := by group
      _ = invAutDSig (a * b) (k + 1) v * invAutDSig (a * b) (k - 1) v * v
            * invAutDSig (a * b) (k + 1) v := by rw [hst]
      _ = invAutDSig (a * b) (k + 1) v * (invAutDSig (a * b) (k - 1) v * v)
            * invAutDSig (a * b) (k + 1) v := by group
      _ = (invAutDSig (a * b) (k - 1) v * v) * invAutDSig (a * b) (k + 1) v
            * invAutDSig (a * b) (k + 1) v := by
          rw [hMc _ hα _ (M.mul_mem hβ hv)]
      _ = invAutDSig (a * b) (k - 1) v * v := by rw [mul_assoc, hαα, mul_one]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hβv1 : ∀ v ∈ M, invAutDSig (a * b) (k - 1) v = v := by
    intro v hv
    have hw : invAutDSig (a * b) (k - 1) v * v ∈ M :=
      M.mul_mem (invAutDSig_mem hrM hv _) hv
    have hfx : (a * b) ^ (k + 1) * (invAutDSig (a * b) (k - 1) v * v) * ((a * b) ^ (k + 1))⁻¹
        = invAutDSig (a * b) (k - 1) v * v := hfix0 v hv
    have hcomm : (a * b) ^ (k + 1) * (invAutDSig (a * b) (k - 1) v * v)
        = (invAutDSig (a * b) (k - 1) v * v) * (a * b) ^ (k + 1) := by
      calc (a * b) ^ (k + 1) * (invAutDSig (a * b) (k - 1) v * v)
          = ((a * b) ^ (k + 1) * (invAutDSig (a * b) (k - 1) v * v) * ((a * b) ^ (k + 1))⁻¹)
              * (a * b) ^ (k + 1) := by group
        _ = (invAutDSig (a * b) (k - 1) v * v) * (a * b) ^ (k + 1) := by rw [hfx]
    have hw1 : invAutDSig (a * b) (k - 1) v * v = 1 :=
      invAutD_rot_fix S ha haL hb hodd hrn h2 hw hcomm
    have hvv : v * v = 1 := S.mem_M_sq hv
    rw [eq_inv_of_mul_eq_one_left hw1]
    exact inv_eq_of_mul_eq_one_right hvv
  have hall : ∀ v ∈ M, v = 1 := by
    intro v hv
    have hfx : (a * b) ^ (k - 1) * v * ((a * b) ^ (k - 1))⁻¹ = v := hβv1 v hv
    have hcomm : (a * b) ^ (k - 1) * v = v * (a * b) ^ (k - 1) := by
      calc (a * b) ^ (k - 1) * v
          = ((a * b) ^ (k - 1) * v * ((a * b) ^ (k - 1))⁻¹) * (a * b) ^ (k - 1) := by group
        _ = v * (a * b) ^ (k - 1) := by rw [hfx]
    exact invAutD_rot_fix S ha haL hb hodd hrn h1 hv hcomm
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.ne_bot
  have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
  exact hl1' (hall l (S.L_le_M hl))

theorem invAutD_fix [Finite G] (S : Prop24Setup A Ab L Lb M) (hrel : L.relIndex A = 2)
    {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb) {g : G}
    (hgN : g ∈ Subgroup.normalizer (M : Set G)) (hgM : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hga : g * a * g⁻¹ = a) (hgr : g * (a * b) * g⁻¹ * (a * b)⁻¹ ∈ M) :
    ∀ x ∈ A ⊔ Ab, g⁻¹ * x⁻¹ * g * x ∈ M := by
  have hcl : Subgroup.closure ({a, a * b} ∪ (M : Set G)) ≤ Subgroup.normalizer (M : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ((hx | hx) | hx)
    · rw [hx]
      exact S.A_le_normalizer_M ha
    · rw [hx]
      exact S.sup_le_normalizer_M
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))
    · exact Subgroup.le_normalizer hx
  have hΩ : ∀ x ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)), g * x * g⁻¹ * x⁻¹ ∈ M := by
    refine invAutD_closure_pred ?_ ?_ ?_ ?_
    · simp
    · rintro x ((hx | hx) | hx)
      · rw [hx, hga, mul_inv_cancel]
        exact M.one_mem
      · rw [hx]
        exact hgr
      · exact M.mul_mem (hgM x hx) (M.inv_mem hx)
    · intro x y hx hy hQx hQy
      rw [show g * (x * y) * g⁻¹ * (x * y)⁻¹
          = (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) by group]
      exact M.mul_mem hQx (invAutD_conj_mem' (hcl hx) hQy)
    · intro x hx hQx
      rw [inv_inv, show g * x⁻¹ * g⁻¹ * x = x⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * x by group]
      exact invAutD_conj_inv_mem' (hcl hx) (M.inv_mem hQx)
  intro x hx
  have hxT : x ∈ Subgroup.closure ({a, a * b} ∪ (M : Set G)) :=
    invAutD_le_closure S hrel ha haL hb hbL hx
  have hc := hΩ x hxT
  have hz : x⁻¹ * (g * x * g⁻¹ * x⁻¹) * x ∈ M := invAutD_conj_inv_mem' (hcl hxT) hc
  have hz' : g⁻¹ * (x⁻¹ * (g * x * g⁻¹ * x⁻¹) * x) * g ∈ M :=
    invAutD_conj_inv_mem' hgN hz
  have e : g⁻¹ * (x⁻¹ * (g * x * g⁻¹ * x⁻¹) * x) * g = g⁻¹ * x⁻¹ * g * x := by group
  rw [e] at hz'
  exact hz'

theorem invAutD_main [Finite G] (S : Prop24Setup A Ab L Lb M) (hrel : L.relIndex A = 2)
    {u : G} (hu : conjSubgroup u (A ⊔ Ab) = A ⊔ Ab) (hC : u ∈ centralizer (A : Set G))
    (hMu : conjSubgroup u M = M) :
    ∃ a₀ ∈ A, ∀ x ∈ A ⊔ Ab, (a₀ * u)⁻¹ * x⁻¹ * (a₀ * u) * x ∈ M := by
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hodd : Odd (orderOf (a * b)) := S.odd_orderOf_mul ha haL hb hbL
  have hrn : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one (a * b)
  have ha2 : a * a = 1 := S.sq_A ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : b * b = 1 := S.sq_Ab hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hara : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, mul_inv_rev, hbinv, hainv, ← mul_assoc, ha2, one_mul]
  obtain ⟨k, m₀, hm₀, hR⟩ := invAutD_conj_rot S hrel ha haL hb hbL hodd hrn hu hC hMu
  have hP := invAutD_defect S hrel ha haL hb hbL hu hC hm₀ hR
  have hcase := invAutD_k_cases S ha haL hb hodd hrn hP
  have hrM := invAutD_rM S ha hb
  have hC' : u * a * u⁻¹ = a := by
    rw [(Subgroup.mem_centralizer_iff.mp hC a ha).symm]
    group
  have hunN : u ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_of_conjSubgroup_eq hMu
  have huM : ∀ m ∈ M, u * m * u⁻¹ ∈ M := fun m hm => invAut_conj_mem hMu hm
  have haM : ∀ m ∈ M, a * m * a⁻¹ ∈ M := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) m).mp hm
  rcases hcase with h1 | h1
  ·
    have hkr : (a * b) ^ k = a * b := by
      have h := zpow_sub_one (a * b) k
      rw [h1] at h
      exact mul_inv_eq_one.mp h.symm
    have hgr : u * (a * b) * u⁻¹ * (a * b)⁻¹ ∈ M := by
      rw [hR, hkr]
      have h := hrM 1 m₀ hm₀
      rwa [zpow_one] at h
    refine ⟨1, A.one_mem, fun x hx => ?_⟩
    have h := invAutD_fix S hrel ha haL hb hbL hunN huM hC' hgr x hx
    simpa using h
  ·
    have hkinv : (a * b) ^ k = (a * b)⁻¹ := by
      have h := zpow_add_one (a * b) k
      rw [h1] at h
      exact eq_inv_of_mul_eq_one_left h.symm
    have hgN : a * u ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mul_mem _ (S.A_le_normalizer_M ha) hunN
    have hgM : ∀ m ∈ M, a * u * m * (a * u)⁻¹ ∈ M := fun m hm => by
      have e : a * u * m * (a * u)⁻¹ = a * (u * m * u⁻¹) * a⁻¹ := by group
      rw [e]
      exact haM _ (huM m hm)
    have hga : a * u * a * (a * u)⁻¹ = a := by
      have e : a * u * a * (a * u)⁻¹ = a * (u * a * u⁻¹) * a⁻¹ := by group
      rw [e, hC']
      group
    have hgr : a * u * (a * b) * (a * u)⁻¹ * (a * b)⁻¹ ∈ M := by
      have e : a * u * (a * b) * (a * u)⁻¹ * (a * b)⁻¹
          = (a * b) * (a * m₀ * a⁻¹) * (a * b)⁻¹ := by
        calc a * u * (a * b) * (a * u)⁻¹ * (a * b)⁻¹
            = a * (u * (a * b) * u⁻¹) * a⁻¹ * (a * b)⁻¹ := by group
          _ = a * ((a * b) ^ k * m₀) * a⁻¹ * (a * b)⁻¹ := by rw [hR]
          _ = (a * (a * b) ^ k * a⁻¹) * (a * m₀ * a⁻¹) * (a * b)⁻¹ := by group
          _ = ((a * b) ^ k)⁻¹ * (a * m₀ * a⁻¹) * (a * b)⁻¹ := by
              rw [invAutD_conj_zpow hara k]
          _ = (a * b) * (a * m₀ * a⁻¹) * (a * b)⁻¹ := by rw [hkinv, inv_inv]
      rw [e]
      have h := hrM 1 (a * m₀ * a⁻¹) (haM m₀ hm₀)
      rwa [zpow_one] at h
    refine ⟨a, ha, fun x hx => ?_⟩
    exact invAutD_fix S hrel ha haL hb hbL hgN hgM hga hgr x hx

end Main

theorem prop24InnerD_holds :
    ∀ (G : Type) [Group G] [Finite G] (A Ab L Lb M : Subgroup G), Prop24Setup A Ab L Lb M →
      L.relIndex A = 2 → ∀ u : G, conjSubgroup u (A ⊔ Ab) = A ⊔ Ab →
      u ∈ centralizer (A : Set G) →
        ∃ a ∈ A, ∀ x ∈ A ⊔ Ab, (a * u)⁻¹ * x⁻¹ * (a * u) * x ∈ M := by
  intro G _ _ A Ab L Lb M S hrel u hu hC
  obtain ⟨hN, hO2, -⟩ := S.tim77_2_4_one CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  haveI := hN
  have hMu : conjSubgroup u M = M :=
    invAut_conj_eq_of_normalizes hO2 S.M_le_X (fun m hm => S.mem_M_sq hm) hu
  exact invAutD_main S hrel hu hC hMu

end CFSG.RankThree.GF2n.Tim77
