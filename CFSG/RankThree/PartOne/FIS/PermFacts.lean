module

public import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.FIS.PermFacts

open Equiv Equiv.Perm

private theorem exists_notMem_of_card_lt {n : ℕ} (s : Finset (Fin n)) (h : s.card < n) :
    ∃ c : Fin n, c ∉ s := by
  by_contra hc
  push Not at hc
  rw [Finset.eq_univ_of_forall hc, Finset.card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

theorem exists_third {n : ℕ} (h3 : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({a, b} : Finset (Fin n))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  exact ⟨c, fun h => hc (by simp [h]), fun h => hc (by simp [h])⟩

theorem exists_fourth {n : ℕ} (h4 : 4 ≤ n) (a b c : Fin n) :
    ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  obtain ⟨d, hd⟩ := exists_notMem_of_card_lt ({a, b, c} : Finset (Fin n))
    (lt_of_le_of_lt Finset.card_le_three (by omega))
  exact ⟨d, fun h => hd (by simp [h]), fun h => hd (by simp [h]), fun h => hd (by simp [h])⟩

theorem swap_mul_comm_of_disjoint {α : Type*} [DecidableEq α] {x y z w : α} (h1 : x ≠ z)
    (h2 : x ≠ w) (h3 : y ≠ z) (h4 : y ≠ w) :
    swap x y * swap z w = swap z w * swap x y := by
  ext a
  simp only [Perm.mul_apply, swap_apply_def]
  grind

theorem disjoint_of_swap_commute {α : Type*} [DecidableEq α] {x y z w : α} (hxy : x ≠ y)
    (hzw : z ≠ w) (hne : swap x y ≠ swap z w)
    (h : swap x y * swap z w = swap z w * swap x y) : x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w := by
  have hx := congrArg (fun f : Perm α => f x) h
  have hy := congrArg (fun f : Perm α => f y) h
  have hz := congrArg (fun f : Perm α => f z) h
  have hw := congrArg (fun f : Perm α => f w) h
  simp only [Perm.mul_apply, swap_apply_def] at hx hy hz hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hc <;> subst hc <;> grind

theorem swap_mul_ne_of_adjacent {α : Type*} [DecidableEq α] {p q s : α} (hpq : p ≠ q)
    (hqs : q ≠ s) (hps : p ≠ s) : swap q s * swap p q ≠ swap p q * swap q s := by
  intro h
  have hq := congrArg (fun f : Perm α => f q) h
  simp only [Perm.mul_apply, swap_apply_def] at hq
  grind

private theorem exists_swap_of_apply_ne {α : Type*} [DecidableEq α] {u v a : α} (huv : u ≠ v)
    (h : swap u v a ≠ a) : ∃ w, w ≠ a ∧ swap u v = swap a w := by
  rcases (swap_apply_ne_self_iff.1 h).2 with rfl | rfl
  · exact ⟨v, huv.symm, rfl⟩
  · exact ⟨u, huv, swap_comm _ _⟩

private theorem exists_common_point {α : Type*} [DecidableEq α] {x y z w : α} (hxy : x ≠ y)
    (hzw : z ≠ w) (hne : swap x y ≠ swap z w) (hshare : ¬ (x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w)) :
    ∃ p q r : α, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ swap x y = swap p q ∧ swap z w = swap p r := by
  by_cases hxz : x = z
  · subst hxz
    exact ⟨x, y, w, hxy, hzw, fun h => hne (by rw [h]), rfl, rfl⟩
  by_cases hxw : x = w
  · subst hxw
    exact ⟨x, y, z, hxy, fun h => hzw h.symm, fun h => hne (by rw [h, swap_comm]),
      rfl, swap_comm _ _⟩
  by_cases hyz : y = z
  · subst hyz
    exact ⟨y, x, w, hxy.symm, hzw, hxw, swap_comm _ _, rfl⟩
  by_cases hyw : y = w
  · subst hyw
    exact ⟨y, x, z, hxy.symm, hzw.symm, hxz, swap_comm _ _, swap_comm _ _⟩
  exact absurd ⟨hxz, hxw, hyz, hyw⟩ hshare

theorem isSwap_conj {α : Type*} [DecidableEq α] {s : Perm α} (hs : s.IsSwap) (g : Perm α) :
    (g * s * g⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  exact ⟨g x, g y, g.injective.ne hxy, (swap_apply_apply g x y).symm⟩

theorem swap_noncomm_three {a b : Perm (Fin 3)} (ha : a.IsSwap) (hb : b.IsSwap) (hab : a ≠ b) :
    a * b ≠ b * a := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨z, w, hzw, rfl⟩ := hb
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := disjoint_of_swap_commute hxy hzw hab h
  have hnd : [x, y, z, w].Nodup := by
    simp [List.nodup_cons, hxy, hzw, h1, h2, h3, h4]
  have := hnd.length_le_card
  simp at this

theorem no_three_commuting {n : ℕ} (h5 : n ≤ 5) {a b c : Perm (Fin n)} (ha : a.IsSwap)
    (hb : b.IsSwap) (hc : c.IsSwap) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : a * b = b * a) (h2 : a * c = c * a) (h3 : b * c = c * b) : False := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨z, w, hzw, rfl⟩ := hb
  obtain ⟨u, v, huv, rfl⟩ := hc
  obtain ⟨e1, e2, e3, e4⟩ := disjoint_of_swap_commute hxy hzw hab h1
  obtain ⟨e5, e6, e7, e8⟩ := disjoint_of_swap_commute hxy huv hac h2
  obtain ⟨e9, e10, e11, e12⟩ := disjoint_of_swap_commute hzw huv hbc h3
  have hnd : [x, y, z, w, u, v].Nodup := by
    simp [List.nodup_cons, hxy, hzw, huv, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  have := hnd.length_le_card
  simp only [List.length_cons, List.length_nil, Fintype.card_fin] at this
  omega

theorem exists_distinguishing_swap {n : ℕ} (h4 : 4 ≤ n) (h5 : n ≤ 5) {a d : Perm (Fin n)}
    (ha : a.IsSwap) (hd : d.IsSwap) (hnc : a * d ≠ d * a) :
    ∃ t : Perm (Fin n), t.IsSwap ∧
      ¬ ((t ≠ d ∧ t * d = d * t) ↔ (t ≠ a ∧ t * a = a * t)) := by
  have _ := h5
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨z, w, hzw, rfl⟩ := hd
  have hshare : ¬ (x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w) := fun h =>
    hnc (swap_mul_comm_of_disjoint h.1 h.2.1 h.2.2.1 h.2.2.2)
  have hne : swap x y ≠ swap z w := fun h => hnc (by rw [h])
  obtain ⟨p, q, r, hpq, hpr, hqr, hap, hdp⟩ := exists_common_point hxy hzw hne hshare
  rw [hap, hdp]
  obtain ⟨s, hsp, hsq, hsr⟩ := exists_fourth h4 p q r
  refine ⟨swap q s, ⟨q, s, hsq.symm, rfl⟩, fun hiff => ?_⟩
  have hcomm : swap q s * swap p r = swap p r * swap q s :=
    swap_mul_comm_of_disjoint hpq.symm hqr hsp hsr
  have hne' : swap q s ≠ swap p r := by
    intro h
    have hq := congrArg (fun f : Perm (Fin n) => f q) h
    simp only [swap_apply_left, swap_apply_of_ne_of_ne hpq.symm hqr] at hq
    exact hsq hq
  exact swap_mul_ne_of_adjacent hpq hsq.symm hsp.symm (hiff.1 ⟨hne', hcomm⟩).2

private theorem fin_three_cases (a b x c : Fin 3) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    c = a ∨ c = b ∨ c = x := by
  revert a b x c
  decide

private theorem star_eq_of_forall_notMem {n : ℕ} {B : Set (Perm (Fin n))} {a b : Fin n}
    (hab : a ≠ b) (hB : ∀ σ ∈ B, σ.IsSwap)
    (hnc : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → u * v ≠ v * u) (he : swap a b ∈ B)
    (hcover : ∀ c, c ≠ a → c ≠ b → swap a c ∈ B ∨ swap b c ∈ B)
    (hnone : ∀ c, c ≠ a → c ≠ b → swap b c ∉ B) :
    B = {σ | σ.IsSwap ∧ σ a ≠ a} := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨u, v, huv, rfl⟩ := hB σ hσ
    refine ⟨⟨u, v, huv, rfl⟩, ?_⟩
    by_cases hσe : swap u v = swap a b
    · rw [hσe, swap_apply_left]
      exact hab.symm
    have hshare : ¬ (u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b) := fun hd =>
      hnc _ hσ _ he hσe (swap_mul_comm_of_disjoint hd.1 hd.2.1 hd.2.2.1 hd.2.2.2)
    refine swap_apply_ne_self_iff.2 ⟨huv, ?_⟩
    by_contra hcon
    have hu : u ≠ a := fun h => hcon (Or.inl h.symm)
    have hv : v ≠ a := fun h => hcon (Or.inr h.symm)
    by_cases hub : u = b
    · have hσ' : swap b v ∈ B := by rwa [← hub]
      exact hnone v hv (fun h => huv (hub.trans h.symm)) hσ'
    · have hvb : v = b := by
        by_contra hvb
        exact hshare ⟨hu, hub, hv, hvb⟩
      have hσ' : swap b u ∈ B := by rwa [swap_comm, ← hvb]
      exact hnone u hu hub hσ'
  · rintro ⟨⟨u, v, huv, rfl⟩, hσa⟩
    obtain ⟨w, hwa, hw⟩ := exists_swap_of_apply_ne huv hσa
    rw [hw]
    by_cases hwb : w = b
    · rw [hwb]
      exact he
    rcases hcover w hwa hwb with h | h
    · exact h
    · exact absurd h (hnone w hwa hwb)

theorem star_char {n : ℕ} (h3 : 3 ≤ n) {B : Set (Perm (Fin n))}
    (hB : ∀ σ ∈ B, σ.IsSwap) (hne : B.Nonempty)
    (hnc : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → a * b ≠ b * a)
    (hinv : ∀ f : Perm (Fin n), f.IsSwap → f ∉ B → ∀ e ∈ B, f * e * f⁻¹ ∈ B) :
    (∃ p : Fin n, B = {σ | σ.IsSwap ∧ σ p ≠ p}) ∨ (n = 3 ∧ B = {σ | σ.IsSwap}) := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b, hab, rfl⟩ := hB e he
  have hcover : ∀ c, c ≠ a → c ≠ b → swap a c ∈ B ∨ swap b c ∈ B := by
    intro c hca hcb
    by_cases h : swap a c ∈ B
    · exact Or.inl h
    · right
      have h' := hinv (swap a c) ⟨a, c, hca.symm, rfl⟩ h _ he
      rwa [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hab.symm hcb.symm,
        swap_comm] at h'
  have hmeet : ∀ x y, x ≠ a → x ≠ b → y ≠ a → y ≠ b → x ≠ y → swap a x ∈ B → swap b y ∈ B →
      False := by
    intro x y hxa hxb hya hyb hxy hx hy
    have hne : swap a x ≠ swap b y := by
      intro h
      have h' := congrArg (fun f : Perm (Fin n) => f a) h
      simp only [swap_apply_left, swap_apply_of_ne_of_ne hab hya.symm] at h'
      exact hxa h'
    exact hnc _ hx _ hy hne (swap_mul_comm_of_disjoint hab hya.symm hxb hxy)
  by_cases hSb : ∀ c, c ≠ a → c ≠ b → swap b c ∉ B
  · exact Or.inl ⟨a, star_eq_of_forall_notMem hab hB hnc he hcover hSb⟩
  by_cases hSa : ∀ c, c ≠ a → c ≠ b → swap a c ∉ B
  · exact Or.inl ⟨b, star_eq_of_forall_notMem hab.symm hB hnc (by rwa [swap_comm])
      (fun c h1 h2 => (hcover c h2 h1).symm) (fun c h1 h2 => hSa c h2 h1)⟩
  right
  obtain ⟨x, hxa, hxb, hx⟩ : ∃ x, x ≠ a ∧ x ≠ b ∧ swap a x ∈ B := by
    by_contra hcon
    exact hSa fun c hca hcb hc => hcon ⟨c, hca, hcb, hc⟩
  obtain ⟨y, hya, hyb, hy⟩ : ∃ y, y ≠ a ∧ y ≠ b ∧ swap b y ∈ B := by
    by_contra hcon
    exact hSb fun c hca hcb hc => hcon ⟨c, hca, hcb, hc⟩
  have hxy : x = y := by
    by_contra h
    exact hmeet x y hxa hxb hya hyb h hx hy
  rw [← hxy] at hy
  have hn : n = 3 := by
    by_contra hn
    obtain ⟨d, hda, hdb, hdx⟩ := exists_fourth (by omega) a b x
    rcases hcover d hda hdb with hd | hd
    · exact hmeet d x hda hdb hxa hxb hdx hd hy
    · exact hmeet x d hxa hxb hda hdb hdx.symm hx hd
  subst hn
  refine ⟨rfl, Set.ext fun σ => ⟨hB σ, fun hσ => ?_⟩⟩
  obtain ⟨u, v, huv, rfl⟩ := hσ
  have hu := fin_three_cases a b x u hab hxa hxb
  have hv := fin_three_cases a b x v hab hxa hxb
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
    | exact absurd rfl huv
    | assumption
    | (rwa [swap_comm])

theorem star_injective {n : ℕ} (h3 : 3 ≤ n) {p q : Fin n}
    (h : {σ : Perm (Fin n) | σ.IsSwap ∧ σ p ≠ p} = {σ | σ.IsSwap ∧ σ q ≠ q}) : p = q := by
  by_contra hpq
  obtain ⟨r, hrp, hrq⟩ := exists_third h3 p q
  have hmem : swap p r ∈ {σ : Perm (Fin n) | σ.IsSwap ∧ σ p ≠ p} :=
    ⟨⟨p, r, hrp.symm, rfl⟩, by rwa [swap_apply_left]⟩
  rw [h] at hmem
  exact hmem.2 (swap_apply_of_ne_of_ne (Ne.symm hpq) (Ne.symm hrq))

theorem mem_closure_swaps_fixing {n : ℕ} (p : Fin n) {σ : Perm (Fin n)} (h : σ p = p) :
    σ ∈ Subgroup.closure {τ : Perm (Fin n) | τ.IsSwap ∧ τ p = p} := by
  have hS : ∀ f ∈ {τ : Perm (Fin n) | τ.IsSwap ∧ τ p = p}, f.IsSwap := fun f hf => hf.1
  rw [mem_closure_isSwap hS]
  refine ⟨Set.toFinite _, fun x => ?_⟩
  by_cases hx : σ x = x
  · rw [hx]
    exact MulAction.mem_orbit_self x
  · have hxp : x ≠ p := by
      rintro rfl
      exact hx h
    have hσp : σ x ≠ p := fun h' => hxp (σ.injective (h'.trans h.symm))
    exact (swap_mem_closure_isSwap hS).1 (Subgroup.subset_closure
      ⟨swap_isSwap_iff.2 hx, swap_apply_of_ne_of_ne hσp.symm hxp.symm⟩)

theorem ncard_isSwap (n : ℕ) : {σ : Perm (Fin n) | σ.IsSwap}.ncard = n * (n - 1) / 2 := by
  have hinj : Set.InjOn (fun σ : Perm (Fin n) => σ.support) {σ | σ.IsSwap} := by
    rintro _ ⟨x, y, hxy, rfl⟩ _ ⟨z, w, hzw, rfl⟩ h
    simp only [support_swap hxy, support_swap hzw] at h
    have hx : x ∈ ({z, w} : Finset (Fin n)) := h ▸ Finset.mem_insert_self _ _
    have hy : y ∈ ({z, w} : Finset (Fin n)) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact swap_comm _ _
    · exact absurd rfl hxy
  have himg : (fun σ : Perm (Fin n) => σ.support) '' {σ | σ.IsSwap} =
      ↑(Finset.powersetCard 2 (Finset.univ : Finset (Fin n))) := by
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact card_support_eq_two.2 hσ
    · intro hs
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
      exact ⟨swap x y, ⟨x, y, hxy, rfl⟩, support_swap hxy⟩
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]

private theorem sq_or_cube_eq_one {G : Type*} [Group G] [Finite G] {g : G}
    (h : orderOf g ≤ 3) : g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  have hpos : 0 < orderOf g := orderOf_pos g
  have hpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  generalize orderOf g = k at hpos hpow h
  interval_cases k
  · left
    rw [pow_one] at hpow
    rw [hpow, one_pow]
  · exact Or.inl hpow
  · exact Or.inr hpow

private theorem involution_swap_or_even {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5) :
    ∀ τ : Perm (Fin n), τ * τ = 1 → τ ≠ 1 →
      (∃ x y : Fin n, x ≠ y ∧ τ = swap x y) ∨ sign τ = 1 := by
  interval_cases n <;> decide +kernel

private theorem involution_swap_or_bad {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5) :
    ∀ τ : Perm (Fin n), τ * τ = 1 → τ ≠ 1 →
      (∃ x y : Fin n, x ≠ y ∧ τ = swap x y) ∨
        ∃ x y : Fin n, x ≠ y ∧ ¬ ((τ * swap x y) ^ 2 = 1 ∨ (τ * swap x y) ^ 3 = 1) := by
  interval_cases n <;> decide +kernel

theorem eq_swaps_of_closed {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5) {T : Set (Perm (Fin n))}
    (hinv : ∀ t ∈ T, t * t = 1 ∧ t ≠ 1) (hconj : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T)
    (hgen : Subgroup.closure T = ⊤) (hord : ∀ s ∈ T, ∀ t ∈ T, orderOf (s * t) ≤ 3) :
    T = {σ | σ.IsSwap} := by
  have hall : ∀ g : Perm (Fin n), ∀ t : Perm (Fin n), t ∈ T ↔ g * t * g⁻¹ ∈ T := by
    intro g
    have hg : g ∈ Subgroup.closure T := by
      rw [hgen]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      intro t
      refine ⟨hconj s hs t, fun ht => ?_⟩
      have hss : s * s = 1 := (hinv s hs).1
      have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
      have h' := hconj s hs _ ht
      rw [hsi] at h'
      have e : s * (s * t * s) * s = t := by
        calc s * (s * t * s) * s = (s * s) * t * (s * s) := by simp only [mul_assoc]
          _ = t := by rw [hss, one_mul, mul_one]
      rwa [e] at h'
    | one => intro t; simp
    | mul g h _ _ ihg ihh =>
      intro t
      refine (ihh t).trans ((ihg _).trans ?_)
      rw [show g * (h * t * h⁻¹) * g⁻¹ = g * h * t * (g * h)⁻¹ by group]
    | inv g _ ihg =>
      intro t
      have h' := ihg (g⁻¹ * t * g⁻¹⁻¹)
      rw [show g * (g⁻¹ * t * g⁻¹⁻¹) * g⁻¹ = t by group] at h'
      exact h'.symm
  have hswap : ∃ s ∈ T, s.IsSwap := by
    by_contra hcon
    have hle : Subgroup.closure T ≤ (sign : Perm (Fin n) →* ℤˣ).ker := by
      rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨ht2, ht1⟩ := hinv t ht
      rcases involution_swap_or_even h3 h5 t ht2 ht1 with ⟨x, y, hxy, hsw⟩ | hs
      · exact absurd ⟨t, ht, x, y, hxy, hsw⟩ hcon
      · exact hs
    rw [hgen] at hle
    have h01 := hle (Subgroup.mem_top (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))
    rw [MonoidHom.mem_ker, sign_swap (Fin.ne_of_val_ne (by simp))] at h01
    exact absurd h01 (by decide)
  obtain ⟨s₀, hs₀T, x₀, y₀, hxy₀, rfl⟩ := hswap
  have hswapsT : ∀ x y : Fin n, x ≠ y → swap x y ∈ T := by
    intro x y hxy
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_swap hxy₀ hxy)
    rw [← hc]
    exact (hall c _).1 hs₀T
  ext τ
  constructor
  · intro hτ
    obtain ⟨hτ2, hτ1⟩ := hinv τ hτ
    rcases involution_swap_or_bad h3 h5 τ hτ2 hτ1 with ⟨x, y, hxy, hsw⟩ | ⟨x, y, hxy, hbad⟩
    · exact ⟨x, y, hxy, hsw⟩
    · exact absurd (sq_or_cube_eq_one (hord τ hτ _ (hswapsT x y hxy))) hbad
  · rintro ⟨x, y, hxy, rfl⟩
    exact hswapsT x y hxy
