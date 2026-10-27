module

public import CFSG.Sporadic.J4.QTElem
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.J4.QT

variable {G : Type*} [Group G]

section Chain

@[expose] def Kc (H : Subgroup G) (b : ℕ → G) : ℕ → Subgroup G
  | 0 => H
  | j + 1 => Kc H b j ⊓ Subgroup.centralizer {b j}

theorem mem_Kc {H : Subgroup G} {b : ℕ → G} {x : G} {m : ℕ} :
    x ∈ Kc H b m ↔ x ∈ H ∧ ∀ i < m, b i * x = x * b i := by
  induction m with
  | zero => simp [Kc]
  | succ m ih =>
    simp only [Kc, Subgroup.mem_inf, ih, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h2 i hi
        · exact h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 m (by omega)⟩

theorem orbit_stab_bound [Finite G] (K : Subgroup G) (b : G) (n : ℕ) (t : ℕ → G)
    (ht : ∀ k < n, t k ∈ K)
    (hd : ∀ k < n, ∀ k' < n, t k * b * (t k)⁻¹ = t k' * b * (t k')⁻¹ → k = k') :
    n * Nat.card ↥(K ⊓ Subgroup.centralizer {b}) ≤ Nat.card ↥K := by
  classical
  have hs : ∀ s : ↥(K ⊓ Subgroup.centralizer {b}), (s : G) * b * (s : G)⁻¹ = b := by
    intro s
    have := Subgroup.mem_centralizer_iff.1 s.2.2 b (Set.mem_singleton b)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  let f : Fin n × ↥(K ⊓ Subgroup.centralizer {b}) → ↥K := fun p =>
    ⟨t p.1 * p.2, K.mul_mem (ht _ p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨k, s⟩ ⟨k', s'⟩ h
    have h1 : t k * (s : G) = t k' * (s' : G) := congrArg Subtype.val h
    have h2 : t k * b * (t k)⁻¹ = t k' * b * (t k')⁻¹ := by
      calc t k * b * (t k)⁻¹ = t k * ((s : G) * b * (s : G)⁻¹) * (t k)⁻¹ := by rw [hs]
        _ = (t k * (s : G)) * b * (t k * (s : G))⁻¹ := by group
        _ = (t k' * (s' : G)) * b * (t k' * (s' : G))⁻¹ := by rw [h1]
        _ = t k' * ((s' : G) * b * (s' : G)⁻¹) * (t k')⁻¹ := by group
        _ = t k' * b * (t k')⁻¹ := by rw [hs]
    have hk : k = k' := Fin.ext (hd k k.2 k' k'.2 h2)
    subst hk
    have : (s : G) = s' := mul_left_cancel h1
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using this

theorem chain_bound [Finite G] (H : Subgroup G) (b : ℕ → G) (cnt : ℕ → ℕ) (t : ℕ → ℕ → G)
    (m : ℕ) (ht : ∀ j < m, ∀ k < cnt j, t j k ∈ Kc H b j)
    (hd : ∀ j < m, ∀ k < cnt j, ∀ k' < cnt j,
      t j k * b j * (t j k)⁻¹ = t j k' * b j * (t j k')⁻¹ → k = k') :
    (∏ j ∈ Finset.range m, cnt j) * Nat.card ↥(Kc H b m) ≤ Nat.card ↥H := by
  induction m with
  | zero => simp [Kc]
  | succ m ih =>
    have ih' := ih (fun j hj => ht j (by omega)) (fun j hj => hd j (by omega))
    have h1 := orbit_stab_bound (Kc H b m) (b m) (cnt m) (t m) (ht m (by omega))
      (hd m (by omega))
    rw [Finset.prod_range_succ]
    calc (∏ j ∈ Finset.range m, cnt j) * cnt m * Nat.card ↥(Kc H b (m + 1))
        = (∏ j ∈ Finset.range m, cnt j) * (cnt m * Nat.card ↥(Kc H b m ⊓
          Subgroup.centralizer {b m})) := by rw [mul_assoc]; rfl
      _ ≤ (∏ j ∈ Finset.range m, cnt j) * Nat.card ↥(Kc H b m) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card ↥H := ih'

variable {u : ℕ → G} {n : ℕ}

theorem centralizer_le_of_chain [Finite G] (hE : Elem u n) (H : Subgroup G) (hEH : Eg u n ≤ H)
    (hcardE : Nat.card ↥(Eg u n) = 2 ^ n) (b : ℕ → G) (hb : ∀ i, b i ∈ Eg u n) (cnt : ℕ → ℕ)
    (t : ℕ → ℕ → G) (m : ℕ) (ht : ∀ j < m, ∀ k < cnt j, t j k ∈ Kc H b j)
    (hd : ∀ j < m, ∀ k < cnt j, ∀ k' < cnt j,
      t j k * b j * (t j k)⁻¹ = t j k' * b j * (t j k')⁻¹ → k = k')
    (hcnt : (∏ j ∈ Finset.range m, cnt j) * 2 ^ n = Nat.card ↥H) :
    ∀ x ∈ H, (∀ y ∈ Eg u n, x * y = y * x) → x ∈ Eg u n := by
  intro x hx hxc
  let C : Subgroup G := H ⊓ Subgroup.centralizer (Eg u n : Set G)
  have hEC : Eg u n ≤ C := fun y hy => ⟨hEH hy, Subgroup.mem_centralizer_iff.2 fun z hz =>
    Eg_comm hE hz hy⟩
  have hCK : C ≤ Kc H b m := fun y hy => mem_Kc.2 ⟨hy.1, fun i _ =>
    Subgroup.mem_centralizer_iff.1 hy.2 (b i) (hb i)⟩
  have hbound := chain_bound H b cnt t m ht hd
  have hpos : 0 < ∏ j ∈ Finset.range m, cnt j := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hcnt
    exact (Nat.card_pos (α := ↥H)).ne' hcnt.symm
  have h1 : Nat.card ↥C ≤ Nat.card ↥(Kc H b m) := Subgroup.card_le_of_le hCK
  have h2 : Nat.card ↥(Kc H b m) ≤ 2 ^ n := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [hcnt]
    exact hbound
  have hCE : Eg u n = C := Subgroup.eq_of_le_of_card_ge hEC (by rw [hcardE]; omega)
  have : x ∈ C := ⟨hx, Subgroup.mem_centralizer_iff.2 fun z hz => (hxc z hz).symm⟩
  rwa [← hCE] at this

end Chain

section Orbits

variable {u : ℕ → G} {n : ℕ}

theorem eta_foldl_xor (h : Elem u n) {D : Subgroup G} (S : List ℕ)
    (hS : ∀ c ∈ S, eta u n c ∈ D) (acc : ℕ) (hacc : eta u n acc ∈ D) :
    eta u n (S.foldl (· ^^^ ·) acc) ∈ D := by
  induction S generalizing acc with
  | nil => exact hacc
  | cons c S ih =>
    refine ih (fun c' hc' => hS c' (List.mem_cons_of_mem _ hc')) _ ?_
    rw [eta_xor h le_rfl]
    exact D.mul_mem hacc (hS c (List.mem_cons_self ..))

theorem eta_injective (h : Elem u n) (h1 : ∀ c < 2 ^ n, c ≠ 0 → eta u n c ≠ 1) :
    ∀ c < 2 ^ n, ∀ d < 2 ^ n, eta u n c = eta u n d → c = d := by
  intro c hc d hd hcd
  by_contra hne
  refine h1 (c ^^^ d) (Nat.xor_lt_two_pow hc hd) (fun h0 => hne (Nat.eq_of_xor_eq_zero h0)) ?_
  rw [eta_xor h le_rfl, hcd]
  exact eta_sq h d

theorem isPGroup_Eg (h : Elem u n) : IsPGroup 2 (Eg u n) := by
  rintro ⟨g, hg⟩
  exact ⟨1, Subtype.ext (by simpa [sq] using Eg_sq h hg)⟩

theorem eg_normalizes (h : Elem u n) (H : Subgroup G) (X : ℤ → G) (act : ℤ → ℕ → ℕ)
    (Lset : List ℤ)
    (hX : ∀ ℓ ∈ Lset, ∀ c, X ℓ * eta u n c * (X ℓ)⁻¹ = eta u n (act ℓ c))
    (hinv : ∀ ℓ ∈ Lset, -ℓ ∈ Lset ∧ X (-ℓ) = (X ℓ)⁻¹)
    (hH : H ≤ Subgroup.closure (X '' {ℓ | ℓ ∈ Lset})) :
    ∀ g ∈ H, ∀ x ∈ Eg u n, g * x * g⁻¹ ∈ Eg u n := by
  have hN : Subgroup.closure (X '' {ℓ | ℓ ∈ Lset}) ≤ Subgroup.normalizer (Eg u n : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨c, -, rfl⟩ := (mem_Eg_iff h).1 hx
      rw [hX ℓ hℓ]
      exact eta_mem_Eg n le_rfl _
    · intro hx
      obtain ⟨hℓ', hXinv⟩ := hinv ℓ hℓ
      obtain ⟨c, -, hc⟩ := (mem_Eg_iff h).1 hx
      have h2 := hX (-ℓ) hℓ' c
      rw [hXinv, ← hc] at h2
      have e : x = (X ℓ)⁻¹ * (X ℓ * x * (X ℓ)⁻¹) * ((X ℓ)⁻¹)⁻¹ := by group
      rw [e, h2]
      exact eta_mem_Eg n le_rfl _
  intro g hg x hx
  exact (Subgroup.mem_normalizer_iff.1 (hN (hH hg)) x).1 hx

theorem minimal_of_orbits (h : Elem u n) (H : Subgroup G) (X : ℤ → G) (act : ℤ → ℕ → ℕ)
    (Lset : List ℤ) (hXH : ∀ ℓ ∈ Lset, X ℓ ∈ H)
    (hX : ∀ ℓ ∈ Lset, ∀ c, X ℓ * eta u n c * (X ℓ)⁻¹ = eta u n (act ℓ c))
    (orbs : List (ℕ × List (ℕ × List ℤ) × List (List ℕ)))
    (hword : ∀ o ∈ orbs, ∀ p ∈ o.2.1, (∀ ℓ ∈ p.2, ℓ ∈ Lset) ∧ p.2.foldr act o.1 = p.1)
    (hcover : ∀ c < 2 ^ n, c ≠ 0 → ∃ o ∈ orbs, ∃ p ∈ o.2.1, p.1 = c)
    (hspan : ∀ o ∈ orbs, ∀ j < n, (∀ c ∈ o.2.2.getD j [], ∃ p ∈ o.2.1, p.1 = c) ∧
      (o.2.2.getD j []).foldl (· ^^^ ·) 0 = 2 ^ j)
    (D : Subgroup G) (hDE : D ≤ Eg u n) (hD : ∀ g ∈ H, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    D = ⊥ ∨ D = Eg u n := by
  by_cases hbot : D = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff h).1 (hDE hdD)
  have hc0 : c ≠ 0 := fun h0 => hd1 (Subtype.ext (by simp [h0, eta_zero]))
  obtain ⟨o, ho, p, hp, hpc⟩ := hcover c hc hc0
  have hconj : ∀ q ∈ o.2.1, ∃ g ∈ H, g * eta u n o.1 * g⁻¹ = eta u n q.1 := by
    intro q hq
    obtain ⟨hlet, hfold⟩ := hword o ho q hq
    refine ⟨(q.2.map X).prod, ?_, ?_⟩
    · refine Subgroup.list_prod_mem H ?_
      intro x hx
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
      exact hXH ℓ (hlet ℓ hℓ)
    · rw [word_conj X act q.2 (fun ℓ hℓ => hX ℓ (hlet ℓ hℓ)), hfold]
  have hroot : eta u n o.1 ∈ D := by
    obtain ⟨g, hg, hgeq⟩ := hconj p hp
    have hp' : eta u n p.1 ∈ D := by rw [hpc]; exact hdD
    have := hD g⁻¹ (H.inv_mem hg) _ hp'
    rw [← hgeq] at this
    have e : g⁻¹ * (g * eta u n o.1 * g⁻¹) * (g⁻¹)⁻¹ = eta u n o.1 := by group
    rwa [e] at this
  have hall : ∀ q ∈ o.2.1, eta u n q.1 ∈ D := by
    intro q hq
    obtain ⟨g, hg, hgeq⟩ := hconj q hq
    rw [← hgeq]
    exact hD g hg _ hroot
  have hbasis : ∀ j < n, u j ∈ D := by
    intro j hj
    obtain ⟨hmem, hxor⟩ := hspan o ho j hj
    have := eta_foldl_xor h (D := D) (o.2.2.getD j []) (fun c hc => by
      obtain ⟨q, hq, rfl⟩ := hmem c hc
      exact hall q hq) 0 (by rw [eta_zero]; exact D.one_mem)
    rwa [hxor, eta_two_pow hj] at this
  refine le_antisymm hDE ?_
  rw [Eg, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact hbasis j hj

end Orbits

section Fusion

theorem dihedral_conj (s t : G) (hs : s * s = 1) (ht : t * t = 1) (hp : (s * t) ^ 33 = 1) :
    (s * t) ^ 16 * s * ((s * t) ^ 16)⁻¹ = t := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    calc s * (s * t) * s⁻¹ = (s * s) * t * s⁻¹ := by group
      _ = t * s := by rw [hs, one_mul, hs']
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hs', ht']
  have h2 : s * (s * t) ^ 16 * s⁻¹ = ((s * t) ^ 16)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : s * ((s * t) ^ 16)⁻¹ * s⁻¹ = (s * t) ^ 16 := by
    calc s * ((s * t) ^ 16)⁻¹ * s⁻¹ = s * (s * (s * t) ^ 16 * s⁻¹) * s⁻¹ := by rw [h2]
      _ = (s * s) * (s * t) ^ 16 * (s⁻¹ * s⁻¹) := by group
      _ = (s * t) ^ 16 := by rw [hs, hs', hs, one_mul, mul_one]
  have h4 : (s * t) ^ 32 = (s * t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hp
  calc (s * t) ^ 16 * s * ((s * t) ^ 16)⁻¹
      = (s * t) ^ 16 * (s * ((s * t) ^ 16)⁻¹ * s⁻¹) * s := by group
    _ = (s * t) ^ 16 * (s * t) ^ 16 * s := by rw [h3]
    _ = (s * t) ^ 32 * s := by rw [← pow_add]
    _ = t := by rw [h4, mul_inv_rev, ht', hs', mul_assoc, hs, mul_one]

end Fusion

end CFSG.Sporadic.J4.QT
