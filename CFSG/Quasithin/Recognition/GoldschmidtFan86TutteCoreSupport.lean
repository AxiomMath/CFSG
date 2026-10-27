module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreWord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreList
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelPset

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem core_list (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : 2 * i ≤ s)
    (hab : Abel Hs (s - i)) (e : ℤ) (he : e = 1 ∨ e = -1) (φ : H →* H)
    (hφ : ∀ K : List ℤ, Even K.length → φ (nfw r l e K) = nfw r l e (K.map (· - i)))
    (hξ : ∀ e' : ℤ, (e' = 1 ∨ e' = -1) → ∀ N : List ℤ, ∃ e'' : ℤ, (e'' = 1 ∨ e'' = -1) ∧
      ξ * nfw r l e' N * ξ = nfw r l e'' (N.map Neg.neg))
    (L : List ℤ) (hL : L.Pairwise (· > ·)) (hL1 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ))
    (hrel : nfw r l e (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) = 1) :
    ∃ K : List ℤ, (∀ t ∈ K, 1 ≤ t ∧ t ≤ ((s - i : ℕ) : ℤ)) ∧ nfw r l 1 K = 1 ∧
      ∀ a : ℤ, 1 ≤ a → K.count a =
        (if a + i ∈ L then 1 else 0) + (if (s : ℤ) - i - a ∈ L then 1 else 0) +
          (if a = (s : ℤ) - 2 * i then 1 else 0) := by
  classical
  obtain ⟨f₁, hf₁⟩ : ∃ f : ℤ → ℤ, ∀ t, f t = t - i := ⟨fun t => t - i, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : ℤ → ℤ, ∀ t, f t = (s : ℤ) - t - i :=
    ⟨fun t => (s : ℤ) - t - i, fun _ => rfl⟩
  have hφ' : ∀ K : List ℤ, Even K.length → φ (nfw r l e K) = nfw r l e (K.map f₁) := by
    intro K hK
    rw [hφ K hK]
    congr 1
    exact List.map_congr_left fun t _ => (hf₁ t).symm
  set LH := L.filter (fun t => decide ((i : ℤ) ≤ t)) with hLH
  set LL := L.filter (fun t => !decide ((i : ℤ) ≤ t)) with hLL
  set LA := L.filter (fun t => decide ((s : ℤ) - i + 1 ≤ t)) with hLA
  set LB := L.filter (fun t => !decide ((s : ℤ) - i + 1 ≤ t)) with hLB
  have hs1 : L = LH ++ LL := decr_split i L hL
  have hs2 : L = LA ++ LB := decr_split ((s : ℤ) - i + 1) L hL
  have hW : (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]).map f₁ =
      LH.map f₁ ++ (LL.map f₁ ++ [0] ++ LA.map f₂) ++ (LB.map f₂ ++ [(s : ℤ) - i - i]) := by
    have e1 : L.map f₁ = LH.map f₁ ++ LL.map f₁ := by rw [← List.map_append, ← hs1]
    have e2 : L.map f₂ = LA.map f₂ ++ LB.map f₂ := by rw [← List.map_append, ← hs2]
    have hcomp : f₁ ∘ (fun t : ℤ => (s : ℤ) - t) = f₂ := funext fun t => by simp [hf₁, hf₂]
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, hcomp, hf₁, sub_self]
    rw [e1, e2]
    simp only [List.append_assoc]
  have hk : s - i < s := by omega
  have hsi : ((s - i : ℕ) : ℤ) = (s : ℤ) - i := by omega
  have hi1 : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
  have memLH : ∀ t ∈ LH, t ∈ L ∧ (i : ℤ) ≤ t := fun t ht => by
    simpa [hLH, List.mem_filter] using ht
  have memLL : ∀ t ∈ LL, t ∈ L ∧ t < (i : ℤ) := fun t ht => by
    simpa [hLL, List.mem_filter] using ht
  have memLA : ∀ t ∈ LA, t ∈ L ∧ (s : ℤ) - i + 1 ≤ t := fun t ht => by
    simpa [hLA, List.mem_filter] using ht
  have memLB : ∀ t ∈ LB, t ∈ L ∧ t < (s : ℤ) - i + 1 := fun t ht => by
    simpa [hLB, List.mem_filter] using ht
  have hP0 : ∀ t ∈ LH.map f₁, 0 ≤ t ∧ t ≤ ((s - i : ℕ) : ℤ) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have := memLH u hu
    have := hL1 u this.1
    rw [hf₁]
    omega
  have hQ0 : ∀ t ∈ LB.map f₂ ++ [(s : ℤ) - i - i], 0 ≤ t ∧ t ≤ ((s - i : ℕ) : ℤ) := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      have := memLB u hu
      have := hL1 u this.1
      rw [hf₂]
      omega
    · rw [List.mem_singleton] at ht
      subst ht
      omega
  have hN0 : ∀ t ∈ (LL.map f₁ ++ [0] ++ LA.map f₂).map Neg.neg,
      0 ≤ t ∧ t ≤ ((i - 1 : ℕ) : ℤ) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rcases List.mem_append.mp hu with hu | hu
    · rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
        have := memLL v hv
        have := hL1 v this.1
        simp only [hf₁]
        omega
      · rw [List.mem_singleton] at hu
        subst hu
        omega
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      have := memLA v hv
      have := hL1 v this.1
      rw [hf₂]
      omega
  have hs0 : s - i ≤ s := by omega
  have hlen : Even (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]).length := by
    simp only [List.length_append, List.length_map, List.length_singleton]
    exact ⟨L.length + 1, by omega⟩
  have h1 : nfw r l e (LH.map f₁ ++ (LL.map f₁ ++ [0] ++ LA.map f₂) ++
      (LB.map f₂ ++ [(s : ℤ) - i - i])) = 1 := by
    have := hφ' _ hlen
    rw [hrel, map_one, hW] at this
    exact this.symm
  have hsg : ∀ (e' : ℤ) (c : Prop) [Decidable c], (e' = 1 ∨ e' = -1) →
      ((if c then e' else -e') = 1 ∨ (if c then e' else -e') = -1) := by
    intro e' c _ he'
    split_ifs <;> omega
  rw [nfw_append, nfw_append] at h1
  generalize hP : LH.map f₁ = P at h1 hP0
  generalize hN : LL.map f₁ ++ [0] ++ LA.map f₂ = N at h1 hN0
  generalize hQ : LB.map f₂ ++ [(s : ℤ) - i - i] = Q at h1 hQ0
  generalize he₁ : (if Even P.length then e else -e) = e₁ at h1
  generalize he₂ : (if Even (P ++ N).length then e else -e) = e₂ at h1
  have he₁' : e₁ = 1 ∨ e₁ = -1 := by rw [← he₁]; exact hsg e _ he
  have he₂' : e₂ = 1 ∨ e₂ = -1 := by rw [← he₂]; exact hsg e _ he
  have hgP : nfw r l e P ∈ Hs (s - i) := nfw_mem_nonneg h hs0 P e hP0
  have hgQ : nfw r l e₂ Q ∈ Hs (s - i) := nfw_mem_nonneg h hs0 Q e₂ hQ0
  have hgN : nfw r l e₁ N = (nfw r l e P)⁻¹ * (nfw r l e₂ Q)⁻¹ := by
    calc nfw r l e₁ N = (nfw r l e P)⁻¹ * (nfw r l e P * nfw r l e₁ N * nfw r l e₂ Q) *
        (nfw r l e₂ Q)⁻¹ := by group
      _ = _ := by rw [h1]; group
  have hgN1 : nfw r l e₁ N ∈ Hs (s - i) := by
    rw [hgN]
    exact mul_mem (inv_mem hgP) (inv_mem hgQ)
  obtain ⟨e'', he'', hxi⟩ := hξ e₁ he₁' N
  have hxiN : ξ * nfw r l e₁ N * ξ ∈ Hs (i - 1) := by
    rw [hxi]
    exact nfw_mem_nonneg h (by omega) _ e'' (by
      intro t ht
      have := hN0 t ht
      simpa using this)
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right h.xi_sq
  have hmapmem : nfw r l e₁ N ∈ (Hs i).map (MulAut.conj ξ).toMonoidHom := by
    refine ⟨ξ * nfw r l e₁ N * ξ, Hs_mono h (by omega : i - 1 ≤ i) (by omega) hxiN, ?_⟩
    show ξ * (ξ * nfw r l e₁ N * ξ) * ξ⁻¹ = nfw r l e₁ N
    rw [hξi]
    calc ξ * (ξ * nfw r l e₁ N * ξ) * ξ = (ξ * ξ) * nfw r l e₁ N * (ξ * ξ) := by group
      _ = nfw r l e₁ N := by rw [h.xi_sq]; simp
  have hN_one : nfw r l e₁ N = 1 := by
    have hmem : nfw r l e₁ N ∈ Hs (s - i) ⊓ (Hs i).map (MulAut.conj ξ).toMonoidHom :=
      ⟨hgN1, hmapmem⟩
    rw [h.inter i (by omega)] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [hN_one, mul_one] at h1
  have hPQ0 : ∀ t ∈ P ++ Q, 0 ≤ t ∧ t ≤ ((s - i : ℕ) : ℤ) := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hP0 t ht
    · exact hQ0 t ht
  have hPQ : nfw r l e (P ++ Q) = 1 := by
    rw [nfw_append, he₁]
    have : nfw r l e₁ Q = nfw r l e₂ Q := by
      rw [nfw_filter_zero h hk hab Q hQ0 e₁ 1 he₁' (Or.inl rfl),
        nfw_filter_zero h hk hab Q hQ0 e₂ 1 he₂' (Or.inl rfl)]
    rw [this]
    exact h1
  have hinj1 : Function.Injective f₁ := fun x y hxy => by
    have := hf₁ x
    have := hf₁ y
    omega
  have hinj2 : Function.Injective f₂ := fun x y hxy => by
    have := hf₂ x
    have := hf₂ y
    omega
  refine ⟨(P ++ Q).filter (fun t => decide (t ≠ 0)), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp ht
    have := hPQ0 t hmem
    simp only [decide_eq_true_eq] at hne
    omega
  · have := nfw_filter_zero h hk hab (P ++ Q) hPQ0 e 1 he (Or.inl rfl)
    rw [← this]
    exact hPQ
  · intro a ha
    rw [count_filter_ite, List.count_append, ← hP, ← hQ, List.count_append]
    have hne : decide (a ≠ 0) = true := by simpa using (by omega : a ≠ 0)
    simp only [hne, ite_true]
    have c1 : List.count a (List.map f₁ LH) = if a + (i : ℤ) ∈ L then 1 else 0 := by
      have := List.count_map_of_injective LH f₁ hinj1 (a + i)
      rw [hf₁, add_sub_cancel_right] at this
      rw [this, hLH, count_filter_ite, count_eq_ite hL]
      have hp : decide ((i : ℤ) ≤ a + i) = true := by
        simpa using (by omega : (i : ℤ) ≤ a + i)
      simp only [hp, ite_true]
    have c2 : List.count a (List.map f₂ LB) = if (s : ℤ) - i - a ∈ L then 1 else 0 := by
      have := List.count_map_of_injective LB f₂ hinj2 ((s : ℤ) - i - a)
      have e2 : f₂ ((s : ℤ) - i - a) = a := by rw [hf₂]; ring
      rw [e2] at this
      rw [this, hLB, count_filter_ite, count_eq_ite hL]
      have hp : (!decide ((s : ℤ) - i + 1 ≤ (s : ℤ) - i - a)) = true := by
        simpa using (by omega : (s : ℤ) - i - a < (s : ℤ) - i + 1)
      simp only [hp, ite_true]
    have c3 : List.count a [(s : ℤ) - i - i] = if a = (s : ℤ) - 2 * i then 1 else 0 := by
      rw [List.count_singleton']
      split_ifs with h1 h2 h2 <;> first | rfl | omega
    rw [c1, c2, c3, add_assoc]

theorem core_support (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : 2 * i ≤ s)
    (hab : Abel Hs (s - i)) (e : ℤ) (he : e = 1 ∨ e = -1) (φ : H →* H)
    (hφ : ∀ K : List ℤ, Even K.length → φ (nfw r l e K) = nfw r l e (K.map (· - i)))
    (hξ : ∀ e' : ℤ, (e' = 1 ∨ e' = -1) → ∀ N : List ℤ, ∃ e'' : ℤ, (e'' = 1 ∨ e'' = -1) ∧
      ξ * nfw r l e' N * ξ = nfw r l e'' (N.map Neg.neg))
    (L : List ℤ) (hL : L.Pairwise (· > ·)) (hL1 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ))
    (hrel : nfw r l e (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) = 1) :
    ∀ b : ℤ, (i : ℤ) < b → b < s →
      (Xor (b ∈ L) ((s : ℤ) - b ∈ L) ↔ (2 * i < s ∧ b = (s : ℤ) - i)) := by
  obtain ⟨K, hK1, hK, hcount⟩ := core_list h hi his hab e he φ hφ hξ L hL hL1 hrel
  have hk : s - i < s := by omega
  have heven := nfw_abel_eq_one h hk hab 1 (Or.inl rfl) K hK1 hK
  intro b hb1 hb2
  have h1 := heven (b - i)
  rw [hcount (b - i) (by omega)] at h1
  have e1 : b - (i : ℤ) + i = b := by ring
  have e2 : (s : ℤ) - i - (b - i) = (s : ℤ) - b := by ring
  have hr : (b - (i : ℤ) = (s : ℤ) - 2 * i) ↔ b = (s : ℤ) - i := by omega
  have hr2 : (2 * i < s ∧ b = (s : ℤ) - i) ↔ b = (s : ℤ) - i :=
    ⟨fun hh => hh.2, fun hh => ⟨by omega, hh⟩⟩
  rw [e1, e2] at h1
  rw [hr2]
  by_cases r' : b = (s : ℤ) - i
  · subst r'
    have hr' : (s : ℤ) - i - i = (s : ℤ) - 2 * i := by ring
    by_cases p : (s : ℤ) - i ∈ L <;> by_cases q : (i : ℤ) ∈ L <;>
      simp [p, q, hr', Xor, Nat.even_iff] at h1 ⊢
  · by_cases p : b ∈ L <;> by_cases q : (s : ℤ) - b ∈ L <;>
      simp [p, q, r', hr, Xor, Nat.even_iff] at h1 ⊢

end CFSG.Quasithin.Fan86.Tutte
