module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusTrans

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin GGOppRad GGOppRadSpU
open CFSG.ClassicalGroups.Orthogonal (quadPlus_single)

variable {n : ℕ} {K : Type} [Field K]

theorem isTotallySingular_stdFlag {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ) {k : ℕ}
    (hk : 2 * k ≤ M + 1) : (plusForm n K).IsTotallySingular (stdFlag ℓ k) := by
  intro v hv
  rw [plusForm_Q, quadPlus_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  have := hℓ t
  by_cases h1 : k ≤ ℓ (Sum.inl t)
  · rw [hv _ h1, zero_mul]
  · rw [hv (Sum.inr t) (by omega), mul_zero]

theorem finrank_V : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]

theorem eq_or_eq_swap_of_middle {d : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel (2 * d) ℓ)
    (hdim : finrank K (stdFlag (K := K) ℓ d) + 1 = n) {c c' : Fin n ⊕ Fin n} (hc : ℓ c = d)
    (hc' : ℓ c' = d) : c' = c ∨ c' = c.swap := by
  classical
  have h1 := (spForm n K).finrank_perp (stdFlag (K := K) ℓ d)
  rw [perp_stdFlag hℓ d, show 2 * d + 1 - d = d + 1 by omega, finrank_stdFlag, finrank_stdFlag,
    finrank_V] at h1
  rw [finrank_stdFlag] at hdim
  simp only [Fintype.card_subtype] at h1 hdim
  by_contra hne
  push Not at hne
  have hcs : ℓ c.swap = d := by
    have := hℓ.add_swap c
    omega
  have hsc : c.swap ≠ c := fun h => by rcases c with c | c <;> simp at h
  have h3 : ({c, c.swap, c'} : Finset (Fin n ⊕ Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hsc.symm, hne.1.symm]),
      Finset.card_pair hne.2.symm]
  have hdisj : Disjoint (Finset.univ.filter fun a => ℓ a < d)
      ({c, c.swap, c'} : Finset (Fin n ⊕ Fin n)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha' with rfl | rfl | rfl <;> omega
  have hsub : (Finset.univ.filter fun a => ℓ a < d) ∪ {c, c.swap, c'} ⊆
      Finset.univ.filter fun a => ℓ a < d + 1 := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with ha | rfl | rfl | rfl <;> omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, h3] at this
  omega

theorem exists_isCompl_of_oriflamme [CharP K 2] {d : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ}
    (hℓ : IsSpLevel (2 * d) ℓ)
    (hdim : 2 * (finrank K (stdFlag (K := K) ℓ d) + 1) = finrank K (Fin n ⊕ Fin n → K))
    {X : Submodule K (Fin n ⊕ Fin n → K)} (hXd : 2 * finrank K X = finrank K (Fin n ⊕ Fin n → K))
    {x : Fin n ⊕ Fin n → K} (hxX : x ∈ X) (hxd : x ∉ stdFlag ℓ d)
    (hXx : X ⊓ (plusForm n K).polar.perp (stdFlag ℓ d) = K ∙ x)
    (hXs : (plusForm n K).IsTotallySingular X) :
    ∃ b, ℓ b = d ∧ (∀ c, ℓ c = d → c = b ∨ c = b.swap) ∧
      IsCompl (stdFlag ℓ d ⊔ K ∙ (Pi.single b 1 : Fin n ⊕ Fin n → K)) X := by
  classical
  rw [finrank_V] at hdim hXd
  have hperp : (plusForm n K).polar.perp (stdFlag ℓ d) = stdFlag ℓ (d + 1) := by
    rw [plusForm_polar, perp_stdFlag hℓ d, show 2 * d + 1 - d = d + 1 by omega]
  have hxp : x ∈ stdFlag ℓ (d + 1) := by
    rw [← hperp]
    exact (Submodule.mem_inf.mp (hXx ▸ Submodule.mem_span_singleton_self x : x ∈ _)).2
  obtain ⟨c, hcd, hxc⟩ : ∃ c, d ≤ ℓ c ∧ x c ≠ 0 := by
    by_contra! h
    exact hxd fun a ha => h a ha
  have hc : ℓ c = d := by
    by_contra hne
    exact hxc (hxp c (by omega))
  have huniq : ∀ c', ℓ c' = d → c' = c ∨ c' = c.swap :=
    fun c' hc' => eq_or_eq_swap_of_middle (K := K) hℓ (by omega) hc hc'
  have hcs : ℓ c.swap = d := by
    have := hℓ.add_swap c
    omega
  have hxs : x c.swap = 0 := by
    have hQ := hXs x hxX
    rw [plusForm_Q, quadPlus_apply] at hQ
    have key : ∀ t, x (Sum.inl t) * x (Sum.inr t) = 0 ∨ (Sum.inl t = c ∨ Sum.inr t = c) := by
      intro t
      by_cases h1 : Sum.inl t = c ∨ Sum.inr t = c
      · exact Or.inr h1
      left
      push Not at h1
      have hs := hℓ t
      have hl : ℓ (Sum.inl t) ≠ d := fun h => by
        rcases huniq _ h with h' | h'
        · exact h1.1 h'
        · have hct : c = Sum.inr t := by rw [← Sum.swap_swap c, ← h']; rfl
          exact h1.2 hct.symm
      by_cases h2 : d + 1 ≤ ℓ (Sum.inl t)
      · rw [hxp _ h2, zero_mul]
      · rw [hxp (Sum.inr t) (by omega), mul_zero]
    rcases c with t₀ | t₀
    · rw [Finset.sum_eq_single t₀ (fun t _ ht => (key t).resolve_right (by simpa using ht))
        (by simp)] at hQ
      exact (mul_eq_zero.mp hQ).resolve_left hxc
    · rw [Finset.sum_eq_single t₀ (fun t _ ht => (key t).resolve_right (by simpa using ht))
        (by simp)] at hQ
      exact (mul_eq_zero.mp hQ).resolve_right hxc
  refine ⟨c.swap, hcs, fun c' hc' => ?_, ?_⟩
  · rw [Sum.swap_swap]
    exact (huniq c' hc').symm
  have hsc : c.swap ≠ c := fun h => by rcases c with c | c <;> simp at h
  have hvan : stdFlag ℓ d ⊔ K ∙ (Pi.single c.swap 1 : Fin n ⊕ Fin n → K) ≤
      LinearMap.ker (LinearMap.proj c) := by
    refine sup_le (fun v hv => hv c (le_of_eq hc.symm)) ?_
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.proj_apply,
      Pi.single_eq_of_ne hsc.symm]
  have hle : stdFlag ℓ d ⊔ K ∙ (Pi.single c.swap 1 : Fin n ⊕ Fin n → K) ≤ stdFlag ℓ (d + 1) :=
    sup_le (stdFlag_mono ℓ (Nat.le_succ d))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (single_mem_stdFlag.mpr (by omega)))
  have hdis : (stdFlag ℓ d ⊔ K ∙ (Pi.single c.swap 1 : Fin n ⊕ Fin n → K)) ⊓ X = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    have hyx : y ∈ K ∙ x := by
      rw [← hXx, hperp]
      exact Submodule.mem_inf.mpr ⟨hy2, hle hy1⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hyx
    have h0 : (s • x) c = 0 := hvan hy1
    rw [Pi.smul_apply, smul_eq_mul] at h0
    rw [(mul_eq_zero.mp h0).resolve_right hxc, zero_smul]
    exact Submodule.zero_mem _
  have hnot : (Pi.single c.swap 1 : Fin n ⊕ Fin n → K) ∉ stdFlag ℓ d := fun h =>
    absurd (single_mem_stdFlag.mp h) (by omega)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (stdFlag ℓ d ⊔ K ∙ (Pi.single c.swap 1 : Fin n ⊕ Fin n → K)) X
  rw [hdis, finrank_bot, Submodule.finrank_sup_span_singleton hnot] at h1
  refine ⟨disjoint_iff.mpr hdis, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  rw [finrank_V]
  omega

@[expose] def varLevel (ℓ : Fin n ⊕ Fin n → ℕ) (d : ℕ) (b : Fin n ⊕ Fin n) : Fin n ⊕ Fin n → ℕ :=
  fun a => if a = b then 2 * d - 1 else if a = b.swap then 2 * d + 1 else 2 * ℓ a

theorem swap_ne_self (b : Fin n ⊕ Fin n) : b.swap ≠ b := fun h => by
  rcases b with b | b <;> simp at h

theorem polar_single_eq (v : Fin n ⊕ Fin n → K) (c : Fin n ⊕ Fin n) :
    polar (quadPlus n K) v (Pi.single c 1) = v c.swap := by
  rcases c with c | c
  · exact polar_quadPlus_single_inl n K v c
  · exact polar_quadPlus_single_inr n K v c

section Var

variable {d : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} {b : Fin n ⊕ Fin n}

theorem varLevel_of_ne {a : Fin n ⊕ Fin n} (h1 : a ≠ b) (h2 : a ≠ b.swap) :
    varLevel ℓ d b a = 2 * ℓ a := by
  simp [varLevel, h1, h2]

theorem varLevel_b : varLevel ℓ d b b = 2 * d - 1 := by
  simp [varLevel]

theorem varLevel_swap : varLevel ℓ d b b.swap = 2 * d + 1 := by
  simp [varLevel, swap_ne_self b]

variable (hℓ : IsSpLevel (2 * d) ℓ) (hd : 1 ≤ d) (hb : ℓ b = d)
  (huniq : ∀ c, ℓ c = d → c = b ∨ c = b.swap)

include hℓ hb in
theorem level_swap_eq : ℓ b.swap = d := by
  have := hℓ.add_swap b
  omega

include hℓ hd hb in
theorem isSpLevel_varLevel : IsSpLevel (4 * d) (varLevel ℓ d b) := by
  intro t
  have hbs := level_swap_eq hℓ hb
  by_cases h1 : Sum.inl t = b
  · subst h1
    rw [varLevel_b, show (Sum.inr t : Fin n ⊕ Fin n) = (Sum.inl t).swap from rfl, varLevel_swap]
    omega
  by_cases h2 : Sum.inr t = b
  · subst h2
    rw [show (Sum.inl t : Fin n ⊕ Fin n) = (Sum.inr t).swap from rfl, varLevel_swap, varLevel_b]
    omega
  have h3 : Sum.inl t ≠ b.swap := fun h => h2 (by rw [← Sum.swap_swap b, ← h]; rfl)
  have h4 : Sum.inr t ≠ b.swap := fun h => h1 (by rw [← Sum.swap_swap b, ← h]; rfl)
  rw [varLevel_of_ne h1 h3, varLevel_of_ne h2 h4]
  have := hℓ t
  omega

include hℓ hd hb huniq in
theorem stdFlag_varLevel (k : ℕ) :
    stdFlag (K := K) ℓ k = stdFlag (varLevel ℓ d b) (if k = d then 2 * d - 1 else 2 * k) := by
  have hbs := level_swap_eq hℓ hb
  have key : ∀ a, (k ≤ ℓ a ↔ (if k = d then 2 * d - 1 else 2 * k) ≤ varLevel ℓ d b a) := by
    intro a
    by_cases ha1 : a = b
    · subst ha1
      rw [varLevel_b, hb]
      split_ifs <;> omega
    by_cases ha2 : a = b.swap
    · subst ha2
      rw [varLevel_swap, hbs]
      split_ifs <;> omega
    · rw [varLevel_of_ne ha1 ha2]
      have hne : ℓ a ≠ d := fun h => (huniq a h).elim ha1 ha2
      split_ifs <;> omega
  ext v
  simp only [mem_stdFlag]
  exact ⟨fun h a ha => h a ((key a).mpr ha), fun h a ha => h a ((key a).mp ha)⟩

include hb in
theorem stdFlag_varLevel_two_mul (hd : 1 ≤ d) (hbs : ℓ b.swap = d) :
    stdFlag (varLevel ℓ d b) (2 * d) =
      stdFlag ℓ d ⊔ K ∙ (Pi.single b 1 : Fin n ⊕ Fin n → K) := by
  classical
  refine le_antisymm (fun v hv => ?_) (sup_le (fun v hv a ha => ?_) ?_)
  · have e : v = (v - v b • Pi.single b 1) + v b • Pi.single b 1 := by abel
    rw [e]
    refine Submodule.add_mem_sup (fun a ha => ?_) (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _))
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hab, smul_zero, sub_zero]
      refine hv a ?_
      by_cases has : a = b.swap
      · rw [has, varLevel_swap]
        omega
      · rw [varLevel_of_ne hab has]
        omega
  · by_cases hab : a = b
    · rw [hab, varLevel_b] at ha
      omega
    refine hv a ?_
    by_cases has : a = b.swap
    · rw [has, hbs]
    · rw [varLevel_of_ne hab has] at ha
      omega
  · rw [Submodule.span_singleton_le_iff_mem]
    exact single_mem_stdFlag.mpr (by rw [varLevel_b]; omega)

include hℓ hd hb huniq in
theorem isUniTri_of_varLevel {g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : ∀ v, quadPlus n K (g v) = quadPlus n K v) (h : IsUniTri (varLevel ℓ d b) g) :
    IsUniTri ℓ g := by
  classical
  have hbs := level_swap_eq hℓ hb
  intro a
  by_cases ha1 : a = b
  · subst ha1
    have := h a
    rw [varLevel_b] at this
    rw [hb, stdFlag_varLevel hℓ hd hb huniq d, ite_eq_left rfl]
    exact this
  by_cases ha2 : a = b.swap
  · subst ha2
    set w : Fin n ⊕ Fin n → K := g (Pi.single b.swap 1) - Pi.single b.swap 1 with hw
    have hw1 := h b.swap
    rw [varLevel_swap] at hw1
    change w ∈ stdFlag (varLevel ℓ d b) (2 * d + 1) at hw1
    have hQw : quadPlus n K w = 0 := by
      rw [quadPlus_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases ht : Sum.inl t = b.swap
      · rw [ht, hw1 b.swap (by rw [varLevel_swap]), zero_mul]
      by_cases ht' : Sum.inr t = b.swap
      · rw [ht', hw1 b.swap (by rw [varLevel_swap]), mul_zero]
      by_cases ht1 : Sum.inl t = b
      · have : Sum.inr t = b.swap := by rw [← ht1]; rfl
        exact absurd this ht'
      by_cases ht2 : Sum.inr t = b
      · have : Sum.inl t = b.swap := by rw [← ht2]; rfl
        exact absurd this ht
      have hs := hℓ t
      have hn1 : ℓ (Sum.inl t) ≠ d := fun h => (huniq _ h).elim ht1 ht
      by_cases hl : d + 1 ≤ ℓ (Sum.inl t)
      · rw [hw1 _ (by rw [varLevel_of_ne ht1 ht]; omega), zero_mul]
      · rw [hw1 (Sum.inr t) (by rw [varLevel_of_ne ht2 ht']; omega), mul_zero]
    have hwb : w b = 0 := by
      have h1 := hg (Pi.single b.swap 1)
      rw [quadPlus_single, show g (Pi.single b.swap 1) = Pi.single b.swap 1 + w by rw [hw]; abel,
        QuadraticMap.map_add (quadPlus n K), quadPlus_single, hQw, zero_add, zero_add, polar_comm,
        polar_single_eq, Sum.swap_swap] at h1
      exact h1
    intro c hc
    by_cases hcb : c = b
    · rw [hcb]
      exact hwb
    by_cases hcs : c = b.swap
    · rw [hcs]
      exact hw1 _ (by rw [varLevel_swap])
    · rw [hbs] at hc
      have hne : ℓ c ≠ d := fun h => (huniq c h).elim hcb hcs
      exact hw1 c (by rw [varLevel_of_ne hcb hcs]; omega)
  · have := h a
    rw [varLevel_of_ne ha1 ha2] at this
    have hne : ℓ a ≠ d := fun h => (huniq a h).elim ha1 ha2
    rw [stdFlag_varLevel hℓ hd hb huniq (ℓ a), ite_eq_right hne]
    exact this

end Var

end GGOppRadOmega

end CFSG.StandardType
