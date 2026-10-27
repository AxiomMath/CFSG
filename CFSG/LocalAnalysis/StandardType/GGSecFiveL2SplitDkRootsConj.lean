module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def flip2 {k : ℕ} (x y : Fin k) (u : Fin k → ℤ) : Fin k → ℤ :=
  fun c => if c = x ∨ c = y then -u c else u c

private theorem flip2_flip {k : ℕ} {x y a : Fin k} (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (P Q : ℤ) :
    flip2 x y (Pi.single a P + Pi.single x Q) = Pi.single a P + Pi.single x (-Q) := by
  funext c
  simp only [flip2]
  by_cases hcx : c = x
  · rw [if_pos (Or.inl hcx), hcx, ggDPair_apply_right hax, ggDPair_apply_right hax]
  by_cases hcy : c = y
  · rw [if_pos (Or.inr hcy), hcy, ggDPair_apply_of_ne (Ne.symm hay) (Ne.symm hxy),
      ggDPair_apply_of_ne (Ne.symm hay) (Ne.symm hxy), neg_zero]
  rw [if_neg (not_or.2 ⟨hcx, hcy⟩)]
  simp only [Pi.add_apply, Pi.single_eq_of_ne hcx]

private theorem pair_comp {k : ℕ} (σ : Equiv.Perm (Fin k)) {a b p q : Fin k} (hσa : σ a = p)
    (hσb : σ b = q) (P Q : ℤ) :
    (Pi.single p P + Pi.single q Q : Fin k → ℤ) ∘ σ = Pi.single a P + Pi.single b Q := by
  subst hσa hσb
  rw [Pi.add_comp, Pi.single_comp_equiv, Pi.single_comp_equiv, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

private theorem exists_perm_two {k : ℕ} {a b p q : Fin k} (hab : a ≠ b) (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm (Fin k), σ a = p ∧ σ b = q := by
  have hba := hab.symm
  have hqp := hpq.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![a, b] ![p, q]
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨σ, by simpa using hσ 0, by simpa using hσ 1⟩

private theorem exists_perm_four {k : ℕ} {a b c d a' b' c' d' : Fin k} (hab : a ≠ b)
    (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hab' : a' ≠ b')
    (hcd' : c' ≠ d') (hac' : a' ≠ c') (had' : a' ≠ d') (hbc' : b' ≠ c') (hbd' : b' ≠ d') :
    ∃ σ : Equiv.Perm (Fin k), σ a = a' ∧ σ b = b' ∧ σ c = c' ∧ σ d = d' := by
  have := hab.symm; have := hcd.symm; have := hac.symm; have := had.symm; have := hbc.symm
  have := hbd.symm; have := hab'.symm; have := hcd'.symm; have := hac'.symm
  have := had'.symm; have := hbc'.symm; have := hbd'.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![a, b, c, d] ![a', b', c', d']
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨σ, by simpa using hσ 0, by simpa using hσ 1, by simpa using hσ 2, by simpa using hσ 3⟩

private theorem exists_notMem {k : ℕ} (s : Finset (Fin k)) (hs : s.card < k) :
    ∃ z : Fin k, z ∉ s := by
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s)
    (t := Finset.univ) (by rwa [Finset.card_univ, Fintype.card_fin])
  exact ⟨z, hz⟩

private theorem conj_mul {k : ℕ} {w g x : ggWeylD k} {γ : Fin k → ℤ}
    {f : (Fin k → ℤ) → Fin k → ℤ} (h : GGDReflRoot k (w * x * w⁻¹) γ)
    (hg : ∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g v) = f (toStdD k v)) :
    GGDReflRoot k (g * w * x * (g * w)⁻¹) (f γ) := by
  have e : g * w * x * (g * w)⁻¹ = g * (w * x * w⁻¹) * g⁻¹ := by group
  rw [e]
  exact h.conj hg

private theorem fork_roots {k : ℕ} (hk : 2 ≤ k) :
    toStdD k (Pi.single ⟨k - 2, by omega⟩ 1) =
        Pi.single ⟨k - 2, by omega⟩ 1 + Pi.single ⟨k - 1, by omega⟩ (-1) ∧
      toStdD k (Pi.single ⟨k - 1, by omega⟩ 1) =
        Pi.single ⟨k - 2, by omega⟩ 1 + Pi.single ⟨k - 1, by omega⟩ 1 := by
  constructor <;> funext c <;>
    simp only [toStdD, Pi.add_apply, Pi.single_apply, Fin.ext_iff] <;> split_ifs <;> omega

theorem ggDk_sameSupp_conj {k : ℕ} (hk : 4 ≤ k) {t t' : ggWeylD k} (h : GGDSameSupp k t t') :
    ∃ w : ggWeylD k,
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple ⟨k - 2, by omega⟩ * w⁻¹ = t ∧
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple ⟨k - 1, by omega⟩ * w⁻¹ = t' := by
  obtain ⟨a, b, s, hab, hs, ht, ht'⟩ := h
  have hk2 : 2 ≤ k := by omega
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_two hab
    (Fin.ne_of_val_ne (by simp only; omega) : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩)
  obtain ⟨g, hg⟩ := ggD_exists_perm hk2 σ
  have hp : GGDReflRoot k
      (g * (coxeterMatrix (isFiniteType_cartanD k)).simple ⟨k - 2, by omega⟩ * g⁻¹)
      (toStdD k (Pi.single ⟨k - 2, by omega⟩ 1) ∘ σ) :=
    (ggDReflRoot_simple k _).conj (f := fun u => u ∘ σ) hg
  have hq : GGDReflRoot k
      (g * (coxeterMatrix (isFiniteType_cartanD k)).simple ⟨k - 1, by omega⟩ * g⁻¹)
      (toStdD k (Pi.single ⟨k - 1, by omega⟩ 1) ∘ σ) :=
    (ggDReflRoot_simple k _).conj (f := fun u => u ∘ σ) hg
  rw [(fork_roots hk2).1, pair_comp σ hσa hσb] at hp
  rw [(fork_roots hk2).2, pair_comp σ hσa hσb] at hq
  rcases hs with rfl | rfl
  · obtain ⟨z, hz⟩ := exists_notMem {a, b} (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    obtain ⟨g', hg'⟩ := ggD_exists_negPair hk2 (Ne.symm hz.2)
    have hg'' : ∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g' v) =
        flip2 b z (toStdD k v) := hg'
    have hp' := conj_mul hp hg''
    have hq' := conj_mul hq hg''
    rw [flip2_flip hab (Ne.symm hz.1) (Ne.symm hz.2), neg_neg] at hp'
    rw [flip2_flip hab (Ne.symm hz.1) (Ne.symm hz.2)] at hq'
    refine ⟨g' * g, hp'.unique hk2 ht (Or.inl rfl), hq'.unique hk2 ht' (Or.inl ?_)⟩
    rw [sub_eq_add_neg, Pi.single_neg]
  · refine ⟨g, hp.unique hk2 ht (Or.inl rfl), hq.unique hk2 ht' (Or.inl ?_)⟩
    rw [Pi.single_neg, sub_neg_eq_add]

private theorem pair_pm {k : ℕ} (a b : Fin k) {P Q p q : ℤ} (hP : P = 1 ∨ P = -1)
    (hQ : Q = 1 ∨ Q = -1) (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) (h : P * Q = p * q) :
    (Pi.single a P + Pi.single b Q : Fin k → ℤ) = Pi.single a p + Pi.single b q ∨
      (Pi.single a P + Pi.single b Q : Fin k → ℤ) = -(Pi.single a p + Pi.single b q) := by
  have key : (P = p ∧ Q = q) ∨ (P = -p ∧ Q = -q) := by
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> rcases hp with rfl | rfl <;>
      rcases hq with rfl | rfl <;> omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (by rw [Pi.single_neg, Pi.single_neg, neg_add])

private theorem exists_signFix {k : ℕ} (hk : 2 ≤ k) {a b z : Fin k} (hab : a ≠ b) (haz : a ≠ z)
    (hbz : b ≠ z) {P Q p q : ℤ} (hP : P = 1 ∨ P = -1) (hQ : Q = 1 ∨ Q = -1)
    (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) :
    ∃ (g : ggWeylD k) (f : (Fin k → ℤ) → Fin k → ℤ),
      (∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g v) = f (toStdD k v)) ∧
      (f (Pi.single a P + Pi.single b Q) = Pi.single a p + Pi.single b q ∨
        f (Pi.single a P + Pi.single b Q) = -(Pi.single a p + Pi.single b q)) ∧
      ∀ u : Fin k → ℤ, u b = 0 → u z = 0 → f u = u := by
  by_cases h : P * Q = p * q
  · exact ⟨1, fun u => u, fun v => by rw [map_one, Module.End.one_apply],
      pair_pm a b hP hQ hp hq h, fun u _ _ => rfl⟩
  obtain ⟨g, hg⟩ := ggD_exists_negPair hk hbz
  refine ⟨g, flip2 b z, hg, ?_, fun u hb hz => ?_⟩
  · rw [flip2_flip hab haz hbz]
    refine pair_pm a b hP (by omega) hp hq ?_
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> rcases hp with rfl | rfl <;>
      rcases hq with rfl | rfl <;> omega
  · funext c
    simp only [flip2]
    split_ifs with hc
    · rcases hc with rfl | rfl
      · rw [hb, neg_zero]
      · rw [hz, neg_zero]
    · rfl

theorem ggDk_disjSupp_conj {k : ℕ} (hk : 5 ≤ k) {t t' : ggWeylD k} (h : GGDDisjSupp k t t')
    {a b : Fin k} (hab : a ≠ b) (h2 : ggCoxeterMatrixD k a b = 2)
    (hf : ¬ (a.val + 2 = k ∧ b.val + 1 = k)) (hf' : ¬ (a.val + 1 = k ∧ b.val + 2 = k)) :
    ∃ w : ggWeylD k, w * (coxeterMatrix (isFiniteType_cartanD k)).simple a * w⁻¹ = t ∧
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple b * w⁻¹ = t' := by
  obtain ⟨a₁, b₁, c₁, d₁, s, s', u, u', h1, h2', h3, h4, h5, h6, hs, hs', hu, hu', ht, ht'⟩ := h
  have hk2 : 2 ≤ k := by omega
  rcases ggCoxeterMatrixD_label_two (by omega) hab h2 with hfk | ⟨A, B, C, D, S, S', U, U', hAB,
    hCD, hAC, hAD, hBC, hBD, hS, hS', hU, hU', hsa, hsb⟩
  · rcases hfk with hfk | hfk
    exacts [absurd hfk hf, absurd hfk hf']
  obtain ⟨z, hz⟩ := exists_notMem {a₁, b₁, c₁, d₁}
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hza, hzb, hzc, hzd⟩ := hz
  obtain ⟨σ, hσa, hσb, hσc, hσd⟩ := exists_perm_four h1 h2' h3 h4 h5 h6 hAB hCD hAC hAD hBC hBD
  obtain ⟨g, hg⟩ := ggD_exists_perm hk2 σ
  have hp : GGDReflRoot k (g * (coxeterMatrix (isFiniteType_cartanD k)).simple a * g⁻¹)
      ((Pi.single A S + Pi.single B S') ∘ σ) := hsa.conj (f := fun u => u ∘ σ) hg
  have hq : GGDReflRoot k (g * (coxeterMatrix (isFiniteType_cartanD k)).simple b * g⁻¹)
      ((Pi.single C U + Pi.single D U') ∘ σ) := hsb.conj (f := fun u => u ∘ σ) hg
  rw [pair_comp σ hσa hσb] at hp
  rw [pair_comp σ hσc hσd] at hq
  obtain ⟨g₁, f₁, hg₁, hf₁, hfix₁⟩ :=
    exists_signFix hk2 h1 (Ne.symm hza) (Ne.symm hzb) hS hS' hs hs'
  obtain ⟨g₂, f₂, hg₂, hf₂, hfix₂⟩ :=
    exists_signFix hk2 h2' (Ne.symm hzc) (Ne.symm hzd) hU hU' hu hu'
  have hp₁ := (conj_mul hp hg₁).of_pm hf₁
  have hq₁ := conj_mul hq hg₁
  rw [hfix₁ _ (ggDPair_apply_of_ne h5 h6 U U') (ggDPair_apply_of_ne hzc hzd U U')] at hq₁
  have hp₂ := conj_mul hp₁ hg₂
  rw [hfix₂ _ (ggDPair_apply_of_ne (Ne.symm h4) (Ne.symm h6) s s')
    (ggDPair_apply_of_ne hza hzb s s')] at hp₂
  have hq₂ := (conj_mul hq₁ hg₂).of_pm hf₂
  exact ⟨g₂ * (g₁ * g), hp₂.unique hk2 ht (Or.inl rfl), hq₂.unique hk2 ht' (Or.inl rfl)⟩

end CFSG.StandardType

end
