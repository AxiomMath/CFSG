module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.PartThree.Ten.SwapKlein
import CFSG.Timmesfeld.Bridge.Asc72WreathConn

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

namespace TenTwoQ

open Equiv SemidirectProduct WreathEndgame

variable {f n : ℕ}

theorem exists_two_off (hn : 5 ≤ n) (a b c : Fin n) :
    ∃ k l : Fin n, k ≠ l ∧ k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ l ≠ a ∧ l ≠ b ∧ l ≠ c := by
  classical
  have hc : 1 < (({a, b, c} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 hc
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
  exact ⟨k, l, hkl, hk.1, hk.2.1, hk.2.2, hl.1, hl.2.1, hl.2.2⟩

theorem perm_eq_one_of_fix {i j : Fin n} (hij : i ≠ j) (σ : Perm (Fin n))
    (hfix : ∀ k, k ≠ i → k ≠ j → σ k = k) (hsign : Perm.sign σ = 1) : σ = 1 := by
  by_cases hσi : σ i = i
  · have hσj : σ j = j := by
      by_contra hne
      have h1 : σ j ≠ i := fun h => hij (σ.injective (h.trans hσi.symm)).symm
      have := hfix (σ j) h1 hne
      exact hne (σ.injective this)
    ext p
    by_cases hpi : p = i
    · rw [hpi, hσi]; rfl
    by_cases hpj : p = j
    · rw [hpj, hσj]; rfl
    · rw [hfix p hpi hpj]; rfl
  · exfalso
    have hσi' : σ i = j := by
      by_contra hne
      have := hfix (σ i) hσi hne
      exact hσi (σ.injective this)
    have hσj : σ j = i := by
      by_contra hne
      have h1 : σ j ≠ j := fun h => hij (σ.injective (hσi'.trans h.symm))
      have := hfix (σ j) hne h1
      exact h1 (σ.injective this)
    have hσ : σ = swap i j := by
      ext p
      by_cases hpi : p = i
      · rw [hpi, hσi', swap_apply_left]
      by_cases hpj : p = j
      · rw [hpj, hσj, swap_apply_right]
      · rw [hfix p hpi hpj, swap_apply_of_ne_of_ne hpi hpj]
    rw [hσ, Perm.sign_swap hij] at hsign
    exact absurd hsign (by decide)

theorem apply_mem_of_commute_swap {k l : Fin n} (hkl : k ≠ l) {σ : Perm (Fin n)}
    (h : σ * swap k l = swap k l * σ) : σ k = k ∨ σ k = l := by
  by_contra hne
  push Not at hne
  have h1 := congrArg (fun τ : Perm (Fin n) => τ k) h
  simp only [Perm.mul_apply, swap_apply_left] at h1
  rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h1
  have h2 : σ l = σ k := by rw [h1]
  exact hkl (σ.injective h2).symm

theorem fixes_and_left_of_commute_swaps (hf : 2 ≤ f) (hn : 5 ≤ n) {i j : Fin n}
    {c : L2Wreath f n}
    (hcommS : ∀ (k l : Fin n) (b : PSL2Model f), k ≠ l → k ≠ i → k ≠ j → l ≠ i → l ≠ j →
      Commute c (swp b k l)) :
    ∀ k : Fin n, k ≠ i → k ≠ j → c.right k = k ∧ c.left k = 1 := by
  intro k hki hkj
  obtain ⟨l, l', hll', hlk, hli, hlj, hl'k, hl'i, hl'j⟩ := exists_two_off hn k i j
  have hperm : ∀ m : Fin n, m ≠ k → m ≠ i → m ≠ j → c.right k = k ∨ c.right k = m := by
    intro m hmk hmi hmj
    have h := (hcommS k m 1 hmk.symm hki hkj hmi hmj).eq
    have h' := congrArg SemidirectProduct.right h
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, swp_right] at h'
    exact apply_mem_of_commute_swap hmk.symm h'
  have hk : c.right k = k := by
    rcases hperm l hlk hli hlj with h | h
    · exact h
    · rcases hperm l' hl'k hl'i hl'j with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hll'
  refine ⟨hk, ?_⟩
  have hinv : c.right⁻¹ k = k := by
    rw [Perm.inv_def]
    exact (Equiv.symm_apply_eq _).2 hk.symm
  have key : ∀ b : PSL2Model f, c.left k * b = b * c.left l := by
    intro b
    have h := (hcommS k l b (Ne.symm hlk) hki hkj hli hlj).eq
    have h' := congrArg (fun x : L2Wreath f n => x.left k) h
    simp only [WreathClass.mul_left_apply, hinv, swp_right, swap_inv, swap_apply_left,
      swp_left_fst (Ne.symm hlk)] at h'
    exact h'
  have h1 : c.left k = c.left l := by simpa using key 1
  have hcen : c.left k ∈ Subgroup.center (PSL2Model f) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have := key b
    rw [← h1] at this
    exact this.symm
  rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hcen
  exact hcen

theorem left_eq_one_of_commute_swp (hf : 2 ≤ f) {i j : Fin n} (hij : i ≠ j) {c : L2Wreath f n}
    (hσ : c.right = 1) {a : PSL2Model f}
    (hc : ∀ t : PSL2Model f, t * t = 1 → Commute c (swp (t * a) i j))
    (hw : Commute c (swp a i j)) : c.left i = 1 ∧ c.left j = 1 := by
  have hE : ∀ b : PSL2Model f, Commute c (swp b i j) → c.left i * b = b * c.left j := by
    intro b h
    have h' := congrArg (fun x : L2Wreath f n => x.left i) h.eq
    simpa only [WreathClass.mul_left_apply, hσ, inv_one, Perm.one_apply, swp_right, swap_inv,
      swap_apply_left, swp_left_fst hij] using h'
  have hEw := hE a hw
  have hj : c.left j = a⁻¹ * c.left i * a := by
    calc c.left j = a⁻¹ * (a * c.left j) := by group
      _ = a⁻¹ * c.left i * a := by rw [← hEw]; group
  have hinv : ∀ t : PSL2Model f, t * t = 1 → Commute (c.left i) t := by
    intro t ht
    have h1 := hE _ (hc t ht)
    show c.left i * t = t * c.left i
    calc c.left i * t = (c.left i * (t * a)) * a⁻¹ := by group
      _ = ((t * a) * c.left j) * a⁻¹ := by rw [h1]
      _ = t * c.left i := by rw [hj]; group
  have hyi : c.left i = 1 := by
    have hle : Subgroup.closure {t : PSL2Model f | t * t = 1} ≤
        Subgroup.centralizer {c.left i} := by
      rw [Subgroup.closure_le]
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.2 (hinv t ht).symm.eq
    rw [WreathConn.closure_mul_self_eq_one_eq_top hf] at hle
    have hcen : c.left i ∈ Subgroup.center (PSL2Model f) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
    rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hcen
    exact hcen
  exact ⟨hyi, by rw [hj, hyi]; group⟩

theorem eq_one_of_commute_swaps (hf : 2 ≤ f) (hn : 5 ≤ n) {w : L2Wreath f n}
    (hw : w ∈ swapSet f n) {c : L2Wreath f n}
    (hc : ∀ s ∈ swapSet f n, Commute s w → Commute c s) (heven : Perm.sign c.right = 1) :
    c = 1 := by
  obtain ⟨i, j, hij, hwr, -⟩ := id hw
  obtain ⟨a, rfl⟩ : ∃ a, w = swp a i j := ⟨_, eq_swp_of_right_eq hw hij hwr⟩
  have hS := fixes_and_left_of_commute_swaps hf hn (i := i) (j := j) (c := c)
    (fun k l b hkl hki hkj hli hlj => hc _ (swp_mem hkl)
      (commute_of_disjoint_right (swp_mem hkl) hw (by
        rw [swp_right, hwr]
        exact (swapDisjoint_iff hkl hij).2 ⟨hki, hkj, hli, hlj⟩)))
  have hσ : c.right = 1 :=
    perm_eq_one_of_fix hij c.right (fun k hki hkj => (hS k hki hkj).1) heven
  obtain ⟨hyi, hyj⟩ := left_eq_one_of_commute_swp hf hij hσ
    (fun t ht => hc _ (swp_mem hij) (by
      have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      refine SwapKlein.commute_swp_swp _ _ hij ?_ ?_
      · rw [mul_inv_rev, ht']; group
      · rw [mul_inv_rev, ht']; group))
    (hc _ hw (Commute.refl _))
  refine SemidirectProduct.ext (funext fun p => ?_) (by rw [hσ]; rfl)
  by_cases hpi : p = i
  · rw [hpi]; exact hyi
  by_cases hpj : p = j
  · rw [hpj]; exact hyj
  · exact (hS p hpi hpj).2

theorem swp_swap_eq (a : PSL2Model f) {k l : Fin n} (hkl : k ≠ l) :
    swp a l k = swp a⁻¹ k l := by
  refine SemidirectProduct.ext ?_ (by rw [swp_right, swp_right, swap_comm])
  funext p
  by_cases hpk : p = k
  · rw [hpk, swp_left_snd hkl.symm, swp_left_fst hkl]
  by_cases hpl : p = l
  · rw [hpl, swp_left_fst hkl.symm, swp_left_snd hkl, inv_inv]
  · rw [swp_left_of_ne hpl hpk, swp_left_of_ne hpk hpl]

theorem coordHom_mem_of_swp_mem (hf : 2 ≤ f) {k l : Fin n} (hkl : k ≠ l)
    (Γ : Subgroup (L2Wreath f n)) (hΓ : ∀ a : PSL2Model f, swp a k l ∈ Γ) (b : PSL2Model f) :
    SetupQ.coordHom f n k b ∈ Γ := by
  classical
  let ε : Fin 2 ↪ Fin n := ⟨![k, l], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]⟩
  have hε0 : ε 0 = k := rfl
  have hε1 : ε 1 = l := rfl
  have hcl : Subgroup.closure (swapSet f 2) ≤ Γ.comap (wreathExt f ε) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨p, q, hpq, hr, h1, h2⟩ := hs
    show wreathExt f ε s ∈ Γ
    rw [eq_swp hpq hr h1 h2, wreathExt_swp]
    have hcases : ∀ p q : Fin 2, p ≠ q → (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by decide
    rcases hcases p q hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hε0, hε1]; exact hΓ _
    · rw [hε0, hε1, swp_swap_eq _ hkl]; exact hΓ _
  have hmem : SetupQ.coordHom f 2 0 b ∈ Subgroup.closure (swapSet f 2) := by
    rw [closure_swapSet_eq_top hf le_rfl]; trivial
  have hid : wreathExt f ε (SetupQ.coordHom f 2 0 b) = SetupQ.coordHom f n k b := by
    rw [SetupQ.coordHom_apply, SetupQ.coordHom_apply]
    refine SemidirectProduct.ext ?_ ?_
    · funext p
      rw [wreathExt_left, left_inl, left_inl]
      by_cases hp : ∃ r, ε r = p
      · obtain ⟨r, rfl⟩ := hp
        rw [ε.injective.extend_apply]
        fin_cases r
        · simp [hε0]
        · simp [hε1, Pi.mulSingle_eq_of_ne hkl.symm]
      · rw [Function.extend_apply' _ _ _ hp]
        have hpk : p ≠ k := fun h => hp ⟨0, h.symm⟩
        simp [Pi.mulSingle_eq_of_ne hpk]
    · rw [wreathExt_right, right_inl, right_inl]
      exact map_one (Equiv.Perm.viaEmbeddingHom ε)
  rw [← hid]
  exact hcl hmem

end TenTwoQ

end CFSG.OddTranspositions.PartThree

end
