module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexSpec

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

universe u

section Orbit

variable {X : Type u} [Group X] {V : Type*} [MulAction X V]

theorem orbOKR_spec (code : V → ℕ) {N k : ℕ} (gen : ℕ → X) (act : ℕ → ℕ → ℕ → Bool)
    (hsurj : ∀ c < N, ∃ w : V, code w = c)
    (hact : ∀ j < k, ∀ v w : V, act j (code v) (code w) = true → gen j • v = w) {root : V}
    {cnt : ℕ} {items : ℕ → Bool} {r : OrbRec}
    (hok : orbOKR N k act (code root) cnt items r = true) :
    ∀ i < cnt, ∃ h ∈ Subgroup.closure (gen '' Set.Iio k), ∃ w : V, code w = r.ord[i]! ∧
      h • root = w := by
  simp only [orbOKR, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h0⟩, hlt⟩, hstep⟩, -⟩ := hok
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨1, Subgroup.one_mem _, root, h0.symm, one_smul _ _⟩
    · have hs := allLt_spec hstep hi
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hs
      rcases hs with h | ⟨⟨hp, hl⟩, he⟩
      · exact absurd h hi0
      · obtain ⟨h', hh', w', hw', hr⟩ := ih _ hp (hp.trans hi)
        have hlti := allLt_spec hlt hi
        simp only [decide_eq_true_eq] at hlti
        obtain ⟨w, hw⟩ := hsurj _ hlti
        refine ⟨gen r.lab[i]! * h', Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hl, rfl⟩) hh',
          w, hw, ?_⟩
        rw [mul_smul, hr]
        apply hact _ hl
        rw [hw', hw]
        exact he

theorem orbOKR_cover (code : V → ℕ) {N k : ℕ} (gen : ℕ → X) (act : ℕ → ℕ → ℕ → Bool)
    (hsurj : ∀ c < N, ∃ w : V, code w = c)
    (hact : ∀ j < k, ∀ v w : V, act j (code v) (code w) = true → gen j • v = w)
    (hinj : Function.Injective code) (hN : ∀ v : V, code v < N) {root : V} {cnt : ℕ}
    {items : ℕ → Bool} {r : OrbRec} (hok : orbOKR N k act (code root) cnt items r = true) {v : V}
    (hv : items (code v) = true) : ∃ h ∈ Subgroup.closure (gen '' Set.Iio k), h • root = v := by
  have hspec := orbOKR_spec code gen act hsurj hact hok
  simp only [orbOKR, Bool.and_eq_true, beq_iff_eq] at hok
  have := allLt_spec hok.2 (hN v)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at this
  rcases this with h | ⟨hlt, hpos⟩
  · rw [hv] at h
    exact absurd h (by decide)
  · obtain ⟨h, hh, w, hw, hr⟩ := hspec _ hlt
    refine ⟨h, hh, ?_⟩
    have : code w = code v := by rw [hw, hpos]
    rw [hr, hinj this]

end Orbit

variable {X : Type u} [Group X] [MulAction X HexVtx]

@[expose] def ActsAs (x : X) (t : Array ℕ) : Prop :=
  ∀ p : Fin 819, ∃ q : Fin 819, t[(p : ℕ)]! = (q : ℕ) ∧ x • (Sum.inl p : HexVtx) = Sum.inl q

theorem ActsAs.mul {x y : X} {t u : Array ℕ} (hx : ActsAs x t) (hy : ActsAs y u) :
    ActsAs (x * y) (compA 819 t u) := by
  intro p
  obtain ⟨q, hq, hyq⟩ := hy p
  obtain ⟨q', hq', hxq⟩ := hx q
  refine ⟨q', ?_, ?_⟩
  · rw [compA_get p.2, hq]
    exact hq'
  · rw [mul_smul, hyq, hxq]

theorem actsAs_one : ActsAs (1 : X) (idA 819) := by
  intro p
  exact ⟨p, idA_get p.2, one_smul _ _⟩

@[expose] def wordElt (g : ℕ → X) : List ℕ → X
  | [] => 1
  | l :: w => g l * wordElt g w

theorem actsAs_wordElt {g : ℕ → X} {G : Array (Array ℕ)} {k : ℕ}
    (hg : ∀ j < k, ActsAs (g j) G[j]!) :
    ∀ w : List ℕ, (∀ l ∈ w, l < k) → ActsAs (wordElt g w) (hexEvalArr G w)
  | [], _ => actsAs_one
  | l :: w, hw =>
    (hg l (hw l (List.mem_cons_self))).mul
      (actsAs_wordElt hg w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')))

theorem hexWordsOK_spec {k : ℕ} {ws : List String} (h : hexWordsOK k ws = true) :
    ∀ s ∈ ws, ∀ l ∈ hexDecode s, l < k := by
  intro s hs l hl
  simp only [hexWordsOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h s hs l hl

theorem hexWordArrs_size (G : Array (Array ℕ)) (ws : List String) :
    (hexWordArrs G ws).size = ws.length := by
  simp [hexWordArrs]

theorem hexWordArrs_get (G : Array (Array ℕ)) (ws : List String) {i : ℕ} (hi : i < ws.length) :
    (hexWordArrs G ws)[i]! = hexEvalArr G (hexDecode ws[i]!) := by
  simp [hexWordArrs, hi]

section Lines

variable [GraphAction X hexGraph] (hmeet : LineMeet) (hp : hexPtsOK lineTab = true)

include hmeet hp

theorem smul_inr_of_lineMaps {x : X} {t : Array ℕ} (hx : ActsAs x t) {v w : Fin 2457}
    (h : hexLineMaps lineTab t v w = true) : x • (Sum.inr v : HexVtx) = Sum.inr w := by
  obtain ⟨h1, h2, h3⟩ := hexPtsOK_spec hp v v.2
  simp only [hexLineMaps, List.all_eq_true, List.mem_range] at h
  have e0 := h 0 (by norm_num)
  have e1 := h 1 (by norm_num)
  let p₀ : Fin 819 := ⟨lineTab[3 * (v : ℕ)]!, by omega⟩
  let p₁ : Fin 819 := ⟨lineTab[3 * (v : ℕ) + 1]!, by omega⟩
  obtain ⟨q₀, hq₀, hxq₀⟩ := hx p₀
  obtain ⟨q₁, hq₁, hxq₁⟩ := hx p₁
  have hqw₀ : q₀ ∈ hexLine w := by
    rw [mem_hexLine_iff, ← hq₀]
    exact e0
  have hqw₁ : q₁ ∈ hexLine w := by
    rw [mem_hexLine_iff, ← hq₁]
    exact e1
  have ha₀ : hexGraph.Adj (Sum.inl p₀) (Sum.inr v) := ⟨0, by norm_num, rfl⟩
  have ha₁ : hexGraph.Adj (Sum.inl p₁) (Sum.inr v) := ⟨1, by norm_num, rfl⟩
  have hne : q₀ ≠ q₁ := by
    intro e
    rw [e] at hxq₀
    have := smul_left_cancel x (hxq₀.trans hxq₁.symm)
    have := Sum.inl.inj this
    have := congrArg Fin.val this
    simp only [p₀, p₁] at this
    omega
  have a₀ := (GraphAction.adj_smul x (Sum.inl p₀) (Sum.inr v)).mpr ha₀
  have a₁ := (GraphAction.adj_smul x (Sum.inl p₁) (Sum.inr v)).mpr ha₁
  rw [hxq₀] at a₀
  rw [hxq₁] at a₁
  generalize x • (Sum.inr v : HexVtx) = u at a₀ a₁
  cases u with
  | inl r => exact absurd a₀ hexGraph_not_adj_inl
  | inr w' => exact congrArg Sum.inr (hmeet w' w q₀ q₁ hne a₀ a₁ hqw₀ hqw₁)

theorem smul_hexOfCode_of_actOK {x : X} {t : Array ℕ} (hx : ActsAs x t) {y c : ℕ} (hy : y < 3276)
    (hc : c < 3276) (h : hexActOK lineTab t y c = true) : x • hexOfCode y = hexOfCode c := by
  by_cases hy1 : y < 819
  · simp only [hexActOK, hy1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hc1, htc⟩ := h
    obtain ⟨q, hq, hxq⟩ := hx ⟨y, hy1⟩
    rw [hexOfCode_inl hy1, hexOfCode_inl hc1, hxq]
    exact congrArg Sum.inl (Fin.ext (by rw [← hq]; exact htc))
  · simp only [hexActOK, hy1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc1, -⟩, hmaps⟩ := h
    rw [hexOfCode_inr (by omega) hy, hexOfCode_inr hc1 hc]
    exact smul_inr_of_lineMaps hmeet hp hx hmaps

end Lines

end CFSG.Quasithin.D4Hex
