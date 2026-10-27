module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvOrth
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvE7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem fs81Nt_exists_ne5 (a b c d e : Fin 8) :
    ∃ k : Fin 8, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d ∧ k ≠ e := by
  classical
  have h : ({a, b, c, d, e} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc ({a, b, c, d, e} : Finset (Fin 8)).card ≤ ({b, c, d, e} : Finset (Fin 8)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ 4 + 1 := Nat.add_le_add_right Finset.card_le_four 1
      _ < 8 := by norm_num
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩

theorem dsign_prod_E7 : ∀ a b : Fin 8, a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → a ≠ b →
    ∏ i : Fin 6, dsign a b i.succ.succ = 1 := by
  decide

omit [Finite G] in
theorem e7_acts {B : Basis3 G (7 + 1)} {b₀ : G} (hloc : LocalE7 B b₀)
    {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s) (hσ0 : σ 0 = 0) (hs0 : s 0 = 1)
    (hσ1 : σ 1 = 1) (hprod : ∏ i : Fin 6, s i.succ.succ = 1) :
    ∃ g ∈ Subgroup.centralizer ({b₀} : Set G), B.Acts g (spMat σ s) := by
  have h : spMat σ s ∈ B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) := by
    rw [hloc.2.2]
    exact ⟨σ, s, hs, ⟨hσ0, hs0, hσ1, hprod⟩, rfl⟩
  obtain ⟨g, hg, hA⟩ := h
  exact ⟨g, hg.1, hA⟩

theorem e7_signRealized {B : Basis3 G (7 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (hloc : LocalE7 B b₀) {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hs0 : s 0 = 1) (hprod : ∏ i : Fin 6, s i.succ.succ = 1) : SignRealized B E s := by
  obtain ⟨g, -, hg⟩ := e7_acts hloc hs (Equiv.Perm.one_apply 0) hs0 (Equiv.Perm.one_apply 1) hprod
  exact ⟨hs, hs0, g, hB.1 ▸ B.mem_normalizer_of_acts hg, hg⟩

theorem e7SignData {B : Basis3 G (7 + 1)} {b₀ : G} {K E : Subgroup G} (hB : Adapted B b₀ K E)
    (hord : orderOf b₀ = 3) (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K))
    (hKn : ∀ g ∈ Subgroup.centralizer ({b₀} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    (hloc : LocalE7 B b₀) :
    SignChanges B.b b₀ E ∧ DiagSigns B E ∧ CoordTrans B b₀ E ∧ KleinSigns B E ∧
      DiagSigns3 B E ∧
      (∃ k₀ k₁ : Fin (7 + 1), k₀ ≠ 0 ∧ k₁ ≠ 0 ∧ k₀ ≠ k₁ ∧ SignRealized B E (dsign k₀ k₁)) := by
  have hb0 := hB.2.1
  have hN : ∀ {g : G} {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}, B.Acts g M →
      g ∈ Subgroup.normalizer (E : Set G) := fun h => hB.1 ▸ B.mem_normalizer_of_acts h
  have h10 : (1 : Fin 8) ≠ 0 := by decide
  have ht1 : SignRealized B E (dsign 1 1) :=
    e7_signRealized hB hloc (dsign_isSign _ _) (by decide) (by decide)
  have hsr : ∀ {a b : Fin 8}, a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → a ≠ b →
      SignRealized B E (dsign a b) := fun ha0 ha1 hb0' hb1 hab =>
    e7_signRealized hB hloc (dsign_isSign _ _) (dsign_of_ne (Ne.symm ha0) (Ne.symm hb0'))
      (dsign_prod_E7 _ _ ha0 ha1 hb0' hb1 hab)
  have hinv : ∀ i : Fin 8, B.b i ^ ((-1 : ZMod 3).val) = (B.b i)⁻¹ := fun i => by
    have h3 : B.b i ^ 3 = 1 := by rw [← B.ord i]; exact pow_orderOf_eq_one _
    exact eq_inv_of_mul_eq_one_left (by
      rw [show (-1 : ZMod 3).val = 2 from rfl, ← pow_succ]
      exact h3)
  have hm1 : (-1 : ZMod 3) ≠ 1 := by decide
  have hneg : ∀ i j : Fin 8, i ≠ 0 → j ≠ i → ∃ s, SignRealized B E s ∧ s i = -1 ∧ s j = 1 ∧
      ∀ l : Fin 8, l ≠ i → s l = 1 ∨ s l = -1 := by
    intro i j hi hji
    by_cases hi1 : i = 1
    · subst hi1
      exact ⟨dsign 1 1, ht1, dsign_left _ _, dsign_of_ne hji hji, fun l _ => dsign_isSign _ _ l⟩
    · obtain ⟨m, hm0, hm1', hmi, hmj⟩ := fs81Nt_exists_ne4 (n := 7) (by norm_num) 0 1 i j
      exact ⟨dsign i m, hsr hi hi1 hm0 hm1' (Ne.symm hmi), dsign_left _ _,
        dsign_of_ne hji (Ne.symm hmj), fun l _ => dsign_isSign _ _ l⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hi hji
    obtain ⟨s, ⟨-, hs0, d, hdN, hd⟩, hsi, hsj, -⟩ := hneg i j hi hji
    refine ⟨d, hdN, ?_, ?_, ?_⟩
    · have := B.acts_spMat_one hd 0
      rwa [hs0, ZMod.val_one, pow_one, hb0] at this
    · rw [B.acts_spMat_one hd i, hsi, hinv]
    · rw [B.acts_spMat_one hd j, hsj, ZMod.val_one, pow_one]
  ·
    intro k l hk hl hlk
    obtain ⟨s, ⟨hs, hs0, d, hdN, hd⟩, hsk, hsl, -⟩ := hneg k l hk hlk
    exact ⟨d, hdN, s, hs, hs0, hd, by rw [hsk, hsl]; exact Ne.symm hm1⟩
  ·
    refine ⟨1, h10, fun k hk => ?_⟩
    by_cases hk1 : k = 1
    · subst hk1
      refine ⟨1, Subgroup.one_mem _, by group, Pi.single 1 1, by rw [B.vec_single]; group, ?_⟩
      simp
    have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by
      rw [hB.1]
      exact hdisj
    have hH1' : B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) = hSeven := hloc.2.2
    have hstab : ∀ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
        (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        (∃ c : ZMod 3, (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 1 1 =
          c • Pi.single 1 1) → (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) ∈ hSeven :=
      fun x hx hxe hxc => by
        rw [← hH1']
        exact B.stab_mem_realized hb0 hx hxe hxc
    have hcard : Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom ⊓ fixE0 7) = 2903040 := by
      rw [card_xg_fixE0 B hb0]
      exact hloc.1
    obtain ⟨x, hxX, hxe, hxmove⟩ := e7_exists_move hstab hcard
    obtain ⟨g, hgC, hg⟩ := B.fix_mem_realized hb0 hxX hxe
    set c := (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 1 1 with hc
    have hc0 : c 0 = 0 :=
      B.fix_preserves_A hb0 hord hB.2.2 hdisj' hKn hxX hxe _ (Pi.single_eq_of_ne (by decide) _)
    have hgb : g * B.b 1 * g⁻¹ = B.vec c := by
      rw [hg 1, hc]
      congr 1
      funext i
      simp [Matrix.mulVec_single]
    obtain ⟨m, hm0, hm1', hcm⟩ : ∃ m : Fin 8, m ≠ 0 ∧ m ≠ 1 ∧ c m ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hxmove
      refine ⟨c 1, funext fun i => ?_⟩
      by_cases hi1 : i = 1
      · subst hi1
        simp
      · by_cases hi0 : i = 0
        · subst hi0
          rw [hc0]
          simp [hi1]
        · rw [hno i hi0 hi1]
          simp [hi1]
    have hσ0 : Equiv.swap m k 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hm0) (Ne.symm hk)
    have hσ1 : Equiv.swap m k 1 = 1 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hm1') (Ne.symm hk1)
    obtain ⟨p, hpC, hp⟩ := e7_acts hloc (s := fun _ => 1) (fun _ => Or.inl rfl) hσ0 rfl hσ1
      (by simp)
    have hpS : p ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hp
    refine ⟨p * g, Subgroup.mul_mem _ (hN hp) (hN hg), ?_, spMat (Equiv.swap m k) (fun _ => 1) *ᵥ c,
      ?_, ?_⟩
    · rw [show p * g * b₀ * (p * g)⁻¹ = p * (g * b₀ * g⁻¹) * p⁻¹ by group,
        ← Subgroup.mem_centralizer_iff.mp hgC b₀ (Set.mem_singleton b₀), mul_inv_cancel_right,
        ← Subgroup.mem_centralizer_iff.mp hpC b₀ (Set.mem_singleton b₀), mul_inv_cancel_right]
    · rw [show p * g * B.b 1 * (p * g)⁻¹ = p * (g * B.b 1 * g⁻¹) * p⁻¹ by group, hgb,
        B.acts_vec' hpS hp]
    · simp only [spMat_mulVec, Equiv.symm_swap, Equiv.swap_apply_right, one_mul]
      exact hcm
  ·
    refine ⟨![1, -1, -1, -1, 1, 1, 1, 1], ![1, 1, 1, 1, -1, -1, -1, -1],
      e7_signRealized hB hloc (by unfold IsSign; decide) (by decide) (by decide),
      e7_signRealized hB hloc (by unfold IsSign; decide) (by decide) (by decide),
      e7_signRealized hB hloc (by unfold IsSign; decide) (by decide) (by decide), by decide⟩
  ·
    intro i j k hi hj hk hji
    by_cases hki : k = i
    · subst hki
      obtain ⟨s, hs, hsj, -, hsign⟩ := hneg j k hj (Ne.symm hji)
      refine ⟨s, hs, ?_⟩
      rw [hsj]
      rcases hsign k (Ne.symm hji) with h | h <;> rw [h] <;> decide
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨s, hs, hsi, -, hsign⟩ := hneg i k hi hji
      refine ⟨s, hs, ?_⟩
      rw [hsi]
      rcases hsign k hji with h | h <;> rw [h] <;> decide
    · by_cases hk1 : k = 1
      · subst hk1
        refine ⟨dsign 1 1, ht1, ?_⟩
        rw [dsign_left, dsign_of_ne (Ne.symm hki) (Ne.symm hki),
          dsign_of_ne (Ne.symm hkj) (Ne.symm hkj), one_mul]
        exact hm1
      · obtain ⟨m, hm0, hm1', hmi, hmj, hmk⟩ := fs81Nt_exists_ne5 0 1 i j k
        refine ⟨dsign k m, hsr hk hk1 hm0 hm1' (Ne.symm hmk), ?_⟩
        rw [dsign_left, dsign_of_ne (Ne.symm hki) (Ne.symm hmi),
          dsign_of_ne (Ne.symm hkj) (Ne.symm hmj), one_mul]
        exact hm1
  ·
    exact ⟨2, 3, by decide, by decide, by decide, hsr (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

end CFSG.StandardType.FrameRoute.FS81

end
