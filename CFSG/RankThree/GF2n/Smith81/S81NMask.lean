module

public import CFSG.RankThree.GF2n.Smith81.S81NModelCommon
public import CFSG.RankThree.GF2n.Smith81.S81NTk

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

@[expose] noncomputable def cf (K : Type*) [Field K] (ξ : Cube K) (s : Finset (Fin 6)) : K :=
  if h : s.card = 3 then coord K ξ ⟨s, h⟩ else 0

theorem cf_apply (ξ : Cube K) (I : Set.powersetCard (Fin 6) 3) : cf K ξ I.val = coord K ξ I := by
  unfold cf
  rw [dif_pos (Set.powersetCard.card_eq I)]

theorem cf_of_card_ne (ξ : Cube K) {s : Finset (Fin 6)} (h : s.card ≠ 3) : cf K ξ s = 0 := by
  unfold cf
  rw [dif_neg h]

theorem cf_add (ξ η : Cube K) (s : Finset (Fin 6)) : cf K (ξ + η) s = cf K ξ s + cf K η s := by
  by_cases h : s.card = 3
  · simp only [cf, dif_pos h, coord_add]
  · simp only [cf, dif_neg h, add_zero]

theorem cf_sub (ξ η : Cube K) (s : Finset (Fin 6)) : cf K (ξ - η) s = cf K ξ s - cf K η s := by
  by_cases h : s.card = 3
  · simp only [cf, dif_pos h, coord_sub]
  · simp only [cf, dif_neg h, sub_zero]

theorem cf_smul (c : K) (ξ : Cube K) (s : Finset (Fin 6)) : cf K (c • ξ) s = c * cf K ξ s := by
  by_cases h : s.card = 3
  · simp only [cf, dif_pos h, coord_smul, smul_eq_mul]
  · simp only [cf, dif_neg h, mul_zero]

theorem cf_zero (s : Finset (Fin 6)) : cf K (0 : Cube K) s = 0 := by
  by_cases h : s.card = 3
  · simp only [cf, dif_pos h, coord_zero]
  · simp only [cf, dif_neg h]

theorem cf_cubeBasis (I : Set.powersetCard (Fin 6) 3) (s : Finset (Fin 6)) :
    cf K (cubeBasis K I) s = if s = I.val then 1 else 0 := by
  by_cases h : s.card = 3
  · simp only [cf, dif_pos h, coord_cubeBasis]
    by_cases hs : s = I.val
    · subst hs; simp
    · rw [if_neg hs, if_neg]; intro h'; exact hs (congrArg Subtype.val h').symm
  · rw [cf_of_card_ne _ h, if_neg]
    intro hs; exact h (hs ▸ Set.powersetCard.card_eq I)

theorem cf_rho_transv [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K) (ξ : Cube K)
    (s : Finset (Fin 6)) :
    cf K (rho K (transvGL K i j hij c) ξ) s =
      cf K ξ s + (if i ∈ s ∧ j ∉ s then c * cf K ξ (insert j (s.erase i)) else 0) := by
  by_cases hs : s.card = 3
  · have key := coord_rho_transvGL_gen i j hij c ξ ⟨s, hs⟩
    by_cases h : i ∈ s ∧ j ∉ s
    · have hc : (insert j (s.erase i)).card = 3 := by
        rw [Finset.card_insert_of_notMem (fun h' => h.2 (Finset.mem_of_mem_erase h')),
          Finset.card_erase_of_mem h.1, hs]
      rw [if_pos h]
      have key' := key
      rw [dif_pos h] at key'
      simp only [cf, dif_pos hs, dif_pos hc]
      exact key'
    · rw [if_neg h]
      have key' := key
      rw [dif_neg h] at key'
      simp only [cf, dif_pos hs]
      simpa using key'
  · have h1 := cf_of_card_ne (rho K (transvGL K i j hij c) ξ) hs
    have h2 := cf_of_card_ne ξ hs
    rw [h1, h2]
    by_cases h : i ∈ s ∧ j ∉ s
    · rw [if_pos h]
      have hc : (insert j (s.erase i)).card ≠ 3 := by
        rw [Finset.card_insert_of_notMem (fun h' => h.2 (Finset.mem_of_mem_erase h')),
          Finset.card_erase_of_mem h.1]
        intro h3
        apply hs
        have := Finset.card_pos.mpr ⟨i, h.1⟩
        omega
      rw [cf_of_card_ne ξ hc]
      simp
    · rw [if_neg h]; simp

@[expose] def mset (m : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun i : Fin 6 => m.testBit i.val)

@[expose] noncomputable def cfm (K : Type*) [Field K] (ξ : Cube K) (m : ℕ) : K :=
  cf K ξ (mset m)

theorem mset_move : ∀ (m : Fin 64) (i j : Fin 6), (m : ℕ).testBit i.val = true →
    (m : ℕ).testBit j.val = false →
    mset ((m : ℕ) - 2 ^ i.val + 2 ^ j.val) = insert j ((mset (m : ℕ)).erase i) := by
  decide +kernel

theorem exists_mask : ∀ s : Finset (Fin 6), ∃ m : Fin 64, mset (m : ℕ) = s := by
  decide +kernel

theorem cfm_ext {ξ η : Cube K} (h : ∀ m : ℕ, m < 64 → cfm K ξ m = cfm K η m) : ξ = η := by
  refine (cubeBasis K).ext_elem fun I => ?_
  obtain ⟨m, hm⟩ := exists_mask I.val
  have := h m m.2
  unfold cfm at this
  rw [hm, cf_apply, cf_apply] at this
  exact this

theorem cfm_add (ξ η : Cube K) (m : ℕ) : cfm K (ξ + η) m = cfm K ξ m + cfm K η m := cf_add _ _ _
theorem cfm_sub (ξ η : Cube K) (m : ℕ) : cfm K (ξ - η) m = cfm K ξ m - cfm K η m := cf_sub _ _ _
theorem cfm_smul (c : K) (ξ : Cube K) (m : ℕ) : cfm K (c • ξ) m = c * cfm K ξ m := cf_smul _ _ _
theorem cfm_zero (m : ℕ) : cfm K (0 : Cube K) m = 0 := cf_zero _

theorem cfm_ub (a b d : Fin 6) (hab : a < b) (hbd : b < d) (m : ℕ) :
    cfm K (ub K a b d hab hbd) m = if mset m = {a, b, d} then 1 else 0 := by
  unfold cfm ub
  rw [cf_cubeBasis]
  rfl

theorem cfm_rho_transv [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K) (ξ : Cube K) (m : ℕ)
    (hm : m < 64) :
    cfm K (rho K (transvGL K i j hij c) ξ) m =
      cfm K ξ m + (if m.testBit i.val = true ∧ m.testBit j.val = false then
        c * cfm K ξ (m - 2 ^ i.val + 2 ^ j.val) else 0) := by
  unfold cfm
  rw [cf_rho_transv]
  have hmem : ∀ x : Fin 6, x ∈ mset m ↔ m.testBit x.val = true := by
    intro x; simp [mset]
  by_cases h : m.testBit i.val = true ∧ m.testBit j.val = false
  · rw [if_pos h, if_pos ⟨(hmem i).mpr h.1, fun h' => by simpa [h.2] using (hmem j).mp h'⟩]
    rw [← mset_move ⟨m, hm⟩ i j h.1 h.2]
  · rw [if_neg h, if_neg]
    intro h'
    exact h ⟨(hmem i).mp h'.1, by
      cases hj : m.testBit j.val
      · rfl
      · exact absurd ((hmem j).mpr hj) h'.2⟩

theorem cfm_rho_X01 [CharP K 2] (ξ : Cube K) (m : ℕ) (hm : m < 64) :
    cfm K (rho K (transvGL K 0 1 (by decide) 1) ξ) m =
      cfm K ξ m + (if m.testBit 0 = true ∧ m.testBit 1 = false then cfm K ξ (m - 1 + 2) else 0) := by
  have := cfm_rho_transv (K := K) 0 1 (by decide) 1 ξ m hm
  simpa using this

theorem cfm_rho_X23 [CharP K 2] (ξ : Cube K) (m : ℕ) (hm : m < 64) :
    cfm K (rho K (transvGL K 2 3 (by decide) 1) ξ) m =
      cfm K ξ m + (if m.testBit 2 = true ∧ m.testBit 3 = false then cfm K ξ (m - 4 + 8) else 0) := by
  have := cfm_rho_transv (K := K) 2 3 (by decide) 1 ξ m hm
  simpa using this

theorem cfm_rho_X45 [CharP K 2] (ξ : Cube K) (m : ℕ) (hm : m < 64) :
    cfm K (rho K (transvGL K 4 5 (by decide) 1) ξ) m =
      cfm K ξ m + (if m.testBit 4 = true ∧ m.testBit 5 = false then cfm K ξ (m - 16 + 32) else 0) := by
  have := cfm_rho_transv (K := K) 4 5 (by decide) 1 ξ m hm
  simpa using this

theorem rho_tInv1 : rho K (tInv1 K) = rho K (transvGL K 0 1 (by decide) 1) := rfl

theorem rho_tInv2 : rho K (tInv2 K) =
    rho K (transvGL K 0 1 (by decide) 1) * rho K (transvGL K 2 3 (by decide) 1) := by
  unfold tInv2 tInv1
  rw [rho_mul]

theorem rho_tInv3 : rho K (tInv3 K) = rho K (transvGL K 0 1 (by decide) 1) *
    rho K (transvGL K 2 3 (by decide) 1) * rho K (transvGL K 4 5 (by decide) 1) := by
  unfold tInv3 tInv2 tInv1
  rw [rho_mul, rho_mul]

theorem ker_range_eq_of_gens {a b : ℕ} (hab : a + b = 20) (F : Cube K →ₗ[K] Cube K)
    (kerG : Fin a → Cube K) (ranG : Fin b → Cube K) (h1 : ∀ i, F (kerG i) = 0)
    (h2 : ∀ i, ranG i ∈ LinearMap.range F) (h3 : LinearIndependent K kerG)
    (h4 : LinearIndependent K ranG) :
    LinearMap.ker F = Submodule.span K (Set.range kerG) ∧
      LinearMap.range F = Submodule.span K (Set.range ranG) := by
  have hk : Submodule.span K (Set.range kerG) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h1 i
  have hr : Submodule.span K (Set.range ranG) ≤ LinearMap.range F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h2 i
  have fk : Module.finrank K (Submodule.span K (Set.range kerG)) = a := by
    rw [finrank_span_eq_card h3, Fintype.card_fin]
  have fr : Module.finrank K (Submodule.span K (Set.range ranG)) = b := by
    rw [finrank_span_eq_card h4, Fintype.card_fin]
  have rn := LinearMap.finrank_range_add_finrank_ker F
  rw [finrank_cube] at rn
  have fr' : b ≤ Module.finrank K (LinearMap.range F) := fr ▸ Submodule.finrank_mono hr
  have fk' : a ≤ Module.finrank K (LinearMap.ker F) := fk ▸ Submodule.finrank_mono hk
  have e1 : Module.finrank K (LinearMap.ker F) = a := by omega
  have e2 : Module.finrank K (LinearMap.range F) = b := by omega
  constructor
  · exact (Submodule.eq_of_le_of_finrank_le hk (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_le hr (by omega)).symm

theorem linearIndependent_of_pivots_mask {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Cube K)
    (p : ι → ℕ) (hp : ∀ j, (mset (p j)).card = 3)
    (h : ∀ i j, cfm K (f i) (p j) = if i = j then (1 : K) else 0) : LinearIndependent K f := by
  classical
  refine linearIndependent_of_pivots f (fun j => ⟨mset (p j), hp j⟩) fun i j => ?_
  have := h i j
  unfold cfm at this
  have e : cf K (f i) (mset (p j)) = coord K (f i) ⟨mset (p j), hp j⟩ :=
    cf_apply (f i) ⟨mset (p j), hp j⟩
  rw [← e, this]
  by_cases hij : i = j <;> simp [hij]

theorem mem_span_of_recon {n : ℕ} (g : Fin n → Cube K) (p : Fin n → ℕ) {η : Cube K}
    (h : η = ∑ i, cfm K η (p i) • g i) : η ∈ Submodule.span K (Set.range g) := by
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem cfm_zero_of_fixed [CharP K 2] (Pos : Fin 6 → Fin 6 → Prop) {ξ : Cube K}
    (h : ∀ (i j : Fin 6) (hij : i ≠ j), Pos i j → rho K (transvGL K i j hij 1) ξ = ξ)
    (m : ℕ) (hm : m < 64)
    (hmv : ∃ i j : Fin 6, i ≠ j ∧ Pos i j ∧ m.testBit j.val = true ∧ m.testBit i.val = false) :
    cfm K ξ m = 0 := by
  obtain ⟨i, j, hij, hP, hj, hi⟩ := hmv
  have hmem : ∀ x : Fin 6, x ∈ mset m ↔ m.testBit x.val = true := by
    intro x; simp [mset]
  have hj' : j ∈ mset m := (hmem j).mpr hj
  have hi' : i ∉ mset m := fun h' => by simpa [hi] using (hmem i).mp h'
  unfold cfm
  by_cases hc : (mset m).card = 3
  · have := fixed_support Pos h ⟨mset m, hc⟩ i j hij hP hj' hi'
    rw [← cf_apply] at this
    exact this
  · exact cf_of_card_ne _ hc

theorem cfm_ext3 {ξ η : Cube K}
    (h : ∀ m : ℕ, m < 64 → (mset m).card = 3 → cfm K ξ m = cfm K η m) : ξ = η := by
  refine cfm_ext fun m hm => ?_
  by_cases hc : (mset m).card = 3
  · exact h m hm hc
  · unfold cfm
    rw [cf_of_card_ne _ hc, cf_of_card_ne _ hc]

theorem mset_eq_iff : ∀ (a b d : Fin 6) (m : Fin 64), a < b → b < d →
    (mset (m : ℕ) = {a, b, d} ↔ (m : ℕ) = 2 ^ a.val + 2 ^ b.val + 2 ^ d.val) := by
  decide +kernel

theorem cfm_ub_mask (a b d : Fin 6) (hab : a < b) (hbd : b < d) (m : ℕ) (hm : m < 64) :
    cfm K (ub K a b d hab hbd) m = if m = 2 ^ a.val + 2 ^ b.val + 2 ^ d.val then 1 else 0 := by
  rw [cfm_ub]
  have := mset_eq_iff a b d ⟨m, hm⟩ hab hbd
  by_cases h : m = 2 ^ a.val + 2 ^ b.val + 2 ^ d.val
  · rw [if_pos h, if_pos (this.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]

theorem exists_mask3 {m : ℕ} (hm : m < 64) (hc : (mset m).card = 3) :
    m = 7 ∨ m = 11 ∨ m = 13 ∨ m = 14 ∨ m = 19 ∨ m = 21 ∨ m = 22 ∨ m = 25 ∨ m = 26 ∨ m = 28 ∨
      m = 35 ∨ m = 37 ∨ m = 38 ∨ m = 41 ∨ m = 42 ∨ m = 44 ∨ m = 49 ∨ m = 50 ∨ m = 52 ∨ m = 56 := by
  have key : ∀ m : Fin 64, (mset (m : ℕ)).card = 3 →
      (m : ℕ) = 7 ∨ (m : ℕ) = 11 ∨ (m : ℕ) = 13 ∨ (m : ℕ) = 14 ∨ (m : ℕ) = 19 ∨ (m : ℕ) = 21 ∨
      (m : ℕ) = 22 ∨ (m : ℕ) = 25 ∨ (m : ℕ) = 26 ∨ (m : ℕ) = 28 ∨ (m : ℕ) = 35 ∨ (m : ℕ) = 37 ∨
      (m : ℕ) = 38 ∨ (m : ℕ) = 41 ∨ (m : ℕ) = 42 ∨ (m : ℕ) = 44 ∨ (m : ℕ) = 49 ∨
      (m : ℕ) = 50 ∨ (m : ℕ) = 52 ∨ (m : ℕ) = 56 := by
    decide +kernel
  exact key ⟨m, hm⟩ hc

end CFSG.RankThree.GF2n.Smith81.A5Cube
