module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultReflPair
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveNorm
import CFSG.Mathlib.Algebra.IsSquareMul

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

theorem fiveReflectionsIn_mono {k : ℕ} {ε π : Bool}
    {H A : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hHA : H ≤ A) :
    fiveReflectionsIn k ε π H ⊆ fiveReflectionsIn k ε π A :=
  fun _ ⟨v, hv, hQ, hπ, hg⟩ => ⟨v, hHA hv, hQ, hπ, hg⟩

theorem fiveReflectionGroupIn_mono {k : ℕ} {ε π : Bool}
    {H A : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hHA : H ≤ A) :
    fiveReflectionGroupIn k ε π H ≤ fiveReflectionGroupIn k ε π A := by
  rw [fiveReflectionGroupIn, fiveReflectionGroupIn]
  exact Subgroup.closure_mono (fiveReflectionsIn_mono hHA)

theorem fiveReflectionGroupIn_le_fiveReflectionGroup (k : ℕ) (ε π : Bool)
    (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) :
    fiveReflectionGroupIn k ε π W ≤ fiveReflectionGroup k ε π := by
  rw [fiveReflectionGroupIn, fiveReflectionGroup]
  refine Subgroup.closure_mono ?_
  rintro g ⟨v, hv, hQ, hπ, hg⟩
  exact ⟨v, hQ, hπ, hg⟩

theorem fiveForm_mulVec_of_mem_fiveReflectionGroupIn {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflectionGroupIn k ε π W)
    (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y :=
  fiveForm_mulVec_of_mem (fiveReflectionGroupIn_le_fiveReflectionGroup k ε π W hg) x y

theorem eq_fiveReflOf_of_mem_fiveReflectionsIn {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflectionsIn k ε π W) :
    ∃ v ∈ W, fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ π = true) ∧
      g = fiveReflOf k ε v := by
  rcases hg with ⟨v, hv, hQ, hπ, hform⟩
  refine ⟨v, hv, hQ, hπ, ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hform (Pi.single i 1), fiveReflOf_mulVec]

theorem fiveReflOf_mem_fiveReflectionGroupIn {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {v : Fin (k + 1) → ZMod 5}
    (hv : v ∈ W) (hQ : fiveForm k ε v v ≠ 0) (hπ : IsSquare (fiveForm k ε v v) ↔ π = true) :
    fiveReflOf k ε v ∈ fiveReflectionGroupIn k ε π W :=
  Subgroup.subset_closure ⟨v, hv, hQ, hπ, fun x => fiveReflOf_mulVec k ε v x⟩

theorem isFiveNondeg_span_fiveHyperbolic {k : ℕ} {ε : Bool} {b b' : Fin (k + 1) → ZMod 5}
    (hbs : fiveForm k ε b b = 0) (hb's : fiveForm k ε b' b' = 0)
    (hbb' : fiveForm k ε b b' = 1) :
    IsFiveNondeg k ε (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5))) := by
  rw [isFiveNondeg_iff]
  intro x hx hxorth
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  have hβ : fiveForm k ε (α • b + β • b') b = 0 :=
    hxorth b (Submodule.subset_span (by simp))
  have hα : fiveForm k ε (α • b + β • b') b' = 0 :=
    hxorth b' (Submodule.subset_span (by simp))
  rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hbs,
    fiveForm_comm k ε b' b, hbb'] at hβ
  rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hbb', hb's] at hα
  simp only [mul_one, mul_zero, add_zero, zero_add] at hβ hα
  rw [hα, hβ, zero_smul, zero_smul, add_zero]

theorem exists_fiveHyperbolicPartner {k : ℕ} {ε : Bool}
    {H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hH : IsFiveNondeg k ε H)
    {b : Fin (k + 1) → ZMod 5} (hb : b ∈ H) (hb0 : b ≠ 0)
    (hbs : fiveForm k ε b b = 0) :
    ∃ b' ∈ H, fiveForm k ε b' b' = 0 ∧ fiveForm k ε b b' = 1 := by
  have hc₀ : ∃ c₀ ∈ H, fiveForm k ε b c₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hb0 ((isFiveNondeg_iff.1 hH) b hb (fun y hy => h y hy))
  obtain ⟨c₀, hc₀H, hc₀ne⟩ := hc₀
  set c₁ : Fin (k + 1) → ZMod 5 := (fiveForm k ε b c₀)⁻¹ • c₀ with hc₁def
  have hc₁H : c₁ ∈ H := by
    rw [hc₁def]
    exact Submodule.smul_mem _ _ hc₀H
  have hbc₁ : fiveForm k ε b c₁ = 1 := by
    rw [hc₁def, fiveForm_smul_right]
    exact inv_mul_cancel₀ hc₀ne
  set lam : ZMod 5 := -(fiveForm k ε c₁ c₁) * (2 : ZMod 5)⁻¹ with hlam
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have hinv2 : (2 : ZMod 5) * (2 : ZMod 5)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  have hkey_gen : ∀ (A : Fin (k + 1) → ZMod 5) (L : ZMod 5),
      fiveForm k ε A b = 1 →
      fiveForm k ε (A + L • b) (A + L • b) = fiveForm k ε A A + 2 * L := by
    intro A L hAb
    rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right, fiveForm_smul_right,
      fiveForm_smul_left, fiveForm_smul_left, fiveForm_smul_right, fiveForm_comm k ε b A,
      hAb, hbs]
    ring
  have hb'gen : ∀ (A : Fin (k + 1) → ZMod 5) (L : ZMod 5),
      fiveForm k ε b A = 1 → fiveForm k ε b (A + L • b) = 1 := by
    intro A L hAb
    rw [fiveForm_add_right, hAb, fiveForm_smul_right, hbs, mul_zero, add_zero]
  refine ⟨c₁ + lam • b, add_mem hc₁H (Submodule.smul_mem _ _ hb), ?_, ?_⟩
  · rw [hkey_gen c₁ lam (by rw [fiveForm_comm]; exact hbc₁)]
    have h2lam : 2 * lam = -(fiveForm k ε c₁ c₁) := by
      rw [hlam]
      rw [show (2 : ZMod 5) * (-(fiveForm k ε c₁ c₁) * (2 : ZMod 5)⁻¹) =
        -(fiveForm k ε c₁ c₁) * ((2 : ZMod 5) * (2 : ZMod 5)⁻¹) by ring]
      rw [hinv2, mul_one]
    rw [h2lam]
    exact add_neg_cancel _
  · exact hb'gen c₁ lam hbc₁

theorem exists_fiveForm_eq_of_nondeg_orth_add {k : ℕ} {ε : Bool}
    {H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hH : IsFiveNondeg k ε H)
    (h4 : 4 ≤ Module.finrank (ZMod 5) H) {b : Fin (k + 1) → ZMod 5} (hb : b ∈ H) (hb0 : b ≠ 0)
    (c γ : ZMod 5) :
    ∃ w' ∈ H, w' ≠ 0 ∧ fiveForm k ε w' w' = c ∧ fiveForm k ε w' b = γ := by
  by_cases hbs : fiveForm k ε b b = 0
  · obtain ⟨b', hb'H, hb's, hbb'⟩ := exists_fiveHyperbolicPartner hH hb hb0 hbs
    have hb'0 : b' ≠ 0 := by
      intro h0
      rw [h0] at hbb'
      simp [fiveForm] at hbb'
    by_cases hγ : γ = 0
    · by_cases hc : c = 0
      · refine ⟨b, hb, hb0, ?_, ?_⟩
        · rw [hbs, hc]
        · rw [hbs, hγ]
      · have hPlane : IsFiveNondeg k ε
            (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5))) :=
          isFiveNondeg_span_fiveHyperbolic hbs hb's hbb'
        have hspan_le : Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5)) ≤ H := by
          rw [Submodule.span_le]
          intro z hz
          rcases hz with rfl | rfl
          · exact hb
          · exact hb'H
        have hH₀ : IsFiveNondeg k ε
            (H ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5)))) :=
          isFiveNondeg_inf_fiveOrth hH hPlane hspan_le
        have hdim₀ := finrank_inf_fiveOrth_add hH hspan_le
        have hle2 : Module.finrank (ZMod 5)
            (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5))) ≤ 2 := by
          have h := finrank_span_finset_le_card (R := ZMod 5)
            ({b, b'} : Finset (Fin (k + 1) → ZMod 5))
          rw [Finset.coe_pair] at h
          exact h.trans Finset.card_le_two
        have h2 : 2 ≤ Module.finrank (ZMod 5)
            ↥(H ⊓ fiveOrth k ε
              (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5)))) := by
          have hSleH : Module.finrank (ZMod 5)
              (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5))) ≤
              Module.finrank (ZMod 5) H := hle2.trans (le_trans (by norm_num) h4)
          rw [Nat.eq_sub_of_add_eq hdim₀, Nat.le_sub_iff_add_le hSleH]
          calc 2 + Module.finrank (ZMod 5)
                (Submodule.span (ZMod 5) ({b, b'} : Set (Fin (k + 1) → ZMod 5))) ≤ 2 + 2 :=
                Nat.add_le_add_left hle2 2
            _ = 4 := by norm_num
            _ ≤ Module.finrank (ZMod 5) H := h4
        obtain ⟨u, huH₀, huQ⟩ := exists_fiveForm_eq_of_nondeg hH₀ h2 (c := c)
        have huH : u ∈ H := (Submodule.mem_inf.mp huH₀).1
        have hub : fiveForm k ε u b = 0 :=
          (mem_fiveOrth.mp (Submodule.mem_inf.mp huH₀).2) b (Submodule.subset_span (by simp))
        refine ⟨b + u, add_mem hb huH, ?_, ?_, ?_⟩
        · intro h0
          have hQ : fiveForm k ε (b + u) (b + u) = c := by
            simp only [fiveForm_add_add, fiveForm_comm k ε b u, hbs, hub, huQ, mul_zero, add_zero]
            ring
          rw [h0] at hQ
          simp [fiveForm] at hQ
          exact hc hQ.symm
        · simp only [fiveForm_add_add, fiveForm_comm k ε b u, hbs, hub, huQ, mul_zero, add_zero]
          ring
        · simp only [fiveForm_add_left, hbs, hub, add_zero, hγ]
    · set μ : ZMod 5 := c * (2 * γ)⁻¹ with hμdef
      have hQ_gen : ∀ (L M : ZMod 5),
          fiveForm k ε (L • b' + M • b) (L • b' + M • b) = 2 * L * M := by
        intro L M
        simp only [fiveForm_add_add, fiveForm_smul_left, fiveForm_smul_right]
        rw [fiveForm_comm k ε b' b, hb's, hbs, hbb']
        ring
      have hB_gen : ∀ (L M : ZMod 5), fiveForm k ε (L • b' + M • b) b = L := by
        intro L M
        simp only [fiveForm_add_left, fiveForm_smul_left]
        rw [fiveForm_comm k ε b' b, hbb', hbs]
        ring
      have hQw' : fiveForm k ε (γ • b' + μ • b) (γ • b' + μ • b) = c := by
        rw [hQ_gen γ μ]
        have hμ : 2 * γ * μ = c := by
          rw [hμdef]
          rw [show 2 * γ * (c * (2 * γ)⁻¹) = c * ((2 * γ) * (2 * γ)⁻¹) by ring]
          rw [mul_inv_cancel₀ (mul_ne_zero (by decide) hγ), mul_one]
        rw [hμ]
      have hBw' : fiveForm k ε (γ • b' + μ • b) b = γ := hB_gen γ μ
      refine ⟨γ • b' + μ • b, add_mem (Submodule.smul_mem _ _ hb'H) (Submodule.smul_mem _ _ hb),
        ?_, hQw', hBw'⟩
      · by_cases hc : c = 0
        · have hμ0 : μ = 0 := by rw [hμdef, hc, zero_mul]
          rw [hμ0, zero_smul, add_zero]
          exact smul_ne_zero hγ hb'0
        · intro h0
          have h := hQw'
          rw [h0] at h
          simp [fiveForm] at h
          exact hc h.symm
  · have hspan_le : Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5)) ≤ H := by
      rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hb
    have hK : IsFiveNondeg k ε
        (H ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5)))) :=
      isFiveNondeg_inf_fiveOrth hH (isFiveNondeg_span_singleton hbs) hspan_le
    have hdimK := finrank_inf_fiveOrth_add hH hspan_le
    have hfr : Module.finrank (ZMod 5)
        (Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5))) = 1 :=
      finrank_span_singleton hb0
    have h3 : 3 ≤ Module.finrank (ZMod 5)
        ↥(H ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5)))) := by
      have hSleH : Module.finrank (ZMod 5)
          (Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5))) ≤
          Module.finrank (ZMod 5) H := by
        rw [hfr]
        exact le_trans (by norm_num) h4
      rw [Nat.eq_sub_of_add_eq hdimK, Nat.le_sub_iff_add_le hSleH]
      calc 3 + Module.finrank (ZMod 5)
            (Submodule.span (ZMod 5) ({b} : Set (Fin (k + 1) → ZMod 5))) = 3 + 1 := by rw [hfr]
        _ = 4 := by norm_num
        _ ≤ Module.finrank (ZMod 5) H := h4
    have hBu : ∀ (L : ZMod 5) (u : Fin (k + 1) → ZMod 5), fiveForm k ε u b = 0 →
        fiveForm k ε (L • b + u) b = L * fiveForm k ε b b := by
      intro L u hu
      simp only [fiveForm_add_left, fiveForm_smul_left, hu, add_zero]
    have hQu : ∀ (L : ZMod 5) (u : Fin (k + 1) → ZMod 5), fiveForm k ε u b = 0 →
        fiveForm k ε (L • b + u) (L • b + u) =
          L ^ 2 * fiveForm k ε b b + fiveForm k ε u u := by
      intro L u hu
      simp only [fiveForm_add_add, fiveForm_smul_left, fiveForm_smul_right,
        fiveForm_comm k ε b u, hu, mul_zero, add_zero]
      ring
    set α : ZMod 5 := γ * (fiveForm k ε b b)⁻¹ with hαdef
    set c' : ZMod 5 := c - γ ^ 2 * (fiveForm k ε b b)⁻¹ with hc'def
    have hQval : ∀ (u : Fin (k + 1) → ZMod 5), fiveForm k ε u b = 0 → fiveForm k ε u u = c' →
        fiveForm k ε (α • b + u) (α • b + u) = c := by
      intro u hu huQ
      rw [hQu α u hu, huQ, hαdef, hc'def]
      field_simp
      ring
    have hBval : ∀ (u : Fin (k + 1) → ZMod 5), fiveForm k ε u b = 0 →
        fiveForm k ε (α • b + u) b = γ := by
      intro u hu
      rw [hBu α u hu, hαdef]
      field_simp
    by_cases hc' : c' = 0
    · obtain ⟨u, huK, hu0, huQ⟩ := exists_fiveForm_eq_zero_of_nondeg hK h3
      have huH : u ∈ H := (Submodule.mem_inf.mp huK).1
      have hub : fiveForm k ε u b = 0 :=
        (mem_fiveOrth.mp (Submodule.mem_inf.mp huK).2) b (Submodule.subset_span (by simp))
      have hQ := hQval u hub (huQ.trans hc'.symm)
      have hB := hBval u hub
      refine ⟨α • b + u, add_mem (Submodule.smul_mem _ _ hb) huH, ?_, hQ, hB⟩
      · by_cases hc : c = 0
        · have hγ0 : γ = 0 := by
            have h1 : γ ^ 2 * (fiveForm k ε b b)⁻¹ = 0 := by
              have h := hc'
              rw [hc'def, hc, zero_sub] at h
              exact neg_eq_zero.mp h
            have h2 : (fiveForm k ε b b)⁻¹ ≠ 0 := inv_ne_zero hbs
            rcases mul_eq_zero.mp h1 with h3' | h3'
            · have : γ * γ = 0 := by simpa [sq] using h3'
              exact mul_self_eq_zero.mp this
            · exact absurd h3' h2
          have hα0 : α = 0 := by rw [hαdef, hγ0, zero_mul]
          rw [hα0, zero_smul, zero_add]
          exact hu0
        · intro h0
          have h := hQ
          rw [h0] at h
          simp [fiveForm] at h
          exact hc h.symm
    · obtain ⟨u, huK, huQ⟩ := exists_fiveForm_eq_of_nondeg hK (by omega) (c := c')
      have huH : u ∈ H := (Submodule.mem_inf.mp huK).1
      have hub : fiveForm k ε u b = 0 :=
        (mem_fiveOrth.mp (Submodule.mem_inf.mp huK).2) b (Submodule.subset_span (by simp))
      have hQ := hQval u hub huQ
      have hB := hBval u hub
      refine ⟨α • b + u, add_mem (Submodule.smul_mem _ _ hb) huH, ?_, hQ, hB⟩
      · intro h0
        have hBz : fiveForm k ε (α • b + u) b = 0 := by rw [h0]; simp [fiveForm]
        rw [hBu α u hub] at hBz
        have hα0 : α = 0 := by
          rcases mul_eq_zero.mp hBz with h | h
          · exact h
          · exact absurd h hbs
        have hu0 : u = 0 := by
          have : α • b + u = u := by rw [hα0, zero_smul, zero_add]
          rw [this] at h0
          exact h0
        rw [hu0] at huQ
        simp [fiveForm] at huQ
        exact hc' huQ.symm

theorem exists_fiveNormal_decomposition {k : ℕ} {ε : Bool}
    {A H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hA : IsFiveNondeg k ε A) (hH : IsFiveNondeg k ε H) (hHA : H ≤ A)
    (hdim : Module.finrank (ZMod 5) H + 1 = Module.finrank (ZMod 5) A) :
    ∃ n ∈ A, n ∉ H ∧ fiveForm k ε n n ≠ 0 ∧ (∀ u ∈ H, fiveForm k ε n u = 0) ∧
      A = H ⊔ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)) := by
  have hL : IsFiveNondeg k ε (A ⊓ fiveOrth k ε H) := isFiveNondeg_inf_fiveOrth hA hH hHA
  have hLdim : Module.finrank (ZMod 5) ↥(A ⊓ fiveOrth k ε H) + Module.finrank (ZMod 5) H =
      Module.finrank (ZMod 5) A := finrank_inf_fiveOrth_add hA hHA
  have hLrank : Module.finrank (ZMod 5) ↥(A ⊓ fiveOrth k ε H) = 1 := by omega
  have hLne : (A ⊓ fiveOrth k ε H) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hLrank
    exact one_ne_zero hLrank.symm
  obtain ⟨n, hnL, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  have hnA : n ∈ A := (Submodule.mem_inf.mp hnL).1
  have hnorth : n ∈ fiveOrth k ε H := (Submodule.mem_inf.mp hnL).2
  have hnH : n ∉ H := by
    intro hnH
    exact hn0 ((isFiveNondeg_iff.1 hH) n hnH (fun u hu => (mem_fiveOrth.mp hnorth) u hu))
  have hsup : H ⊔ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)) = A := by
    have hle : H ⊔ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)) ≤ A :=
      sup_le hHA (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hnA))
    have hinf : H ⊓ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzH, hzspan⟩ := Submodule.mem_inf.mp hz
      rw [Submodule.mem_span_singleton] at hzspan
      obtain ⟨μ, rfl⟩ := hzspan
      by_cases hμ : μ = 0
      · rw [hμ, zero_smul]
        exact Submodule.zero_mem ⊥
      · exfalso
        apply hnH
        have hn : n = μ⁻¹ • (μ • n) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
        rw [hn]
        exact Submodule.smul_mem _ _ hzH
    have hfr : Module.finrank (ZMod 5)
        (Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5))) = 1 :=
      finrank_span_singleton hn0
    apply Submodule.eq_of_le_of_finrank_eq hle
    have h := Submodule.finrank_sup_add_finrank_inf_eq H
      (Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)))
    rw [hinf, finrank_bot, hfr] at h
    simp at h
    omega
  have hnQ : fiveForm k ε n n ≠ 0 := by
    intro hQn
    have hsup_le : H ⊔ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5)) ≤
        fiveOrth k ε (Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5))) := by
      apply sup_le
      · intro u hu
        exact mem_fiveOrth.mpr (fun w hw => by
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨μ, rfl⟩ := hw
          rw [fiveForm_smul_right, fiveForm_comm k ε u n, (mem_fiveOrth.mp hnorth) u hu, mul_zero])
      · intro w hw
        rw [Submodule.mem_span_singleton] at hw
        obtain ⟨μ, rfl⟩ := hw
        exact mem_fiveOrth.mpr (fun v hv => by
          rw [Submodule.mem_span_singleton] at hv
          obtain ⟨ν, rfl⟩ := hv
          rw [fiveForm_smul_left, fiveForm_smul_right, hQn]
          ring)
    have hrad : ∀ u ∈ A, fiveForm k ε n u = 0 := by
      intro u hu
      have hu' : u ∈ fiveOrth k ε (Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5))) := by
        apply hsup_le
        rw [hsup]
        exact hu
      have h1 := (mem_fiveOrth.mp hu') n (Submodule.mem_span_singleton_self n)
      rwa [fiveForm_comm] at h1
    exact hn0 ((isFiveNondeg_iff.1 hA) n hnA hrad)
  exact ⟨n, hnA, hnH, hnQ, fun u hu => (mem_fiveOrth.mp hnorth) u hu, hsup.symm⟩

theorem exists_eq_add_smul_of_mem_sup_span {k : ℕ}
    {H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {n z : Fin (k + 1) → ZMod 5}
    (hz : z ∈ H ⊔ Submodule.span (ZMod 5) ({n} : Set (Fin (k + 1) → ZMod 5))) :
    ∃ b ∈ H, ∃ s : ZMod 5, z = b + s • n := by
  rw [Submodule.mem_sup] at hz
  obtain ⟨b, hbH, c, hc, hbc⟩ := hz
  rw [Submodule.mem_span_singleton] at hc
  obtain ⟨s, rfl⟩ := hc
  exact ⟨b, hbH, s, by rw [hbc]⟩

theorem fiveReflOf_mem_sup_of_decomposition {k : ℕ} {ε π : Bool}
    {H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hH : IsFiveNondeg k ε H)
    (h4 : 4 ≤ Module.finrank (ZMod 5) H)
    {x n b y w : Fin (k + 1) → ZMod 5} {s t : ZMod 5}
    (hxQ : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true)
    (hnorth : ∀ u ∈ H, fiveForm k ε n u = 0)
    (hxs : x = b + s • n) (hbH : b ∈ H) (hs : s ≠ 0) (hb0 : b ≠ 0)
    (hyw : y = w + t • n) (hwH : w ∈ H) (hw0 : w ≠ 0)
    (hyQ : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ π = true) :
    fiveReflOf k ε y ∈
      fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} := by
  have hxiso : ∀ a b, fiveForm k ε
      ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a)
      ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b) =
      fiveForm k ε a b :=
    fiveForm_mulVec_of_mem (Subgroup.subset_closure (fiveReflOf_mem hxQ hxπ))
  set γ : ZMod 5 := (2 * s)⁻¹ * (t * (fiveForm k ε x x - 2 * s ^ 2 * fiveForm k ε n n))
    with hγdef
  have hγrel : 2 * s * γ = t * fiveForm k ε x x - 2 * s ^ 2 * t * fiveForm k ε n n := by
    rw [hγdef]
    rw [show 2 * s * ((2 * s)⁻¹ * (t * (fiveForm k ε x x - 2 * s ^ 2 * fiveForm k ε n n))) =
      t * (fiveForm k ε x x - 2 * s ^ 2 * fiveForm k ε n n) by
        rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by decide) hs), one_mul]]
    ring
  obtain ⟨w', hw'H, hw'0, hw'Q, hw'b⟩ :=
    exists_fiveForm_eq_of_nondeg_orth_add hH h4 hbH hb0 (fiveForm k ε w w) γ
  obtain ⟨g₀, hg₀L, hg₀w⟩ : ∃ g₀ ∈ fiveReflectionGroupIn k ε π H,
      (g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w' := by
    by_cases hwQ : fiveForm k ε w w = 0
    · exact exists_mem_fiveReflectionGroupIn_apply_eq_of_singular hH h4 hwH hw'H hw0 hw'0 hwQ
        (by rw [hw'Q, hwQ])
    · exact exists_mem_fiveReflectionGroupIn_apply_eq hH h4 hwH hw'H hw'Q.symm hwQ
  have hg₀iso : ∀ a b, fiveForm k ε
      ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a)
      ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b) = fiveForm k ε a b :=
    fiveForm_mulVec_of_mem_fiveReflectionGroupIn hg₀L
  have hg₀n : (g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n = n :=
    fiveReflectionGroupIn_mulVec_eq_of_mem_fiveOrth (mem_fiveOrth.mpr hnorth) g₀ hg₀L
  have hv : (g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y = w' + t • n := by
    rw [hyw, Matrix.mulVec_add, Matrix.mulVec_smul, hg₀w, hg₀n]
  have hBvx : fiveForm k ε ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) x =
      γ + s * t * fiveForm k ε n n := by
    rw [hv, hxs]
    simp only [fiveForm_add_left, fiveForm_add_right, fiveForm_smul_left, fiveForm_smul_right,
      fiveForm_comm k ε w' n, hnorth w' hw'H, hnorth b hbH, hw'b, mul_zero,
      add_zero]
    ring
  set c₀ : ZMod 5 :=
    2 * fiveForm k ε ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) x *
      (fiveForm k ε x x)⁻¹ with hc₀def
  have hc₀s : c₀ * s = t := by
    rw [hc₀def, hBvx]
    have hγ' : 2 * s * (γ + s * t * fiveForm k ε n n) = t * fiveForm k ε x x := by
      linear_combination hγrel
    field_simp [hxQ]
    linear_combination hγ'
  have hz_eq : (fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ
      ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = w' - c₀ • b := by
    have hcoef : 2 * fiveForm k ε ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) x *
        (fiveForm k ε x x)⁻¹ = c₀ := hc₀def.symm
    rw [fiveReflOf_mulVec, hcoef, hv, hxs, smul_add, smul_smul]
    have htcs : t = c₀ * s := sub_eq_zero.mp (by rw [hc₀s, sub_self])
    rw [htcs]
    abel
  have hzH : w' - c₀ • b ∈ H := sub_mem hw'H (Submodule.smul_mem _ _ hbH)
  have hzQ : fiveForm k ε (w' - c₀ • b) (w' - c₀ • b) = fiveForm k ε y y := by
    have h1 : fiveForm k ε (w' - c₀ • b) (w' - c₀ • b) =
        fiveForm k ε ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y)
          ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) := by
      rw [← hz_eq]
      exact hxiso _ _
    exact h1.trans (hg₀iso y y)
  have hrz : fiveReflOf k ε (w' - c₀ • b) ∈ fiveReflectionGroupIn k ε π H :=
    fiveReflOf_mem_fiveReflectionGroupIn hzH (by rw [hzQ]; exact hyQ) (by rw [hzQ]; exact hyπ)
  set g : GL (Fin (k + 1)) (ZMod 5) := fiveReflOf k ε x * g₀ with hgdef
  have hgL : g ∈ fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} := by
    rw [hgdef]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl)))
      (Subgroup.mem_sup_left hg₀L)
  have hgy : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y = w' - c₀ • b := by
    rw [hgdef, Matrix.GeneralLinearGroup.coe_mul]
    simp only [← Matrix.mulVec_mulVec]
    exact hz_eq
  have hgiso : ∀ a b, fiveForm k ε
      ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a)
      ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b) = fiveForm k ε a b := by
    intro a b
    rw [hgdef, Matrix.GeneralLinearGroup.coe_mul]
    simp only [← Matrix.mulVec_mulVec]
    rw [hxiso ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a)
      ((g₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b), hg₀iso a b]
  have hconj : g * fiveReflOf k ε y * g⁻¹ = fiveReflOf k ε (w' - c₀ • b) := by
    rw [conj_fiveReflOf hgiso y, hgy]
  have hfin : fiveReflOf k ε y = g⁻¹ * fiveReflOf k ε (w' - c₀ • b) * g := by
    rw [← hconj]
    group
  rw [hfin]
  exact mul_mem (mul_mem (inv_mem hgL) (Subgroup.mem_sup_left hrz)) hgL

theorem fiveReflOf_mem_fiveReflectionGroupIn_sup_of_hyperplane {k : ℕ} {ε π : Bool}
    {A H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hA : IsFiveNondeg k ε A) (hH : IsFiveNondeg k ε H) (hHA : H ≤ A)
    (hdim : Module.finrank (ZMod 5) H + 1 = Module.finrank (ZMod 5) A)
    (h4 : 4 ≤ Module.finrank (ZMod 5) H)
    {x : Fin (k + 1) → ZMod 5} (hxA : x ∈ A) (hxH : x ∉ H)
    (hxQ : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true)
    {h : Fin (k + 1) → ZMod 5} (hh : h ∈ H) (hxh : fiveForm k ε x h ≠ 0)
    {y : Fin (k + 1) → ZMod 5} (hyA : y ∈ A) (hyQ : fiveForm k ε y y ≠ 0)
    (hyπ : IsSquare (fiveForm k ε y y) ↔ π = true) :
    fiveReflOf k ε y ∈
      fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} := by
  obtain ⟨n, hnA, hnH, hnQ, hnorth, hAeq⟩ := exists_fiveNormal_decomposition hA hH hHA hdim
  have hxiso : ∀ a b, fiveForm k ε
      ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a)
      ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b) =
      fiveForm k ε a b :=
    fiveForm_mulVec_of_mem (Subgroup.subset_closure (fiveReflOf_mem hxQ hxπ))
  have hxL : fiveReflOf k ε x ∈
      fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))
  obtain ⟨b, hbH, s, hxs⟩ := exists_eq_add_smul_of_mem_sup_span (by rw [← hAeq]; exact hxA)
  have hs : s ≠ 0 := by
    intro hs0
    apply hxH
    rw [hxs, hs0, zero_smul, add_zero]
    exact hbH
  have hb0 : b ≠ 0 := by
    intro hb_eq
    apply hxh
    have h1 : fiveForm k ε x h = fiveForm k ε b h := by
      rw [hxs, fiveForm_add_left, fiveForm_smul_left, hnorth h hh, mul_zero, add_zero]
    rw [h1, hb_eq]
    simp [fiveForm]
  obtain ⟨w, hwH, t, hyw⟩ := exists_eq_add_smul_of_mem_sup_span (by rw [← hAeq]; exact hyA)
  by_cases hw0 : w = 0
  · have ht : t ≠ 0 := by
      intro ht0
      apply hyQ
      rw [hyw, hw0, ht0, zero_smul, add_zero]
      simp [fiveForm]
    have hyn : fiveReflOf k ε y = fiveReflOf k ε n := by
      rw [hyw, hw0, zero_add]
      exact fiveReflOf_smul k ε n ht
    have hnπ : IsSquare (fiveForm k ε n n) ↔ π = true := by
      have hQy : fiveForm k ε y y = t * t * fiveForm k ε n n := by
        rw [hyw, hw0, zero_add, fiveForm_smul_left, fiveForm_smul_right]
        ring
      rw [hQy] at hyπ
      rwa [CFSG.isSquare_mul_self_mul_iff ht] at hyπ
    set w_z : Fin (k + 1) → ZMod 5 :=
      -(2 * s * fiveForm k ε n n * (fiveForm k ε x x)⁻¹) • b with hwzdef
    set t_z : ZMod 5 := 1 - 2 * s * fiveForm k ε n n * (fiveForm k ε x x)⁻¹ * s with htzdef
    have hnx : fiveForm k ε n x = s * fiveForm k ε n n := by
      rw [hxs, fiveForm_add_right, fiveForm_smul_right, hnorth b hbH]
      ring
    have hz_eq : (fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n =
        w_z + t_z • n := by
      rw [fiveReflOf_mulVec, hnx, hwzdef, htzdef, hxs, smul_add, smul_smul]
      module
    have hwzH : w_z ∈ H := by
      rw [hwzdef]
      exact Submodule.smul_mem _ _ hbH
    have hwz0 : w_z ≠ 0 := by
      have hcoef : -(2 * s * fiveForm k ε n n * (fiveForm k ε x x)⁻¹) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) hs) hnQ)
          (inv_ne_zero hxQ))
      rw [hwzdef]
      exact smul_ne_zero hcoef hb0
    have hzQ : fiveForm k ε
        ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n)
        ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n) ≠ 0 := by
      rw [hxiso n n]
      exact hnQ
    have hzπ : IsSquare (fiveForm k ε
        ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n)
        ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n)) ↔
        π = true := by
      rw [hxiso n n]
      exact hnπ
    have hrz : fiveReflOf k ε
        ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n) ∈
        fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} :=
      fiveReflOf_mem_sup_of_decomposition hH h4 hxQ hxπ hnorth hxs hbH hs hb0 hz_eq hwzH hwz0
        hzQ hzπ
    have hconj : fiveReflOf k ε x * fiveReflOf k ε n * (fiveReflOf k ε x)⁻¹ =
        fiveReflOf k ε
          ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n) :=
      conj_fiveReflOf hxiso n
    have hxn : fiveReflOf k ε n = (fiveReflOf k ε x)⁻¹ *
        fiveReflOf k ε
          ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n) *
        fiveReflOf k ε x := by
      rw [← hconj]
      group
    rw [hyn, hxn]
    exact mul_mem (mul_mem (inv_mem hxL) hrz) hxL
  · exact fiveReflOf_mem_sup_of_decomposition hH h4 hxQ hxπ hnorth hxs hbH hs hb0 hyw hwH hw0
      hyQ hyπ

end CFSG.OddTranspositions.PartThree

end
