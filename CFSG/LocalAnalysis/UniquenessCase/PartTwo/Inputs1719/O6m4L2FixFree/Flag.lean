module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix CFSG.LieType.BorelTits

private theorem eq_bot_or_eq_of_le_of_finrank_eq_one_F04 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {W U : Submodule K V} (hW : Module.finrank K W = 1) (hUW : U ≤ W) :
    U = ⊥ ∨ U = W := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  haveI : Nontrivial W :=
    Module.nontrivial_of_finrank_pos (R := K) (M := W) (by rw [hW]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  have hWspan : W = K ∙ (u : V) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hW u.2 fun h => hu (Subtype.ext h)
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hv : v ∈ K ∙ (u : V) := by
    rw [← hWspan]
    exact hUW hvU
  rw [Submodule.mem_span_singleton] at hv
  obtain ⟨cc, hcc⟩ := hv
  have hcc0 : cc ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcc
    exact hv0 hcc.symm
  have huU : (u : V) ∈ U := by
    have : (u : V) = cc⁻¹ • v := by
      rw [← hcc, smul_smul, inv_mul_cancel₀ hcc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hvU
  rw [hWspan]
  refine le_antisymm ?_ ?_
  · rwa [← hWspan]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact huU

private theorem singSeq_eq_bot_or_eq_of_finrank_eq_one_F04 {K V H : Type} [Field K]
    [AddCommGroup V] [Module K V] [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)
    (R : Subgroup H) (h1 : Module.finrank K ↥(singSeq Φ ρ R (Module.finrank K V)) = 1)
    {k : ℕ} (hk : k ≤ Module.finrank K V) :
    singSeq Φ ρ R k = ⊥ ∨ singSeq Φ ρ R k = singSeq Φ ρ R (Module.finrank K V) :=
  eq_bot_or_eq_of_le_of_finrank_eq_one_F04 h1 (singSeq_mono Φ ρ R hk)

private theorem exists_finrank_three_le_F04 {F : Type} [Field F] {W : Submodule F (Idx → F)}
    (hW : 3 ≤ Module.finrank F W) :
    ∃ U : Submodule F (Idx → F), U ≤ W ∧ Module.finrank F U = 3 := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := W) (n := 3) hW
  let b : Fin 3 → (Idx → F) := fun i => ((f i : W) : Idx → F)
  have hb : LinearIndependent F b := hf.map' W.subtype W.ker_subtype
  refine ⟨Submodule.span F (Set.range b), ?_, ?_⟩
  · intro x hx
    exact Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact (f i).2) hx
  · rw [finrank_span_eq_card hb]
    simp

theorem finrank_idx (F : Type) [Field F] : Module.finrank F (Idx → F) = 6 := by
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem preserves_Q6 {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (g : ↥(Omega6 F b c)) (x : Idx → F) :
    (Phi6 hirr).Q (Rep6 F b c g x) = (Phi6 hirr).Q x := by
  have h : Rep6 F b c g x = Matrix.mulVec ((g : GL Idx F) : Matrix Idx Idx F) x :=
    natRep_apply (Omega6 F b c) g x
  rw [h]
  exact orthGroup_preserves (Phi6 hirr).Q (statedOmega_le_orthGroup (Phi6 hirr).Q g.2) x

theorem noQuotientReflection_6 {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoQuotientReflection (Phi6 hirr) (Rep6 F b c) := by
  intro h Z hZ a ha hQa
  simpa only [Rep6, natRep_apply] using
    not_reflection_on_quotient_of_mem_statedOmega (Phi6 hirr) h.2 hZ ha hQa

theorem le_flagKernel_six {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R : Subgroup ↥(Omega6 F b c)} (hR : IsPGroup 2 ↥R) :
    R ≤ flagKernel (Rep6 F b c) (singFlag (Phi6 hirr) (Rep6 F b c) R) :=
  le_flagKernel_singFlag (p := 2) (Φ := Phi6 hirr) (ρ := Rep6 F b c)
    (preserves_Q6 hirr) (noQuotientReflection_6 hirr) R hR

theorem singSeq_six_ne_bot {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R : Subgroup ↥(Omega6 F b c)} (hR : IsPGroup 2 ↥R)
    (hR1 : R ≠ ⊥) : singSeq (Phi6 hirr) (Rep6 F b c) R 6 ≠ ⊥ := by
  intro hW
  have hdim : Module.finrank F (Idx → F) = 6 := finrank_idx F
  have hflag6 : singFlag (Phi6 hirr) (Rep6 F b c) R 6 = ⊥ := by
    have h := singFlag_finrank (Φ := Phi6 hirr) (ρ := Rep6 F b c) R
    rw [hdim] at h
    rw [h]
    exact hW
  have hflag7 : singFlag (Phi6 hirr) (Rep6 F b c) R 7 = ⊤ := by
    have h := singFlag_finrank_succ (Φ := Phi6 hirr) (ρ := Rep6 F b c) R
    rw [hdim] at h
    rw [show (6 : ℕ) + 1 = 7 from rfl, hW, (Phi6 hirr).polar.perp_bot] at h
    exact h
  have hker : R ≤ flagKernel (Rep6 F b c) (singFlag (Phi6 hirr) (Rep6 F b c) R) :=
    le_flagKernel_six hirr hR
  have htriv : ∀ g ∈ R, Rep6 F b c g = 1 := by
    intro g hg
    apply LinearMap.ext
    intro x
    have h1 := (hker hg).2 6 x
      (by rw [show (6 : ℕ) + 1 = 7 from rfl, hflag7]; trivial)
    rw [hflag6, Submodule.mem_bot] at h1
    simpa using sub_eq_zero.mp h1
  refine hR1 ?_
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact natRep_injective (Omega6 F b c) (by
    have hm : Rep6 F b c g = Rep6 F b c 1 := by rw [htriv g hg, map_one]
    exact hm)

theorem finrank_singSeq_le_two {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (R : Subgroup ↥(Omega6 F b c)) (k : ℕ) :
    Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R k) ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨U, hUW, hU3⟩ :=
    exists_finrank_three_le_F04 (W := singSeq (Phi6 hirr) (Rep6 F b c) R k) (by omega)
  obtain ⟨u, huU, hu0⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_quadMinus_ne_zero (K := F) (b := b) (c := c) hirr
      (n := 3) (by norm_num) U hU3
  have hQ0 : (Phi6 hirr).Q u = 0 := (hUW huU).2
  have huquad : CFSG.LieType.Universal.Spin.quadMinus 3 F b c u = 0 := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus 3 F b c]
    exact hQ0
  exact hu0 huquad

theorem singFlag_mem_of_finrank_eq_one {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V) (R : Subgroup H)
    (h1 : Module.finrank K ↥(singSeq Φ ρ R (Module.finrank K V)) = 1) (k : ℕ) :
    singFlag Φ ρ R k = ⊥ ∨ singFlag Φ ρ R k = singSeq Φ ρ R (Module.finrank K V) ∨
      singFlag Φ ρ R k = Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V)) ∨
      singFlag Φ ρ R k = ⊤ := by
  by_cases hk : k ≤ Module.finrank K V
  · have hsk : singFlag Φ ρ R k = singSeq Φ ρ R k :=
      isoCompletion_of_le (F := Φ.polar) (X := singSeq Φ ρ R) (m := Module.finrank K V) hk
    rcases singSeq_eq_bot_or_eq_of_finrank_eq_one_F04 Φ ρ R h1 hk with h | h
    · exact Or.inl (hsk.trans h)
    · exact Or.inr (Or.inl (hsk.trans h))
  · by_cases hk2 : k ≤ 2 * Module.finrank K V + 1
    · have hsk : singFlag Φ ρ R k =
          Φ.polar.perp (singSeq Φ ρ R (2 * Module.finrank K V + 1 - k)) := by
        change isoCompletion Φ.polar (singSeq Φ ρ R) (Module.finrank K V) k =
          Φ.polar.perp (singSeq Φ ρ R (2 * Module.finrank K V + 1 - k))
        unfold isoCompletion
        rw [if_neg hk, if_pos hk2]
      have hj : 2 * Module.finrank K V + 1 - k ≤ Module.finrank K V := by omega
      rcases singSeq_eq_bot_or_eq_of_finrank_eq_one_F04 Φ ρ R h1 hj with h | h
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hsk, h, ReflForm.perp_bot]
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [hsk, h]
    · have hsk : singFlag Φ ρ R k = ⊤ := by
        change isoCompletion Φ.polar (singSeq Φ ρ R) (Module.finrank K V) k = ⊤
        exact isoCompletion_of_lt (F := Φ.polar) (X := singSeq Φ ρ R)
          (m := Module.finrank K V) (by omega)
      exact Or.inr (Or.inr (Or.inr hsk))

theorem sub_mem_of_flag_dichotomy {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (ρ : H →* Module.End K V) {Fl : ℕ → Submodule K V} (h0 : Fl 0 = ⊥)
    {C D : Submodule K V} (hdich : ∀ k, Fl k ≤ C ∨ D ≤ Fl k) (hex : ∃ k, D ≤ Fl k)
    {R : Subgroup H} (hR : R ≤ flagKernel ρ Fl) : ∀ g ∈ R, ∀ x ∈ D, ρ g x - x ∈ C := by
  classical
  intro g hg x hx
  obtain ⟨-, hlow⟩ := hR hg
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hj0 | hjpos
  · have hDbot : D ≤ (⊥ : Submodule K V) := by
      rw [← h0, ← hj0]
      exact Nat.find_spec hex
    have hx0 : x = 0 := by
      have := hDbot hx
      simpa using this
    rw [hx0, map_zero, sub_zero]
    exact Submodule.zero_mem C
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
    have hnot : ¬ D ≤ Fl i := fun h => Nat.find_min hex (m := i) (by omega) h
    have hCi : Fl i ≤ C := (hdich i).resolve_right hnot
    refine hCi (hlow i x ?_)
    have hxfind : x ∈ Fl (i + 1) := by
      rw [show i + 1 = Nat.find hex by omega]
      exact Nat.find_spec hex hx
    exact hxfind

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
