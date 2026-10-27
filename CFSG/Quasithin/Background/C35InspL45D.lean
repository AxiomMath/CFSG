module

public import CFSG.Quasithin.Background.C35InspL45C
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod

noncomputable def glEquivSL (n : ℕ) :
    GL (Fin n) (ZMod 2) ≃* SpecialLinearGroup (Fin n) (ZMod 2) :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
      refine ⟨⟨(g : Matrix (Fin n) (Fin n) (ZMod 2)), ?_⟩, Units.ext rfl⟩
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hu (Matrix.GeneralLinearGroup.det g),
        Units.val_one]⟩).symm

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem exists_sl_of_l45 {K : Subgroup A} (hc : Subgroup.center ↥K = ⊥)
    (hfam : IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      ∃ ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2), Function.Bijective ψ := by
  let e₁ : ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  rcases hfam with h | h | h
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two h
    exact ⟨4, Or.inl rfl, (e₁.trans e).toMonoidHom, (e₁.trans e).bijective⟩
  · obtain ⟨e⟩ := h
    obtain ⟨φ, -⟩ := exists_iso_alt8_carm
    let e' := ((e₁.trans e).trans φ).trans (glEquivSL 4)
    exact ⟨4, Or.inl rfl, e'.toMonoidHom, e'.bijective⟩
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two h
    exact ⟨5, Or.inr rfl, (e₁.trans e).toMonoidHom, (e₁.trans e).bijective⟩

theorem t34_sq : SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) *
    SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) = 1 := by
  decide +kernel

theorem t34_cube : (SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) *
    (SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 3 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) *
      (SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 3 by decide) (1 : ZMod 2))⁻¹)) ^ 3 =
      1 ∧
    SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) *
    (SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 3 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (3 : Fin 5) ≠ 4 by decide) (1 : ZMod 2) *
      (SpecialLinearGroup.transvection (show (4 : Fin 5) ≠ 3 by decide) (1 : ZMod 2))⁻¹) ≠ 1 := by
  decide +kernel

theorem t01_sq : SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) *
    SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) = 1 := by
  decide +kernel

theorem t01_cube : (SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) *
    (SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) *
      (SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) (1 : ZMod 2))⁻¹)) ^ 3 =
      1 ∧
    SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) *
    (SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) (1 : ZMod 2) *
      (SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) (1 : ZMod 2))⁻¹) ≠ 1 := by
  decide +kernel

theorem transvection_mem_flag {n : ℕ} {k l : Fin n} (hkl : k ≠ l) {I : Set ℕ}
    (h : ∀ c ∈ I, ¬ ((l : ℕ) < c ∧ c ≤ (k : ℕ))) :
    SpecialLinearGroup.transvection hkl (1 : ZMod 2) ∈ flagStabilizer n (ZMod 2) I := by
  refine mem_flagStabilizer_of_entries fun r c' d hd hl hk => ?_
  refine transvection_entry hkl (fun he => by subst he; omega) fun ⟨h1, h2⟩ => ?_
  subst h1 h2
  exact h d hd ⟨hl, hk⟩

theorem l45_holds : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A),
    C35Data K Y M₀ V → Subgroup.center ↥K = ⊥ →
    (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) →
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ C35Concl2a n K Y M₀ V) ∨ C35Concl2b K Y M₀ V := by
  intro A _ _ K Y M₀ V hD hc hfam
  classical
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hD.parabolic.1
  obtain ⟨n, hn, ψ, hψ⟩ := exists_sl_of_l45 hc hfam
  obtain ⟨g, I, a, m, h, α, hm3, ha, hb, hno, hIc, hprop, hQ, hM, hαs, hker, hblk, hcross⟩ :=
    l45_config hD hc hM₀K (by omega) (by omega) ψ hψ
  have hθ : Function.Bijective ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) :=
    ⟨(MulAut.conj g⁻¹).injective.comp hψ.1, (MulAut.conj g⁻¹).surjective.comp hψ.2⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have hmn : m < n := by omega
    rcases (by omega : m + 1 = n ∨ (m = 3 ∧ n = 5)) with h1 | ⟨rfl, rfl⟩
    · have hI : I = {m} := by
        ext c
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have := hIc c hc
          have := hno c hc
          show c = m
          omega
        · rw [hc]
          rcases hb with hb | hb
          · omega
          · simpa using hb
      left
      exact ⟨n, hn, concl2a_nat hD hM₀K hc (by omega) h1 h _ hθ α hαs hker hblk hcross
        (hI ▸ hQ)⟩
    · have h3I : 3 ∈ I := by
        rcases hb with hb | hb
        · omega
        · simpa using hb
      by_cases h4I : 4 ∈ I
      · have hI : I = {3, 4} := by
          ext c
          refine ⟨fun hc => ?_, fun hc => ?_⟩
          · have := hIc c hc
            have := hno c hc
            show c = 3 ∨ c = 4
            omega
          · rcases hc with rfl | rfl
            · exact h3I
            · exact h4I
        subst hI
        exact Or.inr (concl2b_nat hD hM₀K hc h _ hθ α hαs hker hblk hcross hQ hM)
      · have hI : I = {3} := by
          ext c
          refine ⟨fun hc => ?_, fun hc => ?_⟩
          · have := hIc c hc
            have := hno c hc
            have h4 : c ≠ 4 := fun h => h4I (h ▸ hc)
            show c = 3
            omega
          · rw [hc]
            exact h3I
        subst hI
        exfalso
        refine false_of_extra hD hM₀K hc h _ hθ α hker (fun x => (hblk x).1) hQ
          (blockLeft_zero _ 3) (blockRight_of_stabilizer fun g hg => mem_flagStabilizer.1 hg 3 rfl)
          _ _ (transvection_mem_flag (show (3 : Fin 5) ≠ 4 by decide) ?_)
          (transvection_mem_flag (show (4 : Fin 5) ≠ 3 by decide) ?_) ?_ t34_sq t34_cube.1
          t34_cube.2
        · intro c hc
          rw [hc]
          simp
        · intro c hc
          rw [hc]
          simp
        · rw [CFSG.LinearGroups.coe_transvection]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
  · by_cases hlast : a + m = n
    · rcases (by omega : a = 1 ∨ (a = 2 ∧ m = 3 ∧ n = 5)) with rfl | ⟨rfl, rfl, rfl⟩
      · have hI : I = {1} := by
          ext c
          refine ⟨fun hc => ?_, fun hc => ?_⟩
          · have := hIc c hc
            have := hno c hc
            show c = 1
            omega
          · rw [hc]
            rcases ha with ha | ha
            · omega
            · exact ha
        left
        exact ⟨n, hn, concl2a_dual hD hM₀K hc (by omega) hlast h _ hθ α hαs hker hblk hcross
          (hI ▸ hQ)⟩
      · have h2I : 2 ∈ I := by
          rcases ha with ha | ha
          · omega
          · exact ha
        by_cases h1I : 1 ∈ I
        · have hI : I = {1, 2} := by
            ext c
            refine ⟨fun hc => ?_, fun hc => ?_⟩
            · have := hIc c hc
              have := hno c hc
              show c = 1 ∨ c = 2
              omega
            · rcases hc with rfl | rfl
              · exact h1I
              · exact h2I
          subst hI
          exact Or.inr (concl2b_dual hD hM₀K hc h _ hθ α hαs hker hblk hcross hQ hM)
        · have hI : I = {2} := by
            ext c
            refine ⟨fun hc => ?_, fun hc => ?_⟩
            · have := hIc c hc
              have := hno c hc
              have h1 : c ≠ 1 := fun h => h1I (h ▸ hc)
              show c = 2
              omega
            · rw [hc]
              exact h2I
          subst hI
          exfalso
          refine false_of_extra hD hM₀K hc h _ hθ α hker (fun x => (hblk x).1) hQ
            (blockLeft_of_stabilizer fun g hg => mem_flagStabilizer.1 hg 2 rfl)
            (blockRight_top _ rfl)
            _ _ (transvection_mem_flag (show (0 : Fin 5) ≠ 1 by decide) ?_)
            (transvection_mem_flag (show (1 : Fin 5) ≠ 0 by decide) ?_) ?_ t01_sq t01_cube.1
            t01_cube.2
          · intro c hc
            rw [hc]
            simp
          · intro c hc
            rw [hc]
            simp
          · rw [CFSG.LinearGroups.coe_transvection]
            ext i j
            fin_cases i <;> fin_cases j <;> rfl
    · exact (false_of_middle hD hM₀K h _ α hker hblk hcross hθ.1 ha0 (by omega)
        (by omega)).elim

end CFSG.Quasithin.C35Pf
