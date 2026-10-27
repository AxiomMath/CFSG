module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Quad

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

@[expose] def sec7SingPts {K : Type} [Field K]
    (Qf : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) → K) :
    Set (Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) :=
  {P | Module.finrank K P = 1 ∧ ∀ v ∈ P, Qf v = 0}

theorem sec7_smul_of_mem_finrank_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : Submodule K V} (hQ : Module.finrank K Q = 1) {x : V} (hx0 : x ≠ 0) (hxQ : x ∈ Q)
    {w : V} (hw : w ∈ Q) : ∃ c : K, c • x = w := by
  have hx' : (⟨x, hxQ⟩ : Q) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').mp hQ ⟨w, hw⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem sec7_eq_of_mem_finrank_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {P P' : Submodule K V} (hP : Module.finrank K P = 1) (hP' : Module.finrank K P' = 1)
    {x : V} (hx0 : x ≠ 0) (hxP : x ∈ P) (hxP' : x ∈ P') : P = P' := by
  apply le_antisymm
  · intro w hw
    obtain ⟨c, rfl⟩ := sec7_smul_of_mem_finrank_one hP hx0 hxP hw
    exact P'.smul_mem c hxP'
  · intro w hw
    obtain ⟨c, rfl⟩ := sec7_smul_of_mem_finrank_one hP' hx0 hxP' hw
    exact P.smul_mem c hxP

theorem sec7_finrank_one_of_gen {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : Submodule K V} {x : V} (hx0 : x ≠ 0) (hxQ : x ∈ Q)
    (hgen : ∀ w ∈ Q, ∃ c : K, c • x = w) : Module.finrank K Q = 1 := by
  have hx' : (⟨x, hxQ⟩ : Q) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  refine (finrank_eq_one_iff_of_nonzero' _ hx').mpr fun w => ?_
  obtain ⟨c, hc⟩ := hgen w.1 w.2
  exact ⟨c, Subtype.ext hc⟩

theorem sec7_exists_ne_zero_of_finrank_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : Submodule K V} (hQ : Module.finrank K Q = 1) : ∃ x ∈ Q, x ≠ 0 := by
  have hne : Q ≠ ⊥ := by
    rintro rfl
    simp at hQ
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

theorem sec7_map_add {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (v w : V) : Q (v + w) = Q v + Q w + polar Q v w := by
  simp only [polar]
  abel

theorem sec7_polar_ne_zero_of_ne {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P₁ P₂ : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)}
    (hP₁ : Module.finrank K P₁ = 1) (hP₂ : Module.finrank K P₂ = 1)
    (hs₁ : ∀ v ∈ P₁, quadMinus 2 K b c v = 0) (hs₂ : ∀ v ∈ P₂, quadMinus 2 K b c v = 0)
    {u₁ u₂ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hu₁ : u₁ ∈ P₁) (hu₁0 : u₁ ≠ 0)
    (hu₂ : u₂ ∈ P₂) (hu₂0 : u₂ ≠ 0) (hne : P₁ ≠ P₂) :
    polar (quadMinus 2 K b c) u₁ u₂ ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := sec7_minusTwo_singular_perp hirr hu₁0 (hs₁ u₁ hu₁) (hs₂ u₂ hu₂) h
  have hu₂P₁ : u₂ ∈ P₁ := by
    rw [ha]
    exact P₁.smul_mem a hu₁
  exact hne (sec7_eq_of_mem_finrank_one hP₁ hP₂ hu₂0 hu₂P₁ hu₂)

theorem sec7_singPts_line_ncard_le_two {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (l : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) (hl : Module.finrank K l = 2) :
    {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ l}.ncard ≤ 2 := by
  by_contra hgt
  push Not at hgt
  have hfin : {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ l}.Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨P₁, P₂, P₃, h₁, h₂, h₃, h12, h13, h23⟩ := (Set.two_lt_ncard_iff hfin).mp hgt
  obtain ⟨⟨hP₁, hs₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨hP₂, hs₂⟩, hl₂⟩ := h₂
  obtain ⟨⟨hP₃, hs₃⟩, hl₃⟩ := h₃
  obtain ⟨u₁, hu₁, hu₁0⟩ := sec7_exists_ne_zero_of_finrank_one hP₁
  obtain ⟨u₂, hu₂, hu₂0⟩ := sec7_exists_ne_zero_of_finrank_one hP₂
  obtain ⟨u₃, hu₃, hu₃0⟩ := sec7_exists_ne_zero_of_finrank_one hP₃
  have hu₁l : u₁ ∈ l := hl₁ hu₁
  have hu₂l : u₂ ∈ l := hl₂ hu₂
  have hu₃l : u₃ ∈ l := hl₃ hu₃
  have hpol := sec7_polar_ne_zero_of_ne hirr hP₁ hP₂ hs₁ hs₂ hu₁ hu₁0 hu₂ hu₂0 h12
  have hli : LinearIndependent K ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hu₁0, rfl⟩
    · exfalso
      apply hpol
      have hu₂eq : u₂ = (-(s * t⁻¹)) • u₁ := by
        have h1 : t⁻¹ • (s • u₁ + t • u₂) = 0 := by rw [hst, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h1
        rw [neg_smul, mul_comm s t⁻¹]
        exact eq_neg_of_add_eq_zero_right h1
      rw [hu₂eq, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hs₁ u₁ hu₁]
      simp
  have hspan : Submodule.span K (Set.range ![u₁, u₂]) = l := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hu₁l, hu₂l]
    · simp [finrank_span_eq_card hli, hl]
  have hmem : u₃ ∈ Submodule.span K (Set.range ![u₁, u₂]) := by
    rw [hspan]
    exact hu₃l
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c', hc'⟩ := hmem
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hc'
  have hexp : quadMinus 2 K b c (c' 0 • u₁ + c' 1 • u₂) =
      c' 0 * c' 1 * polar (quadMinus 2 K b c) u₁ u₂ := by
    rw [sec7_map_add, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hs₁ u₁ hu₁, hs₂ u₂ hu₂]
    simp only [smul_zero, add_zero, zero_add, smul_eq_mul]
    ring
  have hz : c' 0 * c' 1 = 0 := by
    have hQ3 := hs₃ u₃ hu₃
    rw [← hc', hexp] at hQ3
    exact (mul_eq_zero.mp hQ3).resolve_right hpol
  rcases mul_eq_zero.mp hz with h0 | h1
  · have hu₃P₂ : u₃ ∈ P₂ := by
      rw [← hc', h0, zero_smul, zero_add]
      exact P₂.smul_mem _ hu₂
    exact h23 (sec7_eq_of_mem_finrank_one hP₂ hP₃ hu₃0 hu₃P₂ hu₃)
  · have hu₃P₁ : u₃ ∈ P₁ := by
      rw [← hc', h1, zero_smul, add_zero]
      exact P₁.smul_mem _ hu₁
    exact h13 (sec7_eq_of_mem_finrank_one hP₁ hP₃ hu₃0 hu₃P₁ hu₃)

theorem sec7_singPts_plane_ncard_le {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (pl : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) (hpl : Module.finrank K pl = 3) :
    {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ pl}.ncard ≤ Nat.card K + 1 := by
  have hV : Module.finrank K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨B, hBdef⟩ : ∃ B : LinearMap.BilinForm K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      B = polarBilin (quadMinus 2 K b c) := ⟨_, rfl⟩
  have hB : ∀ x y, B x y = polar (quadMinus 2 K b c) x y := by
    intro x y
    rw [hBdef, QuadraticMap.polarBilin_apply_apply]
  have hBnd : B.Nondegenerate := by
    rw [hBdef]
    exact nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hfo : ∀ W : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      Module.finrank K (B.orthogonal W) = 4 - Module.finrank K W := by
    intro W
    rw [LinearMap.BilinForm.finrank_orthogonal hBnd W, hV]
  have hO : Module.finrank K (B.orthogonal pl) = 1 := by
    have h1 := hfo pl
    omega
  obtain ⟨a, haO, ha0⟩ := sec7_exists_ne_zero_of_finrank_one hO
  have hperp : ∀ m ∈ pl, polar (quadMinus 2 K b c) a m = 0 := by
    intro m hm
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp haO) m hm
    rw [hB, QuadraticMap.polar_comm] at h
    exact h
  have h2zero : ∀ x : K, (2 : ℕ) • x = 0 := fun x => by
    rw [two_nsmul, CharTwo.add_self_eq_zero]
  by_cases hQa : quadMinus 2 K b c a = 0
  · have hsub : {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ pl} ⊆
        ({Submodule.span K {a}} :
          Set (Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))) := by
      rintro P ⟨⟨hP, hs⟩, hPl⟩
      obtain ⟨u, hu, hu0⟩ := sec7_exists_ne_zero_of_finrank_one hP
      obtain ⟨c', hc'⟩ :=
        sec7_minusTwo_singular_perp hirr ha0 hQa (hs u hu) (hperp u (hPl hu))
      rw [Set.mem_singleton_iff]
      apply sec7_eq_of_mem_finrank_one hP (finrank_span_singleton ha0) hu0 hu
      rw [hc']
      exact Submodule.smul_mem _ c' (Submodule.mem_span_singleton_self a)
    calc {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ pl}.ncard
        ≤ ({Submodule.span K {a}} :
            Set (Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
      _ ≤ Nat.card K + 1 := by omega
  · have hle : pl ≤ B.orthogonal (Submodule.span K {a}) := by
      intro m hm
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [hB, QuadraticMap.polar_smul_left, hperp m hm, smul_zero]
    have hO' : Module.finrank K (B.orthogonal (Submodule.span K {a})) = 3 := by
      have h1 := hfo (Submodule.span K {a})
      have h2 := finrank_span_singleton (K := K) ha0
      omega
    have hpl_eq : pl = B.orthogonal (Submodule.span K {a}) :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have haPl : a ∈ pl := by
      rw [hpl_eq, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [hB, QuadraticMap.polar_smul_left, QuadraticMap.polar_self, h2zero, smul_zero]
    have hane : (⟨a, haPl⟩ : pl) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    obtain ⟨N, hN⟩ : ∃ N : Submodule K pl, N = Submodule.span K {(⟨a, haPl⟩ : pl)} :=
      ⟨_, rfl⟩
    have hNmem : ∀ x : pl, x ∈ N ↔
        ∃ c' : K, c' • a = (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) := by
      intro x
      rw [hN, Submodule.mem_span_singleton]
      constructor
      · rintro ⟨c', hc'⟩
        exact ⟨c', by subst hc'; rfl⟩
      · rintro ⟨c', hc'⟩
        exact ⟨c', Subtype.ext hc'⟩
    have hnotN : ∀ (u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) (hu : u ∈ pl), u ≠ 0 →
        quadMinus 2 K b c u = 0 → (⟨u, hu⟩ : pl) ∉ N := by
      intro u hu hu0 hQu hmem
      obtain ⟨c', hc'⟩ := (hNmem ⟨u, hu⟩).mp hmem
      have hc'' : c' • a = u := hc'
      have hQc : quadMinus 2 K b c (c' • a) = c' * c' * quadMinus 2 K b c a := by
        rw [QuadraticMap.map_smul, smul_eq_mul]
      rw [hc'', hQu] at hQc
      have hcc : c' * c' = 0 := (mul_eq_zero.mp hQc.symm).resolve_right hQa
      have hc0 : c' = 0 := mul_self_eq_zero.mp hcc
      apply hu0
      rw [← hc'', hc0, zero_smul]
    have hU2 : Module.finrank K (↥pl ⧸ N) = 2 := by
      have h1 := Submodule.finrank_quotient_add_finrank N
      have h2 : Module.finrank K N = 1 := by
        rw [hN]
        exact finrank_span_singleton hane
      omega
    have hT2 : Nat.card (Projectivization K (↥pl ⧸ N)) = Nat.card K + 1 :=
      Projectivization.card_of_finrank_two K _ hU2
    have hTcard : {H : Submodule K (↥pl ⧸ N) | Module.finrank K H = 1}.ncard =
        Nat.card K + 1 := by
      rw [← hT2, ← Nat.card_coe_set_eq]
      exact (Nat.card_congr (Projectivization.equivSubmodule K (↥pl ⧸ N))).symm
    have hTfin : {H : Submodule K (↥pl ⧸ N) | Module.finrank K H = 1}.Finite :=
      Set.finite_of_ncard_ne_zero (by rw [hTcard]; omega)
    have hmaps : ∀ P ∈ {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ pl},
        (P.comap pl.subtype).map N.mkQ ∈
          {H : Submodule K (↥pl ⧸ N) | Module.finrank K H = 1} := by
      rintro P ⟨⟨hP, hs⟩, hPl⟩
      obtain ⟨u, hu, hu0⟩ := sec7_exists_ne_zero_of_finrank_one hP
      have hupl : u ∈ pl := hPl hu
      have hmu : (⟨u, hupl⟩ : pl) ∈ P.comap pl.subtype := hu
      have hū : N.mkQ (⟨u, hupl⟩ : pl) ≠ 0 := by
        intro h
        have h' := LinearMap.mem_ker.mpr h
        rw [Submodule.ker_mkQ] at h'
        exact hnotN u hupl hu0 (hs u hu) h'
      have hūmem : N.mkQ (⟨u, hupl⟩ : pl) ∈ (P.comap pl.subtype).map N.mkQ :=
        Submodule.mem_map.mpr ⟨_, hmu, rfl⟩
      rw [Set.mem_setOf_eq]
      apply sec7_finrank_one_of_gen hū hūmem
      intro w hw
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
      have hxP : (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ∈ P := hx
      obtain ⟨c', hc'⟩ := sec7_smul_of_mem_finrank_one hP hu0 hu hxP
      have hx' : c' • (⟨u, hupl⟩ : pl) = x := Subtype.ext hc'
      refine ⟨c', ?_⟩
      rw [← hx', LinearMap.map_smul]
    have hinj : Set.InjOn (fun P : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) =>
        (P.comap pl.subtype).map N.mkQ) {P | P ∈ sec7SingPts (quadMinus 2 K b c) ∧ P ≤ pl} := by
      rintro P ⟨⟨hP, hs⟩, hPl⟩ P' ⟨⟨hP', hs'⟩, -⟩ hPP
      have hPP' : (P.comap pl.subtype).map N.mkQ = (P'.comap pl.subtype).map N.mkQ := hPP
      obtain ⟨u, hu, hu0⟩ := sec7_exists_ne_zero_of_finrank_one hP
      have hupl : u ∈ pl := hPl hu
      have hmu : (⟨u, hupl⟩ : pl) ∈ P.comap pl.subtype := hu
      have hū : N.mkQ (⟨u, hupl⟩ : pl) ∈ (P'.comap pl.subtype).map N.mkQ := by
        rw [← hPP']
        exact Submodule.mem_map.mpr ⟨_, hmu, rfl⟩
      obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp hū
      have hdiff : x - (⟨u, hupl⟩ : pl) ∈ LinearMap.ker N.mkQ := by
        rw [LinearMap.mem_ker, map_sub, hxe, sub_self]
      rw [Submodule.ker_mkQ] at hdiff
      obtain ⟨c', hc'⟩ := (hNmem _).mp hdiff
      have hc'' : c' • a = (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) - u := hc'
      have hxV : (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = u + c' • a := by
        rw [hc'']
        abel
      have hxP' : (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ∈ P' := hx
      have hQx : quadMinus 2 K b c (u + c' • a) = c' * c' * quadMinus 2 K b c a := by
        rw [sec7_map_add, hs u hu, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_comm (quadMinus 2 K b c) u a, hperp u hupl, smul_zero, add_zero,
          zero_add, smul_eq_mul]
      have hcc : c' * c' * quadMinus 2 K b c a = 0 := by
        rw [← hQx, ← hxV]
        exact hs' _ hxP'
      have hc0 : c' = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp hcc).resolve_right hQa)
      have hxu : (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = u := by
        rw [hxV, hc0, zero_smul, add_zero]
      have huP' : u ∈ P' := by
        rw [← hxu]
        exact hxP'
      exact sec7_eq_of_mem_finrank_one hP hP' hu0 hu huP'
    have hcard := Set.ncard_le_ncard_of_injOn
      (fun P : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) =>
        (P.comap pl.subtype).map N.mkQ) hmaps hinj hTfin
    rw [hTcard] at hcard
    exact hcard

theorem sec7ov_exists_pair {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hnd : (polarBilin (quadMinus 2 K b c)).Nondegenerate) :
    ∃ u₀ w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, quadMinus 2 K b c u₀ = 0 ∧ u₀ ≠ 0 ∧
      polar (quadMinus 2 K b c) u₀ w = 1 := by
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      u₀ = Pi.single (Sum.inl ⟨0, by omega⟩) 1 := ⟨_, rfl⟩
  have hQu₀ : quadMinus 2 K b c u₀ = 0 := by
    rw [hu₀def, quadMinus_apply]
    simp [Pi.single_apply]
  have hu₀0 : u₀ ≠ 0 := by
    rw [hu₀def]
    intro h
    have h1 := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp at h1
  obtain ⟨w₁, hw₁⟩ : ∃ w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      polar (quadMinus 2 K b c) u₀ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu₀0
    apply hnd.1 u₀
    intro y
    exact hcon y
  refine ⟨u₀, (polar (quadMinus 2 K b c) u₀ w₁)⁻¹ • w₁, hQu₀, hu₀0, ?_⟩
  rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw₁]

theorem sec7ov_W_ncard {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hnd : (polarBilin (quadMinus 2 K b c)).Nondegenerate)
    {u₀ w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hQu₀ : quadMinus 2 K b c u₀ = 0)
    (hu₀0 : u₀ ≠ 0) (hw : polar (quadMinus 2 K b c) u₀ w = 1) :
    {t | polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0}.ncard =
      Nat.card K ^ 2 := by
  have hV : Module.finrank K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have h2zero : ∀ x : K, (2 : ℕ) • x = 0 := fun x => by
    rw [two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨B, hBdef⟩ : ∃ B : LinearMap.BilinForm K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      B = polarBilin (quadMinus 2 K b c) := ⟨_, rfl⟩
  have hB : ∀ x y, B x y = polar (quadMinus 2 K b c) x y := by
    intro x y
    rw [hBdef, QuadraticMap.polarBilin_apply_apply]
  have hBnd : B.Nondegenerate := by
    rw [hBdef]
    exact hnd
  have hli : LinearIndependent K ![u₀, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : polar (quadMinus 2 K b c) u₀ (s • u₀ + t • w) = 0 := by
      rw [hst, QuadraticMap.polar_zero_right]
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQu₀, hw] at h1
    have ht : t = 0 := by simpa using h1
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hu₀0, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      W = B.orthogonal (Submodule.span K (Set.range ![u₀, w])) := ⟨_, rfl⟩
  have hu₀s : u₀ ∈ Submodule.span K (Set.range ![u₀, w]) :=
    Submodule.subset_span ⟨0, by simp⟩
  have hws : w ∈ Submodule.span K (Set.range ![u₀, w]) :=
    Submodule.subset_span ⟨1, by simp⟩
  have hWmem : ∀ t, t ∈ W ↔
      polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0 := by
    intro t
    rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have h1 := h u₀ hu₀s
      have h2 := h w hws
      rw [hB] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩ n hn
      rw [Submodule.mem_span_range_iff_exists_fun] at hn
      obtain ⟨c', rfl⟩ := hn
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      rw [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, h1, h2]
      simp
  have hWfin : Module.finrank K W = 2 := by
    have h1 : Module.finrank K (B.orthogonal (Submodule.span K (Set.range ![u₀, w]))) =
        Module.finrank K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) -
          Module.finrank K (Submodule.span K (Set.range ![u₀, w])) :=
      LinearMap.BilinForm.finrank_orthogonal hBnd _
    have h2 : Module.finrank K (Submodule.span K (Set.range ![u₀, w])) = 2 := by
      rw [finrank_span_eq_card hli]
      simp
    rw [hWdef]
    omega
  have hset : {t | polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0} =
      (W : Set (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) :=
    Set.ext fun t => (hWmem t).symm
  rw [hset, ← Nat.card_coe_set_eq]
  have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥W)
  rw [hWfin] at h
  exact h

theorem sec7ov_A_ncard {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {u₀ w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hQu₀ : quadMinus 2 K b c u₀ = 0)
    (hw : polar (quadMinus 2 K b c) u₀ w = 1) :
    {u | polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0}.ncard =
      {t | polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0}.ncard := by
  have hwpol : polar (quadMinus 2 K b c) w u₀ = 1 := by
    rw [QuadraticMap.polar_comm]
    exact hw
  have h2zero : ∀ x : K, (2 : ℕ) • x = 0 := fun x => by
    rw [two_nsmul, CharTwo.add_self_eq_zero]
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn
      (fun u => u - w - polar (quadMinus 2 K b c) w (u - w) • u₀) ?_ ?_ (Set.toFinite _)
    · intro u hu
      have hu' : polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0 := hu
      obtain ⟨hu1, -⟩ := hu'
      simp only [Set.mem_setOf_eq]
      generalize hκ : polar (quadMinus 2 K b c) w (u - w) = κ
      constructor
      · rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQu₀, hu1, hw]
        simp
      · rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hκ, hwpol]
        simp
    · intro u hu u' hu' hEq
      have hEq' : u - w - polar (quadMinus 2 K b c) w (u - w) • u₀ =
          u' - w - polar (quadMinus 2 K b c) w (u' - w) • u₀ := hEq
      have hu1' : polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0 := hu
      have hu'1' : polar (quadMinus 2 K b c) u₀ u' = 1 ∧ quadMinus 2 K b c u' = 0 := hu'
      obtain ⟨-, hu2⟩ := hu1'
      obtain ⟨hu'1, hu'2⟩ := hu'1'
      generalize polar (quadMinus 2 K b c) w (u - w) = κ at hEq'
      generalize polar (quadMinus 2 K b c) w (u' - w) = κ' at hEq'
      have h4 : u = u' + (κ - κ') • u₀ := by
        calc u = (u - w - κ • u₀) + w + κ • u₀ := by abel
          _ = (u' - w - κ' • u₀) + w + κ • u₀ := by rw [hEq']
          _ = u' + (κ - κ') • u₀ := by rw [sub_smul]; abel
      have hQu' : quadMinus 2 K b c u = κ - κ' := by
        rw [h4, sec7_map_add (quadMinus 2 K b c) u' ((κ - κ') • u₀),
          QuadraticMap.map_smul, hQu₀, smul_zero, add_zero, hu'2, zero_add,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_comm (quadMinus 2 K b c) u' u₀,
          hu'1, smul_eq_mul, mul_one]
      have hδ : κ - κ' = 0 := by
        rw [← hQu']
        exact hu2
      rw [hδ, zero_smul, add_zero] at h4
      exact h4
  · refine Set.ncard_le_ncard_of_injOn
      (fun t => w + t + quadMinus 2 K b c (w + t) • u₀) ?_ ?_ (Set.toFinite _)
    · intro t ht
      have ht' : polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0 := ht
      obtain ⟨h1, -⟩ := ht'
      have h1' : polar (quadMinus 2 K b c) t u₀ = 0 := by
        rw [QuadraticMap.polar_comm]
        exact h1
      simp only [Set.mem_setOf_eq]
      constructor
      · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQu₀, hw, h1]
        simp
      · rw [sec7_map_add (quadMinus 2 K b c) (w + t) (quadMinus 2 K b c (w + t) • u₀),
          QuadraticMap.map_smul, hQu₀, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_add_left, hwpol, h1', smul_zero, add_zero, add_zero, smul_eq_mul,
          mul_one]
        exact CharTwo.add_self_eq_zero _
    · intro t ht t' ht' hEq
      have ht1 : polar (quadMinus 2 K b c) u₀ t = 0 ∧ polar (quadMinus 2 K b c) w t = 0 := ht
      have ht1' : polar (quadMinus 2 K b c) u₀ t' = 0 ∧
          polar (quadMinus 2 K b c) w t' = 0 := ht'
      obtain ⟨-, h2⟩ := ht1
      obtain ⟨-, h2'⟩ := ht1'
      have hEq' : w + t + quadMinus 2 K b c (w + t) • u₀ =
          w + t' + quadMinus 2 K b c (w + t') • u₀ := hEq
      have hp := congrArg (polar (quadMinus 2 K b c) w) hEq'
      simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_self, h2zero, hwpol, h2, h2', smul_eq_mul, mul_one, smul_zero,
        add_zero, zero_add] at hp
      rw [hp] at hEq'
      exact add_left_cancel (add_right_cancel hEq')

theorem sec7ov_mem_sing_of_normalized {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {u₀ u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hu : polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0) :
    Submodule.span K {u} ∈ sec7SingPts (quadMinus 2 K b c) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, QuadraticMap.polar_zero_right] at hu1
    exact zero_ne_one hu1
  simp only [sec7SingPts, Set.mem_setOf_eq]
  refine ⟨finrank_span_singleton hu0, ?_⟩
  intro v hv
  obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [QuadraticMap.map_smul, hu2, smul_zero]

theorem sec7ov_span_mem_sing {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hu₀0 : u₀ ≠ 0)
    (hQu₀ : quadMinus 2 K b c u₀ = 0) :
    Submodule.span K {u₀} ∈ sec7SingPts (quadMinus 2 K b c) := by
  simp only [sec7SingPts, Set.mem_setOf_eq]
  refine ⟨finrank_span_singleton hu₀0, ?_⟩
  intro v hv
  obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [QuadraticMap.map_smul, hQu₀, smul_zero]

theorem sec7ov_exists_normalized {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hQu₀ : quadMinus 2 K b c u₀ = 0)
    (hu₀0 : u₀ ≠ 0) {P : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)}
    (hP : Module.finrank K P = 1) (hs : ∀ v ∈ P, quadMinus 2 K b c v = 0)
    (hPu : P ≠ Submodule.span K {u₀}) :
    ∃ u, (polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0) ∧
      Submodule.span K {u} = P := by
  have hex : ∃ v ∈ P, polar (quadMinus 2 K b c) u₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv, hv0⟩ := sec7_exists_ne_zero_of_finrank_one hP
    obtain ⟨c', hc'⟩ := sec7_minusTwo_singular_perp hirr hu₀0 hQu₀ (hs v hv) (hcon v hv)
    have hvspan : v ∈ Submodule.span K {u₀} := by
      rw [hc']
      exact Submodule.smul_mem _ c' (Submodule.mem_span_singleton_self u₀)
    exact hPu (sec7_eq_of_mem_finrank_one hP (finrank_span_singleton hu₀0) hv0 hv hvspan)
  obtain ⟨v, hv, hpv⟩ := hex
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      x = (polar (quadMinus 2 K b c) u₀ v)⁻¹ • v := ⟨_, rfl⟩
  have hkv : polar (quadMinus 2 K b c) u₀ x = 1 := by
    rw [hx, QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hpv]
  have hne : x ≠ 0 := by
    intro h
    rw [h, QuadraticMap.polar_zero_right] at hkv
    exact zero_ne_one hkv
  have hQx : quadMinus 2 K b c x = 0 := by
    rw [hx, QuadraticMap.map_smul, hs v hv, smul_zero]
  have hxP : x ∈ P := by
    rw [hx]
    exact P.smul_mem _ hv
  refine ⟨x, ⟨hkv, hQx⟩, ?_⟩
  exact sec7_eq_of_mem_finrank_one (finrank_span_singleton hne) hP hne
    (Submodule.mem_span_singleton_self x) hxP

theorem sec7ov_singPts_eq {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hQu₀ : quadMinus 2 K b c u₀ = 0)
    (hu₀0 : u₀ ≠ 0) :
    sec7SingPts (quadMinus 2 K b c) = insert (Submodule.span K {u₀})
      ((fun u => Submodule.span K {u}) ''
        {u | polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0}) := by
  ext P
  rw [Set.mem_insert_iff]
  constructor
  · rintro ⟨hP, hs⟩
    by_cases hPu : P = Submodule.span K {u₀}
    · exact Or.inl hPu
    · right
      obtain ⟨u, hu, hspan⟩ := sec7ov_exists_normalized hirr hQu₀ hu₀0 hP hs hPu
      exact ⟨u, hu, hspan⟩
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · exact sec7ov_span_mem_sing hu₀0 hQu₀
    · exact sec7ov_mem_sing_of_normalized hu

theorem sec7ov_span_injOn {K : Type} [Field K] {b c : K}
    {u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} :
    Set.InjOn (fun u => Submodule.span K {u})
      {u | polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0} := by
  intro u hu u' hu' hEq
  have hu1 : polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0 := hu
  have hu'1 : polar (quadMinus 2 K b c) u₀ u' = 1 ∧ quadMinus 2 K b c u' = 0 := hu'
  have hEq' : Submodule.span K {u} = Submodule.span K {u'} := hEq
  have hm : u' ∈ Submodule.span K {u} := by
    rw [hEq']
    exact Submodule.mem_span_singleton_self u'
  obtain ⟨c₁, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hc1 : polar (quadMinus 2 K b c) u₀ u' = c₁ * polar (quadMinus 2 K b c) u₀ u := by
    rw [← hc, QuadraticMap.polar_smul_right, smul_eq_mul]
  have hc2 : c₁ = 1 := by
    rw [hu1.1, hu'1.1, mul_one] at hc1
    exact hc1.symm
  rw [← hc, hc2, one_smul]

theorem sec7ov_span_notMem {K : Type} [Field K] {b c : K}
    {u₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hQu₀ : quadMinus 2 K b c u₀ = 0) :
    Submodule.span K {u₀} ∉ (fun u => Submodule.span K {u}) ''
      {u | polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0} := by
  rintro ⟨u, hu, hEq⟩
  have hu' : polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0 := hu
  have hEq' : Submodule.span K {u} = Submodule.span K {u₀} := hEq
  have hmem : u ∈ Submodule.span K {u₀} := by
    rw [← hEq']
    exact Submodule.mem_span_singleton_self u
  obtain ⟨c₁, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 : polar (quadMinus 2 K b c) u₀ u = 0 := by
    rw [← hc]
    simp [QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQu₀]
  rw [hu'.1] at h0
  exact one_ne_zero h0

theorem sec7_singPts_ncard {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (sec7SingPts (quadMinus 2 K b c)).ncard = Nat.card K ^ 2 + 1 := by
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨u₀, w, hQu₀, hu₀0, hw⟩ := sec7ov_exists_pair hnd
  rw [sec7ov_singPts_eq hirr hQu₀ hu₀0,
    Set.ncard_insert_of_notMem (sec7ov_span_notMem hQu₀)
      ((Set.toFinite {u | polar (quadMinus 2 K b c) u₀ u = 1 ∧ quadMinus 2 K b c u = 0}).image _),
    Set.InjOn.ncard_image (sec7ov_span_injOn (u₀ := u₀)), sec7ov_A_ncard hQu₀ hw,
    sec7ov_W_ncard hnd hQu₀ hu₀0 hw]

end CFSG.RankThree.GF2n.Stroth80
