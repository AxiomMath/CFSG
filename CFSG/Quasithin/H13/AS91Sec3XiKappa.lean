module

public import CFSG.Quasithin.H13.AS91Sec3Orbit
public import Certificates.Certificate89013
public import CFSG.Quasithin.H13.AS91Sec3Transport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem zero_lt_1771 : (0 : ℕ) < 1771 := by norm_num

theorem zero_lt_3795 : (0 : ℕ) < 3795 := by norm_num

theorem uTabs_getD_mem (j : Fin 4) : Native.uTabs.getD j #[] ∈ Native.uTabs := by
  revert j
  decide +kernel

theorem existsUnique_fin_of_lt {k : ℕ} {P : ℕ → Prop} (h : ∃! i, i < k ∧ P i) :
    ∃! i : Fin k, P i := by
  obtain ⟨i, ⟨hi, hP⟩, hu⟩ := h
  exact ⟨⟨i, hi⟩, hP, fun j hj => Fin.ext (hu j.1 ⟨j.2, hj⟩)⟩

theorem xi_smul_iff' {g : S24} (hg : g ∈ M24g) {U W : Finset (Finset (Fin 24))} (i : Fin 4) :
    Xi (g • U) W i ↔ Xi U (g⁻¹ • W) i := by
  have h₀ := xi_smul_iff (U := U) (W := g⁻¹ • W) hg i
  rw [smul_inv_smul] at h₀
  exact h₀

theorem kappa_smul_iff' {g : S24} (hg : g ∈ M24g) {U l : Finset (Finset (Fin 24))}
    (i : Fin 4) : Kappa (g • U) l i ↔ Kappa U (g⁻¹ • l) i := by
  have h₀ := kappa_smul_iff (U := U) (l := g⁻¹ • l) hg i
  rw [smul_inv_smul] at h₀
  exact h₀

theorem xi_exists_step {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : ∀ W, IsSextet W → ∃! i : Fin 4, Xi U W i) (W : Finset (Finset (Fin 24)))
    (hW : IsSextet W) : ∃! i : Fin 4, Xi (g • U) W i := by
  have e : ∀ i : Fin 4, Xi (g • U) W i ↔ Xi U (g⁻¹ • W) i := fun i => xi_smul_iff' hg i
  exact (existsUnique_congr e).2 (hU _ ((isSextet_smul_iff (M24g.inv_mem hg)).2 hW))

theorem xi_orbit_step {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : ∀ (W W' : Finset (Finset (Fin 24))) (i : Fin 4), IsSextet W → IsSextet W' →
      Xi U W i → Xi U W' i → ∃ k ∈ M24g, k • U = U ∧ k • W = W')
    (W W' : Finset (Finset (Fin 24))) (i : Fin 4) (hW : IsSextet W) (hW' : IsSextet W')
    (h : Xi (g • U) W i) (h' : Xi (g • U) W' i) :
    ∃ k ∈ M24g, k • (g • U) = g • U ∧ k • W = W' := by
  have e : ∀ X, Xi (g • U) X i ↔ Xi U (g⁻¹ • X) i := fun X => xi_smul_iff' hg i
  obtain ⟨k, hk, hkU, hkW⟩ := hU (g⁻¹ • W) (g⁻¹ • W') i
    ((isSextet_smul_iff (M24g.inv_mem hg)).2 hW) ((isSextet_smul_iff (M24g.inv_mem hg)).2 hW')
    ((e W).1 h) ((e W').1 h')
  refine ⟨g * k * g⁻¹, M24g.mul_mem (M24g.mul_mem hg hk) (M24g.inv_mem hg), ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hkU]
  · rw [mul_smul, mul_smul, hkW, smul_inv_smul]

theorem kappa_exists_step {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : ∀ l, IsTrio l → ∃! i : Fin 4, Kappa U l i) (l : Finset (Finset (Fin 24)))
    (hl : IsTrio l) : ∃! i : Fin 4, Kappa (g • U) l i := by
  have e : ∀ i : Fin 4, Kappa (g • U) l i ↔ Kappa U (g⁻¹ • l) i :=
    fun i => kappa_smul_iff' hg i
  exact (existsUnique_congr e).2 (hU _ ((isTrio_smul_iff (M24g.inv_mem hg)).2 hl))

theorem kappa_orbit_step {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : ∀ (l l' : Finset (Finset (Fin 24))) (i : Fin 4), IsTrio l → IsTrio l' →
      Kappa U l i → Kappa U l' i → ∃ k ∈ M24g, k • U = U ∧ k • l = l')
    (l l' : Finset (Finset (Fin 24))) (i : Fin 4) (hl : IsTrio l) (hl' : IsTrio l')
    (h : Kappa (g • U) l i) (h' : Kappa (g • U) l' i) :
    ∃ k ∈ M24g, k • (g • U) = g • U ∧ k • l = l' := by
  have e : ∀ X, Kappa (g • U) X i ↔ Kappa U (g⁻¹ • X) i := fun X => kappa_smul_iff' hg i
  obtain ⟨k, hk, hkU, hkl⟩ := hU (g⁻¹ • l) (g⁻¹ • l') i
    ((isTrio_smul_iff (M24g.inv_mem hg)).2 hl) ((isTrio_smul_iff (M24g.inv_mem hg)).2 hl')
    ((e l).1 h) ((e l').1 h')
  refine ⟨g * k * g⁻¹, M24g.mul_mem (M24g.mul_mem hg hk) (M24g.inv_mem hg), ?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hkU]
  · rw [mul_smul, mul_smul, hkl, smul_inv_smul]

theorem ncard_xi_step {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : ∀ i : Fin 4, {W | IsSextet W ∧ Xi U W i}.ncard = ![1, 90, 240, 1440] i) (i : Fin 4) :
    {W | IsSextet W ∧ Xi (g • U) W i}.ncard = ![1, 90, 240, 1440] i := by
  have hset : {W | IsSextet W ∧ Xi (g • U) W i} =
      (fun W => g • W) '' {W | IsSextet W ∧ Xi U W i} := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hW, hX⟩
      exact ⟨g⁻¹ • W, ⟨(isSextet_smul_iff (M24g.inv_mem hg)).2 hW, (xi_smul_iff' hg i).1 hX⟩,
        smul_inv_smul g W⟩
    · rintro ⟨W₁, ⟨hW₁, hX₁⟩, rfl⟩
      exact ⟨(isSextet_smul_iff hg).2 hW₁, (xi_smul_iff hg i).2 hX₁⟩
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]
  exact hU i

section Checks

theorem uTabs_fix_sextet :
    Native.uTabs.all (fun g => Native.imgSext g Native.baseSext == Native.baseSext) = true := by
  have h : Native.sextFactsCheck () = true := Certificates.certificate89013
  simp only [Native.sextFactsCheck, Bool.and_eq_true] at h
  exact h.1.1

theorem xiCheck :
    Native.classOrbitCheck 1771 (labelClasses 1771 4 (Native.xiB 0))
      [1, 90, 240, 1440] (Native.sextSteps Native.uTabs) = true := by
  have h : Native.sextFactsCheck () = true := Certificates.certificate89013
  simp only [Native.sextFactsCheck, Bool.and_eq_true] at h
  exact h.1.2

theorem kappaCheck :
    Native.classOrbitCheck 3795 (labelClasses 3795 4 (Native.kappaB (Native.trioSexts ()) 0))
      [15, 180, 720, 2880] (Native.trioSteps Native.uTabs) = true := by
  have h : Native.sextFactsCheck () = true := Certificates.certificate89013
  simp only [Native.sextFactsCheck, Bool.and_eq_true] at h
  exact h.2

end Checks

section Cert

theorem uPerm_smul_sextFin_zero (j : Fin 4) : uPerm j • sextFin 0 = sextFin 0 := by
  have h1 : Native.imgSext (Native.uTabs.getD j #[]) Native.baseSext = Native.baseSext :=
    beq_iff_eq.1 (List.all_eq_true.1 uTabs_fix_sextet _ (uTabs_getD_mem j))
  rw [smul_sextFin (q := 0) (repT_uPerm j) zero_lt_1771, sextList_zero, h1, sextFin,
    sextList_zero]

theorem xi_base_unique {q : ℕ} (hq : q < 1771) :
    ∃! i : Fin 4, Xi (sextFin 0) (sextFin q) i := by
  obtain ⟨-, hpart, -⟩ := classOrbitCheck_spec xiCheck
  have e : ∀ i : Fin 4, (Native.xiB 0 q).getD i false = true ↔ Xi (sextFin 0) (sextFin q) i :=
    fun i => xiB_iff zero_lt_1771 hq i
  exact (existsUnique_congr e).1 (existsUnique_fin_of_lt (hpart q hq))

theorem xi_base_orbit {q q' : ℕ} (hq : q < 1771) (hq' : q' < 1771) {i : Fin 4}
    (h : Xi (sextFin 0) (sextFin q) i) (h' : Xi (sextFin 0) (sextFin q') i) :
    ∃ k ∈ M24g, k • sextFin 0 = sextFin 0 ∧ k • sextFin q = sextFin q' := by
  obtain ⟨p₀, hp₀, -, -, hreach⟩ := (classOrbitCheck_spec xiCheck).2.2 i.1 i.2
  have hmem : ∀ x, x < 1771 → Xi (sextFin 0) (sextFin x) i →
      x ∈ (List.range 1771).filter (fun p => (Native.xiB 0 p).getD i false) :=
    fun x hx hX => List.mem_filter.2 ⟨List.mem_range.2 hx, (xiB_iff zero_lt_1771 hx i).2 hX⟩
  obtain ⟨σ, hσ, hσ0, hσq⟩ := reachOK_sext_fix (sextFin 0) Native.uTabs uPerm repT_uPerm
    uPerm_mem uPerm_smul_sextFin_zero hreach hp₀ q (hmem q hq h)
  obtain ⟨σ', hσ', hσ0', hσq'⟩ := reachOK_sext_fix (sextFin 0) Native.uTabs uPerm repT_uPerm
    uPerm_mem uPerm_smul_sextFin_zero hreach hp₀ q' (hmem q' hq' h')
  refine ⟨σ' * σ⁻¹, M24g.mul_mem hσ' (M24g.inv_mem hσ), ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hσ0.symm, hσ0']
  · rw [mul_smul, inv_smul_eq_iff.2 hσq.symm, hσq']

theorem xi_orbit_base (W W' : Finset (Finset (Fin 24))) (i : Fin 4) (hW : IsSextet W)
    (hW' : IsSextet W') (h : Xi (sextFin 0) W i) (h' : Xi (sextFin 0) W' i) :
    ∃ k ∈ M24g, k • sextFin 0 = sextFin 0 ∧ k • W = W' := by
  obtain ⟨q, hq, rfl⟩ := (isSextet_iff W).1 hW
  obtain ⟨q', hq', rfl⟩ := (isSextet_iff W').1 hW'
  exact xi_base_orbit hq hq' h h'

theorem xi_exists_base (W : Finset (Finset (Fin 24))) (hW : IsSextet W) :
    ∃! i : Fin 4, Xi (sextFin 0) W i := by
  obtain ⟨q, hq, rfl⟩ := (isSextet_iff W).1 hW
  exact xi_base_unique hq

theorem ncard_xi_base (i : Fin 4) :
    {W | IsSextet W ∧ Xi (sextFin 0) W i}.ncard = ![1, 90, 240, 1440] i := by
  obtain ⟨-, -, -, hlen, -⟩ := (classOrbitCheck_spec xiCheck).2.2 i.1 i.2
  have hcount := ncard_eq_length_filter (F := sextFin) (n := 1771)
    (fun p hp p' hp' he => sextFin_injective hp hp' he) (P := IsSextet) isSextet_iff
    (fun q => (Native.xiB 0 q).getD i false) (Q := fun W => Xi (sextFin 0) W i)
    (fun p hp => (xiB_iff zero_lt_1771 hp i).symm)
  rw [hcount, hlen]
  fin_cases i <;> rfl

theorem kappa_base_unique {p : ℕ} (hp : p < 3795) :
    ∃! i : Fin 4, Kappa (sextFin 0) (trioFin p) i := by
  obtain ⟨-, hpart, -⟩ := classOrbitCheck_spec kappaCheck
  have e : ∀ i : Fin 4, (Native.kappaB (Native.trioSexts ()) 0 p).getD i false = true ↔
      Kappa (sextFin 0) (trioFin p) i := fun i => kappaB_iff zero_lt_1771 hp i
  exact (existsUnique_congr e).1 (existsUnique_fin_of_lt (hpart p hp))

theorem kappa_base_orbit {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) {i : Fin 4}
    (h : Kappa (sextFin 0) (trioFin p) i) (h' : Kappa (sextFin 0) (trioFin p') i) :
    ∃ k ∈ M24g, k • sextFin 0 = sextFin 0 ∧ k • trioFin p = trioFin p' := by
  obtain ⟨p₀, hp₀, -, -, hreach⟩ := (classOrbitCheck_spec kappaCheck).2.2 i.1 i.2
  have hmem : ∀ x, x < 3795 → Kappa (sextFin 0) (trioFin x) i →
      x ∈ (List.range 3795).filter
        (fun p => (Native.kappaB (Native.trioSexts ()) 0 p).getD i false) :=
    fun x hx hK => List.mem_filter.2 ⟨List.mem_range.2 hx, (kappaB_iff zero_lt_1771 hx i).2 hK⟩
  obtain ⟨σ, hσ, hσ0, hσp⟩ := reachOK_trio_fix (sextFin 0) Native.uTabs uPerm repT_uPerm
    uPerm_mem uPerm_smul_sextFin_zero hreach hp₀ p (hmem p hp h)
  obtain ⟨σ', hσ', hσ0', hσp'⟩ := reachOK_trio_fix (sextFin 0) Native.uTabs uPerm repT_uPerm
    uPerm_mem uPerm_smul_sextFin_zero hreach hp₀ p' (hmem p' hp' h')
  refine ⟨σ' * σ⁻¹, M24g.mul_mem hσ' (M24g.inv_mem hσ), ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hσ0.symm, hσ0']
  · rw [mul_smul, inv_smul_eq_iff.2 hσp.symm, hσp']

theorem kappa_orbit_base (l l' : Finset (Finset (Fin 24))) (i : Fin 4) (hl : IsTrio l)
    (hl' : IsTrio l') (h : Kappa (sextFin 0) l i) (h' : Kappa (sextFin 0) l' i) :
    ∃ k ∈ M24g, k • sextFin 0 = sextFin 0 ∧ k • l = l' := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff l).1 hl
  obtain ⟨p', hp', rfl⟩ := (isTrio_iff l').1 hl'
  exact kappa_base_orbit hp hp' h h'

theorem kappa_exists_base (l : Finset (Finset (Fin 24))) (hl : IsTrio l) :
    ∃! i : Fin 4, Kappa (sextFin 0) l i := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff l).1 hl
  exact kappa_base_unique hp

theorem xi_existsUnique {U W : Finset (Finset (Fin 24))} (hU : IsSextet U) (hW : IsSextet W) :
    ∃! i : Fin 4, Xi U W i :=
  forall_sextet_of_base (P := fun U => ∀ W, IsSextet W → ∃! i : Fin 4, Xi U W i)
    (fun _ hg _ hU => xi_exists_step hg hU) xi_exists_base hU W hW

theorem xi_orbit {U W W' : Finset (Finset (Fin 24))} (hU : IsSextet U) (hW : IsSextet W)
    (hW' : IsSextet W') {i : Fin 4} (h : Xi U W i) (h' : Xi U W' i) :
    ∃ g ∈ M24g, g • U = U ∧ g • W = W' :=
  forall_sextet_of_base
    (P := fun U => ∀ (W W' : Finset (Finset (Fin 24))) (i : Fin 4), IsSextet W → IsSextet W' →
      Xi U W i → Xi U W' i → ∃ g ∈ M24g, g • U = U ∧ g • W = W')
    (fun _ hg _ hU => xi_orbit_step hg hU) xi_orbit_base hU W W' i hW hW' h h'

theorem ncard_xi {U : Finset (Finset (Fin 24))} (hU : IsSextet U) (i : Fin 4) :
    {W | IsSextet W ∧ Xi U W i}.ncard = ![1, 90, 240, 1440] i :=
  forall_sextet_of_base
    (P := fun U => ∀ i : Fin 4, {W | IsSextet W ∧ Xi U W i}.ncard = ![1, 90, 240, 1440] i)
    (fun _ hg _ hU => ncard_xi_step hg hU) ncard_xi_base hU i

theorem kappa_existsUnique {U l : Finset (Finset (Fin 24))} (hU : IsSextet U) (hl : IsTrio l) :
    ∃! i : Fin 4, Kappa U l i :=
  forall_sextet_of_base (P := fun U => ∀ l, IsTrio l → ∃! i : Fin 4, Kappa U l i)
    (fun _ hg _ hU => kappa_exists_step hg hU) kappa_exists_base hU l hl

theorem kappa_orbit {U l l' : Finset (Finset (Fin 24))} (hU : IsSextet U) (hl : IsTrio l)
    (hl' : IsTrio l') {i : Fin 4} (h : Kappa U l i) (h' : Kappa U l' i) :
    ∃ g ∈ M24g, g • U = U ∧ g • l = l' :=
  forall_sextet_of_base
    (P := fun U => ∀ (l l' : Finset (Finset (Fin 24))) (i : Fin 4), IsTrio l → IsTrio l' →
      Kappa U l i → Kappa U l' i → ∃ g ∈ M24g, g • U = U ∧ g • l = l')
    (fun _ hg _ hU => kappa_orbit_step hg hU) kappa_orbit_base hU l l' i hl hl' h h'

end Cert

end CFSG.Quasithin.H13.AS91.M24G
