module

public import CFSG.Quasithin.H13.AS91Sec3Orbit
public import Certificates.Certificate89012
public import CFSG.Quasithin.H13.AS91Sec3Transport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

section Native


theorem deltaCheck_true : Native.deltaCheck () = true := Certificates.certificate89012

theorem lTabs_fix {g : Array ℕ} (hg : g ∈ Native.lTabs) :
    Native.imgTrio g Native.baseTrio = Native.baseTrio := by
  have h := deltaCheck_true
  simp only [Native.deltaCheck, Bool.and_eq_true] at h
  have ha := List.all_eq_true.1 h.1.1.1 g hg
  simpa only [beq_iff_eq] using ha

theorem deltaCheck_orbit :
    Native.classOrbitCheck 3795 (labelClasses 3795 5 (Native.deltaB (Native.trioSexts ()) 0))
      [1, 42, 56, 1008, 2688] (Native.trioSteps Native.lTabs) = true := by
  have h := deltaCheck_true
  simp only [Native.deltaCheck, Bool.and_eq_true] at h
  exact h.1.1.2

theorem coplanar_deltaB {p : ℕ} (hp : p < 3795) :
    Native.coplanar (Native.trioSexts ()) 0 p = true ↔
      ((Native.deltaB (Native.trioSexts ()) 0 p).getD 0 false = true ∨
        (Native.deltaB (Native.trioSexts ()) 0 p).getD 1 false = true ∨
        (Native.deltaB (Native.trioSexts ()) 0 p).getD 2 false = true) := by
  have h := deltaCheck_true
  simp only [Native.deltaCheck, Bool.and_eq_true] at h
  have hc := List.all_eq_true.1 h.1.2 (p, Native.deltaB (Native.trioSexts ()) 0 p)
    (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)
  simp only [beq_iff_eq] at hc
  rw [hc]
  simp only [Bool.or_eq_true, or_assoc]

theorem deltaB_symm {p : ℕ} (hp : p < 3795) :
    Native.deltaB (Native.trioSexts ()) p 0 = Native.deltaB (Native.trioSexts ()) 0 p := by
  have h := deltaCheck_true
  simp only [Native.deltaCheck, Bool.and_eq_true] at h
  have hd := List.all_eq_true.1 h.2 (p, Native.deltaB (Native.trioSexts ()) 0 p)
    (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)
  simpa only [beq_iff_eq] using hd

end Native

section Transport


theorem delta_trio_pair_of_base {Q : Finset (Finset (Fin 24)) → Finset (Finset (Fin 24)) → Prop}
    (hQ : ∀ g ∈ M24g, ∀ l k, Q l k → Q (g • l) (g • k))
    (h0 : ∀ p < 3795, Q (trioFin 0) (trioFin p)) {l k : Finset (Finset (Fin 24))}
    (hl : IsTrio l) (hk : IsTrio k) : Q l k := by
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  obtain ⟨p, hp, hpk⟩ := (isTrio_iff (g • k)).1 ((isTrio_smul_iff hg).2 hk)
  have h := hQ g⁻¹ (M24g.inv_mem hg) _ _ (h0 p hp)
  rwa [← hgl, inv_smul_smul, hpk, inv_smul_smul] at h

end Transport

section Cert


theorem lPerm_smul_trioFin_zero (j : Fin 4) : lPerm j • trioFin 0 = trioFin 0 := by
  have hj : (j : ℕ) < Native.lTabs.length := j.2
  have hmem : Native.lTabs.getD j #[] ∈ Native.lTabs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rw [smul_trioFin (repT_lPerm j) (by norm_num : 0 < 3795), trioList_zero, lTabs_fix hmem,
    trioFin, trioList_zero]

theorem delta_base_existsUnique {p : ℕ} (hp : p < 3795) :
    ∃! i : Fin 5, Delta (trioFin 0) (trioFin p) i := by
  obtain ⟨-, huniq, -⟩ := classOrbitCheck_spec deltaCheck_orbit
  obtain ⟨i, ⟨hi, hb⟩, hu⟩ := huniq p hp
  refine ⟨⟨i, hi⟩, (deltaB_iff (by norm_num : 0 < 3795) hp ⟨i, hi⟩).1 hb, fun j hj => ?_⟩
  exact Fin.ext (hu j ⟨j.2, (deltaB_iff (by norm_num : 0 < 3795) hp j).2 hj⟩)

theorem delta_base_orbit {p p' : ℕ} (hp : p < 3795) (hp' : p' < 3795) {i : Fin 5}
    (h : Delta (trioFin 0) (trioFin p) i) (h' : Delta (trioFin 0) (trioFin p') i) :
    ∃ g ∈ M24g, g • trioFin 0 = trioFin 0 ∧ g • trioFin p = trioFin p' := by
  obtain ⟨-, -, hcls⟩ := classOrbitCheck_spec deltaCheck_orbit
  obtain ⟨p₀, hp₀, -, -, hreach⟩ := hcls i i.2
  have hmem : ∀ q < 3795, Delta (trioFin 0) (trioFin q) i → q ∈ (List.range 3795).filter
      fun q => (Native.deltaB (Native.trioSexts ()) 0 q).getD i false := by
    intro q hq hD
    rw [List.mem_filter, List.mem_range]
    exact ⟨hq, (deltaB_iff (by norm_num : 0 < 3795) hq i).2 hD⟩
  obtain ⟨σ, hσ, hσ0, hσp⟩ := reachOK_trio_fix (trioFin 0) Native.lTabs lPerm repT_lPerm lPerm_mem
    lPerm_smul_trioFin_zero hreach hp₀ p (hmem p hp h)
  obtain ⟨σ', hσ', hσ'0, hσ'p⟩ := reachOK_trio_fix (trioFin 0) Native.lTabs lPerm repT_lPerm
    lPerm_mem lPerm_smul_trioFin_zero hreach hp₀ p' (hmem p' hp' h')
  refine ⟨σ' * σ⁻¹, M24g.mul_mem hσ' (M24g.inv_mem hσ), ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hσ0.symm, hσ'0]
  · rw [mul_smul, inv_smul_eq_iff.2 hσp.symm, hσ'p]

theorem getD_delta_sizes (i : Fin 5) :
    [1, 42, 56, 1008, 2688].getD i 0 = ![1, 42, 56, 1008, 2688] i := by
  fin_cases i <;> rfl

theorem ncard_delta_base (i : Fin 5) :
    {k | IsTrio k ∧ Delta (trioFin 0) k i}.ncard = ![1, 42, 56, 1008, 2688] i := by
  obtain ⟨-, -, hcls⟩ := classOrbitCheck_spec deltaCheck_orbit
  obtain ⟨-, -, -, hlen, -⟩ := hcls i i.2
  have key := ncard_eq_length_filter (F := trioFin) (n := 3795)
    (fun p hp p' hp' h => trioFin_injective hp hp' h) (P := IsTrio) isTrio_iff
    (fun p => (Native.deltaB (Native.trioSexts ()) 0 p).getD i false)
    (Q := fun k => Delta (trioFin 0) k i) fun p hp =>
      (deltaB_iff (by norm_num : 0 < 3795) hp i).symm
  exact key.trans (hlen.trans (getD_delta_sizes i))

theorem delta_base_symm {p : ℕ} (hp : p < 3795) {i : Fin 5}
    (h : Delta (trioFin 0) (trioFin p) i) : Delta (trioFin p) (trioFin 0) i := by
  refine (deltaB_iff hp (by norm_num : 0 < 3795) i).1 ?_
  rw [deltaB_symm hp]
  exact (deltaB_iff (by norm_num : 0 < 3795) hp i).2 h

theorem coplanar_base_iff {p : ℕ} (hp : p < 3795) :
    Coplanar (trioFin 0) (trioFin p) ↔ Delta (trioFin 0) (trioFin p) 0 ∨
      Delta (trioFin 0) (trioFin p) 1 ∨ Delta (trioFin 0) (trioFin p) 2 := by
  rw [← coplanar_iff (by norm_num : 0 < 3795) hp, coplanar_deltaB hp]
  exact or_congr (deltaB_iff (by norm_num : 0 < 3795) hp 0)
    (or_congr (deltaB_iff (by norm_num : 0 < 3795) hp 1)
      (deltaB_iff (by norm_num : 0 < 3795) hp 2))

theorem delta_existsUnique {l k : Finset (Finset (Fin 24))} (hl : IsTrio l) (hk : IsTrio k) :
    ∃! i : Fin 5, Delta l k i := by
  have hQ : ∀ g ∈ M24g, ∀ l k : Finset (Finset (Fin 24)), (∃! i : Fin 5, Delta l k i) →
      ∃! i : Fin 5, Delta (g • l) (g • k) i := by
    intro g hg l k ⟨i, hi, hu⟩
    exact ⟨i, (delta_smul_iff hg i).2 hi, fun j hj => hu j ((delta_smul_iff hg j).1 hj)⟩
  exact delta_trio_pair_of_base (Q := fun l k => ∃! i : Fin 5, Delta l k i) hQ
    (fun p hp => delta_base_existsUnique hp) hl hk

theorem delta_orbit {l k k' : Finset (Finset (Fin 24))} (hl : IsTrio l) (hk : IsTrio k)
    (hk' : IsTrio k') {i : Fin 5} (h : Delta l k i) (h' : Delta l k' i) :
    ∃ g ∈ M24g, g • l = l ∧ g • k = k' := by
  have hQ : ∀ g ∈ M24g, ∀ l k : Finset (Finset (Fin 24)),
      (∀ (k' : Finset (Finset (Fin 24))) (i : Fin 5), IsTrio k' → Delta l k i → Delta l k' i →
        ∃ h ∈ M24g, h • l = l ∧ h • k = k') →
      ∀ (k' : Finset (Finset (Fin 24))) (i : Fin 5), IsTrio k' → Delta (g • l) (g • k) i →
        Delta (g • l) k' i → ∃ h ∈ M24g, h • g • l = g • l ∧ h • g • k = k' := by
    intro g hg l k hQ k' i hk' hD hD'
    have hD0 : Delta l k i := (delta_smul_iff hg i).1 hD
    have hD1 : Delta l (g⁻¹ • k') i := by
      have := (delta_smul_iff (M24g.inv_mem hg) i).2 hD'
      rwa [inv_smul_smul] at this
    obtain ⟨h, hh, hhl, hhk⟩ := hQ (g⁻¹ • k') i ((isTrio_smul_iff (M24g.inv_mem hg)).2 hk') hD0 hD1
    refine ⟨g * h * g⁻¹, M24g.mul_mem (M24g.mul_mem hg hh) (M24g.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, hhl]
    · rw [mul_smul, mul_smul, inv_smul_smul, hhk, smul_inv_smul]
  have key := delta_trio_pair_of_base
    (Q := fun l k => ∀ (k' : Finset (Finset (Fin 24))) (i : Fin 5), IsTrio k' → Delta l k i →
      Delta l k' i → ∃ g ∈ M24g, g • l = l ∧ g • k = k') hQ
    (fun p hp k' i hk' hD hD' => by
      obtain ⟨p', hp', rfl⟩ := (isTrio_iff k').1 hk'
      exact delta_base_orbit hp hp' hD hD') hl hk
  exact key k' i hk' h h'

theorem ncard_delta {l : Finset (Finset (Fin 24))} (hl : IsTrio l) (i : Fin 5) :
    {k | IsTrio k ∧ Delta l k i}.ncard = ![1, 42, 56, 1008, 2688] i := by
  have hP : ∀ g ∈ M24g, ∀ l : Finset (Finset (Fin 24)),
      (∀ i : Fin 5, {k | IsTrio k ∧ Delta l k i}.ncard = ![1, 42, 56, 1008, 2688] i) →
        ∀ i : Fin 5, {k | IsTrio k ∧ Delta (g • l) k i}.ncard = ![1, 42, 56, 1008, 2688] i := by
    intro g hg l hl i
    have hset : {k | IsTrio k ∧ Delta (g • l) k i} =
        (fun k => g • k) '' {k | IsTrio k ∧ Delta l k i} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨hk, hd⟩
        refine ⟨g⁻¹ • k, ⟨(isTrio_smul_iff (M24g.inv_mem hg)).2 hk, ?_⟩, smul_inv_smul g k⟩
        have := (delta_smul_iff (M24g.inv_mem hg) i).2 hd
        rwa [inv_smul_smul] at this
      · rintro ⟨k₀, ⟨hk₀, hd⟩, rfl⟩
        exact ⟨(isTrio_smul_iff hg).2 hk₀, (delta_smul_iff hg i).2 hd⟩
    rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]
    exact hl i
  exact forall_trio_of_base (P := fun l => ∀ i : Fin 5,
    {k | IsTrio k ∧ Delta l k i}.ncard = ![1, 42, 56, 1008, 2688] i) hP ncard_delta_base hl i

theorem delta_symm {l k : Finset (Finset (Fin 24))} (hl : IsTrio l) (hk : IsTrio k) {i : Fin 5}
    (h : Delta l k i) : Delta k l i := by
  have hQ : ∀ g ∈ M24g, ∀ l k : Finset (Finset (Fin 24)), (∀ i : Fin 5, Delta l k i → Delta k l i) →
      ∀ i : Fin 5, Delta (g • l) (g • k) i → Delta (g • k) (g • l) i := by
    intro g hg l k hQ i hd
    exact (delta_smul_iff hg i).2 (hQ i ((delta_smul_iff hg i).1 hd))
  have key := delta_trio_pair_of_base
    (Q := fun l k => ∀ i : Fin 5, Delta l k i → Delta k l i) hQ
    (fun p hp i hd => delta_base_symm hp hd) hl hk
  exact key i h

theorem coplanar_iff_delta {l k : Finset (Finset (Fin 24))} (hl : IsTrio l) (hk : IsTrio k) :
    Coplanar l k ↔ Delta l k 0 ∨ Delta l k 1 ∨ Delta l k 2 := by
  have hQ : ∀ g ∈ M24g, ∀ l k : Finset (Finset (Fin 24)),
      (Coplanar l k ↔ Delta l k 0 ∨ Delta l k 1 ∨ Delta l k 2) →
        (Coplanar (g • l) (g • k) ↔
          Delta (g • l) (g • k) 0 ∨ Delta (g • l) (g • k) 1 ∨ Delta (g • l) (g • k) 2) := by
    intro g hg l k h
    rw [coplanar_smul_iff hg, delta_smul_iff hg 0, delta_smul_iff hg 1, delta_smul_iff hg 2]
    exact h
  exact delta_trio_pair_of_base
    (Q := fun l k => (Coplanar l k ↔ Delta l k 0 ∨ Delta l k 1 ∨ Delta l k 2)) hQ
    (fun p hp => coplanar_base_iff hp) hl hk

end Cert

end CFSG.Quasithin.H13.AS91.M24G
