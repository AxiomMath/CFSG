module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCores

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (rootTorusParam)

section Param

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

omit [Field K] in
theorem permMatrix_mul_diagonal_eq {R : Type*} [CommRing R] (σ : Equiv.Perm (Fin n))
    (d : Fin n → R) : σ.permMatrix R * diagonal d = diagonal (d ∘ σ) * σ.permMatrix R := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.comp_apply]
  split_ifs with hij
  · rw [hij, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

theorem comp_symm_mem_unitaryTorusParam_iff (ρ : Equiv.Perm (Fin n)) {I : Finset (Fin n)}
    {c : Fin n → Kˣ} :
    c ∘ ρ.symm ∈ unitaryTorusParam h (I.map ρ.toEmbedding) ↔ c ∈ unitaryTorusParam h I := by
  have hb := LinearPilot.comp_symm_mem_blockTorusParam_iff (K := K) ρ (I := I) (c := c)
  rw [LinearPilot.mem_blockTorusParam, LinearPilot.mem_blockTorusParam] at hb
  rw [mem_unitaryTorusParam, mem_unitaryTorusParam]
  constructor
  · rintro ⟨hN, hrest⟩
    exact ⟨fun i => by simpa using hN (ρ i), hb.1 hrest⟩
  · rintro ⟨hN, hrest⟩
    exact ⟨fun i => hN (ρ.symm i), hb.2 hrest⟩

@[expose] def unitaryPermParam (ρ : Equiv.Perm (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) : unitaryTorusParam h (∅ : Finset (Fin n)) :=
  ⟨c.1 ∘ ρ.symm, by
    simpa using (comp_symm_mem_unitaryTorusParam_iff h ρ (I := ∅) (c := c.1)).2 c.2⟩

theorem coe_unitaryPermParam (ρ : Equiv.Perm (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    (unitaryPermParam h ρ c).1 = c.1 ∘ ρ.symm :=
  rfl

theorem unitaryPermParam_unitaryPermParam_symm (ρ : Equiv.Perm (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    unitaryPermParam h ρ (unitaryPermParam h ρ.symm c) = c :=
  Subtype.ext (funext fun i => by simp [coe_unitaryPermParam])

end Param

section Monomial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem permSU_mul_torusDiagSU (ρ : Equiv.Perm (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    permSU h ρ.symm * torusDiagSU h c * (permSU h ρ.symm)⁻¹ =
      torusDiagSU h (unitaryPermParam h ρ c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_permSU, coe_torusDiagSU]
  exact permMatrix_mul_diagonal_eq ρ.symm _

theorem unitaryProj_permSU_conj_torusDiagSU (ρ : Equiv.Perm (Fin n))
    (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    unitaryProj h n (permSU h ρ.symm) * unitaryProj h n (torusDiagSU h c) *
        (unitaryProj h n (permSU h ρ.symm))⁻¹ =
      unitaryProj h n (torusDiagSU h (unitaryPermParam h ρ c)) := by
  rw [← map_mul, ← map_inv, ← map_mul, permSU_mul_torusDiagSU]

theorem map_conj_unitaryBlockTorus (ρ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    (unitaryBlockTorus h I).map (MulAut.conj (unitaryProj h n (permSU h ρ.symm))).toMonoidHom =
      unitaryBlockTorus h (I.map ρ.toEmbedding) := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_unitaryBlockTorus h).1 hy
    rw [unitaryProj_permSU_conj_torusDiagSU]
    exact unitaryProj_torusDiagSU_mem_unitaryBlockTorus h
      ((comp_symm_mem_unitaryTorusParam_iff h ρ).2 hc)
  · intro hx
    obtain ⟨c, hc, rfl⟩ := (mem_unitaryBlockTorus h).1 hx
    refine ⟨unitaryProj h n (torusDiagSU h (unitaryPermParam h ρ.symm c)),
      unitaryProj_torusDiagSU_mem_unitaryBlockTorus h ?_, ?_⟩
    · rw [← comp_symm_mem_unitaryTorusParam_iff h ρ, coe_unitaryPermParam]
      simpa [Function.comp_def] using hc
    · rw [unitaryProj_permSU_conj_torusDiagSU, unitaryPermParam_unitaryPermParam_symm]

theorem map_conj_unitaryRootTorus (ρ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    (unitaryRootTorus h hab).map (MulAut.conj (unitaryProj h n (permSU h ρ.symm))).toMonoidHom =
      unitaryRootTorus h (ρ.injective.ne hab) := by
  rw [unitaryRootTorus, unitaryRootTorus, ← MonoidHom.range_comp]
  congr 1
  refine MonoidHom.ext fun κ => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [unitaryProj_permSU_conj_torusDiagSU]
  congr 2
  exact Subtype.ext (LinearPilot.rootTorusParam_comp_symm ρ a b (κ : Kˣ))

end Monomial

section Transport

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ} (e : L ≃* unitaryPSU h n)

theorem exists_pieceCore_map_conj (ρ : Equiv.Perm (Fin n)) :
    ∃ w ∈ L, (∀ I : Finset (Fin n),
      pieceCore e (I.map ρ.toEmbedding) = (pieceCore e I).map (MulAut.conj w).toMonoidHom ∧
      modelToG e (blockSU h (I.map ρ.toEmbedding)) =
        (modelToG e (blockSU h I)).map (MulAut.conj w).toMonoidHom) ∧
      ∀ (a b : Fin n) (hab : a ≠ b),
        neighbourCore e (ρ.injective.ne hab) =
          (neighbourCore e hab).map (MulAut.conj w).toMonoidHom := by
  refine ⟨((e.symm (unitaryProj h n (permSU h ρ.symm)) : L) : G),
    (e.symm (unitaryProj h n (permSU h ρ.symm))).2,
    fun I => ⟨pieceCore_eq_map_conj e (map_conj_unitaryBlockTorus h ρ I), ?_⟩,
    fun a b hab => neighbourCore_eq_map_conj e hab _ (map_conj_unitaryRootTorus h ρ hab)⟩
  rw [← modelToG_map_conj, map_conj_blockSU_of_mul_eq h _ (blockComplProj_mul_permSU h ρ I)]

theorem exists_conjugate_pieceCore (ρ : Equiv.Perm (Fin n)) :
    ∃ w ∈ L, ∀ I : Finset (Fin n),
      conjugate (pieceCore e I) w = pieceCore e (I.map ρ.toEmbedding) := by
  obtain ⟨w, hw, hI, -⟩ := exists_pieceCore_map_conj h e ρ
  refine ⟨w⁻¹, L.inv_mem hw, fun I => ?_⟩
  rw [conjugate, inv_inv, (hI I).1]

theorem exists_neighbourCore_eq_map_conj {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ w ∈ L, neighbourCore e hcd = (neighbourCore e hab).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨ρ, hρa, hρb⟩ := LinearPilot.exists_perm_apply_eq_apply_eq hab hcd
  obtain ⟨w, hw, -, hN⟩ := exists_pieceCore_map_conj h e ρ
  refine ⟨w, hw, ?_⟩
  have h1 := hN a b hab
  have e1 : neighbourCore e (ρ.injective.ne hab) = neighbourCore e hcd := by
    rw [neighbourCore_def, neighbourCore_def]
    congr 2
    subst hρa hρb
    rfl
  rw [← e1, h1]

end Transport

end CFSG.SeitzReduction.UnitaryPilot
