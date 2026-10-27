module

public import CFSG.Monster.Existence.TwoPoint.CoPairKEquiv
public import CFSG.Monster.Existence.TwoPoint.CoPairDefs
public import CFSG.Monster.Existence.TwoPoint.CoPairCertW1
public import CFSG.Monster.Existence.TwoPoint.CoPairKOrbit
public import CFSG.Monster.Existence.TwoPoint.CoPairCertMcL
public import CFSG.Sporadic.McL.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.CoPair
  CFSG.Monster.Existence.CoPair.Native

theorem natCard_coPair_mcl :
    Nat.card ↥(Kstab v0 ⊓ Kstab coW1) = 898128000 := by
  obtain ⟨D, hD⟩ := orbW1K_eq_true
  have h := natCard_inf_of_orbit (ncard_orbit_of_orbOK hD)
  rw [show dec seedW1 = coW1 from coW1_eq_dec.symm] at h
  omega

theorem toMat_eq_of_basisOK {d : ℕ} {S S' Tinv : Array CFSG.F3.Native.V}
    (h : CFSG.Sporadic.VecOrbit.Native.basisOK d S Tinv = true)
    (h' : CFSG.Sporadic.VecOrbit.Native.basisOK d S' Tinv = true) :
    CFSG.F3.Native.toMat d S = CFSG.F3.Native.toMat d S' := by
  unfold CFSG.Sporadic.VecOrbit.Native.basisOK at h h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h h'
  obtain ⟨⟨⟨⟨-, hSwf⟩, hTwf⟩, hTs⟩, hTS⟩ := h
  obtain ⟨⟨⟨⟨-, hSwf'⟩, -⟩, -⟩, hTS'⟩ := h'
  have e1 := CFSG.F3.Native.toMat_eq_of_eqM hTS
  have e2 := CFSG.F3.Native.toMat_eq_of_eqM hTS'
  rw [CFSG.F3.Native.toMat_mul hTs (CFSG.F3.Native.rowsWF_of_wfM hTwf)
    (CFSG.F3.Native.rowsWF_of_wfM hSwf), CFSG.F3.Native.toMat_idM] at e1
  rw [CFSG.F3.Native.toMat_mul hTs (CFSG.F3.Native.rowsWF_of_wfM hTwf)
    (CFSG.F3.Native.rowsWF_of_wfM hSwf'), CFSG.F3.Native.toMat_idM] at e2
  have e3 := mul_eq_one_comm.1 e1
  calc CFSG.F3.Native.toMat d S
      = CFSG.F3.Native.toMat d S * (CFSG.F3.Native.toMat d Tinv * CFSG.F3.Native.toMat d S') := by
        rw [e2, Matrix.mul_one]
    _ = (CFSG.F3.Native.toMat d S * CFSG.F3.Native.toMat d Tinv) * CFSG.F3.Native.toMat d S' := by
        rw [Matrix.mul_assoc]
    _ = CFSG.F3.Native.toMat d S' := by rw [e3, Matrix.one_mul]

theorem labels_mcl {VL SA SB : ℕ}
    (h : CFSG.KC.CoPair.mclVecOK VL SA SB) :
    ∃ E : ℕ → Fin 275,
      (∀ l < 275, E (CFSG.KC.CoPair.f16 SA l) = MulAction.toPerm CFSG.Sporadic.McL.a (E l)) ∧
      (∀ l < 275, E (CFSG.KC.CoPair.f16 SB l) = MulAction.toPerm CFSG.Sporadic.McL.b (E l)) ∧
      ∀ k : Fin 275, ∃ l < 275, E l = k := by
  classical
  obtain ⟨hv, hbasis⟩ := h
  let mv : ℕ → (Fin 21 → ZMod 3) :=
    fun j => CFSG.F3.Native.vecOf 21 (CFSG.KC.CoPair.decVM (CFSG.KC.CoPair.f64 VL j))
  have hmA : ∀ j < 275, CFSG.Sporadic.McL.a • mv j = mv (CFSG.KC.CoPair.f16 SA j) := fun j hj => by
    obtain ⟨hwf, -, -, hA, -⟩ := hv j hj
    rw [CFSG.Sporadic.McL.smul_vec, CFSG.Sporadic.McL.mat_a,
      ← CFSG.Sporadic.VecOrbit.vecOf_comb_transpose _ hwf]
    exact CFSG.Sporadic.VecOrbit.vecOf_eq_of_beq hA
  have hmB : ∀ j < 275, CFSG.Sporadic.McL.b • mv j = mv (CFSG.KC.CoPair.f16 SB j) := fun j hj => by
    obtain ⟨hwf, -, -, -, hB⟩ := hv j hj
    rw [CFSG.Sporadic.McL.smul_vec, CFSG.Sporadic.McL.mat_b,
      ← CFSG.Sporadic.VecOrbit.vecOf_comb_transpose _ hwf]
    exact CFSG.Sporadic.VecOrbit.vecOf_eq_of_beq hB
  let U : Set (Fin 21 → ZMod 3) := mv '' Set.Iio 275
  have hU : U.Finite := (Set.finite_Iio 275).image mv
  have hinv : ∀ g : CFSG.Sporadic.McL.J, ∀ y ∈ U, g • y ∈ U := by
    have hle : Subgroup.closure ({CFSG.Sporadic.McL.a, CFSG.Sporadic.McL.b} :
        Set CFSG.Sporadic.McL.J) ≤ VisCert.invSubgroup U hU := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl) <;> rintro _ ⟨j, hj, rfl⟩
      · exact ⟨_, (hv j hj).2.1, (hmA j hj).symm⟩
      · exact ⟨_, (hv j hj).2.2.1, (hmB j hj).symm⟩
    intro g
    exact hle (by rw [CFSG.Sporadic.McL.closure_ab]; trivial)
  obtain ⟨-, -, -, -, -, -, -, hb3170, -⟩ := CFSG.Sporadic.McL.actionChecks_parts
  have hT := toMat_eq_of_basisOK hb3170 hbasis
  have hq0 : CFSG.Sporadic.McL.vecPt 0 = mv 0 := by
    funext j
    have := congrFun (congrFun hT ⟨0, by norm_num⟩) j
    rw [CFSG.F3.Native.toMat_apply, CFSG.F3.Native.toMat_apply] at this
    simpa [CFSG.Sporadic.McL.vecPt, mv, CFSG.F3.Native.vecOf, CFSG.Sporadic.McL.Native.chainQ]
      using this
  have hsize : CFSG.Sporadic.McL.orb.pts.size = 275 := CFSG.Sporadic.McL.orb_size
  have hO : MulAction.orbit CFSG.Sporadic.McL.J (CFSG.Sporadic.McL.vecPt 0) = U := by
    have hsub : MulAction.orbit CFSG.Sporadic.McL.J (CFSG.Sporadic.McL.vecPt 0) ⊆ U := by
      rintro _ ⟨g, rfl⟩
      exact hinv g _ ⟨0, by norm_num, hq0.symm⟩
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hU
    rw [CFSG.Sporadic.McL.orbit_eq, hsize]
    calc U.ncard ≤ (Set.Iio 275).ncard := Set.ncard_image_le (Set.finite_Iio _)
      _ = (CFSG.Sporadic.McL.vecPt '' Set.Iio 275).ncard := by
        refine (Set.InjOn.ncard_image fun i hi j hj hij => ?_).symm
        exact CFSG.Sporadic.McL.vecPt_inj (by rw [hsize]; exact hi) (by rw [hsize]; exact hj) hij
  have hmem : ∀ j < 275, mv j ∈ MulAction.orbit CFSG.Sporadic.McL.J (CFSG.Sporadic.McL.vecPt 0) :=
    fun j hj => by
      rw [hO]
      exact ⟨j, hj, rfl⟩
  let E : ℕ → Fin 275 := fun j =>
    if hj : j < 275 then CFSG.Sporadic.McL.ptEquiv.symm ⟨mv j, hmem j hj⟩ else 0
  have hE : ∀ j (hj : j < 275), (CFSG.Sporadic.McL.ptEquiv (E j) : Fin 21 → ZMod 3) = mv j :=
    fun j hj => by simp only [E, dite_eq_left hj, Equiv.apply_symm_apply]
  refine ⟨E, fun l hl => ?_, fun l hl => ?_, fun k => ?_⟩
  · apply CFSG.Sporadic.McL.ptEquiv.injective
    apply Subtype.ext
    rw [MulAction.toPerm_apply, CFSG.Sporadic.McL.ptEquiv_smul, MulAction.orbit.coe_smul,
      hE _ (hv l hl).2.1, hE l hl, hmA l hl]
  · apply CFSG.Sporadic.McL.ptEquiv.injective
    apply Subtype.ext
    rw [MulAction.toPerm_apply, CFSG.Sporadic.McL.ptEquiv_smul, MulAction.orbit.coe_smul,
      hE _ (hv l hl).2.2.1, hE l hl, hmB l hl]
  · have hk : (CFSG.Sporadic.McL.ptEquiv k : Fin 21 → ZMod 3) ∈ U := hO ▸ (CFSG.Sporadic.McL.ptEquiv k).2
    obtain ⟨j, hj, hjk⟩ := hk
    exact ⟨j, hj, CFSG.Sporadic.McL.ptEquiv.injective (Subtype.ext (by rw [hE j hj]; exact hjk))⟩

theorem coPair_mcl :
    Nonempty (↥(Kstab v0 ⊓ Kstab coW1) ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  obtain ⟨D, VL, hok, hvec⟩ := mclK_eq_true
  have hlab := labels_mcl hvec
  have hH : Subgroup.closure ({MulAction.toPerm CFSG.Sporadic.McL.a,
      MulAction.toPerm CFSG.Sporadic.McL.b} : Set (Equiv.Perm (Fin 275))) =
        (MulAction.toPermHom CFSG.Sporadic.McL.J (Fin 275)).range := by
    rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.McL.closure_ab, MonoidHom.map_closure,
      Set.image_pair]
    rfl
  have hinj : Function.Injective (MulAction.toPermHom CFSG.Sporadic.McL.J (Fin 275)) :=
    MulAction.toPerm_injective
  have hcardJ : Nat.card (MulAction.toPermHom CFSG.Sporadic.McL.J (Fin 275)).range =
      898128000 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, CFSG.Sporadic.McL.card_J]
  have hcard : Nat.card (kvStab (dec 1)) =
      Nat.card (MulAction.toPermHom CFSG.Sporadic.McL.J (Fin 275)).range := by
    rw [hcardJ, Nat.card_congr (kvStabEquivInf (dec 1)).toEquiv, ← coW1_eq_dec]
    exact natCard_coPair_mcl
  obtain ⟨E, hea, heb, hes⟩ := hlab
  obtain ⟨e⟩ := kvStab_equiv_of_eqOK (w := 1) hok (by norm_num) E
    (MulAction.toPerm CFSG.Sporadic.McL.a) (MulAction.toPerm CFSG.Sporadic.McL.b)
    hea heb hes hH hcard
  rw [coW1_eq_dec]
  exact ⟨(kvStabEquivInf (dec 1)).symm.trans
    (e.trans ((MonoidHom.ofInjective hinj).symm.trans CFSG.Sporadic.McL.mclEquivJ.symm))⟩

end CFSG.Monster.Existence
