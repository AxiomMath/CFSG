module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CX
public import CFSG.Quasithin.Background.E2TwoCCases
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Vol2.Ch10SecQ3CJ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CL
public import CFSG.Quasithin.Vol2.Ch10SecQ3CM
public import CFSG.Quasithin.Vol2.Ch10SecQ3CN
public import CFSG.Quasithin.Vol2.Ch10SecQ4S9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_K_dataC (hE22 : E2.E22StatementC)
    (he23 : E2.E23Statement) (hAS : Ch11.SecH.AS_I_1_3_L2) (h1021 : Ch10.Stmt10_2_1)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hn3 : ¬ Ch10.Case10_1_1Three T L I) :
    ∃ (K : Subgroup G) (k : ℕ), 2 ≤ k ∧ K ∈ cComp H ∧ H = K ⊔ T ∧
      E2.E22CasesC H T (H ⊓ fsuM T L) K ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      ∃ (hel : IsElemAbelian 2 (VZ T H))
        (I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))),
        twoResidual H ≤ thompsonJ H ∧ E23Data H T (VZ T H) hel I' ∧ ∃ K₀ ∈ I', ∃ t ∈ T,
          (E2.IsL2Natural K₀ (fixV (autI hel (twoResidual H))) k ∨ (E2.IsA5Module K₀ ∧ k = 2)) ∧
          autI hel (K.map (MulAut.conj t).toMonoidHom) = oTwoUpper K₀ := by
  have hmin := SecB.minParabolic_of_isHStar h331 hyp hH
  have := hyp.fsu.simple
  have hKloc : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : SQTKGroup ↥H := InternalSec.sqtkGroup_of_localSQTK hKloc hH.1.2
  have hns : ¬ Group.IsSolvable ↥H := fun hsol =>
    absurd hn1 (not_lt.mpr (E1.solvable_nParam_le_one hsol))
  obtain ⟨⟨K, hKc, hHK, hKq, hcases⟩, -⟩ := hE22.exists_cases hmin hSQ hns
  obtain ⟨hel, hc⟩ := SecF.C10E4.e23Concl_H he23 h1021 h331 hyp hH hZH hn3
  obtain ⟨-, -, hO⟩ := SecF.C10P4F.vz_facts h331 hyp hH
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨h2J', I', hD⟩ := e23Data_of_concl hc
  have hcard := hD.card
  have hJ := hD.jeq
  have hcomm := hD.comm
  have htrans := hD.trans
  have htypes := hD.types
  have h2J : oTwoUpper H ≤ thompsonJ H := SecE.twoResidual_eq_oTwoUpper H ▸ h2J'
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ ∈ I' := Finset.card_pos.mp (by omega)
  have hKs : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ∈ cComp H := fun t ht =>
    H13.LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hTH ht))
  have hKW : ¬ K ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    hZH (commutator_eq_bot_of_le_centralizer hHK h)
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKJ : K ≤ thompsonJ H := by
    have h1 := oTwoUpper_mono hKH
    rw [← eq_oTwoUpper_of_perfect hKperf] at h1
    exact h1.trans h2J
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKperf]
  have hAperf : ⁅autI hel K, autI hel K⁆ = autI hel K := by
    rw [← range_convK hel (hKH.trans hHN), MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      hKtop]
  have hAne : autI hel K ≠ ⊥ := fun h => hKW ((autI_eq_bot_iff hel (hKH.trans hHN)).mp h)
  have hty : ∃ k : ℕ, (E2.IsL2Natural K₀ (fixV (autI hel (twoResidual H))) k ∧ 2 ≤ k) ∨
      (E2.IsA5Module K₀ ∧ k = 2) := by
    rcases htypes K₀ hK₀ with ⟨j, hj⟩ | h5
    · rcases Nat.lt_or_ge j 2 with hj1 | hj2
      · exfalso
        have hj1' : j = 1 := by have := hj.1; omega
        subst hj1'
        have hsol : ∀ L' ∈ I', Group.IsSolvable ↥L' := by
          intro L' hL'
          obtain ⟨t, -, ht⟩ := htrans K₀ hK₀ L' hL'
          rw [← ht]
          exact isSolvable_conjAut (isSolvable_of_isL2Natural_one hj) t
        have hS := isSolvable_iSup hcard hsol hcomm
        rw [← hJ] at hS
        exact hAne (eq_bot_of_perfect_of_le hS (autI_mono hel hKJ) hAperf)
      · exact ⟨j, Or.inl ⟨hj, hj2⟩⟩
    · exact ⟨2, Or.inr ⟨h5, rfl⟩⟩
  obtain ⟨k, hj⟩ := hty
  have hk2 : 2 ≤ k := hj.elim (fun h => h.2) fun h => h.2 ▸ le_rfl
  obtain ⟨hCs, hnc, F, _, _, hF, ⟨eC⟩⟩ := exists_sl2_of_component hj
  obtain ⟨t, ht, hle⟩ := exists_le_autI_map' hel hHN hyp.fsu.sylow.1 hKc hHK h2J hJ hcomm hK₀
    hCs hnc
  set C := oTwoUpper K₀ with hCdef
  have htN : t ∈ Subgroup.normalizer (VZ T H : Set G) := hHN (hTH ht)
  set φ := convI hel ⟨t, htN⟩ with hφ
  have hconj := autI_map_conj (K := K) hel htN
  rw [← hφ] at hconj
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (C : Set _) := by
    rw [hJ]
    refine iSup₂_le fun L' hL' => ?_
    refine le_trans ?_ (SecF.C10P4F.le_normalizer_oTwoUpper K₀)
    by_cases h : L' = K₀
    · rw [h]; exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun a ha b hb => hcomm L' hL' K₀ hK₀ h a ha b hb
  have hKtJ : K.map (MulAut.conj t).toMonoidHom ≤ thompsonJ H := by
    have h1 := oTwoUpper_mono (le_of_mem_cComp (hKs t ht))
    rw [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (hKs t ht))] at h1
    exact h1.trans h2J
  have hAtN := (autI_mono hel hKtJ).trans hJN
  set C' := C.map (MulAut.conj φ⁻¹).toMonoidHom with hC'
  have hmemC' : ∀ x, x ∈ C' ↔ φ * x * φ⁻¹ ∈ C := by
    intro x
    rw [hC', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hC'le : C' ≤ autI hel K := by
    intro x hx
    have h1 := hle ((hmemC' x).mp hx)
    rw [hconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
    simpa [mul_assoc] using h1
  have hC'N : autI hel K ≤ Subgroup.normalizer (C' : Set _) := by
    intro z hz
    have hz' : φ * z * φ⁻¹ ∈ autI hel (K.map (MulAut.conj t).toMonoidHom) := by
      rw [hconj]
      exact ⟨z, hz, rfl⟩
    have hN := hAtN hz'
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [hmemC', hmemC']
    have e1 : φ * (z * x * z⁻¹) * φ⁻¹ =
        (φ * z * φ⁻¹) * (φ * x * φ⁻¹) * (φ * z * φ⁻¹)⁻¹ := by group
    rw [e1]
    exact Subgroup.mem_normalizer_iff.mp hN _
  have hnc' : ∃ a ∈ C', ∃ b ∈ C', a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    refine ⟨φ⁻¹ * a * φ, (hmemC' _).mpr (by simpa [mul_assoc] using ha), φ⁻¹ * b * φ,
      (hmemC' _).mpr (by simpa [mul_assoc] using hb), fun h => hab ?_⟩
    have := congrArg (fun x => φ * x * φ⁻¹) h
    simpa [mul_assoc] using this
  have hOK : pCoreOf 2 K ≤ Subgroup.centralizer (VZ T H : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)).trans hO
  have heq := eq_autI_of_normal hel (hKH.trans hHN) hKq hOK hC'le hC'N hnc'
  let eA : ↥(autI hel K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulEquiv.subgroupCongr heq.symm).trans
      ((Subgroup.equivMapOfInjective C (MulAut.conj φ⁻¹).toMonoidHom
        (MulAut.conj φ⁻¹).injective).symm.trans eC)
  have hquot := nonempty_quot_equiv_of_autI hAS hel (hKH.trans hHN) hKq hOK hk2 hF eA
  refine ⟨K, k, hk2, hKc, hHK, hcases, ⟨F, inferInstance, inferInstance, hF, hquot⟩, hel, I',
    h2J', hD, K₀, hK₀, t, ht, hj.imp (fun h => h.1) id, ?_⟩
  rw [hconj, ← heq]
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hmemC']
  simp [mul_assoc, hCdef]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
