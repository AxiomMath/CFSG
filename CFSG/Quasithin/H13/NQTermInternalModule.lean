module

public import CFSG.Quasithin.H13.NQSetupDefs
public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedGeneral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quasithinOmegaOneCenter_le_centerTorsion (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ centerTorsion 2 T := by
  rw [quasithinOmegaOneCenter, Subgroup.closure_le]
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  rw [SetLike.mem_coe, mem_centerTorsion_iff]
  exact ⟨hzT, fun k hk => Subgroup.mem_centralizer_iff.mp hzC k hk, hz2⟩

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine SetLike.coe_injective ?_
  rw [Subgroup.coe_map]
  exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hg

theorem nonquasisimple_normalizer_internal_module_properties {T L M : Subgroup G}
    (h : QTNQ T L M) :
    CFSG.IsCharacteristicP 2 M ∧
    (primeReducedAggregate M 2).Characteristic ∧ IsPrimeReduced 2 (primeReducedAggregate M 2) ∧
    quasithinOmegaOneCenter T ≤ qtnqVc M ∧
    (qtnqU L M ≠ ⊥ ∧ qtnqU L M ≤ M ∧ ((qtnqU L M).subgroupOf M).Normal ∧
      CFSG.IsElementaryAbelian 2 (qtnqU L M)) ∧
    Subgroup.normalizer (M : Set G) = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := h.l_le
  have hTM : T ≤ M := h.t_le
  have hT : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hM2 : IsTwoLocal M := h.max_two_local.1
  have hchar : QuasithinUnique.CharTwo M :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT hM2 hTM
  have hcharP : CFSG.IsCharacteristicP 2 M :=
    QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hchar
  obtain ⟨-, -, hred, hcharV, -, -, -, -, hVel, -⟩ :=
    qt_prime_reduced_aggregate_characteristic_maximal (↥M) 2
  have hMVc : M ≤ Subgroup.normalizer (qtnqVc M : Set G) :=
    Subgroup.le_normalizer.trans
      (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hML : M ≤ Subgroup.normalizer (L : Set G) := h.eq_normalizer.le
  have hVcM : qtnqVc M ≤ M := Subgroup.map_subtype_le _
  have hZ : quasithinOmegaOneCenter T ≤ qtnqVc M := by
    have hTs : IsPGroup 2 (T.subgroupOf M) :=
      h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
    have hTi : ¬ 2 ∣ (T.subgroupOf M).index := fun hd => h.sylow.2
      (hd.trans (Subgroup.relIndex_dvd_index_of_le hTM))
    set T' : Sylow 2 M := hTs.toSylow hTi
    have hT' : (T' : Subgroup M) = T.subgroupOf M := IsPGroup.toSylow_coe hTs hTi
    have hZT : (quasithinOmegaOneCenter T).subgroupOf M ≤ centerTorsion 2 (T' : Subgroup M) := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      obtain ⟨hzT, hzc, hz2⟩ :=
        mem_centerTorsion_iff.mp (quasithinOmegaOneCenter_le_centerTorsion T hz)
      rw [mem_centerTorsion_iff, hT']
      refine ⟨hzT, fun k hk => Subtype.ext (hzc k hk), Subtype.ext hz2⟩
    obtain ⟨-, -, hZW, hWR⟩ :=
      QuasithinUnique.Setup.qt_characteristic_p_Sylow_center_reduced_closure 2 hcharP T' hZT
    intro z hz
    have hzM : z ∈ M :=
      hTM (mem_centerTorsion_iff.mp (quasithinOmegaOneCenter_le_centerTorsion T hz)).1
    exact ⟨⟨z, hzM⟩, hWR (hZW hz), rfl⟩
  have hUVc : qtnqU L M ≤ qtnqVc M := by
    rw [qtnqU, Subgroup.commutator_le]
    intro v hv l hl
    have hl' : l ∈ Subgroup.normalizer (qtnqVc M : Set G) := hMVc (hLM hl)
    have h1 : l * v⁻¹ * l⁻¹ ∈ qtnqVc M :=
      (Subgroup.mem_normalizer_iff.mp hl' v⁻¹).mp ((qtnqVc M).inv_mem hv)
    rw [commutatorElement_def]
    have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [e]
    exact (qtnqVc M).mul_mem hv h1
  have hUM : qtnqU L M ≤ M := hUVc.trans hVcM
  have hUn : ((qtnqU L M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUM]
    intro m hm
    refine mem_normalizer_of_map_conj_eq ?_
    rw [qtnqU, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer' (hMVc hm),
      map_conj_eq_of_mem_normalizer' (hML hm)]
  have hVcel : CFSG.IsElementaryAbelian 2 (qtnqVc M) := isElementaryAbelian_map hVel _
  have hUel : CFSG.IsElementaryAbelian 2 (qtnqU L M) := isElementaryAbelian_of_le hUVc hVcel
  have hU1 : qtnqU L M ≠ ⊥ := by
    intro hU
    have hLC : L ≤ Subgroup.centralizer (qtnqVc M : Set G) := by
      rw [qtnqU, Subgroup.commutator_eq_bot_iff_le_centralizer] at hU
      exact Subgroup.le_centralizer_iff.mp hU
    have hLR : L = (CFSG.solvableRadical ↥L).map L.subtype := by
      rw [← h.centralizer_eq_radical]
      exact (inf_eq_left.mpr hLC).symm
    have hRtop : CFSG.solvableRadical ↥L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [← hLR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    obtain ⟨-, hsolv, -, -⟩ :=
      QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥L
    rw [hRtop] at hsolv
    have hLsolv : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup ↥L).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    obtain ⟨hL1, hLL, -⟩ := h.faithful_local.1.2.1
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLL
    have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
    exact Group.IsPerfect.not_isSolvable (↥L) hLsolv
  refine ⟨hcharP, hcharV, hred, hZ, ⟨hU1, hUM, hUn, hUel⟩, ?_⟩
  obtain ⟨P, hP1, hP2, hMP⟩ := hM2
  have hPO : P ≤ pCoreOf 2 M := by
    rw [hMP]
    exact LieType.BorelTits.le_pCoreOf_normalizer 2 P hP2
  have hO1 : pCoreOf 2 M ≠ ⊥ := fun h0 => hP1 (le_bot_iff.mp (h0 ▸ hPO))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hO1, LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have hNO : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    h.max_two_local.2 _ hloc (LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  refine le_antisymm ?_ Subgroup.le_normalizer
  calc Subgroup.normalizer (M : Set G)
      ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
        LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M
    _ = M := hNO

end CFSG.Quasithin.H13.NQTerm
