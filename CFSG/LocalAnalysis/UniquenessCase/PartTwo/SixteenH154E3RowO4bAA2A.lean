module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAD
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Ovoid
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaMinusFourTrans
public import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Subgroup
open CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow
open scoped Matrix Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem s16h_e3_natCard_statedOmega (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) = 262080 := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two, hK]
  norm_num

theorem s16h_e3_natCard_isometryCore (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) = 524160 := by
  have hQ : ⇑(quadMinus 2 K b c) = StatedQuadMinus 2 K b c := coe_quadMinus (n := 2) (K := K) b c
  have hcardO : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) := by
    rw [CFSG.MatrixModel.isometryCore, closure_isometries_eq_comap hQ]
    conv_rhs => rw [← Subgroup.map_comap_eq_self_of_surjective
      (f := (toLinEquiv s16h_H5E3RkιA K).toMonoidHom)
      (toLinEquiv s16h_H5E3RkιA K).surjective
      (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c))]
    exact (Subgroup.card_map_of_injective (toLinEquiv s16h_H5E3RkιA K).injective).symm
  have hstated : Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ =
      Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
    rw [CFSG.SeitzReduction.F4Pilot.statedOmega_quadMinus_eq_map 2 b c]
    exact (Subgroup.card_map_of_injective (MulEquiv.injective _)).symm
  have hcard2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) =
      2 * Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) := by
    rw [card_orth_two_minus hirr, hstated]
  rw [hcardO, hcard2, s16h_e3_natCard_statedOmega hK hirr]

private theorem s16h_e3_ncard_sdiff {α : Type*} {s t : Set α} (h : s ⊆ t) (ht : t.Finite) :
    (t \ s).ncard = t.ncard - s.ncard := by
  classical
  have hs : s.Finite := ht.subset h
  have hts : (t \ s).Finite := ht.sdiff
  haveI : Fintype ↥t := ht.fintype
  haveI : Fintype ↥s := hs.fintype
  haveI : Fintype ↥(t \ s) := hts.fintype
  have e_s : ↥s ≃ {x : ↥t // (x : α) ∈ s} :=
    (Equiv.subtypeSubtypeEquivSubtype (p := fun x => x ∈ t) (q := fun x => x ∈ s)
      (fun {x} hx => h hx)).symm
  have e_c : ↥(t \ s) ≃ {x : ↥t // (x : α) ∉ s} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ t) (fun x => x ∉ s)).symm
  have hcard : Nat.card ↥s + Nat.card ↥(t \ s) = Nat.card ↥t :=
    (Nat.card_sum).symm.trans (Nat.card_congr
      ((Equiv.sumCongr e_s e_c).trans (Equiv.Set.sumCompl {x : ↥t | (x : α) ∈ s})))
  rw [← Nat.card_coe_set_eq (t \ s), ← Nat.card_coe_set_eq t, ← Nat.card_coe_set_eq s]
  omega

private theorem s16h_e3_quadMinus_smul (a : K) (v : s16h_H5E3RkιA → K) :
    StatedQuadMinus 2 K b c (a • v) = a ^ 2 * StatedQuadMinus 2 K b c v := by
  rw [← coe_quadMinus (n := 2) (K := K) b c]
  rw [QuadraticMap.map_smul]
  simp [smul_eq_mul, pow_two]

private theorem s16h_e3_quadMinus_zero : StatedQuadMinus 2 K b c (0 : s16h_H5E3RkιA → K) = 0 := by
  rw [← coe_quadMinus (n := 2) (K := K) b c]
  exact QuadraticMap.map_zero (quadMinus 2 K b c)

private theorem s16h_e3_natCard_finrank_one (hK : Nat.card K = 2 ^ 3) :
    {P : Submodule K (s16h_H5E3RkιA → K) | Module.finrank K P = 1}.ncard = 585 := by
  have hfin : Module.finrank K (s16h_H5E3RkιA → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [s16h_H5E3RkιA]
  rw [← Nat.card_coe_set_eq]
  change Nat.card {P : Submodule K (s16h_H5E3RkιA → K) // Module.finrank K P = 1} = 585
  rw [← Nat.card_congr (Projectivization.equivSubmodule K (s16h_H5E3RkιA → K))]
  rw [Projectivization.card_of_finrank (k := K) (V := s16h_H5E3RkιA → K) hfin, hK]
  norm_num [Finset.sum_range_succ]

private theorem s16h_e3_singPts_ncard (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (sec7SingPts (StatedQuadMinus 2 K b c)).ncard = Nat.card K ^ 2 + 1 := by
  have h := congrArg sec7SingPts (coe_quadMinus (n := 2) (K := K) (b := b) (c := c))
  rw [← h]
  exact sec7_singPts_ncard hirr

private theorem s16h_e3_nonSingPts_ncard (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {P : Submodule K (s16h_H5E3RkιA → K) | Module.finrank K P = 1 ∧
      P ∉ sec7SingPts (StatedQuadMinus 2 K b c)}.ncard = 520 := by
  have hsub : sec7SingPts (StatedQuadMinus 2 K b c) ⊆
      {P : Submodule K (s16h_H5E3RkιA → K) | Module.finrank K P = 1} :=
    fun P hP => hP.1
  change ({P : Submodule K (s16h_H5E3RkιA → K) | Module.finrank K P = 1} \
    sec7SingPts (StatedQuadMinus 2 K b c)).ncard = 520
  rw [s16h_e3_ncard_sdiff hsub (Set.toFinite _), s16h_e3_natCard_finrank_one hK,
    s16h_e3_singPts_ncard hirr, hK]
  norm_num

private theorem s16h_e3_shell_ncard (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {μ : K} (hμ : μ ≠ 0) :
    {x : s16h_H5E3RkιA → K | StatedQuadMinus 2 K b c x = μ}.ncard = 520 := by
  have hQ0 := s16h_e3_quadMinus_zero (K := K) (b := b) (c := c)
  refine (Set.ncard_congr (t := {P : Submodule K (s16h_H5E3RkιA → K) |
      Module.finrank K P = 1 ∧ P ∉ sec7SingPts (StatedQuadMinus 2 K b c)})
    (fun x _ => Submodule.span K {x}) ?_ ?_ ?_).trans (s16h_e3_nonSingPts_ncard hK hirr)
  · intro x hx
    have hxQ : StatedQuadMinus 2 K b c x = μ := hx
    have hx0 : x ≠ 0 := fun h => hμ (by rw [h, hQ0] at hxQ; exact hxQ.symm)
    refine ⟨finrank_span_singleton hx0, ?_⟩
    intro hmem
    exact hμ (by rw [← hxQ]; exact hmem.2 x (Submodule.mem_span_singleton_self x))
  · intro x y hx hy hspan
    have hxQ : StatedQuadMinus 2 K b c x = μ := hx
    have hyQ : StatedQuadMinus 2 K b c y = μ := hy
    have hymem : y ∈ Submodule.span K {x} := by
      rw [hspan]
      exact Submodule.mem_span_singleton_self y
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hymem
    have hdy : StatedQuadMinus 2 K b c y = d ^ 2 * μ := by
      rw [← hd, s16h_e3_quadMinus_smul, hxQ]
    have hd2 : d ^ 2 = 1 := by
      rw [hdy] at hyQ
      exact mul_right_cancel₀ hμ (hyQ.trans (one_mul μ).symm)
    have hd1 : d = 1 := by
      have h : (d + 1) * (d + 1) = 0 := by
        rw [show (d + 1) * (d + 1) = d * d + (d + d) + 1 by ring,
          CharTwo.add_self_eq_zero d, add_zero, ← pow_two, hd2, CharTwo.add_self_eq_zero]
      have h2 : d + 1 = 0 := mul_self_eq_zero.mp h
      have h3 : d = -1 := eq_neg_iff_add_eq_zero.mpr h2
      rwa [CharTwo.neg_eq] at h3
    rw [← hd, hd1, one_smul]
  · intro P hP
    obtain ⟨hPfin, hPns⟩ := hP
    have hex : ∃ v ∈ P, StatedQuadMinus 2 K b c v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hPns ⟨hPfin, hcon⟩
    obtain ⟨v, hvP, hvQ⟩ := hex
    have hv0 : v ≠ 0 := by
      intro h
      exact hvQ (by rw [h, hQ0])
    have hPspan : P = Submodule.span K {v} := by
      refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem v P).mpr hvP)
      obtain ⟨d, hd⟩ := sec7_smul_of_mem_finrank_one hPfin hv0 hvP hw
      rw [← hd]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    obtain ⟨d, hd⟩ := isSquare_of_charTwo' (μ / StatedQuadMinus 2 K b c v)
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact (div_ne_zero hμ hvQ) (hd.trans (by ring))
    refine ⟨d • v, ?_, ?_⟩
    · show StatedQuadMinus 2 K b c (d • v) = μ
      rw [s16h_e3_quadMinus_smul, pow_two, ← hd, div_mul_cancel₀ _ hvQ]
    · rw [hPspan]
      apply le_antisymm
      · exact (Submodule.span_singleton_le_iff_mem (d • v) (Submodule.span K {v})).mpr
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · exact (Submodule.span_singleton_le_iff_mem v (Submodule.span K {d • v})).mpr
          (Submodule.mem_span_singleton.mpr
            ⟨d⁻¹, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩)

private theorem s16h_e3_orbit_mul_stab_card (G : Type) {V : Type} [Group G] [MulAction G V]
    (v : V) :
    Nat.card (MulAction.orbit G v) * Nat.card ↥(MulAction.stabilizer G v) = Nat.card G := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G v)
  rw [Nat.card_prod] at h
  exact h

private theorem s16h_e3_stab_subgroupOf_card {G V : Type} [Group G] [MulAction G V]
    (H : Subgroup G) (v : V) :
    Nat.card ↥(MulAction.stabilizer H v) = Nat.card ↥(H ⊓ MulAction.stabilizer G v) := by
  rw [← MulAction.stabilizer_subgroupOf H v, inf_comm,
    ← Subgroup.subgroupOf_map_subtype (MulAction.stabilizer G v) H]
  exact (Subgroup.card_subtype H ((MulAction.stabilizer G v).subgroupOf H)).symm

private theorem s16h_e3_mem_orbit_natImage_iff {Γ : Subgroup (GL s16h_H5E3RkιA K)}
    {v w : StdMod s16h_H5E3RkιA K} :
    w ∈ MulAction.orbit (↥(natImage Γ)) v ↔
      ∃ A ∈ Γ, (A : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ Multiplicative.toAdd v =
        Multiplicative.toAdd w := by
  constructor
  · intro hw
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hw
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp h.2
    refine ⟨γ.1, γ.2, ?_⟩
    have h1 : h.1 = matAut γ.1 := by
      rw [← hγ]
      exact matHom_apply γ.1
    have h2 : w = h.1 v := hh.symm
    rw [h2, h1]
    rfl
  · rintro ⟨A, hA, hAx⟩
    refine MulAction.mem_orbit_iff.mpr ⟨⟨matAut A, ⟨⟨A, hA⟩, rfl⟩⟩, ?_⟩
    change Multiplicative.ofAdd ((A : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ
      Multiplicative.toAdd v) = w
    rw [hAx, ofAdd_toAdd]

private theorem s16h_e3_exists_isometry_mulVec_eq (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x y : s16h_H5E3RkιA → K}
    (hx : StatedQuadMinus 2 K b c x ≠ 0) (hy : StatedQuadMinus 2 K b c y ≠ 0)
    (hxy : StatedQuadMinus 2 K b c x = StatedQuadMinus 2 K b c y) :
    ∃ A ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c),
      (A : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ x = y := by
  have hQ : ⇑(quadMinus 2 K b c) = StatedQuadMinus 2 K b c := coe_quadMinus (n := 2) (K := K) b c
  have hx0 : x ≠ 0 := fun h => hx (by rw [← hQ, h]; exact QuadraticMap.map_zero _)
  have hy0 : y ≠ 0 := fun h => hy (by rw [← hQ, h]; exact QuadraticMap.map_zero _)
  have hli : LinearIndependent K ![x] := (linearIndependent_unique_iff).mpr (by simpa using hx0)
  have hli' : LinearIndependent K ![y] := (linearIndependent_unique_iff).mpr (by simpa using hy0)
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_apply_eq
    (nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
    ![x] ![y] hli hli' (fun i => by simpa [hQ] using hxy.symm)
    (fun i j => by
      simp only [Matrix.cons_val_fin_one]
      rw [QuadraticMap.polar_self, QuadraticMap.polar_self, CharTwo.two_nsmul,
        CharTwo.two_nsmul])
  refine ⟨(toLinEquiv s16h_H5E3RkιA K).symm g, ?_, ?_⟩
  · rw [CFSG.MatrixModel.isometryCore, closure_isometries_eq_comap hQ, Subgroup.mem_comap]
    simpa using hgO
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    exact hg ⟨0, by norm_num⟩

private theorem s16h_e3_orbit_isometryCore_eq_shell (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    MulAction.orbit
        (↥(natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)))) v =
      {w : StdMod s16h_H5E3RkιA K | StatedQuadMinus 2 K b c (Multiplicative.toAdd w) =
        StatedQuadMinus 2 K b c (Multiplicative.toAdd v)} := by
  ext w
  constructor
  · intro hw
    obtain ⟨A, hA, hAx⟩ :=
      (s16h_e3_mem_orbit_natImage_iff
        (Γ := CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))).mp hw
    have hiso := apply_mulVec_of_mem_isometryCore (Q₀ := StatedQuadMinus 2 K b c) hA
      (Multiplicative.toAdd v)
    rw [hAx] at hiso
    exact hiso
  · intro hw
    have hwQ : StatedQuadMinus 2 K b c (Multiplicative.toAdd w) ≠ 0 := by rw [hw]; exact hv
    obtain ⟨A, hA, hAx⟩ := s16h_e3_exists_isometry_mulVec_eq hirr hv hwQ hw.symm
    exact (s16h_e3_mem_orbit_natImage_iff
      (Γ := CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))).mpr ⟨A, hA, hAx⟩

private theorem s16h_e3_orbit_isometryCore_ncard (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    Nat.card (MulAction.orbit
      (↥(natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)))) v) = 520 := by
  rw [s16h_e3_orbit_isometryCore_eq_shell hirr hv]
  exact s16h_e3_shell_ncard hK hirr hv

private theorem s16h_e3_stab_isometryCore_card (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    Nat.card ↥(natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) ⊓
      MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v) = 1008 := by
  let O := natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))
  let S := MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v
  have hOcard : Nat.card ↥O = 524160 := by
    dsimp [O]
    rw [natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
    exact s16h_e3_natCard_isometryCore hK hirr
  have hOS := s16h_e3_orbit_mul_stab_card O v
  rw [s16h_e3_orbit_isometryCore_ncard hK hirr hv, hOcard] at hOS
  change Nat.card ↥(O ⊓ S) = 1008
  rw [← s16h_e3_stab_subgroupOf_card O v]
  omega

private theorem s16h_e3_orbit_statedOmega_eq_singular (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {v : StdMod s16h_H5E3RkιA K} (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0)
    (hv0 : Multiplicative.toAdd v ≠ 0) :
    MulAction.orbit (↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)))) v =
      {w : StdMod s16h_H5E3RkιA K | StatedQuadMinus 2 K b c (Multiplicative.toAdd w) = 0 ∧
        Multiplicative.toAdd w ≠ 0} := by
  have hQ : ⇑(quadMinus 2 K b c) = StatedQuadMinus 2 K b c :=
    coe_quadMinus (n := 2) (K := K) b c
  ext w
  constructor
  · intro hw
    obtain ⟨A, hA, hAx⟩ :=
      (s16h_e3_mem_orbit_natImage_iff
        (Γ := StatedOmega (StatedQuadMinus 2 K b c))).mp hw
    have hiso := apply_mulVec_of_mem_isometryCore (Q₀ := StatedQuadMinus 2 K b c)
      (statedOmega_le_isometryCore _ hA) (Multiplicative.toAdd v)
    rw [hAx] at hiso
    refine ⟨?_, ?_⟩
    · rw [hiso, hv]
    · intro h0
      apply hv0
      have h1 : (A : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ Multiplicative.toAdd v = 0 := by
        rw [hAx, h0]
      have h2 := congrArg (fun z => ((A⁻¹ : GL s16h_H5E3RkιA K) :
        Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ z) h1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      exact h2
  · intro hw
    obtain ⟨hwQ, hw0⟩ := hw
    obtain ⟨A, hA, hAx⟩ := omegaMinusFourSingularTrans_holds (K := K) (b := b) (c := c) hirr
      (Multiplicative.toAdd v) (Multiplicative.toAdd w) hv0 hw0
      (by rw [hQ]; exact hv) (by rw [hQ]; exact hwQ)
    exact (s16h_e3_mem_orbit_natImage_iff
      (Γ := StatedOmega (StatedQuadMinus 2 K b c))).mpr ⟨A, hA, hAx⟩

private theorem s16h_e3_nonzeroVectors_ncard (hK : Nat.card K = 2 ^ 3) :
    {x : s16h_H5E3RkιA → K | x ≠ 0}.ncard = 4095 := by
  have hι : Nat.card s16h_H5E3RkιA = 4 := by
    rw [Nat.card_eq_fintype_card]
    simp [s16h_H5E3RkιA]
  have hV : Nat.card (s16h_H5E3RkιA → K) = 4096 := by
    rw [Nat.card_fun, hK, hι]
    norm_num
  have h := s16h_e3_ncard_sdiff (s := ({0} : Set (s16h_H5E3RkιA → K))) (t := Set.univ)
    (fun x _ => Set.mem_univ x) Set.finite_univ
  rw [Set.ncard_univ, Set.ncard_singleton] at h
  rw [show (Set.univ \ {0} : Set (s16h_H5E3RkιA → K)) = {x | x ≠ 0} by
    ext x; simp] at h
  rw [h, hV]

private theorem s16h_e3_nonsingularVectors_ncard (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {x : s16h_H5E3RkιA → K | StatedQuadMinus 2 K b c x ≠ 0}.ncard = 3640 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype {μ : K // μ ≠ 0} := Fintype.ofFinite _
  let e : {x : s16h_H5E3RkιA → K // StatedQuadMinus 2 K b c x ≠ 0} ≃
      Σ μ : {μ : K // μ ≠ 0}, {x : s16h_H5E3RkιA → K // StatedQuadMinus 2 K b c x = μ.1} :=
    (Equiv.sigmaSubtypeFiberEquivSubtype (f := StatedQuadMinus 2 K b c)
      (p := fun x => StatedQuadMinus 2 K b c x ≠ 0) (q := fun μ => μ ≠ 0)
      (fun x => Iff.rfl)).symm
  rw [← Nat.card_coe_set_eq]
  change Nat.card {x : s16h_H5E3RkιA → K // StatedQuadMinus 2 K b c x ≠ 0} = 3640
  rw [Nat.card_congr e, Nat.card_sigma]
  have hsum : (∑ μ : {μ : K // μ ≠ 0},
      Nat.card {x : s16h_H5E3RkιA → K // StatedQuadMinus 2 K b c x = μ.1}) =
      ∑ _μ : {μ : K // μ ≠ 0}, 520 := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    exact s16h_e3_shell_ncard hK hirr μ.2
  rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hKc : Nat.card {μ : K // μ ≠ 0} = Nat.card K - 1 := by
    rw [← Nat.card_units (α := K)]
    exact Nat.card_congr
      { toFun := fun μ => Units.mk0 μ.1 μ.2
        invFun := fun u => ⟨(u : K), u.ne_zero⟩
        left_inv := fun μ => Subtype.ext rfl
        right_inv := fun u => Units.ext rfl }
  rw [← Nat.card_eq_fintype_card, hKc, hK]
  norm_num

private theorem s16h_e3_singularVectors_ncard_vec (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {x : s16h_H5E3RkιA → K | x ≠ 0 ∧ StatedQuadMinus 2 K b c x = 0}.ncard = 455 := by
  have hsub : {x : s16h_H5E3RkιA → K | StatedQuadMinus 2 K b c x ≠ 0} ⊆
      {x : s16h_H5E3RkιA → K | x ≠ 0} := by
    intro x hx
    exact fun h => hx (by rw [h]; exact s16h_e3_quadMinus_zero (K := K) (b := b) (c := c))
  have h := s16h_e3_ncard_sdiff hsub (Set.toFinite _)
  rw [show {x : s16h_H5E3RkιA → K | x ≠ 0 ∧ StatedQuadMinus 2 K b c x = 0} =
      ({x : s16h_H5E3RkιA → K | x ≠ 0} \
        {x : s16h_H5E3RkιA → K | StatedQuadMinus 2 K b c x ≠ 0}) by
    ext x
    by_cases hx : StatedQuadMinus 2 K b c x = 0 <;> simp [hx]]
  rw [h, s16h_e3_nonzeroVectors_ncard hK, s16h_e3_nonsingularVectors_ncard hK hirr]

theorem s16h_H5E3_singularVectors_ncard (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {w : StdMod s16h_H5E3RkιA K | StatedQuadMinus 2 K b c (Multiplicative.toAdd w) = 0 ∧
      Multiplicative.toAdd w ≠ 0}.ncard = 455 := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card {w : StdMod s16h_H5E3RkιA K //
    StatedQuadMinus 2 K b c (Multiplicative.toAdd w) = 0 ∧ Multiplicative.toAdd w ≠ 0} = 455
  rw [Nat.card_congr (Equiv.subtypeEquiv (Multiplicative.toAdd)
    (p := fun w => StatedQuadMinus 2 K b c (Multiplicative.toAdd w) = 0 ∧
      Multiplicative.toAdd w ≠ 0)
    (q := fun x => x ≠ 0 ∧ StatedQuadMinus 2 K b c x = 0)
    (fun w => by simp only [and_comm]))]
  exact s16h_e3_singularVectors_ncard_vec hK hirr

private theorem s16h_e3_stab_singular_card (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0)
    (hv0 : Multiplicative.toAdd v ≠ 0) :
    Nat.card ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
      MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v) = 576 := by
  let Ω := natImage (StatedOmega (StatedQuadMinus 2 K b c))
  have hΩcard : Nat.card ↥Ω = 262080 := by
    dsimp [Ω]
    rw [natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
    exact s16h_e3_natCard_statedOmega hK hirr
  have horb : Nat.card (MulAction.orbit (↥Ω) v) = 455 := by
    rw [s16h_e3_orbit_statedOmega_eq_singular hirr hv hv0]
    exact s16h_H5E3_singularVectors_ncard hK hirr
  have hOS := s16h_e3_orbit_mul_stab_card (↥Ω) v
  rw [horb, hΩcard] at hOS
  have hk : Nat.card ↥(MulAction.stabilizer Ω v) = 576 := by omega
  rwa [s16h_e3_stab_subgroupOf_card Ω v] at hk

theorem s16h_H5E3_stab_dvd_nonsingular (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {q : ℕ} (hq : q = 3 ∨ q = 7)
    {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    q ∣ Nat.card ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
      MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v) := by
  let Ω := natImage (StatedOmega (StatedQuadMinus 2 K b c))
  let O := natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))
  let S := MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v
  have hΩO : Ω ≤ O := by
    change natImage (StatedOmega (StatedQuadMinus 2 K b c)) ≤
      natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))
    rw [natImage_eq_map, natImage_eq_map]
    exact Subgroup.map_mono (statedOmega_le_isometryCore _)
  have hcardO : Nat.card ↥(O ⊓ S) = 1008 := s16h_e3_stab_isometryCore_card hK hirr hv
  have hdvd : Nat.card ↥(Ω ⊓ S) ∣ 1008 := by
    rw [← hcardO]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right S hΩO)
  have hΩcard : Nat.card ↥Ω = 262080 := by
    dsimp [Ω]
    rw [natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
    exact s16h_e3_natCard_statedOmega hK hirr
  have hOS := s16h_e3_orbit_mul_stab_card (↥Ω) v
  rw [hΩcard] at hOS
  have hsub : MulAction.orbit (↥Ω) v ⊆
      {w : StdMod s16h_H5E3RkιA K | StatedQuadMinus 2 K b c (Multiplicative.toAdd w) =
        StatedQuadMinus 2 K b c (Multiplicative.toAdd v)} := by
    intro w hw
    obtain ⟨A, hA, hAx⟩ :=
      (s16h_e3_mem_orbit_natImage_iff (Γ := StatedOmega (StatedQuadMinus 2 K b c))).mp hw
    have hiso := apply_mulVec_of_mem_isometryCore (Q₀ := StatedQuadMinus 2 K b c)
      (statedOmega_le_isometryCore _ hA) (Multiplicative.toAdd v)
    rw [hAx] at hiso
    exact hiso
  have horble : Nat.card (MulAction.orbit (↥Ω) v) ≤ 520 := by
    calc Nat.card (MulAction.orbit (↥Ω) v) = (MulAction.orbit (↥Ω) v).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({w : StdMod s16h_H5E3RkιA K | StatedQuadMinus 2 K b c (Multiplicative.toAdd w) =
            StatedQuadMinus 2 K b c (Multiplicative.toAdd v)}).ncard := Set.ncard_le_ncard hsub
      _ = 520 := s16h_e3_shell_ncard hK hirr hv
  have hge : 504 ≤ Nat.card ↥(Ω ⊓ S) := by
    rw [← s16h_e3_stab_subgroupOf_card Ω v]
    nlinarith [hOS, horble, Nat.zero_le (Nat.card ↥(MulAction.stabilizer Ω v))]
  obtain ⟨d, hd⟩ := hdvd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd; omega
    · exact h
  have hdle : d ≤ 2 := by nlinarith
  have hd12 : d = 1 ∨ d = 2 := by omega
  have hk : Nat.card ↥(Ω ⊓ S) = 1008 ∨ Nat.card ↥(Ω ⊓ S) = 504 := by
    rcases hd12 with rfl | rfl
    · left; rw [mul_one] at hd; omega
    · right; omega
  rcases hk with hk | hk <;> rw [hk] <;> rcases hq with rfl | rfl <;> norm_num

theorem s16h_H5E3_stab_dvd_singular (hK : Nat.card K = 2 ^ 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v : StdMod s16h_H5E3RkιA K}
    (hv : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0)
    (hv0 : Multiplicative.toAdd v ≠ 0) :
    3 ∣ Nat.card ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
      MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v) := by
  have h := s16h_e3_stab_singular_card hK hirr hv hv0
  rw [h]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
