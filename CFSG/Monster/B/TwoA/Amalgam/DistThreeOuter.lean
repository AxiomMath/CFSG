module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuterCore
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceNode

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_inv_apply)

private theorem mem_sphereFour_symm'
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have hord : ∀ a b : CVert, LabelFour a b → LabelFour b a := by
    intro a b h
    have e : lblOrd b a = lblOrd a b := by
      rw [lblOrd, lblOrd, ← MulEquiv.orderOf_eq (MulAut.conj (clabel a)) (clabel b * clabel a),
        MulAut.conj_apply]
      congr 1
      group
    rw [LabelFour, e]
    exact h
  exact ⟨fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord v w h.2⟩,
    fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord w v h.2⟩⟩

theorem exists_switch_lift
    {k : Jhat} (hτ : wAct v0 (jhatToKv0 k) Unitary.sigmaW = Unitary.tauW) :
    ∃ g : Jhat, jhatToKv0 g = Unitary.swG ∧ cvMul (cvOf (jhatS k)) (jhatS g) = cv0 := by
  obtain ⟨g, hg⟩ := jhatToKv0_surjective Unitary.swG
  have hpt : piPt 1 = piPt (k * g) := by
    apply Subtype.ext
    rw [coe_piPt_one, coe_piPt_mul, coe_piPt, hτ, hg, Unitary.wAct_swG_tauW]
  have ha : jhatToKv0 a0J = 1 := jhatToKv0_eq_one_of_mem_Ehat a0J.2 a0_mem_Ehat
  rcases piPt_eq_iff.1 hpt with h | h
  · refine ⟨g, hg, ?_⟩
    rw [cvMul_jhatS, h]
    rfl
  · refine ⟨g * a0J⁻¹, by rw [map_mul, map_inv, ha, inv_one, mul_one, hg], ?_⟩
    rw [cvMul_jhatS, ← mul_assoc, ← cvMul_jhatS, h, cvMul_jhatS, mul_one, mul_inv_cancel]
    rfl

theorem inv_mul_mul_mem_P1 {x : Dfull} (hx : x ∈ P1) {q : Dfull} (hq : q ∈ P1) :
    q⁻¹ * x * q ∈ P1 :=
  P1.mul_mem (P1.mul_mem (P1.inv_mem hq) hx) hq

theorem exists_base_transv
    (hX : DistThreePathFact) (hT : DistThreeBaseTransvFact)
    {v u : CVert} (hu : u ∈ sphereDistThree v) :
    ∃ (g : Shat) (k : Jhat), cvMul v g = cvOf (jhatS k) ∧ cvOf (jhatS k) ≠ cv0 ∧
      ¬ cgraph.Adj cv0 (cvOf (jhatS k)) ∧
      wAct v0 (jhatToKv0 k) Unitary.sigmaW = Unitary.tauW ∧
      ∃ (hP : clabel (cvMul u g) ∈ P1) (R : Submodule CFSG.Fischer.F4 Unitary.V6),
        R ∈ Unitary.ptOrbit 0 ∧ p1Proj ⟨_, hP⟩ = Unitary.transvU R := by
  obtain ⟨w, hwu, hw⟩ := hX.1 v u hu
  obtain ⟨g, k, hwg, hvg, hτ⟩ := exists_normalized_base hw
  have h4 : cvOf (jhatS k) ∈ sphereFour cv0 := by
    rw [← hwg, ← hvg]
    exact sphereFour_cvMul (mem_sphereFour_symm'.1 hw) g
  obtain ⟨hk0', hk, -⟩ := cgraph_dist_eq_two_iff.1 h4.1
  have hadj₀ : cgraph.Adj cv0 (cvMul u g) := by
    rw [← hwg]
    exact (cgraph_adj_cvMul w u g).2 ((cgraph.adj_comm _ _).1 hwu)
  have hd₀ : cvMul u g ∈ sphereDistThree (cvOf (jhatS k)) := by
    rw [← hvg]
    exact sphereDistThree_cvMul hu g
  obtain ⟨hP, R, hR, hsR⟩ := hT k (cvMul u g) h4 hτ
    (hX.2 (cvOf (jhatS k)) cv0 (mem_sphereFour_symm'.1 h4) ⟨hadj₀, hd₀⟩)
  exact ⟨g, k, hvg, Ne.symm hk0', hk, hτ, hP, R, hR, hsR⟩

theorem exists_Q4_conj_genU
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))
    (hτ : wAct v0 (jhatToKv0 k) Unitary.sigmaW = Unitary.tauW) {x : Dfull} (hx : x ∈ P1)
    {R : Submodule CFSG.Fischer.F4 Unitary.V6} (hR : R ∈ Unitary.ptOrbit 0)
    (hxR : p1Proj ⟨x, hx⟩ = Unitary.transvU R) :
    ∃ q : Jhat, ((q : Dfull)) ∈ Q4 k ∧
      ∀ hq : ((q : Dfull))⁻¹ * x * q ∈ P1, p1Proj ⟨_, hq⟩ = Unitary.genU 6 := by
  have hRsp : Rsp ∈ Unitary.orbitA R := by
    rw [Unitary.orbitA_of_mem_ptOrbit (by norm_num) hR, ← Unitary.singPt_five]
    exact Unitary.singPt_five_mem
  obtain ⟨a, ha, hRa⟩ := hRsp
  have hsingR : Unitary.IsSingPt R := by
    rw [← Unitary.fixTauPts_eq] at hR
    exact hR.1
  have hconjR : Unitary.genU 6 = a⁻¹ * Unitary.transvU R * a := by
    rw [← Unitary.transvU_Rsp, ← hRa, Unitary.transvU_sigmaAct hsingR]
  have hmap := map_Q4 hk0 hk
  rw [psiW_labE, hτ] at hmap
  have haQ : (a : Kstab v0) ∈ ((Q4 k).subgroupOf Jhat).map jhatToKv0 := by
    rw [hmap]
    exact ⟨a.2, Unitary.mem_Atau.1 ha⟩
  obtain ⟨q, hq, hqa⟩ := haQ
  have hqQ : ((q : Jhat) : Dfull) ∈ Q4 k := Subgroup.mem_subgroupOf.1 hq
  have hqP : ((q : Jhat) : Dfull) ∈ P1 := Q4_le_P1 hqQ
  refine ⟨q, hqQ, fun hq' => ?_⟩
  have hpq : p1Proj ⟨_, hqP⟩ = a := by
    apply Subtype.ext
    rw [coe_p1Proj]
    exact hqa
  have e : (⟨_, hq'⟩ : P1) = (⟨_, hqP⟩ : P1)⁻¹ * ⟨x, hx⟩ * ⟨_, hqP⟩ := rfl
  rw [e, map_mul, map_mul, map_inv, hpq, hxR, hconjR]

theorem jhatToKv0_switch_conj
    {x : Dfull} (hx : x ∈ P1) (hxr : p1Proj ⟨x, hx⟩ = Unitary.genU 6)
    {ĝ : Jhat} (hĝ : jhatToKv0 ĝ = Unitary.swG) (hxJ : ((ĝ : Dfull))⁻¹ * x * ĝ ∈ Jhat) :
    jhatToKv0 ⟨_, hxJ⟩ = (Unitary.swU : Kstab v0) := by
  have e : (⟨_, hxJ⟩ : Jhat) = ĝ⁻¹ * ⟨x, P1_le_Jhat hx⟩ * ĝ := rfl
  have hxK : jhatToKv0 ⟨x, P1_le_Jhat hx⟩ = CFSG.Monster.B.TwoA.Co2Inv.rK := by
    have h := congrArg (fun z : Unitary.Usig => (z : Kstab v0)) hxr
    rw [coe_p1Proj] at h
    rw [h]
    exact genK_six
  rw [e, map_mul, map_mul, map_inv, hĝ, hxK]
  exact (Unitary.native_unitary_transvection_switches_to_field_involution.2.2.2.2.2.2.1).symm

theorem exists_conj_mem_P1_swU
    (hX : DistThreePathFact) (hT : DistThreeBaseTransvFact)
    {v u : CVert} (hu : u ∈ sphereDistThree v) :
    ∃ Y : Shat, cvMul cv0 Y = v ∧
      ((Y * clabelS u * Y⁻¹ : Shat) : Dfull) ∈ P1 ∧
      ∀ hP : ((Y * clabelS u * Y⁻¹ : Shat) : Dfull) ∈ P1,
        p1Proj ⟨_, hP⟩ = Unitary.swU := by
  have hs := (native_distance_three_labels_commute_and_fix_endpoints_of hX hT hu).1
  obtain ⟨g, k, hvg, hk0, hk, hτ, hP₀, R, hR, hsR⟩ := exists_base_transv hX hT hu
  obtain ⟨q, hqQ, hq⟩ := exists_Q4_conj_genU hk0 hk hτ hP₀ hR hsR
  have hqP : ((q : Jhat) : Dfull) ∈ P1 := Q4_le_P1 hqQ
  have hqfix := ((native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
    (jhatS q)).2 hqQ
  obtain ⟨ĝ, hĝ, hĝk⟩ := exists_switch_lift hτ
  have hvX : cvMul v (g * jhatS q * jhatS ĝ) = cv0 := by
    rw [cvMul_mul, cvMul_mul, hvg, hqfix.2, hĝk]
  have hY : cvMul cv0 (g * jhatS q * jhatS ĝ)⁻¹ = v := by
    rw [← hvX, cvMul_inv_cancel]
  refine ⟨(g * jhatS q * jhatS ĝ)⁻¹, hY, ?_⟩
  set X : Shat := g * jhatS q * jhatS ĝ with hXdef
  have hlab : X⁻¹ * clabelS u * X⁻¹⁻¹ = (jhatS ĝ)⁻¹ * ((jhatS q)⁻¹ * clabelS (cvMul u g) *
      jhatS q) * jhatS ĝ := by
    rw [inv_inv, clabelS_cvMul, hXdef]
    group
  have hx₁P : ((jhatS q : Dfull))⁻¹ * clabel (cvMul u g) * (jhatS q : Dfull) ∈ P1 :=
    inv_mul_mul_mem_P1 hP₀ hqP
  have hcoe : ((X⁻¹ * clabelS u * X⁻¹⁻¹ : Shat) : Dfull) =
      ((ĝ : Dfull))⁻¹ * (((q : Dfull))⁻¹ * clabel (cvMul u g) * q) * ĝ := by
    rw [hlab]
    rfl
  have hmemE : ((X⁻¹ * clabelS u * X⁻¹⁻¹ : Shat) : Dfull) ∈ Eam := by
    have hfix : X⁻¹ * clabelS u * X⁻¹⁻¹ ∈ vStab cv0 := by
      rw [mem_vStab, inv_inv, ← hvX, ← cvMul_mul,
        show X * (X⁻¹ * clabelS u * X) = clabelS u * X by group, cvMul_mul, mem_vStab.1 hs]
    exact mem_vStab_cv0.1 hfix
  have hxJ : ((ĝ : Dfull))⁻¹ * (((q : Dfull))⁻¹ * clabel (cvMul u g) * q) * ĝ ∈ Jhat :=
    Jhat.mul_mem (Jhat.mul_mem (Jhat.inv_mem ĝ.2) (P1_le_Jhat hx₁P)) ĝ.2
  have hP : ((X⁻¹ * clabelS u * X⁻¹⁻¹ : Shat) : Dfull) ∈ P1 :=
    ⟨by rw [hcoe]; exact hxJ, Eam_le_centralizer hmemE⟩
  refine ⟨hP, fun hP' => ?_⟩
  apply Subtype.ext
  rw [coe_p1Proj]
  have e : (⟨_, P1_le_Jhat hP'⟩ : Jhat) = ⟨_, hxJ⟩ := Subtype.ext hcoe
  rw [e]
  exact jhatToKv0_switch_conj hx₁P (hq hx₁P) hĝ hxJ

theorem stabToEam_injective
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    Function.Injective (stabToEam hs) := by
  intro y z h
  have h1 : ((stabToEam hs y : Eam) : Dfull) = ((stabToEam hs z : Eam) : Dfull) :=
    congrArg Subtype.val h
  have h' : s * (y : Shat) * s⁻¹ = s * z * s⁻¹ := Subtype.ext h1
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

@[expose] def stabEquivEam
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) : vStab v ≃* Eam :=
  MulEquiv.ofBijective (stabToEam hs) ⟨stabToEam_injective hs, stabToEam_surjective hs⟩

theorem map_commutator_stabEquivEam
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    (commutator (vStab v)).map (stabEquivEam hs).toMonoidHom = commutator Eam := by
  have hr : (stabEquivEam hs).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (stabEquivEam hs).surjective
  rw [map_commutator_eq, hr, ← _root_.commutator_def]

theorem mem_commutator_vStab_iff
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (y : vStab v) :
    y ∈ commutator (vStab v) ↔ stabToEam hs y ∈ commutator Eam := by
  rw [← map_commutator_stabEquivEam hs]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, e⟩
    rw [(stabEquivEam hs).injective e] at hz
    exact hz

theorem index_commutator_vStab
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    (commutator (vStab v)).index = 2 := by
  have e : commutator (vStab v) = (commutator Eam).comap (stabEquivEam hs).toMonoidHom := by
    ext y
    exact mem_commutator_vStab_iff hs y
  rw [e, Subgroup.index_comap_of_surjective (f := (stabEquivEam hs).toMonoidHom) _
    (stabEquivEam hs).surjective]
  exact short_F4_derived_standard_perfect_cover.1

theorem comap_Ginl_eq_commutator
    {v : CVert} {ρ : vStab v →* GStar} (hρ : Function.Surjective ρ) :
    Ginl.comap ρ = commutator (vStab v) := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  have hle : commutator (vStab v) ≤ Ginl.comap ρ := by
    rw [← Subgroup.map_le_iff_le_comap, map_commutator_eq, MonoidHom.range_eq_top.2 hρ,
      ← _root_.commutator_def, commutator_GStar]
  have hidx : (Ginl.comap ρ).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hρ, index_Ginl]
  have : (Ginl.comap ρ).FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  exact (Subgroup.eq_of_index_dvd_index hle (by rw [hidx, index_commutator_vStab hs])).symm

theorem native_distance_three_label_is_outer_local_involution_of
    (hX : DistThreePathFact)
    (hT : DistThreeBaseTransvFact) {v u : CVert} (hu : u ∈ sphereDistThree v) :
    clabelS u ∈ vStab v ∧
    (∀ y : vStab v, (y : Shat) = clabelS u → y ∉ commutator (vStab v)) ∧
    ∀ ρ : vStab v →* GStar, Function.Surjective ρ → ∀ y : vStab v, (y : Shat) = clabelS u →
      (ρ y).right ≠ 1 ∧ ρ y ∉ Ginl := by
  have hs := (native_distance_three_labels_commute_and_fix_endpoints_of hX hT hu).1
  obtain ⟨Y, hY, hP, himg⟩ := exists_conj_mem_P1_swU hX hT hu
  have hnot : ∀ y : vStab v, (y : Shat) = clabelS u → y ∉ commutator (vStab v) := by
    intro y hy hmem
    rw [mem_commutator_vStab_iff hY] at hmem
    have e : stabToEam hY y = ⟨_, P1_le_Eam_d3 hP⟩ := by
      apply Subtype.ext
      show ((Y * y * Y⁻¹ : Shat) : Dfull) = _
      rw [hy]
    rw [e, mem_commutator_iff_p1Proj hP, himg hP] at hmem
    exact Unitary.swU_not_mem_linU hmem
  refine ⟨hs, hnot, fun ρ hρ y hy => ?_⟩
  have hG : ρ y ∉ Ginl := by
    intro h
    have : y ∈ Ginl.comap ρ := h
    rw [comap_Ginl_eq_commutator hρ] at this
    exact hnot y hy this
  refine ⟨fun h => hG ?_, hG⟩
  show ρ y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  exact h

end CFSG.Monster.B.TwoA.Amalgam
