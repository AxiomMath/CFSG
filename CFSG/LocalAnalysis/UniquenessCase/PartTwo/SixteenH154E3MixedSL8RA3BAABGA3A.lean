module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA3AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABEA
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_involution_of_C_TZ_eq_top
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (TA TB : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hTA_T : TA ≤ T) (hTB_T : TB ≤ T)
    (hTA_syl : CFSG.ABGLocalTools.IsSylowOf 2 TA (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hTB_syl : CFSG.ABGLocalTools.IsSylowOf 2 TB
      (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)))
    (hTS : T ⊓ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) = TA ⊔ TB) :
    ∃ τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      τ ∈ T ∧
      τ ∉ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) ∧
      τ ^ 2 = 1 ∧
      (lBar ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj τ).toMonoidHom =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ∧
      TA.map (MulAut.conj τ).toMonoidHom = TB ∧
      T = (T ⊓ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)) ⊔ Subgroup.zpowers τ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hV := h.hyp151.isElemAbelian
  let W := Vtil ⊥ V hV
  let Mb : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let A : Subgroup (MulAut W) := lBar ⊥ V hV L
  let B : Subgroup (MulAut W) := barSub ⊥ V hV (conjSubgroup L x)
  let NA : Subgroup (MulAut W) := Subgroup.normalizer (A : Set (MulAut W))
  let N : Subgroup (MulAut W) := Mb ⊓ NA
  have hTM : T ≤ Mb := hT.le
  have hNidx : N.relIndex Mb = 2 := by
    let act : MulAction Mb (Subgroup (MulAut W)) :=
      { smul := fun g H => H.map (MulAut.conj (g : MulAut W)).toMonoidHom
        one_smul := fun H => by
          show H.map (MulAut.conj (((1 : Mb) : MulAut W))).toMonoidHom = H
          rw [show ((1 : Mb) : MulAut W) = 1 from rfl]
          exact Subgroup.map_id H
        mul_smul := fun g g' H => by
          show H.map (MulAut.conj (((g * g' : Mb) : MulAut W))).toMonoidHom =
            (H.map (MulAut.conj (((g' : Mb) : MulAut W))).toMonoidHom).map
              (MulAut.conj (((g : Mb) : MulAut W))).toMonoidHom
          rw [Subgroup.map_map]
          congr 1 }
    letI : MulAction Mb (Subgroup (MulAut W)) := act
    have hstab : MulAction.stabilizer Mb A = N.subgroupOf Mb := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hg => ⟨g.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hg⟩,
        fun hg => (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.2⟩
    have horbit : MulAction.orbit Mb A = {X : Subgroup (MulAut W) |
        ∃ φ ∈ Mb, X = A.map (MulAut.conj φ).toMonoidHom} := by
      ext X
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(g : MulAut W), g.2, rfl⟩
      · rintro ⟨φ, hφ, rfl⟩
        exact ⟨⟨φ, hφ⟩, rfl⟩
    have hidx_orbit : (MulAction.stabilizer Mb A).index = s15 D.M ⊥ V hV L := by
      rw [MulAction.index_stabilizer]
      change (MulAction.orbit Mb A).ncard = s15 D.M ⊥ V hV L
      rw [horbit]
      rfl
    show (N.subgroupOf Mb).index = 2
    rw [← hstab, hidx_orbit, hs2]
  have hNnorm : Mb ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).1
      (Subgroup.normal_of_index_eq_two hNidx)
  have hTN_eq : T ⊓ NA = T ⊓ N := by
    show T ⊓ NA = T ⊓ (Mb ⊓ NA)
    rw [← inf_assoc, inf_eq_left.mpr hTM]
  have hPrel : (T ⊓ NA).relIndex T = 2 := by
    rw [hTN_eq]
    exact s16h_sylow_inf_normal_index_two hT inf_le_left hNnorm hNidx
  have hBne : B ≠ A := by
    intro hBA
    have hc : barSub ⊥ V hV (conjSubgroup L x) = barSub ⊥ V hV L := hBA
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 hV hxM).2 hc)
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil ⊥ V := hMs hxM
  let u : MulAut W := actTil ⊥ V hV ⟨x, hxs⟩
  have huMb : u ∈ Mb := actTil_mem_barSub ⊥ V hV hxM hxs
  have hBu' : B = A.map (MulAut.conj u⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup (V₀ := ⊥) (V := V) hV hxs L
  have huNA : u ∉ NA := by
    intro hu
    have hAu : A.map (MulAut.conj u⁻¹).toMonoidHom = A :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (NA.inv_mem hu)
    exact hBne (hBu'.trans hAu)
  have hu'Mb : u⁻¹ ∈ Mb := Mb.inv_mem huMb
  have hu'NA : u⁻¹ ∉ NA := fun hh => huNA (by simpa using NA.inv_mem hh)
  have hconj : ∀ s ∈ T, s ∉ NA → A.map (MulAut.conj s).toMonoidHom = B := by
    intro s hsT hsNA
    have hsMb : s ∈ Mb := hTM hsT
    have hsN : s ∉ N := fun hh => hsNA (Subgroup.mem_inf.mp hh).2
    have hu'N : u⁻¹ ∉ N := fun hh => hu'NA (Subgroup.mem_inf.mp hh).2
    have hsuN : s⁻¹ * u⁻¹ ∈ N := by
      have h1 : ((⟨s, hsMb⟩ : Mb)⁻¹) ∉ N.subgroupOf Mb := by
        rw [Subgroup.mem_subgroupOf]
        intro hmem
        exact hsN (by simpa using N.inv_mem hmem)
      have h2 : ((⟨u⁻¹, hu'Mb⟩ : Mb)) ∉ N.subgroupOf Mb := by
        rw [Subgroup.mem_subgroupOf]
        exact hu'N
      have hiff : ((⟨s, hsMb⟩ : Mb)⁻¹ ∈ N.subgroupOf Mb) ↔
          ((⟨u⁻¹, hu'Mb⟩ : Mb) ∈ N.subgroupOf Mb) :=
        ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
      have hmem := (Subgroup.mul_mem_iff_of_index_two (H := N.subgroupOf Mb)
        hNidx).mpr hiff
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
    have hsuNA : s⁻¹ * u⁻¹ ∈ NA := (Subgroup.mem_inf.mp hsuN).2
    have hA_su : A.map (MulAut.conj (s⁻¹ * u⁻¹)).toMonoidHom = A :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hsuNA
    have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom =
        (MulAut.conj (s⁻¹ * u⁻¹)).toMonoidHom := by
      have h : MulAut.conj s⁻¹ * MulAut.conj u⁻¹ = MulAut.conj (s⁻¹ * u⁻¹) := by
        rw [← map_mul]
      rw [← h]
      rfl
    have hABt : A = B.map (MulAut.conj s⁻¹).toMonoidHom := by
      calc A = A.map (MulAut.conj (s⁻¹ * u⁻¹)).toMonoidHom := hA_su.symm
        _ = (A.map (MulAut.conj u⁻¹).toMonoidHom).map
              (MulAut.conj s⁻¹).toMonoidHom := by
              rw [← hcomp, ← Subgroup.map_map]
        _ = B.map (MulAut.conj s⁻¹).toMonoidHom := by rw [← hBu']
    have hfinal : A.map (MulAut.conj s).toMonoidHom = B := by
      rw [hABt, Subgroup.map_map]
      have hcomp2 : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom =
          MonoidHom.id (MulAut W) := by
        have h : MulAut.conj s * MulAut.conj s⁻¹ = (1 : MulAut (MulAut W)) := by
          rw [← map_mul, mul_inv_cancel, map_one]
        rw [show (MulAut.conj s).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom =
            (MulAut.conj s * MulAut.conj s⁻¹).toMonoidHom from rfl, h]
        rfl
      rw [hcomp2, Subgroup.map_id]
    exact hfinal
  have hcomm : ⁅A, B⁆ = ⊥ := by
    simpa only [A, B, lBar] using (h.hyp151.commute x hxM hxn).1
  have hBcentA : B ≤ Subgroup.centralizer (A : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact hcomm)
  have hABbot : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hz
    have hzcent : (⟨z, hz.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hBcentA hz.2)) (y : MulAut W) y.2
    have hcentA := s16h_sl28_center_eq_bot_of_isSLn_two (m := 3) (by norm_num) hrow.1
    have hzbot : (⟨z, hz.1⟩ : ↥A) ∈ (⊥ : Subgroup ↥A) := hcentA ▸ hzcent
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzbot)
  obtain ⟨τ, hτT, hτNA, hτ2, hAτ, hTAτ, hTsup⟩ :=
    s16h_sl28_involution_of_index_two_normalizer (X := MulAut W)
      hT.isPGroup hPrel hTS hTA_syl.le hTB_syl.le hTA_T hTB_T hTA_syl hTB_syl
      hcomm hABbot hconj
  exact ⟨τ, hτT, hτNA, hτ2, hAτ, hTAτ, hTsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
