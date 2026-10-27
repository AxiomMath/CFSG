module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2SylowDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInterLeCentralizerFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ImageDihedralSylowOddKernel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalCenterlessDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientCenterAutomorphism
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open Matrix
noncomputable section
namespace CFSG.GorensteinWalter

universe u

private theorem central_automorphism_eq_one_local
    {E : Type u} [Group E]
    (hperf : Group.IsPerfect E) (α β : E ≃* E)
    (hdelta : ∀ x : E, α x * (β x)⁻¹ ∈ Subgroup.center E) :
    α = β := by
  apply MulEquiv.ext
  intro x
  let : Bracket E E := commutatorElement
  have hcomm : ∀ a b : E, α ⁅a, b⁆ = β ⁅a, b⁆ := by
    intro a b
    have hza := Subgroup.mem_center_iff.mp (hdelta a)
    have hzb := Subgroup.mem_center_iff.mp (hdelta b)
    have htarget : ⁅α a, α b⁆ = ⁅β a, β b⁆ := by
      rw [show α a = (α a * (β a)⁻¹) * β a by group,
        show α b = (α b * (β b)⁻¹) * β b by group]
      let za : E := α a * (β a)⁻¹
      let zb : E := α b * (β b)⁻¹
      have hza_center : za ∈ Subgroup.center E := by simpa [za] using hdelta a
      have hzb_center : zb ∈ Subgroup.center E := by simpa [zb] using hdelta b
      have hleft : ∀ z x y : E, z ∈ Subgroup.center E →
          ⁅z * x, y⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hzy : ⁅z, y⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_center_iff.mp hz y).symm
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hzy, hzc]
        simp
      have hright : ∀ z x y : E, z ∈ Subgroup.center E →
          ⁅x, y * z⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hxy : ⁅x, z⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_center_iff.mp hz x
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hxy]
        simpa [mul_assoc] using hzc
      rw [hleft za (β a) (zb * β b) hza_center]
      rw [show zb * β b = β b * zb by
        exact (Subgroup.mem_center_iff.mp hzb_center (β b)).symm]
      rw [hright zb (β a) (β b) hzb_center]
    simpa only [map_commutatorElement] using htarget
  have hx : x ∈ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ := by
    have htop : Group.IsPerfect (↥(⊤ : Subgroup E)) := by
      let : Group.IsPerfect E := hperf
      infer_instance
    have hcommtop : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ :=
      (Subgroup.isPerfect_iff (H := (⊤ : Subgroup E))).mp htop
    rw [hcommtop]
    trivial
  rw [Subgroup.commutator_def] at hx
  refine Subgroup.closure_induction (p := fun y _hy => α y = β y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨a, _ha, b, _hb, rfl⟩
    exact hcomm a b
  · simp
  · intro a b _ha _hb ha hb
    rw [map_mul, ha, hb, map_mul]
  · intro a _ha ha
    rw [map_inv, ha, map_inv]

/-- The semilinear action of the second-case maximal subgroup on its selected
component quotient, together with the pointwise conjugation compatibility
needed by the Fitting-subgroup argument. -/
public structure SecondCasePSL2ActionData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K] where
  primePower : IsOddPrimePower (Nat.card K)
  modelEquiv : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)
  fieldCardGtThree : 3 < Nat.card K
  f : (↥w.M) →* PGammaL2 K
  ker_odd : Odd (Nat.card f.ker)
  pslRange_le : pGammaL2PSLRange K ≤ f.range
  range_dihedral : HasDihedralSylowTwo f.range
  fieldRange_odd :
    Odd (Nat.card (pGammaL2FieldProjection K f.range).range)
  action_eq : ∀ (m : ↥w.M) (x : d.E),
    pGammaL2ToMulAutPSL2 K primePower fieldCardGtThree (f m)
        (modelEquiv.some
          (QuotientGroup.mk' (Subgroup.center d.E) x)) =
      modelEquiv.some
        (QuotientGroup.mk' (Subgroup.center d.E)
          ⟨(m : G) * (x : G) * (m : G)⁻¹,
            d.E_normal.2 (m : G) m.2 (x : G) x.2⟩)

public theorem secondCase_psl2_action_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    Nonempty (SecondCasePSL2ActionData w d K) := by
  have hcard : 3 < Nat.card K := secondCase_psl2_field_card_gt_three d K hK e
  rcases hK with ⟨p, n, hp, hpodd, hn, hKcard⟩
  let : Fact p.Prime := ⟨hp⟩
  let hK' : IsOddPrimePower (Nat.card K) := ⟨p, n, hp, hpodd, hn, hKcard⟩
  let M0 : Type u := ↥w.M
  let : Group M0 := inferInstance
  have hEleM : d.E ≤ w.M := d.E_component.1
  let E0 : Subgroup M0 := d.E.subgroupOf w.M
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEleM]
    intro x y hx hy
    exact d.E_normal.2 y hy x hx
  let eE0 : E0 ≃* d.E := Subgroup.subgroupOfEquivOfLe hEleM
  let conj0 : M0 →* MulAut E0 := MulAut.conjNormal (H := E0)
  let conjE : M0 →* MulAut d.E :=
    (MulAut.congr eE0).toMonoidHom.comp conj0
  let qAut : MulAut d.E →* MulAut (d.E ⧸ Subgroup.center d.E) :=
    quotientCenterAutomorphism d.E
  let qAction : M0 →* MulAut (d.E ⧸ Subgroup.center d.E) :=
    qAut.comp conjE
  let autPSL : M0 →* MulAut (PSL2 K) :=
    (MulAut.congr e.some).toMonoidHom.comp qAction
  let semie : PGammaL2 K ≃* MulAut (PSL2 K) :=
    pGammaL2EquivMulAutPSL2 K hK' hcard
      (pGammaL2ToMulAutPSL2_surjective K hKcard hK' hcard)
  let fmap : M0 →* PGammaL2 K := semie.symm.toMonoidHom.comp autPSL
  have hconj_congr {H S : Type u} [Group H] [Group S]
      (ee : H ≃* S) (z : H) :
      MulAut.congr ee (MulAut.conj z) = MulAut.conj (ee z) := by
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  have hqconj (n : d.E) :
      qAut (conjE ⟨n, hEleM n.2⟩) =
        MulAut.conj (QuotientGroup.mk' (Subgroup.center d.E) n) := by
    apply MulEquiv.ext
    intro z
    refine QuotientGroup.induction_on z ?_
    intro x
    change (qAut (conjE ⟨n, hEleM n.2⟩))
        (QuotientGroup.mk' (Subgroup.center d.E) x) = _
    rw [quotientCenterAutomorphism_apply_mk]
    apply congrArg (QuotientGroup.mk' (Subgroup.center d.E))
    change eE0 ((conj0 ⟨n, hEleM n.2⟩) (eE0.symm x)) = _
    have hc := MulAut.conjNormal_apply
      (G := M0) (H := E0) ⟨n, hEleM n.2⟩ (eE0.symm x)
    apply Subtype.ext
    change ((↑((conj0 ⟨n, hEleM n.2⟩) (eE0.symm x)) : M0) : G) =
      n * (x : G) * n⁻¹
    exact congrArg (fun z : M0 => (z : G)) hc
  have hpglconj (y : PSL2 K) :
      pgl2InnerAutPSL2 K hK' hcard
          (Matrix.ProjectiveSpecialLinearGroup.toPGL y) =
        MulAut.conj y := by
    apply MulEquiv.ext
    intro z
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [pgl2InnerAutPSL2_toPGL]
  have hPSL : pGammaL2PSLRange K ≤ fmap.range := by
    intro x hx
    rw [mem_pGammaL2PSLRange_iff] at hx
    rcases hx with ⟨y, rfl⟩
    obtain ⟨n, hnq⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center d.E) (e.some.symm y)
    let m : M0 := ⟨n, hEleM n.2⟩
    refine ⟨m, ?_⟩
    apply semie.injective
    simp only [fmap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    simp only [semie, pGammaL2EquivMulAutPSL2,
      MulEquiv.ofBijective_apply]
    change autPSL m = pGammaL2ToMulAutPSL2 K hK' hcard
      (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    rw [pGammaL2ToMulAutPSL2_inl]
    simp [autPSL, qAction, m, hqconj, hconj_congr, hnq, hpglconj]
  have hMdihedral : HasDihedralSylowTwo M0 :=
    secondCase_psl2_hasDihedralSylowTwo hmin c w d K hK' e
  let O : Subgroup M0 := pPrimeCore 2 M0
  let : O.Normal := by dsimp [O]; infer_instance
  have hOodd : Odd (Nat.card O) := by
    exact Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (p := 2) (G := M0))
  let qM : M0 →* (M0 ⧸ O) := QuotientGroup.mk' O
  have hqMsurj : Function.Surjective qM := by
    exact QuotientGroup.mk'_surjective O
  have hqMker : qM.ker = O := by
    simpa [qM] using (QuotientGroup.ker_mk' O)
  have hqMkerodd : Odd (Nat.card qM.ker) := by
    rw [hqMker]
    exact hOodd
  have hQdRange : HasDihedralSylowTwo qM.range :=
    image_hasDihedralSylowTwo_of_odd_kernel hMdihedral qM hqMkerodd
  let eQ : qM.range ≃* (M0 ⧸ O) :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hqMsurj)).trans
      Subgroup.topEquiv
  have hQd : HasDihedralSylowTwo (M0 ⧸ O) :=
    hasDihedralSylowTwo_of_mulEquiv eQ.symm hQdRange
  have hE0ne : E0 ≠ ⊥ := by
    intro hbot
    apply (Subgroup.nontrivial_iff_ne_bot d.E).mp d.E_component.2.2.1
    have hmap : E0.map w.M.subtype = d.E :=
      Subgroup.map_subgroupOf_eq_of_le hEleM
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hE0perf : Group.IsPerfect E0 := by
    let : Group.IsPerfect d.E :=
      (Group.isPerfect_def).2 d.E_component.2.2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := eE0.symm.toMonoidHom) eE0.symm.surjective
  have hE0sn : E0.IsSubnormal := d.E_component.2.1
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  let Ebar : Subgroup (M0 ⧸ O) := E0.map qM
  have hEbarData := perfect_subnormal_image_le_normal_odd_index
    E0 hE0perf hE0ne hE0sn O hOsolv
      (⊤ : Subgroup (M0 ⧸ O)) (by infer_instance) (by simp)
  have hEbarne : Ebar ≠ ⊥ := by simpa [Ebar] using hEbarData.1
  have hEbarperf : Group.IsPerfect Ebar := by simpa [Ebar] using hEbarData.2.1
  have hEbarsn : Ebar.IsSubnormal := by simpa [Ebar] using hEbarData.2.2.1
  let fE : E0 →* Ebar :=
    (qM.comp E0.subtype).codRestrict Ebar (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hfEsurj : Function.Surjective fE := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hcenterE0odd : Odd (Nat.card (Subgroup.center E0)) := by
    have hc : Nat.card (Subgroup.center E0) =
        Nat.card (Subgroup.center d.E) :=
      Nat.card_congr (Subgroup.centerCongr eE0).toEquiv
    rw [hc]
    exact d.center_odd
  let Z : Subgroup M0 := (Subgroup.center E0).map E0.subtype
  have hZnormal : Z.Normal := by
    refine { conj_mem := ?_ }
    intro z hz m
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, rfl⟩
    have hmE : m * (z0 : M0) * m⁻¹ ∈ E0 :=
      hE0normal.conj_mem (z0 : M0) z0.2 m
    refine Subgroup.mem_map.mpr ⟨⟨m * (z0 : M0) * m⁻¹, hmE⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    have hymE : m⁻¹ * (y : M0) * m ∈ E0 := by
      simpa using hE0normal.conj_mem (y : M0) y.2 m⁻¹
    have hzcomm0 := (Subgroup.mem_center_iff.mp hz0)
      (⟨m⁻¹ * (y : M0) * m, hymE⟩ : E0)
    have hzcomm : (z0 : M0) * (m⁻¹ * (y : M0) * m) =
        (m⁻¹ * (y : M0) * m) * (z0 : M0) :=
      (congrArg Subtype.val hzcomm0).symm
    have hconj := congrArg (fun a : M0 => m * a * m⁻¹) hzcomm
    simpa [mul_assoc] using hconj.symm
  have hZodd : Odd (Nat.card Z) := by
    rw [show Nat.card Z = Nat.card (Subgroup.center E0) by
      dsimp [Z]
      exact Subgroup.card_map_of_injective E0.subtype_injective]
    exact hcenterE0odd
  have hZleO : Z ≤ O := by
    exact le_sSup ⟨hZnormal, Nat.coprime_two_left.mpr hZodd⟩
  have hcenter_le_O : Subgroup.center E0 ≤ O.comap E0.subtype := by
    intro z hz
    exact hZleO (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
  have hkerE_le_O : fE.ker ≤ O.comap E0.subtype := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hqz : qM (E0.subtype z) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    exact (QuotientGroup.eq_one_iff (N := O) (E0.subtype z)).mp hqz
  have hkerEodd : Odd (Nat.card fE.ker) := by
    exact Odd.of_dvd_nat hOodd
      ((Subgroup.card_dvd_of_le hkerE_le_O).trans
        (Subgroup.card_comap_dvd_of_injective O E0.subtype E0.subtype_injective))
  have hkerEcenter : fE.ker = Subgroup.center E0 := by
    apply le_antisymm
    · have hkerCop : Nat.Coprime 2 (Nat.card fE.ker) :=
        Nat.coprime_two_left.mpr hkerEodd
      have hkerCore : fE.ker ≤ pPrimeCore 2 E0 :=
        le_sSup ⟨inferInstance, hkerCop⟩
      exact hkerCore.trans (pPrimeCore_le_center_of_isQuasisimple
        (isQuasisimple_mulEquiv_local eE0.symm d.E_component.2.2))
    · intro z hz
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff (N := O) (E0.subtype z)).2
      exact hcenter_le_O hz
  let eRange : fE.range ≃* Ebar :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hfEsurj)).trans
      Subgroup.topEquiv
  let eQuot : (E0 ⧸ fE.ker) ≃* Ebar :=
    (QuotientGroup.quotientKerEquivRange fE).trans eRange
  let eCenterKer : (E0 ⧸ Subgroup.center E0) ≃*
      (E0 ⧸ fE.ker) :=
    QuotientGroup.quotientMulEquivOfEq
      (M := Subgroup.center E0) (N := fE.ker) hkerEcenter.symm
  let eEbar : (E0 ⧸ Subgroup.center E0) ≃* Ebar := eCenterKer.trans eQuot
  let eCenter : (E0 ⧸ Subgroup.center E0) ≃*
      (d.E ⧸ Subgroup.center d.E) :=
    QuotientGroup.congr (Subgroup.center E0) (Subgroup.center d.E)
      eE0 (map_center_eq_center_of_mulEquiv eE0)
  let eModel0 : (E0 ⧸ Subgroup.center E0) ≃* PSL2 K :=
    eCenter.trans e.some
  let eEbarPSL : Ebar ≃* PSL2 K := eEbar.symm.trans eModel0
  have hEbarCenter : Subgroup.center Ebar = ⊥ :=
    center_eq_bot_of_mulEquiv eEbarPSL (psl2_center_eq_bot K)
  have hEbarSylow : HasDihedralSylowTwo Ebar := by
    exact hasDihedralSylowTwo_of_mulEquiv eEbarPSL
      (psl2_odd_hasDihedralSylowTwo_model K hK')
  have hEbarNormal : Ebar.Normal := by
    dsimp [Ebar]
    exact Subgroup.Normal.map hE0normal qM hqMsurj
  have hQcore : pPrimeCore 2 (M0 ⧸ O) = ⊥ := by
    simpa [O] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := M0) 2)
  have hCbar : Subgroup.centralizer (Ebar : Set (M0 ⧸ O)) = ⊥ :=
    centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
      hQd hQcore Ebar hEbarNormal hEbarCenter hEbarSylow
  have hfkerleO : fmap.ker ≤ O := by
    intro m hm
    have hfmapone : fmap m = 1 := MonoidHom.mem_ker.mp hm
    have hautone : autPSL m = 1 := by
      calc
        autPSL m = semie (fmap m) := by simp [fmap]
        _ = semie 1 := by rw [hfmapone]
        _ = 1 := by simp
    have hqActionone : qAction m = 1 := by
      apply (MulAut.congr e.some).injective
      change MulAut.congr e.some (qAction m) = MulAut.congr e.some 1
      have hcongr_one : MulAut.congr e.some (1 : MulAut (d.E ⧸
          Subgroup.center d.E)) = 1 := by
        apply MulEquiv.ext
        intro x
        simp
      have hautone' : MulAut.congr e.some (qAction m) = 1 := by
        simpa [autPSL] using hautone
      exact hautone'.trans hcongr_one.symm
    have hqAutone : qAut (conjE m) = 1 := by
      simpa [qAction] using hqActionone
    have hdEperf : Group.IsPerfect d.E :=
      (Group.isPerfect_def).2 d.E_component.2.2.2.1
    have hdelta : ∀ x : d.E,
        (conjE m) x * x⁻¹ ∈ Subgroup.center d.E := by
      intro x
      have hqeq : QuotientGroup.mk' (Subgroup.center d.E) ((conjE m) x) =
          QuotientGroup.mk' (Subgroup.center d.E) x := by
        have hx := congrArg (fun a : MulAut (d.E ⧸ Subgroup.center d.E) =>
          a (QuotientGroup.mk' (Subgroup.center d.E) x)) hqAutone
        change qAut (conjE m)
            (QuotientGroup.mk' (Subgroup.center d.E) x) = _ at hx
        rw [quotientCenterAutomorphism_apply_mk] at hx
        exact hx
      have hqone : QuotientGroup.mk' (Subgroup.center d.E)
          ((conjE m) x * x⁻¹) = 1 := by
        calc
          QuotientGroup.mk' (Subgroup.center d.E) ((conjE m) x * x⁻¹) =
              QuotientGroup.mk' (Subgroup.center d.E) ((conjE m) x) *
                (QuotientGroup.mk' (Subgroup.center d.E) x)⁻¹ := by
                  rw [map_mul, map_inv]
          _ = 1 := by rw [hqeq]; simp
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center d.E)
        ((conjE m) x * x⁻¹)).mp hqone
    have hconjEone : conjE m = 1 := by
      exact central_automorphism_eq_one_local hdEperf (conjE m) 1 hdelta
    have hmcentE : ∀ z : E0, m * (z : M0) = (z : M0) * m := by
      intro z
      have hz := congrArg (fun a : d.E ≃* d.E => a (eE0 z))
        hconjEone
      have hz' : eE0 ((conj0 m) z) = eE0 z := by
        simpa [conjE] using hz
      have hz0 : (conj0 m) z = z := eE0.injective hz'
      have hconj := MulAut.conjNormal_apply (G := M0) (H := E0) m z
      have hconj' : m * (z : M0) * m⁻¹ = (z : M0) := by
        calc
          m * (z : M0) * m⁻¹ = ((conj0 m) z : M0) := by
            simpa [conj0] using hconj.symm
          _ = (z : M0) := congrArg Subtype.val hz0
      calc
        m * (z : M0) = (m * (z : M0) * m⁻¹) * m := by group
        _ = (z : M0) * m := by rw [hconj']
    have hmcent : m ∈ Subgroup.centralizer (E0 : Set M0) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hmcentE ⟨z, hz⟩).symm
    have hqcent : qM m ∈ Subgroup.centralizer (Ebar : Set (M0 ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
      have hcomm := (Subgroup.mem_centralizer_iff.mp hmcent) z hz
      have hcommq := congrArg qM hcomm
      simpa [map_mul, hzy] using hcommq
    have hqbot : qM m = 1 := by
      have : qM m ∈ (⊥ : Subgroup (M0 ⧸ O)) := by
        rw [← hCbar]
        exact hqcent
      exact Subgroup.mem_bot.mp this
    exact (QuotientGroup.eq_one_iff (N := O) m).mp hqbot
  have hfkerodd : Odd (Nat.card fmap.ker) := by
    exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hfkerleO)
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let : Finite fmap.range := inferInstance
  have hRangeD : HasDihedralSylowTwo fmap.range :=
    image_hasDihedralSylowTwo_of_odd_kernel hMdihedral fmap hfkerodd
  have hfieldodd : Odd (Nat.card
      (pGammaL2FieldProjection K fmap.range).range) :=
    pGammaL2_field_projection_range_odd_of_dihedral
      K hK' hcard fmap.range hPSL hRangeD
  have haction (m : M0) (x : d.E) :
      pGammaL2ToMulAutPSL2 K hK' hcard (fmap m)
          (e.some (QuotientGroup.mk' (Subgroup.center d.E) x)) =
        e.some (QuotientGroup.mk' (Subgroup.center d.E)
          ⟨(m : G) * (x : G) * (m : G)⁻¹,
            d.E_normal.2 (m : G) m.2 (x : G) x.2⟩) := by
    have hsemie : semie (fmap m) = autPSL m := by
      simp [fmap]
    change semie (fmap m)
        (e.some (QuotientGroup.mk' (Subgroup.center d.E) x)) = _
    rw [hsemie]
    change (MulAut.congr e.some (qAction m))
        (e.some (QuotientGroup.mk' (Subgroup.center d.E) x)) = _
    rw [MulAut.congr_apply]
    change e.some
        ((qAction m)
          (e.some.symm
            (e.some (QuotientGroup.mk' (Subgroup.center d.E) x)))) = _
    rw [e.some.symm_apply_apply]
    change e.some
        ((qAut (conjE m))
          (QuotientGroup.mk' (Subgroup.center d.E) x)) = _
    rw [quotientCenterAutomorphism_apply_mk]
    apply congrArg e.some
    apply congrArg (QuotientGroup.mk' (Subgroup.center d.E))
    apply Subtype.ext
    change (eE0 ((conj0 m) (eE0.symm x)) : G) =
      (m : G) * (x : G) * (m : G)⁻¹
    have hconj := MulAut.conjNormal_apply (G := M0) (H := E0)
      m (eE0.symm x)
    exact congrArg (fun z : M0 => (z : G)) hconj
  exact ⟨{
    primePower := hK'
    modelEquiv := e
    fieldCardGtThree := hcard
    f := fmap
    ker_odd := hfkerodd
    pslRange_le := hPSL
    range_dihedral := hRangeD
    fieldRange_odd := hfieldodd
    action_eq := haction }⟩

end CFSG.GorensteinWalter
