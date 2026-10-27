module

public import CFSG.LocalAnalysis.StandardType.GGF4N2CentralImageE6
public import CFSG.LocalAnalysis.StandardType.GGF4N2CentralImageE6Marked
public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartDefs
public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDefs
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphFamily
import CFSG.RankThree.PartTwo.Census.Exceptional.Minuscule
import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAmalgam
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
import CFSG.Permutation.FiveTransitive.PrimeFreeOrderLift
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestLift
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType.N2InternalFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.N2Chart
open CFSG.StandardType.N2E6Native

local notation "E6sc" => e6Data_valid.minGroup F4

local instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance e6RankNeZero : NeZero CFSG.Blueprint.Chevalley.Tag.E6.rank := ⟨by decide⟩


theorem card_center_e6_four : Nat.card (Subgroup.center E6sc) = 3 := by
  have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F4).1
  have hF : Nat.card F4 = 4 := by
    simpa using GaloisField.card 2 2 (by decide)
  simpa [hF] using h

theorem eq_one_of_mem_center_of_pow_five {z : E6sc}
    (hz : z ∈ Subgroup.center E6sc) (hz5 : z ^ 5 = 1) : z = 1 := by
  let x : Subgroup.center E6sc := ⟨z, hz⟩
  have h3 : orderOf x ∣ 3 := by
    have h := orderOf_dvd_natCard x
    rwa [card_center_e6_four] at h
  have h5 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    exact hz5)
  have h1 : orderOf x = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h3 h5)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

theorem not_five_dvd_card_ker {G : Type} [Group G] (psi : E6sc →* G)
    (hker : psi.ker ≤ Subgroup.center E6sc) : ¬ 5 ∣ Nat.card psi.ker := by
  have hd := Subgroup.card_dvd_of_le hker
  rw [card_center_e6_four] at hd
  intro h5
  have h := h5.trans hd
  norm_num at h

theorem orderOf_map_eq_five {G : Type} [Group G] (psi : E6sc →* G)
    (hker : psi.ker ≤ Subgroup.center E6sc) {a : E6sc} (ha : orderOf a = 5) :
    orderOf (psi a) = 5 := by
  have ha5 : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  apply orderOf_eq_prime
  · rw [← map_pow, ha5, map_one]
  · intro h1
    have ha1 : a = 1 := eq_one_of_mem_center_of_pow_five
      (hker (MonoidHom.mem_ker.mpr h1)) ha5
    rw [ha1, orderOf_one] at ha
    norm_num at ha

theorem exists_adjoint_five_in_highRoot :
    ∃ a : adjointGroup .E6 F4,
      a ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E6 F4).subgroupOf
        (adjointGroup .E6 F4) ∧ orderOf a = 5 := by
  obtain ⟨P, hP, -, hcard⟩ :=
    CFSG.SeitzReduction.E6Pilot.exists_nonsplit_le_subgroupOf_highRootSL2
      (τ := .E6) (K := F4)
  have hP5 : Nat.card P = 5 := by
    have hF : Nat.card F4 = 4 := by simpa using GaloisField.card 2 2 (by decide)
    simpa [hF] using hcard
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP5])
  exact ⟨a, hP a.property, (Subgroup.orderOf_coe a).trans ha⟩

theorem isRoot_nativeTheta : IsRoot .E6 (e6NativeGamma 3) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

theorem coe_e6Isogeny_of_pinned_rootSL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {alpha : Fin Tag.E6.rank → ℤ} (halpha : IsRoot .E6 alpha)
    (rho : Matrix.SpecialLinearGroup (Fin 2) F →* e6Data_valid.minGroup F)
    (hupper : ∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) =
      e6Data_valid.xm F alpha c)
    (hlower : ∀ c, rho (sl2Lower c) = e6Data_valid.xm F (-alpha) c)
    (s : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((e6Isogeny F (rho s) : adjointGroup .E6 F) : ModGL .E6 F) =
      rootSL2 .E6 F alpha s := by
  have hext : (adjointGroup .E6 F).subtype.comp ((e6Isogeny F).comp rho) =
      rootSL2 .E6 F alpha := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change ((e6Isogeny F (rho (CFSG.RankThree.CentralCover.sl2Upper c)) :
          adjointGroup .E6 F) : ModGL .E6 F) = rootSL2 .E6 F alpha (uSL c)
      rw [hupper, CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm halpha,
        CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo halpha]
    · change ((e6Isogeny F (rho (sl2Lower c)) : adjointGroup .E6 F) :
          ModGL .E6 F) = rootSL2 .E6 F alpha (vSL c)
      rw [hlower, CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm (IsRoot.neg halpha),
        CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo halpha]
  exact DFunLike.congr_fun hext s

theorem e6Isogeny_pinned_native_highRootSL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (rho : Matrix.SpecialLinearGroup (Fin 2) F →* e6Data_valid.minGroup F)
    (hupper : ∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) =
      e6Data_valid.xm F (e6NativeGamma 3) c)
    (hlower : ∀ c, rho (sl2Lower c) = e6Data_valid.xm F (-e6NativeGamma 3) c)
    (s : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((e6Isogeny F (rho s) : adjointGroup .E6 F) : ModGL .E6 F) =
      rootSL2 .E6 F (e6NativeGamma 3) s :=
  coe_e6Isogeny_of_pinned_rootSL2 isRoot_nativeTheta rho hupper hlower s

theorem nativeTheta_strongly_orthogonal (j : Fin Tag.E6.rank) (hj : j ≠ 1) :
    e6NativeGamma 3 + Pi.single j 1 ≠ 0 ∧ e6NativeGamma 3 - Pi.single j 1 ≠ 0 ∧
      ¬ IsRoot .E6 (e6NativeGamma 3 + Pi.single j 1) ∧
      ¬ IsRoot .E6 (e6NativeGamma 3 - Pi.single j 1) := by
  have h : ∀ j : Fin Tag.E6.rank, j ≠ 1 →
      e6NativeGamma 3 + Pi.single j 1 ≠ 0 ∧ e6NativeGamma 3 - Pi.single j 1 ≠ 0 ∧
        ¬ IsRoot .E6 (e6NativeGamma 3 + Pi.single j 1) ∧
        ¬ IsRoot .E6 (e6NativeGamma 3 - Pi.single j 1) := by
    simp_rw [isRoot_iff_mem_artifactRoots]
    decide +kernel
  exact h j hj

theorem exists_pinned_native_highRootSL2 :
    ∃ rho : Matrix.SpecialLinearGroup (Fin 2) F4 →* E6sc,
      Function.Injective rho ∧
      (∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) = e6Data_valid.xm F4 (e6NativeGamma 3) c) ∧
      (∀ c, rho (sl2Lower c) = e6Data_valid.xm F4 (-e6NativeGamma 3) c) ∧
      ∀ A, rho A ∈ e6Data_valid.rootGroup F4 (e6NativeGamma 3) ⊔
        e6Data_valid.rootGroup F4 (-e6NativeGamma 3) := by
  let hV := e6Data_valid
  obtain ⟨j, N, sigma, sigma', hsigma, hsigma', htransport⟩ :=
    CFSG.RankThree.PartTwo.Census.Exceptional.exists_weyl_transport hV F4 isRoot_nativeTheta
  have hneg : (-1 : F4) = 1 := neg_eq_of_add_eq_zero_left (by
    simpa only [one_add_one_eq_two, Nat.cast_ofNat] using CharP.cast_eq_zero F4 2)
  have hs : sigma = 1 := by
    rcases hsigma with h | h
    · exact h
    · exact h.trans hneg
  have hs' : sigma' = 1 := by
    rcases hsigma' with h | h
    · exact h
    · exact h.trans hneg
  have hlower : ∀ c : F4,
      CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2 hV F4 j (sl2Lower c) =
        hV.xm F4 (-Pi.single j 1) c := by
    intro c
    apply hV.endo_injective F4
    rw [CFSG.RankThree.PartTwo.Census.Exceptional.endo_simpleSL2, hV.endo_xm,
      coe_sl2Lower, hV.blockOp_lower]
  let rho := (MulAut.conj N).toMonoidHom.comp
    (CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2 hV F4 j)
  refine ⟨rho, (MulAut.conj N).injective.comp
    (CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2_injective hV F4 j), ?_, ?_, ?_⟩
  · intro c
    change N * CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2 hV F4 j
      (CFSG.RankThree.CentralCover.sl2Upper c) * N⁻¹ = _
    rw [CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2_upper]
    simpa only [hs, one_mul] using (htransport c).1
  · intro c
    change N * CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2 hV F4 j (sl2Lower c) * N⁻¹ = _
    rw [hlower]
    simpa only [hs', one_mul] using (htransport c).2
  · intro A
    have hle : (hV.rootGroup F4 (Pi.single j 1) ⊔ hV.rootGroup F4 (-Pi.single j 1)).map
        (MulAut.conj N).toMonoidHom ≤
        hV.rootGroup F4 (e6NativeGamma 3) ⊔ hV.rootGroup F4 (-e6NativeGamma 3) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup
        (CFSG.RankThree.PartTwo.Census.Exceptional.map_conj_rootGroup_le hV F4 fun c => (htransport c).1)
        (CFSG.RankThree.PartTwo.Census.Exceptional.map_conj_rootGroup_le hV F4 fun c => (htransport c).2)
    exact hle ⟨_, CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2_mem hV F4 j A, rfl⟩

theorem native_highRoot_le_centralizer_firstA5 :
    e6Data_valid.rootGroup F4 (e6NativeGamma 3) ⊔
      e6Data_valid.rootGroup F4 (-e6NativeGamma 3) ≤
        Subgroup.centralizer ((CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
          CFSG.SeitzReduction.F4Pilot.e6A5Nodes : Subgroup E6sc) : Set E6sc) := by
  rw [Subgroup.le_centralizer_iff]
  unfold CFSG.LieType.CurtisTits.levi
  refine iSup_le fun j => iSup_le fun hj => ?_
  have hj1 : j ≠ 1 := CFSG.SeitzReduction.F4Pilot.ne_one_of_mem_e6A5Nodes hj
  obtain ⟨h1, h2, h3, h4⟩ := nativeTheta_strongly_orthogonal j hj1
  exact Subgroup.le_centralizer_iff.mp
    (CFSG.RankThree.PartTwo.Census.Exceptional.rankOne_le_centralizer e6Data_valid F4
      isRoot_nativeTheta (IsRoot.basis (τ := .E6) j) h1 h2 h3 h4)

theorem map_firstA5_eq_range {G : Type} [Group G]
    (psi : Matrix.SpecialLinearGroup (Fin 6) F4 →* G)
    (hpsi : psi.ker ≤ Subgroup.center _) (Psi : E6sc →* G)
    (h0 : (CFSG.LieType.CurtisTits.rankOne (e6Datum F4).rootGroup 0).map Psi =
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 0).range.map psi)
    (h2 : (CFSG.LieType.CurtisTits.rankOne (e6Datum F4).rootGroup 2).map Psi =
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 1).range.map psi)
    (h3 : (CFSG.LieType.CurtisTits.rankOne (e6Datum F4).rootGroup 3).map Psi =
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 2).range.map psi)
    (h4 : (CFSG.LieType.CurtisTits.rankOne (e6Datum F4).rootGroup 4).map Psi =
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi)
    (h5 : (CFSG.LieType.CurtisTits.rankOne (e6Datum F4).rootGroup 5).map Psi =
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 4).range.map psi) :
    (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
      CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi = psi.range := by
  let V : Fin 5 → Subgroup G := fun i =>
    (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 i).range.map psi
  have hm : ∀ j : Fin Tag.E6.rank, j ≠ 1 → j ∈ CFSG.SeitzReduction.F4Pilot.e6A5Nodes := by
    decide +kernel
  have hgen : (⨆ i, V i) = psi.range := (ggStdChain_map_of_ker_le_center psi hpsi).2.2
  rw [← hgen]
  simp only [CFSG.LieType.CurtisTits.levi, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    fin_cases j
    · exact h0.le.trans (le_iSup V 0)
    · exact (CFSG.SeitzReduction.F4Pilot.ne_one_of_mem_e6A5Nodes hj rfl).elim
    · exact h2.le.trans (le_iSup V 1)
    · exact h3.le.trans (le_iSup V 2)
    · exact h4.le.trans (le_iSup V 3)
    · exact h5.le.trans (le_iSup V 4)
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_iSup_of_le (0 : Fin 6)
        (le_iSup_of_le (hm 0 (by decide)) h0.symm.le)
    · exact le_iSup_of_le (2 : Fin 6)
        (le_iSup_of_le (hm 2 (by decide)) h2.symm.le)
    · exact le_iSup_of_le (3 : Fin 6)
        (le_iSup_of_le (hm 3 (by decide)) h3.symm.le)
    · exact le_iSup_of_le (4 : Fin 6)
        (le_iSup_of_le (hm 4 (by decide)) h4.symm.le)
    · exact le_iSup_of_le (5 : Fin 6)
        (le_iSup_of_le (hm 5 (by decide)) h5.symm.le)

theorem exists_internal_five_of_given_Psi {G : Type} [Group G]
    (Psi : E6sc →* G) (hker : Psi.ker ≤ Subgroup.center E6sc) {K : Subgroup G}
    (hA5 : (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
      CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi = K)
    (t : Matrix.SpecialLinearGroup (Fin 2) F4) (ht : orderOf t = 5) :
    ∃ rho : Matrix.SpecialLinearGroup (Fin 2) F4 →* E6sc, Function.Injective rho ∧
      (∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) =
        e6Data_valid.xm F4 (e6NativeGamma 3) c) ∧
      (∀ c, rho (sl2Lower c) = e6Data_valid.xm F4 (-e6NativeGamma 3) c) ∧
      (∀ A, rho A ∈ Subgroup.centralizer ((CFSG.LieType.CurtisTits.levi
        (e6Datum F4).rootGroup CFSG.SeitzReduction.F4Pilot.e6A5Nodes : Subgroup E6sc) : Set E6sc)) ∧
      Psi (rho t) ∈ Psi.range ∧ Psi (rho t) ∈ Subgroup.centralizer (K : Set G) ∧
      orderOf (Psi (rho t)) = 5 := by
  obtain ⟨rho, hinj, hupper, hlower, hroot⟩ := exists_pinned_native_highRootSL2
  have hcent : ∀ A, rho A ∈ Subgroup.centralizer ((CFSG.LieType.CurtisTits.levi
      (e6Datum F4).rootGroup CFSG.SeitzReduction.F4Pilot.e6A5Nodes : Subgroup E6sc) : Set E6sc) :=
    fun A => native_highRoot_le_centralizer_firstA5 (hroot A)
  refine ⟨rho, hinj, hupper, hlower, hcent, ⟨rho t, rfl⟩, ?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hk' : k ∈ (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
        CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi := by rw [hA5]; exact hk
    obtain ⟨u, hu, rfl⟩ := hk'
    have hc := Subgroup.mem_centralizer_iff.mp (hcent t) u hu
    simpa only [map_mul] using congrArg Psi hc
  · exact orderOf_map_eq_five Psi hker ((orderOf_injective rho hinj t).trans ht)

theorem exists_internal_five_of_twoSL6Charts_of_t {G : Type} [Group G]
    (psi1 psi2 : Matrix.SpecialLinearGroup (Fin 6) F4 →* G)
    (h1 : psi1.ker ≤ Subgroup.center _) (h2 : psi2.ker ≤ Subgroup.center _)
    (hJ : psi1.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)) =
      psi2.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)))
    (hM : ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi1,
      ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi2,
        a * b = b * a)
    (t : Matrix.SpecialLinearGroup (Fin 2) F4) (ht : orderOf t = 5) :
    ∃ Psi : E6sc →* G, Psi.ker ≤ Subgroup.center E6sc ∧
      Psi.range = psi1.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi2 ∧
      (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
        CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi = psi1.range ∧
      ∃ rho : Matrix.SpecialLinearGroup (Fin 2) F4 →* E6sc, Function.Injective rho ∧
        (∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) =
          e6Data_valid.xm F4 (e6NativeGamma 3) c) ∧
        (∀ c, rho (sl2Lower c) = e6Data_valid.xm F4 (-e6NativeGamma 3) c) ∧
        (∀ A, rho A ∈ Subgroup.centralizer ((CFSG.LieType.CurtisTits.levi
          (e6Datum F4).rootGroup CFSG.SeitzReduction.F4Pilot.e6A5Nodes : Subgroup E6sc) : Set E6sc)) ∧
        Psi (rho t) ∈ psi1.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi2 ∧
        Psi (rho t) ∈ Subgroup.centralizer (psi1.range : Set G) ∧ orderOf (Psi (rho t)) = 5 := by
  obtain ⟨Psi, hker, hrange, hnodes⟩ :=
    ggE6Psi_of_twoSL6Charts (by decide : 2 ≤ 2) psi1 psi2 h1 h2 hJ hM
  change E6sc →* G at Psi
  have hA5 := map_firstA5_eq_range psi1 h1 Psi
    (hnodes 0) (hnodes 2) (hnodes 3) (hnodes 4) (hnodes 5)
  obtain ⟨rho, hinj, hupper, hlower, hcent, hX, hK, horder⟩ :=
    exists_internal_five_of_given_Psi Psi hker hA5 t ht
  exact ⟨Psi, hker, hrange, hA5, rho, hinj, hupper, hlower, hcent, hrange ▸ hX, hK, horder⟩

theorem exists_internal_five_of_twoSL6Charts_marked_of_t {G : Type} [Group G]
    (psi1 psi2 : Matrix.SpecialLinearGroup (Fin 6) F4 →* G)
    (h1 : psi1.ker ≤ Subgroup.center _) (h2 : psi2.ker ≤ Subgroup.center _)
    (hJ : psi1.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)) =
      psi2.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)))
    (hM : ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi1,
      ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi2,
        a * b = b * a)
    (t : Matrix.SpecialLinearGroup (Fin 2) F4) (ht : orderOf t = 5) :
    ∃ Psi : E6sc →* G, Psi.ker ≤ Subgroup.center E6sc ∧
      Psi.range = psi1.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi2 ∧
      Psi.comp (CFSG.SeitzReduction.F4Pilot.slToE6Sc F4) = psi1 ∧
      (∀ k : Fin 5, Psi.comp (CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2
        e6Data_valid F4 (CFSG.SeitzReduction.E6Pilot.chainNode k)) =
        psi1.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 k)) ∧
      Psi.comp (CFSG.RankThree.PartTwo.Census.Exceptional.simpleSL2 e6Data_valid F4 1) =
        psi2.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3) ∧
      (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
        CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi = psi1.range ∧
      ∃ rho : Matrix.SpecialLinearGroup (Fin 2) F4 →* E6sc, Function.Injective rho ∧
        (∀ c, rho (CFSG.RankThree.CentralCover.sl2Upper c) =
          e6Data_valid.xm F4 (e6NativeGamma 3) c) ∧
        (∀ c, rho (sl2Lower c) = e6Data_valid.xm F4 (-e6NativeGamma 3) c) ∧
        (∀ A, rho A ∈ Subgroup.centralizer ((CFSG.LieType.CurtisTits.levi
          (e6Datum F4).rootGroup CFSG.SeitzReduction.F4Pilot.e6A5Nodes : Subgroup E6sc) : Set E6sc)) ∧
        Psi (rho t) ∈ psi1.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi2 ∧
        Psi (rho t) ∈ Subgroup.centralizer (psi1.range : Set G) ∧ orderOf (Psi (rho t)) = 5 ∧
        ∀ s, ((e6Isogeny F4 (rho s) : adjointGroup .E6 F4) : ModGL .E6 F4) =
          rootSL2 .E6 F4 (e6NativeGamma 3) s := by
  obtain ⟨Psi, hker, hrange, hsl6, hchain, hbranch⟩ :=
    ggE6Psi_of_twoSL6Charts_marked (by decide : 2 ≤ 2) psi1 psi2 h1 h2 hJ hM
  change E6sc →* G at Psi
  have hsl6' : Psi.comp (CFSG.SeitzReduction.F4Pilot.slToE6Sc F4) = psi1 := hsl6
  have hA5 : (CFSG.LieType.CurtisTits.levi (e6Datum F4).rootGroup
      CFSG.SeitzReduction.F4Pilot.e6A5Nodes).map Psi = psi1.range := by
    have h := congrArg MonoidHom.range hsl6'
    rw [MonoidHom.range_comp, CFSG.SeitzReduction.F4Pilot.range_slToE6Sc] at h
    exact h
  obtain ⟨rho, hinj, hupper, hlower, hcent, hX, hK, horder⟩ :=
    exists_internal_five_of_given_Psi Psi hker hA5 t ht
  exact ⟨Psi, hker, hrange, hsl6', hchain, hbranch, hA5,
    rho, hinj, hupper, hlower, hcent, hrange ▸ hX, hK, horder,
    e6Isogeny_pinned_native_highRootSL2 rho hupper hlower⟩

theorem exists_internal_five_of_twoSL6Charts {G : Type} [Group G]
    (psi1 psi2 : Matrix.SpecialLinearGroup (Fin 6) F4 →* G)
    (h1 : psi1.ker ≤ Subgroup.center _) (h2 : psi2.ker ≤ Subgroup.center _)
    (hJ : psi1.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)) =
      psi2.comp (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 4 0 (by norm_num)))
    (hM : ∀ a ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi1,
      ∀ b ∈ (CFSG.ClassicalInvolution.WeakCT.blockSL F4 6 3 3 (by norm_num)).range.map psi2,
        a * b = b * a) :
    ∃ a : G,
      a ∈ psi1.range ⊔ (CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 3).range.map psi2 ∧
      a ∈ Subgroup.centralizer (psi1.range : Set G) ∧ orderOf a = 5 := by
  obtain ⟨t, ht⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F4)
  have ht5 : orderOf t = 5 := by
    have hF : Nat.card F4 = 4 := by simpa using GaloisField.card 2 2 (by decide)
    simpa [hF] using ht
  obtain ⟨Psi, -, -, -, rho, -, -, -, -, hX, hK, horder⟩ :=
    exists_internal_five_of_twoSL6Charts_of_t psi1 psi2 h1 h2 hJ hM t ht5
  exact ⟨Psi (rho t), hX, hK, horder⟩

end CFSG.StandardType.N2InternalFive
