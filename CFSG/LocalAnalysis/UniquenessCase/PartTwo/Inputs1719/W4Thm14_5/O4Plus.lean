module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NaturalO4PlusSubnormal
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFourComponents
import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

theorem isL2_of_isSubnormal_isNaturalO4Plus {W : Type} [CommGroup W] [Finite W]
    {R L : Subgroup (MulAut W)} {e : ℕ} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hLR : CFSG.Open.IsSubnormal L R) (hnat : IsNaturalO4Plus R e) : IsL2 ↥L e := by
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    PartTwo.exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hq hLR hnat
  have hq' : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
  have := MinDegLow.nontrivial_of_isQuasisimple hq
  exact CFSG.Quasithin.H13.lieModel_psl_two_of_mulEquiv hq'.1 hK
    (φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))

private theorem map_conj_eq_of_conjSet_eq {A : Type*} [Group A] {R Y : Subgroup A}
    (hR1 : conjSet R Y = {R}) {g : A} (hg : g ∈ Y) :
    R.map (MulAut.conj g).toMonoidHom = R := by
  have h : R.map (MulAut.conj g).toMonoidHom ∈ conjSet R Y := ⟨g, hg, rfl⟩
  rw [hR1] at h
  exact h

private theorem commV_eq_top_of_conjSet_eq {W : Type} [CommGroup W] {R Y : Subgroup (MulAut W)}
    (hsum : IsDirSumOver (conjSet R Y) commV) (hR1 : conjSet R Y = {R}) : commV R = ⊤ := by
  rw [eq_top_iff, ← hsum.2]
  refine iSup_le fun X => ?_
  have hX : (X : Subgroup (MulAut W)) = R :=
    Set.mem_singleton_iff.mp ((Set.ext_iff.mp hR1 _).mp X.2)
  rw [hX]

theorem iSup_map_conj_eq_commutator {W : Type} [CommGroup W] [Finite W]
    {Y L R : Subgroup (MulAut W)} {e : ℕ} (hq : CFSG.Open.IsQuasisimple ↥L) (hRY : R ≤ Y)
    (hLR : CFSG.Open.IsSubnormal L R) (hnat : IsNaturalO4Plus R e)
    (hR1 : conjSet R Y = {R}) :
    (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) = ⁅R, R⁆ := by
  have hLR' : L ≤ R := hLR.le
  set H := ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom
  have hconjH : ∀ g ∈ Y, ∀ x ∈ L, g * x * g⁻¹ ∈ H := fun g hg x hx =>
    le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => L.map (MulAut.conj g).toMonoidHom) g hg le_rfl
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
  refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
  ·
    have hLg : L.map (MulAut.conj g).toMonoidHom ≤ R :=
      (Subgroup.map_mono hLR').trans (map_conj_eq_of_conjSet_eq hR1 hg).le
    have hperf : ⁅L, L⁆ = L := by
      have h := congrArg (Subgroup.map L.subtype) hq.1
      rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    calc L.map (MulAut.conj g).toMonoidHom = (⁅L, L⁆).map (MulAut.conj g).toMonoidHom := by
          rw [hperf]
      _ = ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ :=
          Subgroup.map_commutator _ _ _
      _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hLg hLg
  ·
    obtain ⟨K₀, _, _, hK₀, h4, -⟩ :=
      PartTwo.exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hq hLR hnat
    obtain ⟨K, _, _, _, hK, ⟨φ⟩⟩ := KO4Swap.exists_mulEquiv_determinantIsometries hnat
    have hK4 : 4 ≤ Nat.card K := by rw [hK, ← hK₀]; exact h4
    have hK2 : Nat.card K ≠ 2 := by omega
    have hK3 : Nat.card K ≠ 3 := by omega
    set X : Subgroup (DeterminantIsometries K) := (H.subgroupOf R).map φ.toMonoidHom
    have hLX : (L.subgroupOf R).map φ.toMonoidHom ≤ X := by
      refine Subgroup.map_mono fun x hx => ?_
      have hx' := hconjH 1 Y.one_mem _ (Subgroup.mem_subgroupOf.mp hx)
      rw [one_mul, inv_one, mul_one] at hx'
      exact Subgroup.mem_subgroupOf.mpr hx'
    have htauX : ∀ y ∈ (L.subgroupOf R).map φ.toMonoidHom, tau * y * tau⁻¹ ∈ X := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨φ.symm tau * l * (φ.symm tau)⁻¹, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hconjH _ (hRY (φ.symm tau).2) _ (Subgroup.mem_subgroupOf.mp hl)
    have htau' : (tau : DeterminantIsometries K)⁻¹ ∉ specialImage K := fun h =>
      tau_notMem_specialImage (by simpa using (specialImage K).inv_mem h)
    have hJX : specialImage K ≤ X := by
      rw [← determinantFactors_sup]
      rcases eq_left_or_right_of_isSubnormal hK4 (KO4Swap.isQuasisimple_map φ hq hLR')
          (KO4Swap.isSubnormal_map φ hLR) with h | h
      · rw [h] at hLX htauX
        refine sup_le hLX fun x hx => ?_
        simpa [mul_assoc] using htauX _ (conj_mem_determinantLeftFactor htau' hx)
      · rw [h] at hLX htauX
        refine sup_le (fun x hx => ?_) hLX
        simpa [mul_assoc] using htauX _ (conj_mem_determinantRightFactor htau' hx)
    have hcomm : commutator ↥R ≤ H.subgroupOf R := by
      have h1 : (commutator ↥R).map φ.toMonoidHom = commutator (DeterminantIsometries K) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ φ.surjective]
      refine (Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp ?_
      rw [h1, determinant_commutator_eq hK2 hK3]
      exact hJX
    calc ⁅R, R⁆ = (commutator ↥R).map R.subtype := by
          rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype]
      _ ≤ (H.subgroupOf R).map R.subtype := Subgroup.map_mono hcomm
      _ ≤ H := by
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_le_left

theorem isOmegaPlus_natOmegaPlus_commutator {W : Type} [CommGroup W]
    {R : Subgroup (MulAut W)} {e : ℕ} (hnat : IsNaturalO4Plus R e) (hR : commV R = ⊤) :
    IsOmegaPlus ↥⁅R, R⁆ 4 e ∧ NatOmegaPlus ⁅R, R⁆ ⊤ ⊥ 4 e := by
  obtain ⟨K, _, _, hK, hreal₀⟩ := hnat
  rw [hR] at hreal₀
  obtain ⟨π, hπ⟩ : ∃ π : ↥(CFSG.PGLModel.orthogonalPlus 2 K) →* ↥R,
      (FFModel.nat (CFSG.PGLModel.orthogonalPlus 2 K)).RealizesVia R ⊤ ⊥ π := hreal₀
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := e) (by
    rw [← Nat.card_eq_fintype_card]
    exact hK)
  have hΩ : StatedOmega (StatedQuadPlus 2 K) =
      ⁅CFSG.PGLModel.orthogonalPlus 2 K, CFSG.PGLModel.orthogonalPlus 2 K⁆ := rfl
  have hΩΓ : StatedOmega (StatedQuadPlus 2 K) ≤ CFSG.PGLModel.orthogonalPlus 2 K := by
    rw [hΩ, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have h1 :
      (Subgroup.inclusion hΩΓ).range = commutator ↥(CFSG.PGLModel.orthogonalPlus 2 K) := by
    rw [Subgroup.inclusion_range]
    apply Subgroup.map_injective (CFSG.PGLModel.orthogonalPlus 2 K).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hΩΓ, _root_.commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hΩ
  have h2 : (commutator ↥(CFSG.PGLModel.orthogonalPlus 2 K)).map π = commutator ↥R := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ.1]
  have hrange : (R.subtype.comp (π.comp (Subgroup.inclusion hΩΓ))).range = ⁅R, R⁆ := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, h1, h2, _root_.commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let π' : ↥(StatedOmega (StatedQuadPlus 2 K)) →* ↥⁅R, R⁆ :=
    (R.subtype.comp (π.comp (Subgroup.inclusion hΩΓ))).codRestrict ⁅R, R⁆ fun γ => by
      rw [← hrange]
      exact ⟨γ, rfl⟩
  have hsurj : Function.Surjective π' := by
    intro h
    have hh : (h : MulAut W) ∈ (R.subtype.comp (π.comp (Subgroup.inclusion hΩΓ))).range := by
      rw [hrange]
      exact h.2
    obtain ⟨γ, hγ⟩ := hh
    exact ⟨γ, Subtype.ext hγ⟩
  have hreal :
      (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))).RealizesVia ⁅R, R⁆ ⊤ ⊥ π' := by
    obtain ⟨-, hZU, hkersec, -, -, -, hker, β, hβs, hβk, hβe⟩ := hπ
    refine ⟨hsurj, hZU, hkersec, fun _ _ _ => Subgroup.mem_top _, fun h z hz => ?_,
      fun _ _ _ => Subgroup.mem_top _, fun γ m hm => hker (Subgroup.inclusion hΩΓ γ) m hm,
      β, hβs, hβk, fun γ u m hu hm hβu => hβe (Subgroup.inclusion hΩΓ γ) u m hu hm hβu⟩
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hinj : Function.Injective π' :=
    CFSG.Quasithin.G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hreal
  have hbot := CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
    (K := K) (n := 2) (by norm_num)
  exact ⟨⟨⟨2, rfl⟩, K, inferInstance, inferInstance, hK,
      ⟨(MulEquiv.ofBijective π' ⟨hinj, hsurj⟩).symm.trans
        (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot)⟩⟩,
    ⟨⟨2, rfl⟩, K, inferInstance, inferInstance, hK, π', hreal⟩⟩

theorem o4Plus_of_conjSet_eq
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {W : Type} [CommGroup W] [Finite W] {Y L T P R H : Subgroup (MulAut W)} {e n : ℕ}
    (hO2 : O2Trivial Y) (hL : IsComponentOf L Y) (hT : IsSylowIn 2 T Y)
    (hPL : P ≤ L) (hinf : Hinf P ≠ ⊥)
    (hnorm : normIn T L ≤ normalizer (P : Set (MulAut W))) (hN : NParam (Hinf P) n)
    (hH : H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (hRY : R ≤ Y) (hsum : IsDirSumOver (conjSet R Y) commV)
    (hLR : CFSG.Open.IsSubnormal L R) (hnat : IsNaturalO4Plus R e)
    (hR1 : conjSet R Y = {R}) :
    P = L ∧ n = e ∧ IsNaturalClassicalModule H n := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hL2 : IsL2 ↥L e := isL2_of_isSubnormal_isNaturalO4Plus hq hLR hnat
  have hPeq : P = L := eq_of_rankOne hO2 hL hT (Or.inl hL2) hPL hinf hnorm
  rw [hPeq, hinf_eq_self hq] at hN
  have hn : n = e := nParam_eq_of_isL2 hSz hq hL2 hN
  refine ⟨hPeq, hn, ?_⟩
  rw [hn, hH, iSup_map_conj_eq_commutator hq hRY hLR hnat hR1]
  exact Or.inr (Or.inr (Or.inl (isOmegaPlus_natOmegaPlus_commutator hnat
    (commV_eq_top_of_conjSet_eq hsum hR1))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
