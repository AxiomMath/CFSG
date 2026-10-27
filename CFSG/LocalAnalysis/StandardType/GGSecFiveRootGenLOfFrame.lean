module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpAbsorb
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGRankOneModel
import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
import CFSG.LocalAnalysis.StandardType.GGRankOneTags
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

private theorem ct_rg_sl2_range_rankOne {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup i := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hMcl : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hMcl
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

private theorem ct_rg_ggOTwoPrime_subgroupOf_normal {G : Type} [Group G] [Finite G]
    (Y : Subgroup G) : ((ggOTwoPrime Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggOTwoPrime_le Y)]
  intro h g hh hg
  have hY : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh
  rw [ggOTwoPrime_map_conj, hY] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

private theorem ct_rg_rankOneIn_isComponentOf {G : Type} [Group G] [Finite G]
    {Bs K Y : Subgroup G} {r : MulAut ↥Bs}
    (hK : CFSG.Assembly.IsComponentOf K Y)
    (hY : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Y)
    (hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn K Bs r)) :
    CFSG.Assembly.IsComponentOf (ggRankOneIn K Bs r)
      (Subgroup.centralizer (ggHyperplane Bs r : Set G)) := by
  set H := Subgroup.centralizer (ggHyperplane Bs r : Set G)
  have hSle : ggRankOneIn K Bs r ≤ K ⊓ H := ggOTwoPrime_le _
  have hKH : CFSG.Assembly.IsSubnormal (K ⊓ H) H := by
    have h := hK.2.1.inf H
    rwa [inf_eq_right.mpr hY] at h
  exact ⟨hSle.trans inf_le_right,
    CFSG.Assembly.IsSubnormal.step hSle (ct_rg_ggOTwoPrime_subgroupOf_normal (K ⊓ H)) hKH, hq⟩

private theorem ct_rg_ggFixG_eq_ggHyperplane {G : Type} [Group G] (Bs : Subgroup G)
    (r : MulAut ↥Bs) : ggFixG Bs r = ggHyperplane Bs r := by
  have h : ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
    ext b; rfl
  rw [ggFixG, ggHyperplane, h]

private theorem ct_rg_isPComponent_subgroupOf {G : Type} [Group G] [Finite G]
    {p : ℕ} {K H : Subgroup G} (hp : p.Prime)
    (hcomp : CFSG.Assembly.IsComponentOf K H) (hpK : p ∣ Nat.card ↥K) :
    CFSG.IsPComponent p (K.subgroupOf H) := by
  have : Fact p.Prime := ⟨hp⟩
  have hKH : K ≤ H := hcomp.1
  have hKn : CFSG.IsComponent (K.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKH).1 hcomp
  have hnot : ¬ (K.subgroupOf H) ≤ CFSG.pPrimeCore p ↥H := by
    intro hle
    have hdvd1 : p ∣ Nat.card ↥(K.subgroupOf H) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
    have hdvd2 : Nat.card ↥(K.subgroupOf H) ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H) :=
      Subgroup.card_dvd_of_le hle
    have hpd : p ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H) := hdvd1.trans hdvd2
    exact (hp.coprime_iff_not_dvd.mp (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H))) hpd
  exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le p hKn hnot

private theorem ct_rg_isQuasisimple_of_levi
    {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {K : Type} [Group K] {D : UniversalRootDatum K}
    (hp : p.Prime) (h1f : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hM : GGRankOneModel D (GaloisField 2 f))
    {ψ : K →* G} (hker : ψ.ker ≤ Subgroup.center K)
    {ε : (coxeterMatrix D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hlevi : ∀ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi D
          (weylAction D.isFiniteType w (Pi.single i 1))).map ψ)
    {r : MulAut ↥Bs}
    (hw : ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      r = ((ε (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹) :
        ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) ∧
      p ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
  obtain ⟨w, i, hw⟩ := hw
  have hlevi1 : ggRankOneIn X Bs ((ε ((coxeterMatrix D.isFiniteType).simple i) :
      ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (ggRootLevi D (Pi.single i 1)).map ψ := by
    have h := hlevi 1 i
    simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
    exact h
  have hr' : ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
      ((ε ((coxeterMatrix D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
        MulAut ↥Bs) * ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)⁻¹ = r := by
    rw [hw, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨g, -, -, hg⟩ := exists_ggRankOneIn_conj_of_mem_ggAutomizer (ε w).2
    ((ε ((coxeterMatrix D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
  rw [hr', hlevi1] at hg
  obtain ⟨φ, hφinj, hφrange⟩ := ct_rg_sl2_range_rankOne hM i
  have hθinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)) :=
    (MulAut.conj g).injective.comp (PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker)
  have hθrange : ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)).range = ggRankOneIn X Bs r := by
    rw [← hg, ← MonoidHom.map_range, ← MonoidHom.map_range ψ φ, hφrange]
    rfl
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    have hp1 : p ∣ 1 := by simpa using hpf
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  have hpq : p ∣ Nat.card (GaloisField 2 f) * (Nat.card (GaloisField 2 f) ^ 2 - 1) := by
    have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hpq' : p ∣ Nat.card (GaloisField 2 f) ^ 2 - 1 := by
      have h1 : Nat.card (GaloisField 2 f) ^ 2 - 1 =
          (Nat.card (GaloisField 2 f) + 1) * (Nat.card (GaloisField 2 f) - 1) := by
        rw [sq]; exact mul_self_tsub_one _
      rw [h1, hq] at *
      exact dvd_mul_of_dvd_right hpf _
    exact dvd_mul_of_dvd_right hpq' _
  refine ⟨?_, ?_⟩
  · rw [← hθrange]
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hθinj).symm hSL
  · rw [← hθrange, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv,
      CFSG.GorensteinWalter.sl2_card_formula]
    exact hpq

theorem ggSecFiveRootGenLInput_holds :
    GGSecFiveRootGenLInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit r hrA hr
  obtain ⟨t, n, f, ψ, hloc, -, htab⟩ :=
    s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hsplit
  simp only [GGTableBPos] at htab
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := htab
  obtain ⟨hp, hp2, hadm, h3rank⟩ := hloc.1
  obtain ⟨hker, hrange, ht, hpf⟩ := hloc.2.1
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs_ea, hxBs, -, -⟩ := hconf.tableB_facts
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.2.2.2.1
  have hW := ggTag_weylMatrix ht hadm
  have hcardι : 3 ≤ (ggU t n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3rank]
    exact h3rank
  have hnotG2 : ¬ ∃ e : Fin 2 ≃ Fin (ggU t n f).D.rank,
      coxeterMatrix (ggU t n f).D.isFiniteType = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, -⟩
    have hc := Fintype.card_congr e
    simp only [Fintype.card_fin] at hc
    omega
  have hAind : (ggAutomizer L Bs : Set (MulAut ↥Bs)) ⊆ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨i, w, hw⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs_ea hNT
    (ggAutomizer L Bs) hAind (Fin (ggU t n f).D.rank)
    (coxeterMatrix (ggU t n f).D.isFiniteType) hW.1 hnotG2 ε hεrefl ⟨r, hrA⟩ hr
  have hqs := ct_rg_isQuasisimple_of_levi (p := p) (f := f) (Bs := Bs) (X := L) hp hadm.2.1
    hpf (ggRankOneModel_of_tag ht hadm h3rank) hker hεlevi
      ⟨w, i, Subtype.ext_iff.mp hw⟩
  have hY : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ?_)
    exact ⟨⟨x, hxBs⟩, ggRM_AL_fixes_x hcfg hxBs r hrA, rfl⟩
  have hcompH : CFSG.Assembly.IsComponentOf (ggRankOneIn L Bs r)
      (Subgroup.centralizer (ggFixG Bs r : Set G)) := by
    rw [ct_rg_ggFixG_eq_ggHyperplane Bs r]
    exact ct_rg_rankOneIn_isComponentOf hLcomp hY hqs.1
  obtain ⟨g, hgL, hgN, hgr⟩ := eq_ggConjAut_of_mem_ggAutomizer hrA
  have hgC : g ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hb' : r b = b := by simpa [ggHyperplane] using hb
    have hfix : ggConjAut Bs hgN b = b := by rw [← hgr]; exact hb'
    have h1 : g * (b : G) * g⁻¹ = (b : G) := by
      have := congrArg (fun z : ↥Bs => (z : G)) hfix
      simpa [ggConjAut_apply] using this
    calc (b : G) * g = (g * (b : G) * g⁻¹) * g := by rw [h1]
      _ = g * (b : G) := by group
  have hm_ne : orderOf g ≠ 0 := (orderOf_pos g).ne'
  let m := ordCompl[2] (orderOf g)
  have hodd : Odd m := by
    change Odd (ordCompl[2] (orderOf g))
    refine Nat.not_even_iff_odd.mp ?_
    rw [even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hm_ne
  have hproj : 2 ^ (orderOf g).factorization 2 * m = orderOf g :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hpow2 : (g ^ m) ^ (2 ^ (orderOf g).factorization 2) = 1 := by
    rw [← pow_mul, mul_comm m, hproj, pow_orderOf_eq_one]
  have hgY : g ∈ L ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := ⟨hgL, hgC⟩
  have hhOtwo : g ^ m ∈ ggRankOneIn L Bs r :=
    Subgroup.subset_closure ⟨Subgroup.pow_mem _ hgY m, (orderOf g).factorization 2, hpow2⟩
  have hhN : g ^ m ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.pow_mem _ hgN m
  have hrm : r ^ m = r := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hr.1, one_pow, one_mul]
  have hhm : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = g ^ m * b * (g ^ m)⁻¹ := by
    intro b
    calc ((r b : ↥Bs) : G) = (((r ^ m) b : ↥Bs) : G) := by rw [hrm]
      _ = (((ggConjAut Bs hgN ^ m) b : ↥Bs) : G) := by rw [hgr]
      _ = g ^ m * b * (g ^ m)⁻¹ := ggConjAut_pow_apply Bs hgN m b
  have hind : r ∈ ggInduced (ggRankOneIn L Bs r) Bs := ⟨g ^ m, hhOtwo, hhN, hhm⟩
  refine ⟨ggRankOneIn L Bs r, hind, ?_, ?_⟩
  · rw [ct_rg_ggFixG_eq_ggHyperplane Bs r]
    exact (ggOTwoPrime_le _).trans inf_le_right
  · exact ct_rg_isPComponent_subgroupOf hp hcompH hqs.2

end CFSG.StandardType

end
