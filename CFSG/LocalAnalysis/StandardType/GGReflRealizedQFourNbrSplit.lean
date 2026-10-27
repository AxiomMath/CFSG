module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpAbsorb
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGRankOneTags
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

private theorem nsReal_ggOTwoPrime_subgroupOf_normal {G : Type} [Group G] [Finite G]
    (Y : Subgroup G) : ((ggOTwoPrime Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggOTwoPrime_le Y)]
  intro h g hh hg
  have hY : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh
  rw [ggOTwoPrime_map_conj, hY] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

private theorem nsReal_ggFixG_eq_ggHyperplane {G : Type} [Group G] (Bs : Subgroup G)
    (r : MulAut ↥Bs) : ggFixG Bs r = ggHyperplane Bs r := by
  have h : ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
    ext b; rfl
  rw [ggFixG, ggHyperplane, h]

private theorem nsReal_isPComponent_subgroupOf {G : Type} [Group G] [Finite G]
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

private theorem nsReal_isQuasisimple_of_levi
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
  obtain ⟨φ, hφinj, hφrange⟩ := s2jn_exists_sl2_range_rankOne hM i
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

theorem ggReflRealizedQFourNbrInput_split :
    ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 → GGSplitLie 3 L →
        ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → GGSplitLie 3 K →
          GGInnerDiagOnLabel GGLabQFour 3 Bs K → GGReflRealizedIn 3 Bs K := by
  intro G _ _ B Bs x L D J 𝒦 hcfg hsplit y K hnb hKsplit _hKq
  obtain ⟨t, n, f, ψ, hadm, h3rank, hker, _hrange, ht, hpf, htab⟩ :=
    s2jn_ggSecFiveKGPosNbrInput'_holds G 3 B Bs x L D J 𝒦 hcfg hsplit y K hnb hKsplit
  simp only [GGTableBPos] at htab
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := htab
  obtain ⟨hp, hp2, -⟩ := s2jn_ggKGPos_prime_rank_ge_four hcfg
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs_ea, -, -, -⟩ := hconf.tableB_facts
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  intro r hrA hr
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
  have hAind : (ggAutomizer K Bs : Set (MulAut ↥Bs)) ⊆ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨i, w, hw⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G 3 Bs hp hp2 hBs_ea hNT
    (ggAutomizer K Bs) hAind (Fin (ggU t n f).D.rank)
    (coxeterMatrix (ggU t n f).D.isFiniteType) hW.1 hnotG2 ε hεrefl ⟨r, hrA⟩ hr
  have hqs := nsReal_isQuasisimple_of_levi (p := 3) (f := f) (Bs := Bs) (X := K) hp hadm.2.1
    hpf (ggRankOneModel_of_tag ht hadm h3rank) hker hεlevi
      ⟨w, i, Subtype.ext_iff.mp hw⟩
  have hSle : ggRankOneIn K Bs r ≤ K ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    ggOTwoPrime_le _
  have hcompH : CFSG.Assembly.IsComponentOf (ggRankOneIn K Bs r)
      (K ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)) :=
    ⟨hSle, CFSG.Assembly.IsSubnormal.step hSle
        (nsReal_ggOTwoPrime_subgroupOf_normal _) (CFSG.Assembly.IsSubnormal.refl _), hqs.1⟩
  have hpc : CFSG.IsPComponent 3
      ((ggRankOneIn K Bs r).subgroupOf (K ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))) :=
    nsReal_isPComponent_subgroupOf hp hcompH hqs.2
  obtain ⟨g, hgK, hgN, hgr⟩ := eq_ggConjAut_of_mem_ggAutomizer hrA
  have hgC : g ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨b, hb, rfl⟩ := hz
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
  have hgY : g ∈ K ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := ⟨hgK, hgC⟩
  have hhOtwo : g ^ m ∈ ggRankOneIn K Bs r :=
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
  have hind : r ∈ ggInduced (ggRankOneIn K Bs r) Bs := ⟨g ^ m, hhOtwo, hhN, hhm⟩
  refine ⟨ggRankOneIn K Bs r, hind, ?_⟩
  rw [nsReal_ggFixG_eq_ggHyperplane Bs r]
  exact (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).mpr
    ⟨hSle, hpc⟩

end CFSG.StandardType

end
