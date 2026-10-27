module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpAbsorb
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem nsRG_ggOTwoPrime_subgroupOf_normal {G : Type} [Group G] [Finite G]
    (Y : Subgroup G) : ((ggOTwoPrime Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggOTwoPrime_le Y)]
  intro h g hh hg
  have hY : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh
  rw [ggOTwoPrime_map_conj, hY] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

private theorem nsRG_rankOneIn_isComponentOf {G : Type} [Group G] [Finite G]
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
    CFSG.Assembly.IsSubnormal.step hSle (nsRG_ggOTwoPrime_subgroupOf_normal (K ⊓ H)) hKH, hq⟩

private theorem nsRG_ggFixG_eq_ggHyperplane {G : Type} [Group G] (Bs : Subgroup G)
    (r : MulAut ↥Bs) : ggFixG Bs r = ggHyperplane Bs r := by
  have h : ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
    ext b; rfl
  rw [ggFixG, ggHyperplane, h]

private theorem nsRG_isPComponent_subgroupOf {G : Type} [Group G] [Finite G]
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

theorem nsRealized_of_quasisimple_rankOne {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hr : GGIsReflection p r) (hqs : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r))
    (hpd : p ∣ Nat.card ↥(ggRankOneIn L Bs r)) : GGRealized p Bs r := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, -, hxBs, -, -⟩ := hconf.tableB_facts
  have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.2.2.2.1
  have hqs' : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) ∧ p ∣ Nat.card ↥(ggRankOneIn L Bs r) :=
    ⟨hqs, hpd⟩
  have hqs := hqs'
  have hY : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ?_)
    exact ⟨⟨x, hxBs⟩, ggRM_AL_fixes_x hcfg hxBs r hrA, rfl⟩
  have hcompH : CFSG.Assembly.IsComponentOf (ggRankOneIn L Bs r)
      (Subgroup.centralizer (ggFixG Bs r : Set G)) := by
    rw [nsRG_ggFixG_eq_ggHyperplane Bs r]
    exact nsRG_rankOneIn_isComponentOf hLcomp hY hqs.1
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
  · rw [nsRG_ggFixG_eq_ggHyperplane Bs r]
    exact (ggOTwoPrime_le _).trans inf_le_right
  · exact nsRG_isPComponent_subgroupOf hp hcompH hqs.2


namespace NSJoin

@[expose] def NSRankOneLInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r →
        CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) ∧ p ∣ Nat.card ↥(ggRankOneIn L Bs r)

@[expose] def NSRankOneLInput : Prop :=
  NSRankOneLInputOf NSTypeAD

theorem nsRootGenLInput_of_rankOne {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hR : NSRankOneLInputOf T) : NSRootGenLInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg r hrA hr
  obtain ⟨hqs, hpd⟩ := hR G p B Bs x L D J 𝒦 hcfg r hrA hr
  exact nsRealized_of_quasisimple_rankOne (ggSecFiveRouteCfg'_of_routeCfg hcfg.1) hrA hr hqs hpd

end NSJoin

end CFSG.StandardType

end
