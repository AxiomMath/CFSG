module

public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import Certificates.Certificate1952
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13722
import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8
import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
import CFSG.LieType.SeitzGeneration.ExcTorusE8One
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem ggE8LangModelAux_finish {τ : Tag} {R p : ℕ} [NeZero p] {C : Type} [Group C]
    {hR : R = τ.rank} {π : Equiv.Perm (Fin R)} {D : LangDatum τ GGL} {ι₀ : C →* ModGL τ GGL}
    {ζ : GGLˣ} (hT : GGTorusData hR p π D ι₀ ζ) (c : C) (c₀ : ModGL τ GGL) (hc₀ : c₀ ∈ D.fix)
    (z : Multiplicative (ggFixAdd p π)) (hz : ι₀ c = c₀ * hT.uMap z * c₀⁻¹) :
    ∃ b ∈ hT.ggBfull, ∃ α : MulAut C, ∀ x : C, α (c * x * c⁻¹) = (b : MulAut C) (α x) := by
  have hN : c₀⁻¹ ∈ Subgroup.normalizer (ι₀.range : Set (ModGL τ GGL)) := by
    rw [← hT.pkg.desc.derived]
    exact Subgroup.normalizer_commutator_ge_left D.fix D.fix (inv_mem hc₀)
  refine ⟨hT.ggBetaHom z, ⟨z, rfl⟩, ggConjAut ι₀ hT.pkg.inj ⟨c₀⁻¹, hN⟩, fun x => ?_⟩
  apply hT.pkg.inj
  rw [hT.ggBetaHom_apply, ggConjAut_apply, ggConjAut_apply, map_mul, map_mul, map_inv, hz]
  dsimp only
  group

private theorem ggE8LangModelAux_sylowConj {G : Type} [Group G] {p m : ℕ} (hp : p.Prime)
    (hS : CFSG.LieType.SeitzGeneration.SylowTorus G p m) {E' : Subgroup G}
    (hE' : CFSG.Open.IsElemAbelian p E') (hcard : p ^ m ≤ Nat.card E') {c : G} (hc : c ^ p = 1) :
    ∃ y : G, y * c * y⁻¹ ∈ E' := by
  obtain ⟨T, E, -, hconj, -, hE, -, hEcard⟩ := hS.exists_torus
  have hpg : ∀ P : Subgroup G, (∀ x ∈ P, x ^ p = 1) → IsPGroup p P := fun P hP x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hP x x.2)⟩
  obtain ⟨g', hg'⟩ := hconj E' (hpg E' hE'.2)
  have hle : E'.map (MulAut.conj g'⁻¹).toMonoidHom ≤ E := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, ht, htu⟩ := hg' hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at htu ⊢
    have h1 : g'⁻¹ * u * g'⁻¹⁻¹ = t := by rw [← htu]; group
    rw [h1]
    refine hE t ht ?_
    rw [← h1, conj_pow, hE'.2 u hu, mul_one, mul_inv_cancel]
  haveI : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero _ hp.ne_zero)
  have heq : E'.map (MulAut.conj g'⁻¹).toMonoidHom = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hEcard, Subgroup.card_map_of_injective (f := (MulAut.conj g'⁻¹).toMonoidHom)
      (MulAut.conj g'⁻¹).injective]
    exact hcard
  have hzp : ∀ x ∈ Subgroup.zpowers c, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  obtain ⟨g, hg⟩ := hconj (Subgroup.zpowers c) (hpg _ hzp)
  obtain ⟨t, ht, htc⟩ := hg (Subgroup.mem_zpowers c)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at htc
  have htp : t ^ p = 1 := by
    have h1 : t = g⁻¹ * c * g⁻¹⁻¹ := by rw [← htc]; group
    rw [h1, conj_pow, hc, mul_one, mul_inv_cancel]
  have htE : t ∈ E := hE t ht htp
  rw [← heq] at htE
  obtain ⟨u, hu, hut⟩ := htE
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hut
  refine ⟨g' * g⁻¹, ?_⟩
  have h2 : g' * g⁻¹ * c * (g' * g⁻¹)⁻¹ = u := by
    rw [← htc, ← hut]
    group
  rw [h2]
  exact hu

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.ExcFramesHalf in
private theorem ggE8LangModelAux_sylowTorus
    {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (h11 : 11 ≤ p) (hreg : GGExcRegime p f) (n : ℕ) :
    SylowTorus (GGKb .E8 n f) p 8 := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  have hS : SylowTorus (adjointGroup Tag.E8 (GaloisField 2 f)) p 8 := by
    rcases hreg with h1 | h1
    · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) = 1 := by
        rw [hK, orderOf_eq_one_iff]
        have h0 : ((2 ^ f - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h1
        rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, sub_eq_zero] at h0
        exact h0
      exact sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) _ hp (by omega) hpK
        (CFSG.RankThree.PartOne.KE.IsWeylMatrix.of_word Tag.E8 e8OneWord)
        [1, 1, 1, 1, 1, 1, 1, 1] e8One_charpoly e8One_pow he
        (not_dvd_of_blocks hp (by omega) (by decide)) (not_dvd_div_of_5040 hp h11 (by decide))
        (by decide)
    · exact sylowTorus_E8_half _ hp h11 (by rw [hK]; exact h1)
  exact hS.of_mulEquiv (ggKbEquivE8 n f).symm

private theorem ggE8LangModelAux_big
    {f p : ℕ} [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (h11 : 11 ≤ p)
    (hreg : GGExcRegime p f)
    (M : GGDatumModel .E8 f p (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (n : ℕ)
    (c : GGKb .E8 n f) (hc : c ^ p = 1) :
    ∃ c₀ ∈ M.D.fix, ∃ z : Multiplicative (ggFixAdd p (piB .E8 p f)),
      ggIota .E8 n f hf c = c₀ * (M.torusData (n := n) hf hp hp2 hreg).uMap z * c₀⁻¹ := by
  classical
  have hT := M.torusData (n := n) hf hp hp2 hreg
  have hidx0 : (ggIota .E8 n f hf).range.relIndex M.D.fix ≠ 0 := by
    haveI := hT.pkg.desc.finite_fix
    haveI : Finite (↥M.D.fix ⧸ (ggIota .E8 n f hf).range.subgroupOf M.D.fix) :=
      Quotient.finite (QuotientGroup.leftRel _)
    exact Subgroup.index_ne_zero_of_finite
  have hco : Nat.Coprime p ((ggIota .E8 n f hf).range.relIndex M.D.fix) :=
    Nat.coprime_of_lt_prime hidx0 (by have := hT.pkg.index_le; omega) hp
  have hinn := hT.ggBfull_le_inn hco
  have hu : ∀ z, hT.uMap z ∈ (ggIota .E8 n f hf).range := fun z =>
    (hT.ggBetaHom_mem_inn_iff z).mp (hinn ⟨z, rfl⟩)
  let φ : Multiplicative (ggFixAdd p (piB .E8 p f)) →* GGKb .E8 n f :=
    (MonoidHom.ofInjective hT.pkg.inj).symm.toMonoidHom.comp
      (hT.uMap.codRestrict (ggIota .E8 n f hf).range hu)
  have hφ : ∀ z, ggIota .E8 n f hf (φ z) = hT.uMap z := fun z => by
    change ggIota .E8 n f hf ((MonoidHom.ofInjective hT.pkg.inj).symm
      ⟨hT.uMap z, hu z⟩) = hT.uMap z
    rw [MonoidHom.apply_ofInjective_symm]
  have huinj : Function.Injective hT.uMap := by
    intro z z' h
    apply hT.ggBetaHom_injective
    ext x
    apply hT.pkg.inj
    rw [hT.ggBetaHom_apply, hT.ggBetaHom_apply, h]
  have hφinj : Function.Injective φ := fun z z' h => huinj (by rw [← hφ, ← hφ, h])
  have hzp : ∀ z : Multiplicative (ggFixAdd p (piB .E8 p f)), z ^ p = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    apply Subtype.ext
    funext i
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, Pi.smul_apply, Pi.zero_apply,
      nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hE : CFSG.Open.IsElemAbelian p φ.range := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp a.2
      obtain ⟨z', hz'⟩ := MonoidHom.mem_range.mp b.2
      apply Subtype.ext
      show (a : GGKb .E8 n f) * b = b * a
      rw [← hz, ← hz', ← map_mul, ← map_mul, mul_comm z z']
    · rintro _ ⟨z, rfl⟩
      rw [← map_pow, hzp, map_one]
  have hcard : p ^ 8 ≤ Nat.card φ.range := by
    have h1 : Nat.card φ.range = Nat.card (Multiplicative (ggFixAdd p (piB .E8 p f))) :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm
    have h2 : Nat.card (Multiplicative (ggFixAdd p (piB .E8 p f))) = p ^ 8 := by
      rw [Nat.card_congr Multiplicative.toAdd, card_ggFixAdd]
      unfold GGFixCard
      have hall : ∀ z : Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p,
          ∀ i, z (piB .E8 p f i) = z i := fun z i => rfl
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [h1, h2]
  obtain ⟨y, z, hz⟩ :=
    ggE8LangModelAux_sylowConj hp (ggE8LangModelAux_sylowTorus hf hp h11 hreg n) hE hcard hc
  refine ⟨ggIota .E8 n f hf y⁻¹, hT.pkg.desc.range_le ⟨y⁻¹, rfl⟩, z, ?_⟩
  rw [← hφ z, hz, map_mul, map_mul, map_inv]
  group

private theorem ggE8LangModelAux_weyl
    {f p : ℕ} (hreg : GGExcRegime p f)
    {w : WeylGroup (langTag .E8)}
    (hw : GGWeylLaw .E8 p f (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) w)
    (a : Fin (langTag .E8).rank → GGLˣ) (ha : ∀ j, a j ^ p = 1)
    (v : Fin (langTag .E8).rank → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a (w • v) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v ^ 2 ^ f := by
  have hwv : w • v = eps p f • v := hw v
  have hzs : ∀ k : ℤ, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a (k • v) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v ^ k := by
    intro k
    simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, Pi.smul_apply,
      smul_eq_mul]
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm, zpow_mul]
  have hxp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v ^ p = 1 := by
    simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]
  rw [hwv, hzs]
  set x := CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v
  unfold eps
  split_ifs with h1
  · obtain ⟨k, hk⟩ := h1
    have h2 : 2 ^ f = p * k + 1 := by
      rw [← hk]
      exact (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    rw [zpow_one, h2, pow_succ, pow_mul, hxp, one_pow, one_mul]
  · obtain ⟨k, hk⟩ := hreg.resolve_left h1
    have h3 : x ^ 2 ^ f * x = 1 := by rw [← pow_succ, hk, pow_mul, hxp, one_pow]
    rw [zpow_neg_one]
    exact (eq_inv_of_mul_eq_one_left h3).symm

open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg in
private theorem ggE8LangModelAux_lang
    {f p : ℕ} [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp7 : p = 3 ∨ p = 5 ∨ p = 7) (hreg : GGExcRegime p f)
    (M : GGDatumModel .E8 f p (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (n : ℕ)
    (c : GGKb .E8 n f) (hc : c ^ p = 1) :
    ∃ c₀ ∈ M.D.fix, ∃ z : Multiplicative (ggFixAdd p (piB .E8 p f)),
      ggIota .E8 n f hf c = c₀ * (M.torusData (n := n) hf hp hp2 hreg).uMap z * c₀⁻¹ := by
  classical
  have hT := M.torusData (n := n) hf hp hp2 hreg
  have hsfix : ggIota .E8 n f hf c ∈ M.D.fix := hT.pkg.desc.range_le ⟨c, rfl⟩
  have hsG : ggIota .E8 n f hf c ∈ adjointGroup (langTag .E8) GGL :=
    ((LangDatum.mem_fix M.D).mp hsfix).1
  have hΦF : ∀ x, M.D.Φ x = entrywiseFrobGL (langTag .E8) GGL 2 f x := fun x => by
    rw [M.hΦ]
    rfl
  have hsΦ : entrywiseFrobGL (langTag .E8) GGL 2 f (ggIota .E8 n f hf c) =
      ggIota .E8 n f hf c := by
    rw [← hΦF]
    exact ((LangDatum.mem_fix M.D).mp hsfix).2
  have hsp : ggIota .E8 n f hf c ^ p = 1 := by rw [← map_pow, hc, map_one]
  have halg :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite (ZMod 2) 2
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt (langTag .E8) p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hp hp2
  obtain ⟨g, hgG, hgT⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_conj_torusGroup_of_pow_eq_one
      hp hmon (ℓ := 2) (Ne.symm hp2) halg hsG hsp
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
  have hsa : ggIota .E8 n f hf c = g * rootDiagUnit (langTag .E8) a * g⁻¹ := by
    rw [← ha]
    group
  have hdp : rootDiagUnit (langTag .E8) a ^ p = 1 := by
    rw [← ha]
    have h1 : g⁻¹ * ggIota .E8 n f hf c * g = g⁻¹ * ggIota .E8 n f hf c * g⁻¹⁻¹ := by
      rw [inv_inv]
    rw [h1, conj_pow, hsp, mul_one, mul_inv_cancel]
  have hap' : a ^ p = 1 := by
    apply rootDiagUnit_injective (τ := langTag .E8)
    rw [rootDiagUnit_one]
    exact (map_pow (rootDiagUnitHom (langTag .E8) GGL) a p).trans hdp
  have hap : ∀ j, a j ^ p = 1 := fun j => by
    have h := congrFun hap' j
    rwa [Pi.pow_apply, Pi.one_apply] at h
  have hstab : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
    rcases hp7 with rfl | rfl | rfl
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a hap).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a hap).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven a hap).le
  have hcent : familyCentralizer (langTag .E8) GGL (fun _ : Unit => a) =
      familyGroup (K := GGL) (fun _ : Unit => a) := by
    have hkernel : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
      ext α
      simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hα, h⟩
        exact ⟨hα, h ()⟩
      · rintro ⟨hα, h⟩
        exact ⟨hα, fun _ => h⟩
    have hgroup : familyGroup (K := GGL) (fun _ : Unit => a) =
        toralRootGroup (langTag .E8) GGL a := by
      simp only [familyGroup, toralRootGroup, hkernel]
    have hcentral : familyCentralizer (langTag .E8) GGL (fun _ : Unit => a) =
        toralCentralizer (langTag .E8) GGL a := by
      ext x
      rw [mem_familyCentralizer, mem_toralCentralizer]
      simp only [forall_const]
    rw [hcentral, hgroup,
      toralCentralizer_eq_toralRootGroup_of_stabilizer_le (langTag .E8) GGL a hstab]
  have hpq : Nat.Coprime p (2 ^ f) := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right f
  have hx : ∀ _ : Unit, entrywiseFrobGL (langTag .E8) GGL 2 f
      (g * rootDiagUnit (langTag .E8) a * g⁻¹) = g * rootDiagUnit (langTag .E8) a * g⁻¹ :=
    fun _ => by rw [← hsa]; exact hsΦ
  obtain ⟨g₁, hg₁G, hg₁F, hg₁⟩ :=
    CFSG.StandardType.ExcElemToral.exists_lang_conj_of_family_twisted 2 hf (fun _ : Unit => a)
      hpq (fun _ j => hap j) (w := M.w) (fun _ v => ggE8LangModelAux_weyl hreg M.hw a hap v)
      hcent hgG hx
  have hc₀ : g₁ * M.D.g0⁻¹ ∈ M.D.fix := by
    rw [LangDatum.mem_fix]
    refine ⟨mul_mem hg₁G (inv_mem M.D.g0_mem), ?_⟩
    rw [map_mul, map_inv, M.D.lang, hΦF g₁, hg₁F, M.hn]
    group
  have hζ : orderOf (ggZeta p hp hp2) = p := hT.ζ_order
  have hζprim : IsPrimitiveRoot ((ggZeta p hp hp2 : GGLˣ) : GGL) p := by
    have h0 := IsPrimitiveRoot.orderOf (ggZeta p hp hp2)
    rw [hζ] at h0
    exact IsPrimitiveRoot.coe_units_iff.mpr h0
  have hexp : ∀ j, ∃ i < p, ggZeta p hp hp2 ^ i = a j := by
    intro j
    obtain ⟨i, hi, hζi⟩ := hζprim.eq_pow_of_pow_eq_one (ξ := ((a j : GGLˣ) : GGL))
      (by rw [← Units.val_pow_eq_pow_val, hap j, Units.val_one])
    exact ⟨i, hi, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζi)⟩
  choose i hi hζi using hexp
  let zv : Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p := fun k =>
    ((i (Fin.cast (rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) k) : ℕ) : ZMod p)
  have hzv : ggParam (rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (ggZeta p hp hp2)
      zv = a := by
    funext j
    exact (congrArg (ggZeta p hp hp2 ^ ·) (ZMod.val_cast_of_lt (hi j))).trans (hζi j)
  let zz : Multiplicative (ggFixAdd p (piB .E8 p f)) := Multiplicative.ofAdd ⟨zv, fun _ => rfl⟩
  have hzz : ggParam (rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (ggZeta p hp hp2) (Multiplicative.toAdd zz).1 = a := hzv
  have hg₁' : g₁ * rootDiagUnit (langTag .E8) a * g₁⁻¹ =
      g * rootDiagUnit (langTag .E8) a * g⁻¹ := hg₁ ()
  refine ⟨g₁ * M.D.g0⁻¹, hc₀, zz, ?_⟩
  rw [GGTorusData.uMap_apply, hzz, hsa, ← hg₁']
  group

private theorem ggE8LangModelAux_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  rcases Nat.lt_or_ge 10 p with h | h
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  · have := hp.two_le
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem ggE8_conj_bfull
    {f p : ℕ} [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (M : GGDatumModel .E8 f p (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (n : ℕ)
    (c : GGKb .E8 n f) (hc : c ^ p = 1) :
    ∃ b ∈ (M.torusData (n := n) hf hp hp2 hreg).ggBfull, ∃ α : MulAut (GGKb .E8 n f),
      ∀ x : GGKb .E8 n f, α (c * x * c⁻¹) = (b : MulAut (GGKb .E8 n f)) (α x) := by
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := ggE8LangModelAux_cases hp hp2
  have hfin : ∃ c₀ ∈ M.D.fix, ∃ z : Multiplicative (ggFixAdd p (piB .E8 p f)),
      ggIota .E8 n f hf c = c₀ * (M.torusData (n := n) hf hp hp2 hreg).uMap z * c₀⁻¹ := by
    rcases hcases with h | h | h | h
    · exact ggE8LangModelAux_lang hf hp hp2 (Or.inl h) hreg M n c hc
    · exact ggE8LangModelAux_lang hf hp hp2 (Or.inr (Or.inl h)) hreg M n c hc
    · exact ggE8LangModelAux_lang hf hp hp2 (Or.inr (Or.inr h)) hreg M n c hc
    · exact ggE8LangModelAux_big hf hp hp2 h hreg M n c hc
  obtain ⟨c₀, hc₀, z, hz⟩ := hfin
  exact ggE8LangModelAux_finish (M.torusData (n := n) hf hp hp2 hreg) c c₀ hc₀ z hz

end CFSG.StandardType.GGFinModel
