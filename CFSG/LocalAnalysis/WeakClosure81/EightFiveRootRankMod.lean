module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSection
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Goldschmidt.Steps.G2Grp
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.LocalAnalysis.WeakClosure81.W19EightAbs
public import CFSG.RankThree.PartOne.U5K.Perfect
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.Foundations
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.Offenders
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement CFSG.Goldschmidt.G2

@[expose] noncomputable def modCommRank {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    (t : LGL 2 F) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range ((t : F →ₗ[ZMod 2] F) - LinearMap.id))

theorem exists_noncentral_chief_factor {N : Type} [Group N] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : N →* LGL 2 V) (h : ¬ IsPGroup 2 ρ.range) :
    ∃ W₁ W₂ : Submodule (ZMod 2) V, IsChiefFactor ρ W₁ W₂ ∧ IsNoncentral ρ W₁ W₂ := by
  by_contra hcon
  refine h ?_
  have h2 := isPGroup_map_of_trivial_on_chief ρ (⊤ : Subgroup N) (fun W₁ W₂ hcf x _ w hw => by
    by_contra hne
    exact hcon ⟨W₁, W₂, hcf, ⟨x, w, hw, hne⟩⟩)
  rwa [MonoidHom.range_eq_map]

private theorem w85g_moduleFinite_of_finite {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] : Module.Finite (ZMod 2) F :=
  Module.Finite.of_finite

private theorem w85g_bar_ker {G : Type} [Group G] {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    φ.ker = (pCoreOf 2 K).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, hφ.ker_iff, Subgroup.mem_subgroupOf]

private theorem w85g_bar_ker_eq_pCore {G : Type} [Group G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    φ.ker = pCore 2 ↥K := by
  rw [w85g_bar_ker hφ, show pCoreOf 2 K = (pCore 2 ↥K).map K.subtype from rfl,
    ← Subgroup.comap_subtype ((pCore 2 ↥K).map K.subtype) K,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective (pCore 2 ↥K)]

private theorem w85g_bar_ker_isPGroup {G : Type} [Group G] [Finite G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) : IsPGroup 2 φ.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [w85g_bar_ker_eq_pCore hφ]
  exact CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K)

private theorem w85g_bar_restrict {G : Type} [Group G] [Finite G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    ∃ ψ : ↥((commutator X).comap φ) →* ↥(commutator X), Function.Surjective ψ ∧
      (∀ n, (ψ n : X) = φ n) ∧ IsPGroup 2 ψ.ker := by
  let M : Subgroup ↥K := (commutator X).comap φ
  let ψ : ↥M →* ↥(commutator X) :=
    (φ.comp (Subgroup.subtype M)).codRestrict (commutator X)
      (fun m => Subgroup.mem_comap.mp m.2)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := hφ.surjective (y : X)
    have hkM : k ∈ M := by
      rw [Subgroup.mem_comap, hk]
      exact y.2
    exact ⟨⟨k, hkM⟩, Subtype.ext hk⟩
  · intro n
    rfl
  · have hker : ψ.ker = φ.ker.comap (Subgroup.subtype M) := by
      rw [show ψ = (φ.comp (Subgroup.subtype M)).codRestrict (commutator X)
          (fun m => Subgroup.mem_comap.mp m.2) from rfl,
        MonoidHom.ker_codRestrict]
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
      rfl
    rw [hker]
    exact (w85g_bar_ker_isPGroup hφ).comap_of_injective _ (Subgroup.subtype_injective M)

private theorem w85g_finrank_sub_le_rk {G : Type} [Group G] [Finite G] {I : Subgroup G}
    [Fact (IsElemAbelian 2 I)] (H : Subgroup G) :
    Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I H) ≤ rk ↥H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite (ZMod 2) (Additive ↥I) := w85g_moduleFinite_of_finite
  have hI2 : IsPGroup 2 I :=
    isPGroup_two_of_sq_eq_one (fun x => Subtype.ext ((Fact.out : IsElemAbelian 2 I).2 x x.2))
  have hIinf : IsPGroup 2 (I ⊓ H : Subgroup G) := hI2.to_le inf_le_left
  have hcard_fin : Nat.card (CFSG.Goldschmidt.G2.sub I H) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I H) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CFSG.Goldschmidt.G2.sub I H),
      Nat.card_zmod]
  have hcard_inf : Nat.card (I ⊓ H : Subgroup G) = 2 ^ rk ↥(I ⊓ H) :=
    card_eq_two_pow_of_isPGroup hIinf
  have hfin : Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I H) = rk ↥(I ⊓ H) := by
    apply Nat.pow_right_injective (by norm_num : 1 < 2)
    show 2 ^ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I H) = 2 ^ rk ↥(I ⊓ H)
    rw [← hcard_fin, CFSG.Goldschmidt.G2.card_sub H, hcard_inf]
  calc Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I H) = rk ↥(I ⊓ H) := hfin
    _ ≤ rk ↥H := rk_mono inf_le_right

theorem bar_odd_card_center {G : Type} [Group G] [Finite G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    Odd (Nat.card (Subgroup.center X)) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.CGT.Timmesfeld75.odd_card_center (K := X) ?_
  intro N hN hP
  have hpker : IsPGroup 2 φ.ker := w85g_bar_ker_isPGroup hφ
  have hQp : IsPGroup 2 (N.comap φ) := hP.comap_of_ker_isPGroup φ hpker
  have hQn : (N.comap φ).Normal := hN.comap φ
  have hQle : N.comap φ ≤ φ.ker := by
    rw [w85g_bar_ker_eq_pCore hφ]
    exact CFSG.LieType.BorelTits.le_pCore (r := 2) hQn hQp
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  obtain ⟨k, hk⟩ := hφ.surjective n
  have hk' : k ∈ N.comap φ := by
    rw [Subgroup.mem_comap, hk]
    exact hn
  have h1 : φ k = 1 := MonoidHom.mem_ker.mp (hQle hk')
  rw [← hk]
  exact h1

theorem bar_involution_not_mem_center {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {X : Type} [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) {v : ↥K}
    (hv : (v : G) * (v : G) = 1) (h1 : φ v ≠ 1) : φ v ∉ Subgroup.center X := by
  intro hc
  have hodd := bar_odd_card_center hφ
  have hvv : v * v = 1 := Subtype.ext hv
  have hsq : φ v ^ 2 = 1 := by rw [pow_two, ← map_mul, hvv, map_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (φ v) = 2 := orderOf_eq_prime hsq h1
  have hdvd : orderOf (⟨φ v, hc⟩ : Subgroup.center X) ∣ Nat.card (Subgroup.center X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem one_le_rk_commutator {G : Type} [Group G] [Finite G] {K I : Subgroup G}
    (hI : IsElemAbelian 2 I) (hK : K ≤ Subgroup.normalizer (I : Set G))
    (hC : K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K) {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) {v : ↥K} (h1 : φ v ≠ 1) :
    1 ≤ rk ↥⁅I, Subgroup.zpowers (v : G)⁆ := by
  by_contra hcon
  rw [not_le] at hcon
  have hI2 : IsPGroup 2 I :=
    isPGroup_two_of_sq_eq_one (fun x => Subtype.ext (hI.2 x x.2))
  have hHI : ⁅I, Subgroup.zpowers (v : G)⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro i hi w hw
    have hwN : w ∈ Subgroup.normalizer (I : Set G) := hK (Subgroup.zpowers_le.mpr v.2 hw)
    have hconj : w * i⁻¹ * w⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp hwN i⁻¹).mp (I.inv_mem hi)
    have hcomm : ⁅i, w⁆ = i * (w * i⁻¹ * w⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact I.mul_mem hi hconj
  have hH2 : IsPGroup 2 ↥⁅I, Subgroup.zpowers (v : G)⁆ := hI2.to_le hHI
  have hzero : rk ↥⁅I, Subgroup.zpowers (v : G)⁆ = 0 := by omega
  have hHbot : ⁅I, Subgroup.zpowers (v : G)⁆ = ⊥ :=
    (rk_eq_zero_iff_of_isPGroup hH2).mp hzero
  have hvcent : (v : G) ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact ((Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hHbot) hi))
      (v : G) (Subgroup.mem_zpowers (v : G))).symm
  have hp : (v : G) ∈ pCoreOf 2 K := hC ⟨v.2, hvcent⟩
  exact h1 ((hφ.ker_iff v).mpr hp)

theorem bar_commutator_facts {G : Type} [Group G] [Finite G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ)
    (hperf : Group.IsPerfect (X ⧸ Subgroup.center X)) (hnt : Nontrivial (X ⧸ Subgroup.center X))
    {v : ↥K} (hv : (v : G) * (v : G) = 1) :
    φ v ∈ commutator X ∧ Group.IsPerfect ↥(commutator X) ∧ commutator X ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXeq : commutator X ⊔ Subgroup.center X = ⊤ :=
    CFSG.RankThree.PartOne.U5K.commutator_sup_center_eq_top (X := X) hperf
  have hYperf : Group.IsPerfect ↥(commutator X) :=
    CFSG.RankThree.PartOne.U5K.isPerfect_commutator (X := X) hperf
  have hYne : commutator X ≠ ⊥ := by
    intro hbot
    have hcenter : Subgroup.center X = ⊤ := by
      have h := hXeq
      rw [hbot, bot_sup_eq] at h
      exact h
    haveI : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [hcenter]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  refine ⟨?_, hYperf, hYne⟩
  let q : X →* X ⧸ commutator X := QuotientGroup.mk' (commutator X)
  have hv_sup : φ v ∈ commutator X ⊔ Subgroup.center X := by
    rw [hXeq]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, z, hz, haz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := commutator X) (t := Subgroup.center X)).mp hv_sup
  have hq : q (φ v) = q z := by
    rw [← haz, map_mul]
    have haq : q a = 1 := by
      change (QuotientGroup.mk' (commutator X)) a = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
    rw [haq, one_mul]
  have hvv : v * v = 1 := Subtype.ext hv
  have hvv2 : (φ v) ^ 2 = 1 := by rw [pow_two, ← map_mul, hvv, map_one]
  have h1 : orderOf (q z) ∣ 2 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have h2 : (q (φ v)) ^ 2 = 1 := by rw [← map_pow, hvv2, map_one]
    rwa [hq] at h2
  have hodd : Odd (orderOf (q z)) := by
    have h1 : orderOf (q z) ∣ orderOf z := orderOf_map_dvd q z
    have h2 : orderOf z ∣ Nat.card (Subgroup.center X) := by
      have h := _root_.orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center X)
      rwa [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat (bar_odd_card_center hφ) (h1.trans h2)
  have hz1 : orderOf (q z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by norm_num)
  have hqz : q z = 1 := orderOf_eq_one_iff.mp hz1
  have hq1 : q (φ v) = 1 := by rw [hq, hqz]
  have : φ v ∈ q.ker := MonoidHom.mem_ker.mpr hq1
  rwa [QuotientGroup.ker_mk'] at this

theorem not_isPGroup_range_conjRep {G : Type} [Group G] [Finite G] {K I : Subgroup G}
    [Fact (IsElemAbelian 2 I)] (hK : K ≤ Subgroup.normalizer (I : Set G))
    (hC : K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K) {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) (hperf : Group.IsPerfect ↥(commutator X))
    (hne : commutator X ≠ ⊥) :
    ¬ IsPGroup 2
      (((CFSG.Goldschmidt.G2.conjRep hK).comp ((commutator X).comap φ).subtype).range) := by
  intro hP
  obtain ⟨ψ, hψs, hψφ, _⟩ := w85g_bar_restrict hφ
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup ↥K := (commutator X).comap φ
  let ρ : ↥M →* LGL 2 (Additive ↥I) := (CFSG.Goldschmidt.G2.conjRep hK).comp (Subgroup.subtype M)
  have hPρ : IsPGroup 2 ρ.range := hP
  have hker_le : ρ.ker ≤ ψ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hcent : (Subgroup.subtype M m : G) ∈ Subgroup.centralizer (I : Set G) :=
      (CFSG.Goldschmidt.G2.conjRep_eq_one_iff hK (Subgroup.subtype M m)).mp hm
    have hp : (Subgroup.subtype M m : G) ∈ pCoreOf 2 K :=
      hC ⟨(Subgroup.subtype M m).2, hcent⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hψφ m]
    simpa using (hφ.ker_iff (Subgroup.subtype M m)).mpr hp
  let g : ↥M ⧸ ρ.ker →* ↥(commutator X) := QuotientGroup.lift ρ.ker ψ hker_le
  let e : ↥M ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  let g' : ρ.range →* ↥(commutator X) := g.comp e.symm.toMonoidHom
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨m, hm⟩ := hψs y
    exact ⟨QuotientGroup.mk m, by
      rw [QuotientGroup.lift_mk ρ.ker hker_le m]
      exact hm⟩
  have hg'surj : Function.Surjective g' := hgsurj.comp e.symm.surjective
  have hYp : IsPGroup 2 ↥(commutator X) := hPρ.of_surjective g' hg'surj
  haveI : Group.IsPerfect ↥(commutator X) := hperf
  haveI : Nontrivial ↥(commutator X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact (Group.IsPerfect.not_isNilpotent ↥(commutator X)) hYp.isNilpotent

theorem exists_bar_restriction {G : Type} [Group G] [Finite G] {K : Subgroup G} {X : Type}
    [Group X] {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    ∃ ψ : ↥((commutator X).comap φ) →* ↥(commutator X), Function.Surjective ψ ∧
      (∀ n, (ψ n : X) = φ n) ∧ IsPGroup 2 ψ.ker :=
  w85g_bar_restrict hφ

theorem exists_sigma_of_bar {M Y : Type} [Group M] [Group Y] (ψ : M →* Y)
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) {F : Type} [AddCommGroup F]
    [Module (ZMod 2) F] [Finite F] (σM : M →* LGL 2 F) (hirr : IsChiefFactor σM ⊤ ⊥) :
    ∃ σ : Y →* LGL 2 F, (∀ m, σ (ψ m) = σM m) ∧ IsChiefFactor σ ⊤ ⊥ := by
  classical
  obtain ⟨hlt, hW1, hW2, hmin⟩ := hirr
  obtain ⟨hle, x, hx, hxn⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  haveI : Nontrivial F := ⟨x, 0, fun h => hxn (by rw [h]; exact Submodule.zero_mem _)⟩
  have hle_ker : ψ.ker ≤ σM.ker := by
    have hirr' : ∀ U : Submodule (ZMod 2) F,
        (∀ k ∈ σM.range, ∀ u ∈ U, k u ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      exact hmin U bot_le le_top (fun m u hu => hU (σM m) ⟨m, rfl⟩ u hu)
    have hn : σM.range ≤ Subgroup.normalizer ((ψ.ker).map σM : Set (LGL 2 F)) := by
      have h := Subgroup.le_normalizer_map (H := ψ.ker) σM
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : ψ.ker.Normal),
        ← MonoidHom.range_eq_map σM] at h
      exact h
    have hbot : (ψ.ker).map σM = ⊥ :=
      eq_bot_of_normal_isPGroup_irreducible (K := σM.range) (N := (ψ.ker).map σM)
        hirr' (Subgroup.map_le_range σM ψ.ker) hn (hker.map σM)
    intro m hm
    rw [MonoidHom.mem_ker]
    have hmem : σM m ∈ (ψ.ker).map σM := ⟨m, hm, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  let σbar : M ⧸ ψ.ker →* LGL 2 F := QuotientGroup.lift ψ.ker σM hle_ker
  let e : M ⧸ ψ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hσfac : ∀ m : M, (σbar.comp e.symm.toMonoidHom) (ψ m) = σM m := by
    intro m
    show σbar (e.symm (ψ m)) = σM m
    have h1 : e (QuotientGroup.mk m) = ψ m := by
      change (QuotientGroup.kerLift ψ) (QuotientGroup.mk m) = ψ m
      rw [QuotientGroup.kerLift_mk]
    rw [← h1, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk ψ.ker hle_ker m
  refine ⟨σbar.comp e.symm.toMonoidHom, hσfac, ?_⟩
  refine ⟨hlt, ?_, ?_, ?_⟩
  · intro y u _
    exact Submodule.mem_top
  · intro y u hu
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  · intro U _ _ hUinv
    exact hmin U bot_le le_top (fun m u hu => by
      have h := hUinv (ψ m) u hu
      rwa [hσfac m] at h)

theorem modCommRank_sectionRep_le {N : Type} [Group N] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : N →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V)
    (h₁ : ∀ g : N, ∀ w ∈ W₁, ρ g w ∈ W₁) (h₂ : ∀ g : N, ∀ w ∈ W₂, ρ g w ∈ W₂) (t : N) :
    modCommRank (sectionRep ρ W₁ W₂ h₁ h₂ t) ≤ modCommRank (ρ t) := by
  classical
  haveI : Module.Finite (ZMod 2) V := w85g_moduleFinite_of_finite
  let f : ↥W₁ →ₗ[ZMod 2] ↥W₁ := (ρ t).restrict (h₁ t)
  let g : ↥W₁ →ₗ[ZMod 2] ↥W₁ := f - LinearMap.id
  let R : Submodule (ZMod 2) ↥W₁ := LinearMap.range g
  let p : Submodule (ZMod 2) ↥W₁ := W₂.comap W₁.subtype
  have hrange : LinearMap.range
      (((sectionRep ρ W₁ W₂ h₁ h₂ t : LGL 2 (SecMod W₁ W₂)) :
        SecMod W₁ W₂ →ₗ[ZMod 2] SecMod W₁ W₂) - LinearMap.id) ≤ R.map p.mkQ := by
    rintro y ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      have hsec : (↑(sectionRep ρ W₁ W₂ h₁ h₂ t) : SecMod W₁ W₂ →ₗ[ZMod 2] SecMod W₁ W₂)
          (Submodule.Quotient.mk z) = Submodule.Quotient.mk (f z) := by
        change secMap W₁ W₂ (ρ t) (h₁ t) (h₂ t) (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk (f z)
        rw [secMap_mk]
        congr 1
      refine Submodule.mem_map.mpr ⟨g z, ⟨z, rfl⟩, ?_⟩
      rw [show g z = f z - z from rfl, map_sub, LinearMap.sub_apply, hsec,
        LinearMap.id_apply]
      rfl
  have hsub : R.map W₁.subtype ≤ LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - LinearMap.id) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨W₁.subtype w, ?_⟩
    rw [← hw]
    show ((ρ t : V →ₗ[ZMod 2] V) - (LinearMap.id : V →ₗ[ZMod 2] V)) (W₁.subtype w) =
      W₁.subtype (g w)
    rw [LinearMap.sub_apply, LinearMap.id_apply, show g w = f w - w from rfl, map_sub]
    rfl
  calc modCommRank (sectionRep ρ W₁ W₂ h₁ h₂ t)
      = Module.finrank (ZMod 2) (LinearMap.range
          (((sectionRep ρ W₁ W₂ h₁ h₂ t : LGL 2 (SecMod W₁ W₂)) :
            SecMod W₁ W₂ →ₗ[ZMod 2] SecMod W₁ W₂) - LinearMap.id)) := rfl
    _ ≤ Module.finrank (ZMod 2) (R.map p.mkQ) := Submodule.finrank_mono hrange
    _ ≤ Module.finrank (ZMod 2) R := Submodule.finrank_map_le p.mkQ R
    _ = Module.finrank (ZMod 2) (R.map W₁.subtype) :=
        (Submodule.equivMapOfInjective W₁.subtype W₁.subtype_injective R).finrank_eq
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ t : V →ₗ[ZMod 2] V) - LinearMap.id)) :=
        Submodule.finrank_mono hsub
    _ = modCommRank (ρ t) := rfl

theorem modCommRank_conjRep_le_rk {G : Type} [Group G] [Finite G] {K I : Subgroup G}
    [Fact (IsElemAbelian 2 I)] (hK : K ≤ Subgroup.normalizer (I : Set G)) (t : ↥K) :
    modCommRank (CFSG.Goldschmidt.G2.conjRep hK t) ≤ rk ↥⁅I, Subgroup.zpowers (t : G)⁆ := by
  classical
  haveI : Module.Finite (ZMod 2) (Additive ↥I) := w85g_moduleFinite_of_finite
  calc modCommRank (CFSG.Goldschmidt.G2.conjRep hK t)
      = Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.comSp (CFSG.Goldschmidt.G2.conjRep hK t)) :=
        rfl
    _ ≤ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub I ⁅I, Subgroup.zpowers (t : G)⁆) :=
        Submodule.finrank_mono (CFSG.Goldschmidt.G2.comSp_le_sub hK t)
    _ ≤ rk ↥⁅I, Subgroup.zpowers (t : G)⁆ := w85g_finrank_sub_le_rk _

theorem sigma_ne_one_of_not_mem_center {X : Type} [Group X]
    (hS : IsSimpleGroup (X ⧸ Subgroup.center X)) (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]
    (σ : ↥(commutator X) →* LGL 2 F) (hσ : ∃ y, σ y ≠ 1) {y : X} (hy : y ∈ commutator X)
    (hyc : y ∉ Subgroup.center X) : σ ⟨y, hy⟩ ≠ 1 := by
  intro h1
  obtain ⟨z, hz⟩ := hσ
  have hXeq : commutator X ⊔ Subgroup.center X = ⊤ :=
    CFSG.RankThree.PartOne.U5K.commutator_sup_center_eq_top (X := X) hperf
  let N : Subgroup ↥(commutator X) := σ.ker
  let Nsub : Subgroup X := N.map (Subgroup.subtype (commutator X))
  have hNsub : Nsub.Normal := by
    refine ⟨fun n hn x => ?_⟩
    have hx_sup : x ∈ commutator X ⊔ Subgroup.center X := by
      rw [hXeq]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, zc, hzc, haz⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := commutator X) (t := Subgroup.center X)).mp hx_sup
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
    rw [← haz, ← hmn]
    have hcentral : ∀ w : X, zc * w = w * zc :=
      fun w => (Subgroup.mem_center_iff.mp hzc w).symm
    have hcalc : (a * zc) * ((commutator X).subtype m) * (a * zc)⁻¹ =
        a * ((commutator X).subtype m) * a⁻¹ := by
      rw [mul_inv_rev]
      calc (a * zc) * ((commutator X).subtype m) * (zc⁻¹ * a⁻¹)
          = a * (zc * ((commutator X).subtype m) * zc⁻¹) * a⁻¹ := by group
        _ = a * ((commutator X).subtype m) * a⁻¹ := by
              rw [hcentral ((commutator X).subtype m)]; group
    rw [hcalc]
    refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : ↥(commutator X)) * m *
      (⟨a, ha⟩ : ↥(commutator X))⁻¹, ?_, rfl⟩
    exact (inferInstance : N.Normal).conj_mem m hm ⟨a, ha⟩
  let Mq : Subgroup (X ⧸ Subgroup.center X) :=
    Nsub.map (QuotientGroup.mk' (Subgroup.center X))
  have hMqnorm : Mq.Normal := hNsub.map _ (QuotientGroup.mk'_surjective _)
  have hMqne : Mq ≠ ⊥ := by
    have hyNsub : y ∈ Nsub := by
      refine Subgroup.mem_map.mpr ⟨⟨y, hy⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr h1
    have hmem : (QuotientGroup.mk' (Subgroup.center X)) y ∈ Mq :=
      Subgroup.mem_map.mpr ⟨y, hyNsub, rfl⟩
    have hne1 : (QuotientGroup.mk' (Subgroup.center X)) y ≠ 1 := by
      simpa only [QuotientGroup.mk'_apply, ne_eq, QuotientGroup.eq_one_iff] using hyc
    intro hbot
    exact hne1 (Subgroup.mem_bot.mp (hbot ▸ hmem))
  have hMqtop : Mq = ⊤ := by
    haveI : Mq.Normal := hMqnorm
    rcases hS.eq_bot_or_eq_top_of_normal Mq with h | h
    · exact absurd h hMqne
    · exact h
  have hsup : Nsub ⊔ Subgroup.center X = ⊤ := by
    have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' (Subgroup.center X)) Nsub
    have hMqtop' : Nsub.map (QuotientGroup.mk' (Subgroup.center X)) = ⊤ := hMqtop
    rw [hMqtop', Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hcomm_le : commutator X ≤ Nsub := by
    rw [show commutator X = ⁅(⊤ : Subgroup X), ⊤⁆ from _root_.commutator_def X,
      Subgroup.commutator_le]
    intro a _ b _
    have ha_sup : a ∈ Nsub ⊔ Subgroup.center X := by
      rw [hsup]
      exact Subgroup.mem_top _
    have hb_sup : b ∈ Nsub ⊔ Subgroup.center X := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨n1, hn1, z1, hz1, h1⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Nsub) (t := Subgroup.center X)).mp ha_sup
    obtain ⟨n2, hn2, z2, hz2, h2⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Nsub) (t := Subgroup.center X)).mp hb_sup
    have hcomm : ⁅a, b⁆ = ⁅n1, n2⁆ := by
      rw [← h1, ← h2, Subgroup.mem_center_iff.mp hz1 n1,
        CFSG.RankThree.PartOne.U5K.commutatorElement_mul_central_left hz1 n1 (n2 * z2),
        Subgroup.mem_center_iff.mp hz2 n2,
        CFSG.RankThree.PartOne.U5K.commutatorElement_mul_central_right hz2 n1 n2]
    rw [hcomm]
    exact Subgroup.commutator_le_self Nsub (Subgroup.commutator_mem_commutator hn1 hn2)
  have hzmem : (z : X) ∈ Nsub := hcomm_le z.2
  obtain ⟨m, hm, hval⟩ := Subgroup.mem_map.mp hzmem
  have hmz : m = z := Subtype.ext hval
  have hzker : z ∈ σ.ker := hmz ▸ hm
  exact hz (MonoidHom.mem_ker.mp hzker)

theorem exists_irreducible_section_of_bar {G : Type} [Group G] [Finite G] {K I : Subgroup G}
    (hI : IsElemAbelian 2 I) (hK : K ≤ Subgroup.normalizer (I : Set G))
    (hC : K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K) {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ)
    (hS : IsSimpleGroup (X ⧸ Subgroup.center X)) (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    {v : ↥K} (hv : (v : G) * (v : G) = 1) (hvc : φ v ∉ Subgroup.center X) :
    ∃ hvX : φ v ∈ commutator X, ∃ (F : Type) (_ : AddCommGroup F) (_ : Module (ZMod 2) F)
      (_ : Finite F) (σ : ↥(commutator X) →* LGL 2 F), IsChiefFactor σ ⊤ ⊥ ∧
        σ ⟨φ v, hvX⟩ ≠ 1 ∧ modCommRank (σ ⟨φ v, hvX⟩) ≤ rk ↥⁅I, Subgroup.zpowers (v : G)⁆ := by
  haveI : Fact (IsElemAbelian 2 I) := ⟨hI⟩
  haveI : Nontrivial (X ⧸ Subgroup.center X) := hS.toNontrivial
  obtain ⟨hvX, hYperf, hYne⟩ := bar_commutator_facts hφ hperf inferInstance hv
  obtain ⟨ψ, hψs, hψφ, hψker⟩ := exists_bar_restriction hφ
  let ρ : ↥((commutator X).comap φ) →* LGL 2 (Additive ↥I) :=
    (CFSG.Goldschmidt.G2.conjRep hK).comp ((commutator X).comap φ).subtype
  obtain ⟨W₁, W₂, hcf, hnc⟩ := exists_noncentral_chief_factor ρ
    (not_isPGroup_range_conjRep hK hC hφ hYperf hYne)
  haveI : Finite (SecMod W₁ W₂) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := W₂.comap W₁.subtype))
      (Submodule.Quotient.mk_surjective (p := W₂.comap W₁.subtype))
  obtain ⟨σ, hσ, hσirr⟩ := exists_sigma_of_bar ψ hψs hψker
    (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1) (isChiefFactor_sectionRep ρ W₁ W₂ hcf)
  have hnt : ∃ y, σ y ≠ 1 := by
    obtain ⟨g, w, -, hw⟩ := isNoncentral_sectionRep ρ W₁ W₂ hcf hnc
    refine ⟨ψ g, fun h1 => hw ?_⟩
    rw [hσ] at h1
    rw [h1]
    simp
  have hvN : v ∈ (commutator X).comap φ := hvX
  have hψv : ψ ⟨v, hvN⟩ = ⟨φ v, hvX⟩ := Subtype.ext (hψφ _)
  have hσt : σ ⟨φ v, hvX⟩ = sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1 ⟨v, hvN⟩ := by
    rw [← hψv, hσ]
  refine ⟨hvX, SecMod W₁ W₂, inferInstance, inferInstance, inferInstance, σ, hσirr, ?_, ?_⟩
  · exact sigma_ne_one_of_not_mem_center hS hperf σ hnt hvX hvc
  · rw [hσt]
    exact (modCommRank_sectionRep_le ρ W₁ W₂ hcf.2.1 hcf.2.2.1 ⟨v, hvN⟩).trans
      (modCommRank_conjRep_le_rk hK v)

end CFSG.LocalAnalysis.WeakClosure81

end
