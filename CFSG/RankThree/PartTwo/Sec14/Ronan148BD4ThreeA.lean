module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofLattice
import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalanceTools
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofSing

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
open scoped commutatorElement

namespace Res148BD4

theorem le_normalizer_commutator_right {G : Type*} [Group G] (V R : Subgroup G) :
    R ≤ Subgroup.normalizer ((⁅V, R⁆ : Subgroup G) : Set G) := by
  have key : ∀ s ∈ R, ∀ y ∈ ⁅V, R⁆, s * y * s⁻¹ ∈ ⁅V, R⁆ := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨x, hx, r, hr, rfl⟩ := hy
      have e : s * ⁅x, r⁆ * s⁻¹ = ⁅x, s⁆⁻¹ * ⁅x, s * r⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.commutator_mem_commutator hx hs))
        (Subgroup.commutator_mem_commutator hx (mul_mem hs hr))
    | one => simp
    | mul y z _ _ hy hz =>
      have e : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
      rw [e]
      exact mul_mem hy hz
    | inv y _ hy =>
      have e : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hy
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key s hs y, fun hy => ?_⟩
  have h := key s⁻¹ (R.inv_mem hs) _ hy
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h

theorem commutator_eq_of_quasisimple {G : Type*} [Group G] [Finite G] {R V : Subgroup G}
    (hRq : CFSG.IsQuasisimple R) (hZ : Nat.card (Subgroup.center R) = 3) (hVR : V ≤ R)
    (hV3 : Nat.Coprime 3 (Nat.card V)) (hV1 : V ≠ ⊥) : ⁅V, R⁆ = R := by
  have hRR : ⁅R, R⁆ = R := by
    have hP := hRq.1
    rw [Group.isPerfect_def] at hP
    rw [← Subgroup.map_subtype_commutator, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hNR : ⁅V, R⁆ ≤ R := (Subgroup.commutator_mono hVR le_rfl).trans hRR.le
  have hnorm : (⁅V, R⁆.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).2 (le_normalizer_commutator_right V R)
  rcases CFSG.ComponentClassification.FooteLit.le_center_or_eq_top_of_normal hRq hnorm with
    hc | htop
  · exfalso
    apply hV1
    have hc' : ⁅⁅V, R⁆, R⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro y hy r hr
      have hyc := hc (Subgroup.mem_subgroupOf.2 hy : (⟨y, hNR hy⟩ : R) ∈ ⁅V, R⁆.subgroupOf R)
      have := (Subgroup.mem_center_iff.1 hyc) ⟨r, hr⟩
      have h' : r * y = y * r := congrArg Subtype.val this
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h'.symm
    have h1 : ⁅⁅R, V⁆, R⁆ = ⊥ := by rw [Subgroup.commutator_comm R V]; exact hc'
    have h2 : ⁅⁅R, R⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hc'
    rw [hRR] at h2
    have hVZ : ∀ (v : G) (hv : v ∈ V), (⟨v, hVR hv⟩ : R) ∈ Subgroup.center R := by
      intro v hv
      refine Subgroup.mem_center_iff.2 fun r => Subtype.ext ?_
      have hm : ⁅(r : G), v⁆ ∈ ⁅R, V⁆ := Subgroup.commutator_mem_commutator r.2 hv
      rw [h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    let f : V →* Subgroup.center R :=
      { toFun := fun v => ⟨⟨v, hVR v.2⟩, hVZ v v.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun v w h => by
      have := congrArg (fun t : Subgroup.center R => ((t : R) : G)) h
      exact Subtype.ext this
    have hdvd : Nat.card V ∣ 3 := by
      rw [← hZ]
      exact Subgroup.card_dvd_of_injective f hf
    have h1V : Nat.card V = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hV3) hdvd
    exact Subgroup.eq_bot_of_card_eq V h1V
  ·
    refine le_antisymm hNR fun r hr => ?_
    have : (⟨r, hr⟩ : R) ∈ ⁅V, R⁆.subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem mem_commutator_centralizer_of_quasisimple {G : Type*} [Group G] [Finite G] {x a : G}
    (hRq : CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set G),
      Subgroup.centralizer ({x} : Set G)⁆ : Subgroup G))
    (hZ : Nat.card (Subgroup.center (⁅Subgroup.centralizer ({x} : Set G),
      Subgroup.centralizer ({x} : Set G)⁆ : Subgroup G)) = 3)
    (hxR : x ∈ ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆)
    {V : Subgroup G} (hVx : V ≤ Subgroup.centralizer ({x} : Set G))
    (ha : a ∈ Subgroup.centralizer ({x} : Set G)) (hV : V = ⁅V, Subgroup.zpowers a⁆)
    (hV3 : Nat.Coprime 3 (Nat.card V)) (hV1 : V ≠ ⊥) :
    x ∈ ⁅V, Subgroup.centralizer ({x} : Set G)⁆ := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set R := ⁅C, C⁆ with hRdef
  have hVR : V ≤ R := by
    rw [hV]
    exact Subgroup.commutator_mono hVx (Subgroup.zpowers_le.2 ha)
  have hRC : R ≤ C := Subgroup.commutator_le.2 fun y hy z hz =>
    C.mul_mem (C.mul_mem (C.mul_mem hy hz) (C.inv_mem hy)) (C.inv_mem hz)
  have hcomm := commutator_eq_of_quasisimple hRq hZ hVR hV3 hV1
  have hx : x ∈ ⁅V, R⁆ := by rw [hcomm]; exact hxR
  exact Subgroup.commutator_mono le_rfl hRC hx

section Model


@[expose] def gQ : Exp3 := ![0, 2, 0, 2]

theorem expCheck_gT : ∀ j : Fin TwistTag.D4.tag.rank,
    (∑ i, ((wordVec [0, 2, 1] (Pi.single j 1) i : ℤ) : ZMod 3) * gT i) = gQ j := by
  decide

theorem rootDiagUnit_tup_gT_mem_tsQv {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ3 : ζ ^ 3 = 1) :
    rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ tsQv Ω vT := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) Ω
    CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.vTt with hn
  have key : n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * n =
      rootDiagUnit TwistTag.D4.tag (tup ζ gQ) := by
    rw [hn, CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.canonicalRep_inv_conj_rootDiagUnit']
    congr 1
    funext j
    rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.wordProd_smul, rootChar_tup hζ3, expCheck_gT j]
    rfl
  have hc : ∀ j : Fin TwistTag.D4.tag.rank,
      ((((2 : ℕ) : ℤ) * Tag.D4.cartan 0 j + Tag.D4.cartan 2 j : ℤ) : ZMod 3) = gQ j := by
    decide
  have htup : ∀ j : Fin TwistTag.D4.tag.rank,
      tup ζ gQ j = (ζ ^ 2) ^ Tag.D4.cartan 0 j * ζ ^ Tag.D4.cartan 2 j := by
    intro j
    rw [← zpow_natCast ζ 2, ← zpow_mul, ← zpow_add,
      CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.zpow_eq_pow_val hζ3, hc j]
    rfl
  have htor : rootDiagUnit TwistTag.D4.tag (tup ζ gQ) = d4A2TorusElt (ζ ^ 2) ζ := by
    rw [d4A2TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    show rootDiagUnit TwistTag.D4.tag _ = rootDiagUnit TwistTag.D4.tag _
    congr 1
    funext j
    exact htup j
  have hmem : rootDiagUnit TwistTag.D4.tag (tup ζ gQ) ∈ subsystemGroup Tag.D4 Ω d4SuppA2 := by
    rw [htor]
    exact d4A2TorusElt_mem _ _
  exact Subgroup.mem_map.2 ⟨_, hmem, by
    show n * rootDiagUnit TwistTag.D4.tag (tup ζ gQ) * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag (tup ζ gT)
    rw [← key]
    group⟩

theorem exists_threeA_model_mem {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq2 : 2 < ℓ ^ f) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      CFSG.IsQuasisimple (⁅Subgroup.centralizer
          ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      Nat.card (Subgroup.center (⁅Subgroup.centralizer
          ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = 3 ∧
      x ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hq3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
    have : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
    omega
  obtain ⟨ε, hε, hqε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((ℓ ^ f : ℕ) : ZMod 3) = ε := by
    rcases hq3 with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L ε)
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L ε := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG hFg' ha
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  obtain ⟨hcomm, hquasi, hcent⟩ := threeSix_singular_three hℓp hℓ3 hf K hK σ hσ L Fr hFr hε
    (Or.inr hq2) g hgG hFg' (tup ζ gT) ha hord vT hv x hx
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_, ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · rw [hcomm]
    exact hquasi
  · rw [hcomm, hcent]
    have h3 : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (((ℓ ^ f : ℕ) : ℤ) - ε) 3).1 (by
        rw [Int.cast_sub, Int.cast_natCast, hqε, sub_self])
      exact_mod_cast h
    have h := Int.gcd_eq_left (by norm_num : (0 : ℤ) ≤ 3) h3
    exact_mod_cast h
  ·
    rw [hcomm, threeSixSingularR_eq_comap (range_threeSixEmb hℓp hf hK hσ Fr hFr) hgG hFg' vT,
      Subgroup.mem_comap, threeSixEmb'_apply, hx]
    have e : g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹) * g =
        rootDiagUnit TwistTag.D4.tag (tup ζ gT) := by group
    rw [e]
    exact rootDiagUnit_tup_gT_mem_tsQv hζ3

theorem mem_commutator_of_conj_dA {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq2 : 2 < ℓ ^ f) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    {b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    {x₀ : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hx₀ : x₀ ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hb : triEmb K σ (AlgebraicClosure K) b =
      x₀ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * x₀⁻¹)
    {a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hab : a * b = b * a)
    {V : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hVb : V ≤ Subgroup.centralizer ({b} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV : V = ⁅V, Subgroup.zpowers a⁆) (hV3 : Nat.Coprime 3 (Nat.card V)) (hV1 : V ≠ ⊥) :
    b ∈ ⁅V, Subgroup.centralizer ({b} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ := by
  obtain ⟨x, k, hk, hxk, hRq, hZ, hxR⟩ := exists_threeA_model_mem hf hℓ3 hK hσ hq2 hζ
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hx₀ hk hb hxk
  set e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom := MulAut.conj c with he
  have hcent : (Subgroup.centralizer
      ({b} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map e.toMonoidHom =
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      rw [← hc]
      simp only [he, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c * w * c⁻¹ * (c * b * c⁻¹) = c * (w * b) * c⁻¹ := by group
        _ = c * (b * w) * c⁻¹ := by rw [hw]
        _ = c * b * c⁻¹ * (c * w * c⁻¹) := by group
    · intro hy
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        rw [← hc] at hy
        calc c⁻¹ * y * c * b = c⁻¹ * (y * (c * b * c⁻¹)) * c := by group
          _ = c⁻¹ * (c * b * c⁻¹ * y) * c := by rw [hy]
          _ = b * (c⁻¹ * y * c) := by group
      · simp only [he, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  set V' := V.map e.toMonoidHom with hV'
  have hV'x : V' ≤
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [← hcent]
    exact Subgroup.map_mono hVb
  have ha' : e a ∈
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [← hcent]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_singleton_iff.2 hab)
  have hV'eq : V' = ⁅V', Subgroup.zpowers (e a)⁆ := by
    have hz : Subgroup.zpowers (e a) = (Subgroup.zpowers a).map e.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hz, hV', ← Subgroup.map_commutator, ← hV]
  have hV'3 : Nat.Coprime 3 (Nat.card V') := by
    rw [hV', Subgroup.card_map_of_injective e.injective]
    exact hV3
  have hV'1 : V' ≠ ⊥ := by
    rw [hV', Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact hV1
  have hmem := mem_commutator_centralizer_of_quasisimple hRq hZ hxR hV'x ha' hV'eq hV'3 hV'1
  rw [← hcent, hV', ← Subgroup.map_commutator] at hmem
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 hmem
  have hwb : w = b := e.injective (hwx.trans (by rw [← hc]; rfl))
  rw [hwb] at hw
  exact hw

end Model

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
