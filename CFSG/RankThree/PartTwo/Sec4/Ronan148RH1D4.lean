module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1G2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11
open CFSG.Assembly.RankThreeEven (projImage)

section Criteria

variable {X P : Type} [Group X] [Group P]

theorem exists_ne_comm_of_simple {E : Type*} [Group E] [Finite E] [IsSimpleGroup E]
    (h4 : 4 ∣ Nat.card E) : ∃ a b : E, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 ((by norm_num : 2 ∣ 4).trans h4)
  haveI hn : (Subgroup.zpowers g).Normal :=
    ⟨fun n hn x => by rw [hcon x n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h | h
  · have hg1 : g = 1 := by
      have := Subgroup.mem_zpowers g
      rwa [h, Subgroup.mem_bot] at this
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  · have hc : Nat.card E = 2 := by
      rw [← hg, ← Nat.card_zpowers, h, Subgroup.card_top]
    rw [hc] at h4
    norm_num at h4

theorem sl2_char_two_data {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* X) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
      Nat.card X = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let e' : X ≃* CFSG.GorensteinWalter.PSL2 F :=
    e.symm.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
  obtain ⟨hsimp, hsolv⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4
  haveI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) := hsimp
  refine ⟨e'.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hsolv
    haveI : IsMulCommutative X := ⟨⟨hcon⟩⟩
    have : Group.IsSolvable X := inferInstance
    exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
  · rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula]

theorem two_pow_dvd_of_mul_gcd {c m f Y : ℕ} (h : c * Nat.gcd 3 m = (2 ^ f) ^ 3 * Y) :
    2 ^ (3 * f) ∣ c := by
  have hd : 2 ^ (3 * f) ∣ c * Nat.gcd 3 m := by
    rw [h, mul_comm 3 f, pow_mul]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (2 ^ (3 * f)) (Nat.gcd 3 m) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 m) (by norm_num))
  exact hcop.dvd_of_dvd_mul_right hd

theorem pCore_two_eq_bot_of_odd_center' {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) : CFSG.pCore 2 K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hP : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hN with htop | hle
  · exfalso
    haveI : Group.IsPerfect K := hK.1
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
    have h2 : IsPGroup 2 K := fun g => by
      obtain ⟨k, hk⟩ := hP ⟨g, htop ▸ Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    exact RonanK429H.not_isPGroup_of_isPerfect h2
  · obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hd : Nat.card (CFSG.pCore 2 K) ∣ Nat.card (Subgroup.center K) :=
      Subgroup.card_dvd_of_le hle
    rw [hk] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hd))
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk

variable [Finite X]

theorem good427_onFree_of_derived_qs {x : X} {R : Subgroup X}
    (hR : ⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆ = R)
    (hRq : IsQuasisimple R) (hodd : Odd (Nat.card (Subgroup.center R)))
    (h60 : Nat.card R ≠ 60) (hON : Nat.card R ≠ 460815505920 * 3) :
    Good427 (Subgroup.centralizer ({x} : Set X)) ∧
      OnFree (Subgroup.centralizer ({x} : Set X)) x := by
  set C := Subgroup.centralizer ({x} : Set X) with hC
  have hCC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hRC : R ≤ C := hR ▸ hCC
  have hqs : QSList R R := eq_of_quasisimple_subnormal le_rfl
    (fun g hg s hs => mul_mem (mul_mem hg hs) (inv_mem hg)) hRq fun u _ v hv huT _ => huT v hv
  have key : ∀ K : Subgroup X, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
      K = R := by
    intro K hKC hKq hKs
    haveI : Group.IsPerfect K := hKq.1
    have hKR : K ≤ R := by
      have h := Subgroup.commutator_mono hKC hKC
      rw [Subgroup.commutator_eq_self (H := K), hR] at h
      exact h
    exact hqs K hKR hKq (isSubnormal_subgroupOf_of_le hRC hKR hKs)
  have hP : CFSG.pCore 2 R = ⊥ := pCore_two_eq_bot_of_odd_center' hRq hodd
  have hcard : Nat.card R = Nat.card (R ⧸ CFSG.pCore 2 R) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 R)
    have h2 : Nat.card (CFSG.pCore 2 R) = 1 := by rw [hP, Subgroup.card_bot]
    rwa [h2, mul_one] at h1
  refine ⟨fun K hKC hKq hKs hA5 => ?_, fun K hKC hKq hKs _ hext => ?_⟩
  · have hKR := key K hKC hKq hKs
    subst hKR
    exact h60 (hcard.trans hA5.card)
  · have hKR := key K hKC hKq hKs
    subst hKR
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
    apply hON
    rw [hcard, Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      CFSG.Sporadic.ON.card_ON, Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]

theorem good427_onFree_of_derived_simple {x : X} (hx1 : x ≠ 1) {S : Subgroup X} [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (h60 : Nat.card S ≠ 60) (hxS : ∀ s ∈ S, s * x = x * s)
    (hder : ∀ a ∈ Subgroup.centralizer ({x} : Set X), ∀ b ∈ Subgroup.centralizer ({x} : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ S) :
    Good427 (Subgroup.centralizer ({x} : Set X)) ∧
      OnFree (Subgroup.centralizer ({x} : Set X)) x := by
  have hSC : S ≤ Subgroup.centralizer ({x} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxS s hs)
  have hder' : ⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hder a ha b hb
  refine ⟨good427_of_derived_le_simple hSC hna h60 hder', fun K hKC hKq _ hxK _ => ?_⟩
  haveI : Group.IsPerfect K := hKq.1
  have hKS : K ≤ S := by
    have h1 := Subgroup.commutator_mono hKC hKC
    rw [Subgroup.commutator_eq_self (H := K)] at h1
    exact h1.trans hder'
  have hZ : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup inferInstance hna
  have hxc : (⟨x, hKS hxK⟩ : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxS g g.2)
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hx1 (congrArg Subtype.val hxc)

theorem good427_of_mulEquiv_derived {C : Subgroup X} (e : C ≃* P) {Q : Subgroup P}
    [IsSimpleGroup Q] (hna : ∃ a b : Q, a * b ≠ b * a) (h60 : Nat.card Q ≠ 60)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Q) : Good427 C := by
  set E : Subgroup X := (Q.map e.symm.toMonoidHom).map C.subtype with hE
  let eQ : Q ≃* E := (Q.equivMapOfInjective _ e.symm.injective).trans
    ((Q.map e.symm.toMonoidHom).equivMapOfInjective _ C.subtype_injective)
  haveI : IsSimpleGroup E := eQ.symm.isSimpleGroup
  have hEC : E ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine good427_of_derived_le_simple hEC ?_ ?_ ?_
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨eQ a, eQ b, fun h => hab (eQ.injective (by rw [map_mul, map_mul, h]))⟩
  · rwa [← Nat.card_congr eQ.toEquiv]
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have hmem : e (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : C)⁻¹ * (⟨b, hb⟩ : C)⁻¹) ∈ Q := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcomm _ _
    refine ⟨e.symm (e (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : C)⁻¹ * (⟨b, hb⟩ : C)⁻¹)), ⟨_, hmem, rfl⟩, ?_⟩
    rw [MulEquiv.symm_apply_apply, commutatorElement_def]
    rfl

end Criteria

namespace TriD4

section Facts


theorem finite_graphFixed
    {K : Type} [Field K] [Finite K] (σ : K →+* K) :
    Finite (graphFixedRootGroup TwistTag.D4 K σ) := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact Finite.of_injective (fun x => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective

open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof in
theorem exists_threeA_model_card
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq2 : 2 < ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ = R ∧
        IsQuasisimple R ∧ Odd (Nat.card (Subgroup.center R)) ∧
        (Nat.card R = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 - 1)) ∨
          Nat.card R = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1))) := by
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
  obtain ⟨d, hdε⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    refine ⟨_, Int.toNat_of_nonneg ?_⟩
    have h0 : (0 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := Int.natCast_nonneg _
    rcases hε with rfl | rfl
    · positivity
    · nlinarith [sq_nonneg (((ℓ ^ f : ℕ) : ℤ) - 1)]
  obtain ⟨-, -, hcomm, hSL, hSU, hquasi, hcent, -, -, hFcard, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.triality_three_six_singular_fixed_centralizers_gen hℓp hf K
      hK σ hσ L Fr hFr hε hdε g hgG hFg' Nat.prime_three (by decide) hℓ3 hq2 (tup ζ gT) ha hord vT
      hv x hx
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, _, hcomm, hquasi, ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  ·
    rw [hcent]
    have h3 : (Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) : ℤ) ∣ 3 := Int.gcd_dvd_left ..
    have h3' : Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) ∣ 3 := by exact_mod_cast h3
    exact (by decide : Odd 3).of_dvd_nat h3'
  · rcases hε with rfl | rfl
    ·
      left
      obtain ⟨e, -⟩ := hSL rfl
      haveI : Finite (RingHom.eqLocusField Fr (RingHom.id L)) :=
        Nat.finite_of_card_ne_zero (by rw [hFcard]; exact pow_ne_zero _ hℓp.ne_zero)
      rw [Nat.card_congr e.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
        CFSG.Open.StatedAPI.card_statedSL_three, hFcard]
    ·
      right
      obtain ⟨U, hU, e, -⟩ := hSU rfl
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.Sec4.E27.card_subgroup_unitarySet hf U hU, mul_assoc]

theorem good427_onFree_threeA
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Good427 (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∧
      OnFree (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
        z := by
  have hf1 : 1 ≤ f := by omega
  haveI := finite_graphFixed (K := K) σ.toRingHom
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hf)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) 2] at h'
    exact absurd h' (by decide)
  obtain ⟨ζ, hζ⟩ := KS11Lie6Proof.exists_units_orderOf_three (AlgebraicClosure K) h3L
  obtain ⟨x, k, hk, hxk, R, hR, hRq, hodd, hcard⟩ :=
    exists_threeA_model_card hf1 (by decide) hq2 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := KS11Lie6Proof.exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := KS11Lie6Proof.exists_conj_of_triEmb_conj hf1 hK hσ
    (KS11Lie5Proof.isPointIrreducible_gA hζ) hk' hk hzk hxk
  have h64 : (2 ^ f) ^ 3 ∣ Nat.card R := by
    rcases hcard with h | h <;> rw [h] <;> exact dvd_mul_right _ _
  have h60 : Nat.card R ≠ 60 := by
    intro h
    rw [h] at h64
    have h1 : (2 ^ 2) ^ 3 ≤ (2 ^ f) ^ 3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hf) 3
    have h2 := Nat.le_of_dvd (by norm_num) h64
    norm_num at h1
    omega
  have hON : Nat.card R ≠ 460815505920 * 3 := by
    intro h
    have hf3 : f ≤ 3 := by
      by_contra hf4
      push Not at hf4
      have h12 : 2 ^ 12 ∣ Nat.card R := by
        refine Dvd.dvd.trans ?_ h64
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      rw [h] at h12
      norm_num at h12
    interval_cases f <;> rcases hcard with h' | h' <;> rw [h'] at h <;> norm_num at h
  obtain ⟨hG, hO⟩ := good427_onFree_of_derived_qs hR hRq hodd h60 hON
  refine ⟨Good427.of_isConj (isConj_iff.mpr ⟨c, hc⟩).symm hG, ?_⟩
  have h1 := hO.map (MulAut.conj c⁻¹)
  have he : (MulAut.conj c⁻¹) x = z := by
    rw [MulAut.conj_apply, ← hc]
    group
  rwa [he] at h1

theorem good427_onFree_threeB
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzM : z ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Good427 (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∧
      OnFree (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
        z := by
  have h3 : ¬ 3 ∣ 2 ^ f := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  haveI := finite_graphFixed (K := K) σ.toRingHom
  obtain ⟨hcomm, -⟩ := KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ f) σ hK hσ h3 z hzM hz3 hz1
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  haveI : Finite (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := Subtype.finite
  have hF₀ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) =
      2 ^ (3 * f) := by
    rw [KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, hK, ← pow_mul, mul_comm]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) :=
    Fintype.ofFinite _
  haveI : CharP (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF₀])
  have h8 : 8 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := by
    rw [hF₀]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hs, hna, hcard⟩ := sl2_char_two_data (by omega) e
  haveI := hs
  refine good427_onFree_of_derived_simple hz1 hna ?_ (fun s hs' => ?_) hcomm
  · rw [hcard]
    intro h
    have h64 : 64 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) ^ 2 := by
      nlinarith
    have : 8 * 63 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) *
        (Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) ^ 2 - 1) :=
      Nat.mul_le_mul h8 (by omega)
    omega
  · exact Subgroup.mem_centralizer_iff.mp hzM s hs'

theorem good427_onFree_inner
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∧
      OnFree (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
        x := by
  have h3 : ¬ 3 ∣ 2 ^ f := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ f) σ hK hσ h3 x hx3 hx1
  have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  have hz : Good427 (Subgroup.centralizer ({g * x * g⁻¹} :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∧
      OnFree (Subgroup.centralizer ({g * x * g⁻¹} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (g * x * g⁻¹) := by
    rcases hg with hS | hM
    · exact good427_onFree_threeA hf hK hσ hS hz3 hz1
    · exact good427_onFree_threeB (by omega) hK hσ hσ3 hM hz3 hz1
  refine ⟨Good427.of_isConj (isConj_iff.mpr ⟨g⁻¹, by group⟩) hz.1, ?_⟩
  have h1 := hz.2.map (MulAut.conj g⁻¹)
  have he : (MulAut.conj g⁻¹) (g * x * g⁻¹) = x := by
    rw [MulAut.conj_apply]
    group
  rwa [he] at h1

theorem good427_pgl
    {π : Bool} {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] (hPi : PiField π 2 f F)
    (hq : ModThree π (2 ^ f)) {X : Type} [Group X] [Finite X] {C : Subgroup X}
    (e : C ≃* projImage (glPi π 3 (2 ^ f) F)) : Good427 C := by
  haveI : Finite (projImage (glPi π 3 (2 ^ f) F)) := Finite.of_equiv C e.toEquiv
  have hle : projImage (slPi π 3 (2 ^ f) F) ≤ projImage (glPi π 3 (2 ^ f) F) := by
    refine Subgroup.map_mono ?_
    cases π with
    | true => exact fun A _ => mem_glPi_true _ A
    | false =>
      intro A hA
      exact (mem_glPi_false hPi.unitary).mpr ((mem_slPi_false hPi.unitary).mp hA).2
  set Q : Subgroup (projImage (glPi π 3 (2 ^ f) F)) :=
    (projImage (slPi π 3 (2 ^ f) F)).subgroupOf (projImage (glPi π 3 (2 ^ f) F)) with hQ
  have hQe : Q ≃* projImage (slPi π 3 (2 ^ f) F) := Subgroup.subgroupOfEquivOfLe hle
  have hq2 : π = true ∨ 2 < 2 ^ f :=
    Or.inr (lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hf))
  haveI := CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.isSimpleGroup_projImage_slPi hPi hq2
  haveI : IsSimpleGroup Q := hQe.isSimpleGroup
  have hiso : IsoLThreePi Q 2 f :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.isoLThreePi_of_projImage_slPi hPi hq hq2 hQe
  have h64 : 2 ^ (3 * f) ∣ Nat.card Q := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
      rw [GaloisField.card 2 f (by omega), ← Nat.card_congr φ.toEquiv] at h
      exact two_pow_dvd_of_mul_gcd h
    · have h := KFacts.KS14.card_projSU_three_mul_gcd 2 f (by omega)
      rw [← Nat.card_congr φ.toEquiv] at h
      exact two_pow_dvd_of_mul_gcd h
  have h64' : 2 ^ 6 ∣ Nat.card Q := (pow_dvd_pow 2 (by omega : 6 ≤ 3 * f)).trans h64
  refine good427_of_mulEquiv_derived e (Q := Q)
    (exists_ne_comm_of_simple ((by norm_num : 4 ∣ 2 ^ 6).trans h64')) ?_ ?_
  · intro h
    rw [h] at h64'
    norm_num at h64'
  · intro a b
    rw [hQ, Subgroup.mem_subgroupOf]
    have h := CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.commutator_mem_projImage_slPi hPi a.2 b.2
    rw [commutatorElement_def] at h
    simpa using h

theorem good427_outer
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hin : ¬ KFacts.IsInnerAut α) : Good427 (Sec4.autFix α) := by
  have hf1 : 1 ≤ f := by omega
  haveI := finite_graphFixed (K := K) σ.toRingHom
  by_cases hstd : Sec4.IsStdGraphFieldConj σ α
  ·
    have hchar : ringChar K = 2 := ringChar.eq K 2
    obtain ⟨eG⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hchar
    have hγ : Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) =
        (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
    have hfixG : Nonempty (Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield σ)) := by
      obtain ⟨β, hβ | hβ⟩ := hstd
      · rw [hβ]
        exact ⟨((RonanK429Lie.autFixConjEquiv β _).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
      · rw [hβ]
        exact ⟨(((RonanK429Lie.autFixConjEquiv β _).trans
          (MulEquiv.subgroupCongr (RonanK429Lie.autFix_inv _))).trans
            (MulEquiv.subgroupCongr hγ)).trans eG⟩
    obtain ⟨eα⟩ := hfixG
    have hk := KFacts.card_fixSubfield_of_cube hf1 hK hσ
    have h3k : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    haveI := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3k
    haveI : IsSimpleGroup (Sec4.autFix α) := eα.isSimpleGroup
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) h3k
    refine good427_of_le_simple le_rfl ?_ ?_ fun _ hKC _ => hKC
    · obtain ⟨-, -, a, b, hab⟩ := hq
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      refine ⟨eα.symm a', eα.symm b', fun h => hab ?_⟩
      have h1 : a' * b' = b' * a' := eα.symm.injective (by rw [map_mul, map_mul, h])
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
    · rw [Nat.card_congr eα.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
      intro h
      unfold CFSG.Open.ordG2 at h
      have hq4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      have hA : 4096 ≤ (2 ^ f) ^ 6 := by
        calc 4096 = 4 ^ 6 := by norm_num
          _ ≤ (2 ^ f) ^ 6 := Nat.pow_le_pow_left hq4 6
      have hC : 16 ≤ (2 ^ f) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq4 2
      have : 4096 * 1 * 1 ≤ (2 ^ f) ^ 6 * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hA (by omega)) (by omega)
      omega
  ·
    obtain ⟨π, F', _, _, hPi, hq, ⟨e⟩⟩ : ∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'),
        PiField π 2 f F' ∧ ModThree π (2 ^ f) ∧
          Nonempty (Sec4.autFix α ≃* projImage (glPi π 3 (2 ^ f) F')) := by
      rcases Nat.even_or_odd f with hev | hodd
      · obtain ⟨F', _, _, hF'c, ⟨e⟩⟩ :=
          Sec8.kF89D4SecondCentEven_holds f hev hf1 K σ hK hσ α hα3 hin hstd
        refine ⟨true, F', inferInstance, inferInstance,
          ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
        obtain ⟨j, rfl⟩ := hev
        change (2 ^ (j + j)) % 3 = 1
        rw [← two_mul, pow_mul]
        norm_num [Nat.pow_mod]
      · rcases Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds
          Sec8.kF82D4SecondCent_holds f hodd K σ hK hσ α hα3 hin with hstd' |
          ⟨γ, y, -, -, -, -, F', _, _, hF'c, ⟨e⟩⟩
        · exact absurd hstd' hstd
        · refine ⟨false, F', inferInstance, inferInstance,
            ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
          obtain ⟨j, rfl⟩ := hodd
          change (2 ^ (2 * j + 1)) % 3 = 2
          rw [pow_succ, pow_mul]
          norm_num [Nat.mul_mod, Nat.pow_mod]
    exact good427_pgl hf hPi hq e

theorem noCfgS427_d4
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    (hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥) :
    NoCfgS427 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro α hα3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 h1
  by_cases hin : KFacts.IsInnerAut α
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot hZ) hord hin
    rw [autFix_conj]
    exact (good427_onFree_inner hf hK hσ hσ3 hx3 hx1).1
  · exact good427_outer hf hK hσ hα3 hin

theorem onFree_of_mulEquiv_d4
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    {S' : Type} [Group S'] (e : S' ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {y : S'}
    (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) : OnFree (Subgroup.centralizer ({y} : Set S')) y := by
  have hx3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hx1 : e y ≠ 1 := by
    rw [Ne, map_eq_one_iff e e.injective]
    exact hy1
  have h1 := (good427_onFree_inner hf hK hσ hσ3 hx3 hx1).2.map e.symm
  rwa [MulEquiv.symm_apply_apply] at h1

end Facts

end TriD4

open TriD4

section Rows


theorem rowOf427_d4
    : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → q.exponent ≠ 1 → RowOf427 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro q hq hq2 hq1 S _ _ _ hna ⟨eSX⟩
  have hm : Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) eSX⟩
  rw [hq2] at hm
  obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, -, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  have hf : 2 ≤ q.exponent := by
    have := q.exponent_pos
    omega
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
    obtain ⟨a, b, hab⟩ := hna
    exact RonanK429.center_eq_bot_of_isSimpleGroup hsimp
      ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  refine row427_of_noCfg_on ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    have hmL : Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 q.p
        q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide)
            (e'.trans eSX)⟩
    rw [hq2] at hmL
    exact RonanK429.center_eq_bot_of_trialityD4 hL hZ3 hmL
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv (e'.trans φ) (noCfgS427_d4 hf hK hσ hσ3 hZ)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3
    exact onFree_of_mulEquiv_d4 hf hK hσ hσ3 (e'.trans φ) hy1 hy3

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
