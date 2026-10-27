module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzCover
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11

section Transfer




theorem row427_of_noCfg_on
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S')
    (hc : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → ∀ y : S', y ≠ 1 →
      y ^ 3 = 1 → ∀ K : Subgroup S', K ≤ Subgroup.centralizer ({y} : Set S') → IsQuasisimple K →
        (K.subgroupOf (Subgroup.centralizer ({y} : Set S'))).IsSubnormal → y ∈ K →
          ¬ IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))) :
    Row427 S := by
  intro G _ _ hG A hA _ hθ L hL ⟨e⟩ d hdA hd1 _ hLd K hK htype
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL) hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hσ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hσ1 : descAut L ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hLd
    have hdC := (descAut_eq_one_iff hL.1.1 ⟨d, hdN⟩).mp h1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hle := map_le_autFix hdN (hK'M.trans inf_le_right)
  have hsn := isSubnormal_bar hdN hK'M hK'sn
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, hext⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q
    have hZK : Subgroup.center (K'.subgroupOf L ⧸ CFSG.pCore 2 (K'.subgroupOf L)) = ⊥ := by
      haveI := (isA5Type_quot_congr eKL hT).isSimpleGroup
      haveI : Group.IsPerfect (K'.subgroupOf L) := hK₁q.1
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ :=
      inf_eq_bot_of_center_eq_bot hK₁q hZK le_rfl hZ3
    have eB := equivBar hK'L hinf
    exact (h (L ⧸ Subgroup.center L) ⟨e⟩) _ hσ3 hσ1 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn (isA5Type_quot_congr eB.symm hT)
  ·
    have hZ : Subgroup.center L = ⊥ := hZS L (sectionFourHyp_subgroup hG L) hL.1 hZ3 ⟨e⟩
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by rw [hZ, inf_bot_eq]
    have eB := equivBar hK'L hinf
    have hdK' : d ∈ K' := hK' ▸ hdK
    have hdL : d ∈ L := hK'L hdK'
    set y : L ⧸ Subgroup.center L := ((⟨d, hdL⟩ : L) : L ⧸ Subgroup.center L) with hy
    have hσ : descAut L ⟨d, hdN⟩ = MulAut.conj y := Ronan148S.descAut_eq_conj hdL
    have hy1 : y ≠ 1 := by
      intro h1
      apply hσ1
      rw [hσ, h1, map_one]
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, QuotientGroup.mk_one]
    rw [hσ, autFix_conj] at hle hsn
    refine hc (L ⧸ Subgroup.center L) ⟨e⟩ y hy1 hy3 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn ⟨⟨d, hdL⟩, hdK', rfl⟩ ?_
    exact Ronan148S.isExtOf_congr (quotPCoreTwoCongr (eK.trans eB)) hext

end Transfer

section OnFree

variable {X Y : Type} [Group X] [Group Y]

@[expose] def OnFree (C : Subgroup X) (y : X) : Prop :=
  ∀ K : Subgroup X, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal → y ∈ K →
    ¬ IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))

theorem OnFree.map (e : X ≃* Y) {y : X}
    (h : OnFree (Subgroup.centralizer ({y} : Set X)) y) :
    OnFree (Subgroup.centralizer ({e y} : Set Y)) (e y) := by
  intro K hKC hKq hKs hyK hext
  have hC : (Subgroup.centralizer ({e y} : Set Y)).map e.symm.toMonoidHom =
      Subgroup.centralizer ({y} : Set X) := by
    rw [centralizer_map_mulEquiv, MulEquiv.symm_apply_apply]
  have hK'C : K.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({y} : Set X) :=
    hC ▸ Subgroup.map_mono hKC
  let eK : K ≃* K.map e.symm.toMonoidHom := K.equivMapOfInjective _ e.symm.injective
  refine h _ hK'C (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq) ?_ ⟨e y, hyK, by simp⟩
    (Ronan148S.isExtOf_congr (quotPCoreTwoCongr eK) hext)
  have := isSubnormal_subgroupOf_map e.symm hKC hKs
  rwa [hC] at this

end OnFree

namespace G2

section Facts


variable {F : Type} [Field F] [Finite F]

theorem short_simple
    [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (KS11Lie4Proof.g2ShortSL2 F) ∧
      (∃ a b : KS11Lie4Proof.g2ShortSL2 F, a * b ≠ b * a) ∧
      Nat.card (KS11Lie4Proof.g2ShortSL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := F)
  let e' : KS11Lie4Proof.g2ShortSL2 F ≃* CFSG.GorensteinWalter.PSL2 F :=
    e.symm.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
  obtain ⟨hsimp, hsolv⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4
  haveI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) := hsimp
  refine ⟨e'.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hsolv
    haveI : IsMulCommutative (KS11Lie4Proof.g2ShortSL2 F) := ⟨⟨hcon⟩⟩
    have : Group.IsSolvable (KS11Lie4Proof.g2ShortSL2 F) := inferInstance
    exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
  · rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula]

theorem good427_threeB
    [CharP F 2] (h3 : 3 ∣ Nat.card F + 1) (h8 : 8 ≤ Nat.card F)
    {z : adjointGroup .G2 F} (hzM : z ∈ KS11Lie4Proof.g2LongSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : Good427 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) := by
  obtain ⟨hcomm, -⟩ := KS11Lie4Proof.g2ThreeBCentMinus_holds F h3 (by omega) z hzM hz3 hz1
  obtain ⟨hs, hna, hcard⟩ := short_simple (F := F) (by omega)
  haveI := hs
  have hSC : KS11Lie4Proof.g2ShortSL2 F ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)) :=
    fun s hs' => Subgroup.mem_centralizer_singleton_iff.mpr
      (KS11Lie4Proof.g2Short_commute_g2Long hs' hzM)
  refine good427_of_derived_le_simple hSC hna ?_ ?_
  · rw [hcard]
    intro h
    have h64 : 64 ≤ Nat.card F ^ 2 := by nlinarith
    have : 8 * 63 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hcomm x hx y hy

theorem onFree_threeB
    [CharP F 2] (h3 : 3 ∣ Nat.card F + 1) (h8 : 8 ≤ Nat.card F)
    {z : adjointGroup .G2 F} (hzM : z ∈ KS11Lie4Proof.g2LongSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : OnFree (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) z := by
  intro K hKC hKq _ hzK _
  obtain ⟨hcomm, -⟩ := KS11Lie4Proof.g2ThreeBCentMinus_holds F h3 (by omega) z hzM hz3 hz1
  obtain ⟨hs, hna, -⟩ := short_simple (F := F) (by omega)
  haveI : Group.IsPerfect K := hKq.1
  have hKS : K ≤ KS11Lie4Proof.g2ShortSL2 F := by
    have h1 := Subgroup.commutator_mono hKC hKC
    rw [Subgroup.commutator_eq_self (H := K)] at h1
    refine h1.trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hcomm x hx y hy
  have hzS := hKS hzK
  have hZ : Subgroup.center (KS11Lie4Proof.g2ShortSL2 F) = ⊥ :=
    RonanK429.center_eq_bot_of_isSimpleGroup hs hna
  have hzc : (⟨z, hzS⟩ : KS11Lie4Proof.g2ShortSL2 F) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (KS11Lie4Proof.g2Short_commute_g2Long g.2 hzM)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hz1 (congrArg Subtype.val hzc)

theorem threeA_data
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) ∧
      Odd (Nat.card (Subgroup.center (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))))) ∧
      (Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) : ℤ) =
        ((2 ^ f : ℕ) : ℤ) ^ 3 * ((((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' F
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hF h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (2 ^ f) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hF]
  have hq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hq
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hq).2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨hSU, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hq
  have hZcard : Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) L)) =
      Nat.gcd 3 (2 ^ f + 1) := by
    rw [hZ]
    exact (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL (by norm_num)).2.2
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZcard]
    exact (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  · have h₀ : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f L := ⟨Nat.prime_two, by omega, by rw [hL, ← pow_mul, mul_comm]⟩
    have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h₀ (n := 3) (by norm_num)
    have hp : ∏ i ∈ Finset.Icc 2 3, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
        (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1) := by
      rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
      norm_num
    rw [hp] at hc
    rw [Nat.card_congr e.toEquiv]
    exact hc

theorem qsList_threeA
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    QSList (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
      (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) :=
  eq_of_quasisimple_subnormal le_rfl (fun g hg s hs => mul_mem (mul_mem hg hs) (inv_mem hg))
    (threeA_data hF hf h3 hzS hz3 hz1).1 fun u _ v hv huT _ => huT v hv

theorem nine_dvd_threeA
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) := by
  have hc := (threeA_data hF hf h3 hzS hz3 hz1).2.2
  rw [hF] at h3
  obtain ⟨t, ht⟩ := h3
  have hQ : ((2 ^ f : ℕ) : ℤ) = 3 * t - 1 := by
    have : ((2 ^ f + 1 : ℕ) : ℤ) = ((3 * t : ℕ) : ℤ) := by rw [ht]
    push_cast at this ⊢
    linarith
  have h9 : (9 : ℤ) ∣ (Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) : ℤ) := by
    rw [hc, hQ]
    exact ⟨(3 * t - 1) ^ 3 * ((3 * t - 1) ^ 2 - 1) * (3 * t ^ 3 - 3 * t ^ 2 + t), by ring⟩
  exact_mod_cast h9

theorem good427_threeA
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : Good427 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) := by
  intro K hKC hKq hKs hA5
  have hKT := qsList_threeA hF hf h3 hzS hz3 hz1 K hKC hKq hKs
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hA5
  have h9 := nine_dvd_threeA hF hf h3 hzS hz3 hz1
  rw [← hKT] at h9
  exact not_dvd_sixty_of_nine_dvd h9 a (ha ▸ dvd_rfl)

theorem pCore_two_eq_bot_of_odd_center
    {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K)
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
      have h2 : 2 ∣ Nat.card (Subgroup.center K) :=
        (dvd_pow_self 2 hk0).trans hd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk

theorem onFree_threeA
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : OnFree (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) z := by
  intro K hKC hKq hKs _ hext
  have hKT := qsList_threeA hF (by omega) h3 hzS hz3 hz1 K hKC hKq hKs
  obtain ⟨hq, hodd, hc⟩ := threeA_data hF (by omega) h3 hzS hz3 hz1
  subst hKT
  have hP := pCore_two_eq_bot_of_odd_center hq hodd
  obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
  have hcardQ : Nat.card ((Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) ⧸
      CFSG.pCore 2 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))) =
      460815505920 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      CFSG.Sporadic.ON.card_ON, Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hcardK : Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) =
      460815505920 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))), hcardQ, hP,
      Subgroup.card_bot, mul_one]
  rw [hcardK] at hc
  have h15 : ((2 ^ 15 : ℕ) : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 3 := by
    have : 2 ^ 15 ∣ (2 ^ f) ^ 3 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact_mod_cast this
  have h15' : ((2 ^ 15 : ℕ) : ℤ) ∣ ((460815505920 * 3 : ℕ) : ℤ) := by
    rw [hc]
    exact h15.mul_right _
  have : 2 ^ 15 ∣ 460815505920 * 3 := by exact_mod_cast h15'
  norm_num at this

end Facts

end G2

namespace G2

section Main


variable {F : Type} [Field F] [Finite F]

theorem three_dvd_two_pow_add_one'
    {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  rw [h2]
  omega

theorem good427_inner
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {x : adjointGroup .G2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set (adjointGroup .G2 F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2Minus_holds F h3 (by omega) x hx3 hx1
  have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  have hconj : IsConj (g * x * g⁻¹) x := isConj_iff.mpr ⟨g⁻¹, by group⟩
  rcases hg with hS | hM
  · exact Good427.of_isConj hconj (good427_threeA hF (by omega) h3 hS hz3 hz1)
  · exact Good427.of_isConj hconj (good427_threeB h3 h8 hM hz3 hz1)

theorem onFree_inner
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (h3 : 3 ∣ Nat.card F + 1)
    {x : adjointGroup .G2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    OnFree (Subgroup.centralizer ({x} : Set (adjointGroup .G2 F))) x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2Minus_holds F h3 (by omega) x hx3 hx1
  have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  have hz : OnFree (Subgroup.centralizer ({g * x * g⁻¹} : Set (adjointGroup .G2 F)))
      (g * x * g⁻¹) := by
    rcases hg with hS | hM
    · exact onFree_threeA hF hf h3 hS hz3 hz1
    · exact onFree_threeB h3 h8 hM hz3 hz1
  have h1 := hz.map (MulAut.conj g⁻¹)
  have he : (MulAut.conj g⁻¹) (g * x * g⁻¹) = x := by
    rw [MulAut.conj_apply]
    group
  rwa [he] at h1

theorem good427_field
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (hodd : Odd f)
    {α : MulAut (adjointGroup .G2 F)} (hα3 : α ^ 3 = 1)
    (hout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α) : Good427 (Sec4.autFix α) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  obtain ⟨φ, hφ, k, hαk⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hchar3 h4 hα3 hout
  obtain ⟨h3f, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
  obtain ⟨m, rfl⟩ := h3f
  have hm3 : 3 ≤ m := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcard : Nat.card (fixSubfield φ) = 2 ^ m := by
    have h := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow φ
    rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
    exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
  have hfixeq : Sec4.autFix (CFSG.RankThree.PartTwo.KFacts.g2FieldHom F φ) =
      (CFSG.RankThree.PartTwo.KFacts.g2Incl φ).range := by
    ext h
    rw [Sec4.mem_autFix, CFSG.RankThree.PartTwo.KFacts.mem_range_g2Incl_iff hchar φ]
  rw [hαk, autFix_conj_eq_map, hfixeq]
  refine Good427.map_mulEquiv _ ?_
  set E := (CFSG.RankThree.PartTwo.KFacts.g2Incl φ).range with hE
  let eE : adjointGroup .G2 (fixSubfield φ) ≃* E :=
    MonoidHom.ofInjective (CFSG.RankThree.PartTwo.KFacts.g2Incl_injective φ)
  have h3k : 3 ≤ Nat.card (fixSubfield φ) := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimp := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3k
  haveI : IsSimpleGroup E := eE.symm.isSimpleGroup
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield φ) h3k
  refine good427_of_le_simple le_rfl ?_ ?_ fun _ hKC _ => hKC
  · obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨eE a', eE b', fun h => hab ?_⟩
    have h1 : a' * b' = b' * a' := eE.injective (by rw [map_mul, map_mul, h])
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
  ·
    obtain ⟨eS⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := fixSubfield φ)
    have hdvd : Nat.card (KS11Lie4Proof.g2ShortSL2 (fixSubfield φ)) ∣ Nat.card E := by
      rw [← Nat.card_congr eE.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [← Nat.card_congr eS.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hcard] at hdvd
    intro h60
    rw [h60] at hdvd
    have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    have h64 : 64 ≤ (2 ^ m) ^ 2 := by nlinarith
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have : 8 * 63 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem noCfgS427_g2
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (hodd : Odd f) :
    NoCfgS427 (adjointGroup .G2 F) := by
  have h3 : 3 ∣ Nat.card F + 1 := hF ▸ three_dvd_two_pow_add_one' hodd
  intro α hα3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 h1
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut α
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot center_adjointGroup_eq_bot) hord hin
    rw [autFix_conj]
    exact good427_inner hF hf h3 hx3 hx1
  · exact good427_field hF hf hodd hα3 hin

theorem onFree_of_mulEquiv
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 5 ≤ f) (hodd : Odd f)
    {S' : Type} [Group S'] (e : S' ≃* adjointGroup .G2 F) {y : S'} (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) : OnFree (Subgroup.centralizer ({y} : Set S')) y := by
  have h3 : 3 ∣ Nat.card F + 1 := hF ▸ three_dvd_two_pow_add_one' hodd
  have hx3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hx1 : e y ≠ 1 := by
    rw [Ne, map_eq_one_iff e e.injective]
    exact hy1
  have h1 := (onFree_inner hF hf h3 hx3 hx1).map e.symm
  rwa [MulEquiv.symm_apply_apply] at h1

theorem center_eq_bot_g2
    (hF : 5 ≤ Nat.card F) {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (θ : L ⧸ Subgroup.center L ≃* adjointGroup .G2 F) :
    Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  set ψ : L →* adjointGroup .G2 F := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψker : ψ.ker = Subgroup.center L := Res6Seitz.ker_centralQuotient θ
  have hψs : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_exists_section_of_central
    (K := F) hF hψs hψker.le
  have h := CFSG.SectionRank.ker_eq_bot_of_section_of_perfect ψ hψker.le σ hσ
  rwa [hψker] at h

end Main

end G2

open G2

section Rows


theorem rowOf427_g2_odd
    : ∀ q : TauCeti.PrimePower, q.p = 2 → Odd q.exponent →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hodd hq S _ _ hs hna ⟨eSX⟩
  have h3q : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 eSX
  rw [hq2] at hF h3q
  have eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  let eG : S ≃* adjointGroup .G2 F := eA.trans eC
  have hf3 : 3 ≤ q.exponent := by
    obtain ⟨j, hj⟩ := hodd
    by_contra hlt
    push Not at hlt
    have : q.exponent = 1 := by omega
    rw [this] at h3q
    norm_num at h3q
  rcases (by obtain ⟨j, hj⟩ := hodd; omega : q.exponent = 3 ∨ 5 ≤ q.exponent) with h3 | h5
  ·
    have hF8 : Nat.card F = 8 := by rw [hF, h3]; norm_num
    refine row427_of_noCfg' fun S' _ _ ⟨e'⟩ => ⟨NoCfgS427.of_mulEquiv (e'.trans eG)
      (noCfgS427_of_compShape not_isA5Type_of_g28CompType fun β hβ hβ1 =>
        CFSG.HardMathSupport.Dickson.Bal207.g28_compShape hF8 hβ hβ1), noONS427_of_card ?_⟩
    have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.G2 q, hq⟩ S'
      ⟨e'.trans eSX⟩
    rw [hcard]
    show ¬ 19 * 31 * 343 ∣ CFSG.Open.orderG2 q.card
    rw [TauCeti.PrimePower.card_def, hq2, h3]
    decide
  · refine row427_of_noCfg_on ?_ ?_ ?_
    · intro L _ _ _ hL _ ⟨e'⟩
      exact center_eq_bot_g2 (by rw [hF]; calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf3) hL ((e'.trans eSX).trans
          (eSX.symm.trans eG))
    · intro S' _ _ ⟨e'⟩
      exact NoCfgS427.of_mulEquiv (e'.trans eG) (noCfgS427_g2 hF h5 hodd)
    · intro S' _ _ ⟨e'⟩ y hy1 hy3
      exact onFree_of_mulEquiv hF h5 hodd (e'.trans eG) hy1 hy3

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
