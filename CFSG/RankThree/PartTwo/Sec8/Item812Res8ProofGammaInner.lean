module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofOmega
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Second
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.FFC2G2
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
import CFSG.RankThree.PartTwo.KFacts.K71Item89
public import CFSG.Quasithin.Background.B5FinOutAlt
public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Recognition.CertU33DcPG

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

@[expose] def IsoPGLThree (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (X ≃* projImage (Sec4.glPi true 3 q K))

namespace Item812Res8

theorem isoPGLThree_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (h : IsoPGLThree Y q) : IsoPGLThree X q := by
  obtain ⟨K, hK, hKf, hKc, ⟨φ⟩⟩ := h
  exact ⟨K, hK, hKf, hKc, ⟨e.trans φ⟩⟩


theorem card_inSubgroup_perfectResidual_dvd {H : Type} [Group H] (C : Subgroup H) :
    Nat.card (inSubgroup perfectResidual C) ∣ Nat.card C := by
  rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_inSubgroup_perfectResidual_eq {H M : Type} [Group H] [Group M] {C : Subgroup H}
    (φ : C ≃* M) : Nat.card (inSubgroup perfectResidual C) = Nat.card (perfectResidual M) := by
  rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective,
    ← KFacts.perfectResidual_map_mulEquiv φ,
    Subgroup.card_map_of_injective φ.injective]

theorem perfectResidual_le_commutator (H : Type*) [Group H] :
    perfectResidual H ≤ commutator H := by
  have h := iInf_le (fun i => derivedSeries H i) 1
  rwa [derivedSeries_one] at h

theorem card_of_isoPGUThree {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsoPGUThree X (2 ^ m)) :
    Nat.card X = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  have hF : Sec4.PiField false 2 m K := ⟨Nat.prime_two, hm, hK⟩
  rw [Nat.card_congr φ.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hF, Sec13.card_slPi_three hF]
  rfl

theorem card_of_isoPGLThree {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsoPGLThree X (2 ^ m)) :
    Nat.card X = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  have hF : Sec4.PiField true 2 m K := ⟨Nat.prime_two, hm, hK⟩
  rw [Nat.card_congr φ.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hF, Sec13.card_slPi_three hF]
  rfl

theorem card_of_isoSUThree {X : Type} [Group X] {f : ℕ} (h : IsoSUThree X (2 ^ f)) :
    Nat.card X = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  rw [Nat.card_congr φ.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK]

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.QuasithinUnique.Bridge.Alt57Model CFSG.Open in
theorem card_commutator_g2_two
    {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) :
    Nat.card ↥⁅H, H⁆ = 6048 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := CFSG.Quasithin.nonempty_commutator_equiv e
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  let F : ↥⁅H, H⁆ ≃* U33G := (((f1.trans f2).trans f3).trans u33EquivSubG2.symm)
  rw [Nat.card_congr F.toEquiv]
  exact card_u33Pres

section

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}

theorem false_of_card_dvd {m N : ℕ}
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1))
    (hC : Nat.card (barCentralizer (Subgroup.zpowers d) L) = N)
    (hN : ¬ (2 ^ m) ^ 3 * (((2 ^ m) ^ 3) ^ 2 - 1) ∣ N) : False := by
  have h := card_inSubgroup_perfectResidual_dvd (barCentralizer (Subgroup.zpowers d) L)
  rw [hres, hC, mul_comm 3 m, pow_mul] at h
  exact hN h

end

end Item812Res8


@[expose] def KF89D4SecondCentY0Even : Prop :=
  ∀ n : ℕ, Even n → 1 ≤ n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
      IsoPGLThree (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ)) (2 ^ n)

@[expose] def KF89D4SecondCentEven : Prop :=
  ∀ n : ℕ, Even n → 1 ≤ n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α ^ 3 = 1 → ¬ IsInnerAut α → ¬ Sec4.IsStdGraphFieldConj σ α →
        IsoPGLThree (Sec4.autFix α) (2 ^ n)


open Item812Res8 Item8ModelProof LangTwistedProof in
theorem kF89D4SecondCentEven_of_y0
    (hY0 : KF89D4SecondCentY0Even) : KF89D4SecondCentEven := by
  intro n hev hn K _ _ σ hK hσ α hα3 hαin hstd
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  have hσ₀3 : σ₀ ^ 3 = 1 := fieldActor_pow_three hK hσ
  have key : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, σ₀ y = y → orderOf y = 3 →
      ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * σ₀) →
        IsoPGLThree (Sec4.autFix (MulAut.conj y * σ₀)) (2 ^ n) := by
    intro y hyσ hy3 hnstd
    have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    have hg3 : (MulAut.conj y * σ₀) ^ 3 = 1 := by
      rw [conj_mul_pow_three σ₀ hσ₀3, hyσ, hyσ, ← pow_three', hy3', map_one]
    obtain ⟨h, y', hy', hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
      d4DiagramCentIrred_holds d4SecondCentIrred_holds hK hσ y hg3
    rcases hy' with hy1 | hy0
    · exfalso
      apply hnstd
      have hy'1 : y' = 1 := Subtype.ext hy1
      refine ⟨MulAut.conj h⁻¹, Or.inl ?_⟩
      rw [hyy, hy'1, map_one, one_mul]
    · have hy'0 : y' = d4TrialityY0Elt K σ := Subtype.ext hy0
      obtain ⟨F, hF, hFf, hFc, ⟨e⟩⟩ := hY0 n hev hn K σ hK hσ
      refine ⟨F, hF, hFf, hFc, ⟨?_⟩⟩
      rw [hyy, hy'0, ← mulAut_congr_eq]
      exact (Sec4.autFixCongrEquiv _ _).trans e
  rcases lang_cases kF82D4LangCoset_holds hn hK hσ hα3 hαin with hstd' | ⟨β, y, hy, hy3, hαβ | hαβ⟩
  · exact (hstd hstd').elim
  · have hcongr : β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ =
        MulAut.congr β (MulAut.conj y * fieldActor σ σ) := by
      ext x
      rfl
    have hnstd : ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * fieldActor σ σ) := by
      rintro ⟨β', h | h⟩
      · exact hstd ⟨β * β', Or.inl (by rw [hαβ, h]; group)⟩
      · exact hstd ⟨β * β', Or.inr (by rw [hαβ, h]; group)⟩
    rw [hαβ, hcongr]
    exact isoPGLThree_of_mulEquiv (Sec4.autFixCongrEquiv β _) (key y hy hy3 hnstd)
  · have hcongr : β * (MulAut.conj y * fieldActor σ σ) * β⁻¹ =
        MulAut.congr β (MulAut.conj y * fieldActor σ σ) := by
      ext x
      rfl
    have hnstd : ¬ Sec4.IsStdGraphFieldConj σ (MulAut.conj y * fieldActor σ σ) := by
      rintro ⟨β', h | h⟩
      · refine hstd ⟨β * β', Or.inr ?_⟩
        rw [← inv_inv α, hαβ, h]
        group
      · refine hstd ⟨β * β', Or.inl ?_⟩
        rw [← inv_inv α, hαβ, h]
        group
    rw [← autFix_inv, hαβ, hcongr]
    exact isoPGLThree_of_mulEquiv (Sec4.autFixCongrEquiv β _) (key y hy hy3 hnstd)

namespace Item812Res8

theorem card_perfectResidual_g2_ne
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) :
    Nat.card (perfectResidual (adjointGroup .G2 K)) ≠ 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
  have hq : 2 ≤ 2 ^ m := two_le_two_pow hm
  have h3m : 2 ^ (3 * m) = (2 ^ m) ^ 3 := by rw [mul_comm, pow_mul]
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    obtain rfl : m = 1 := by omega
    set H := adjointGroup .G2 K
    obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
    obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hK (Subgroup.topEquiv.trans E)
    have hcard := card_commutator_g2_two hK (Subgroup.topEquiv.trans E)
    have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    have heq : perfectResidual H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      le_antisymm (perfectResidual_le_commutator H)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
    rw [heq, hcard]
    norm_num
  ·
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hperf := CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K h3
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf, Subgroup.card_top,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, h3m, CFSG.Open.ordG2]
    exact fun h => ne_g2 hq h.symm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}

theorem innerDiag_of_projSp {m : ℕ} (hm : 1 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * m)))
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := e₁.trans (projSpEquivStatedProj 2 (GaloisField 2 (3 * m)))
  by_cases hout : InducesOuterTheta d L
  · exfalso
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := m) (by omega) hd3 hout ⟨e₁⟩
    refine false_of_card_dvd hres ((Nat.card_congr ι.toEquiv).trans
      (Sec19.Step1911Proof.card_projSp_two hm)) ?_
    rw [pow_mul]
    exact not_dvd_symplectic (two_le_two_pow hm)
  · exact Or.inl (.psp4even (GaloisField 2 (3 * m))
      ⟨E, (inducesKind_inner_iff L _ E d).mpr ⟨hdN, hout⟩⟩)

theorem innerDiag_of_projSU {m : ℕ} (hm : 1 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * m))
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := unitaryFieldData_galoisField 2 (3 * m) (by omega)
  have hq : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  set E := e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)
  by_cases hout : InducesOuterTheta d L
  · rcases inducesKindPSU3_diagonal_or_field L hq hd3 hout E with hdg | hf
    · exact Or.inr (.psu3 hU hq ⟨E, hdg⟩)
    · exfalso
      obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq hd3 ⟨E, hf⟩
      obtain rfl : f₀ = m := by omega
      refine false_of_card_dvd hres (card_of_isoPGUThree hm hC) ?_
      exact not_dvd_unitary (two_le_two_pow hm)
  · exact Or.inl (.psu3 hU hq ⟨E, (inducesKind_inner_iff L _ E d).mpr ⟨hdN, hout⟩⟩)

theorem innerDiag_of_isoSUThree {m : ℕ} (hm : 1 ≤ m)
    (hL : IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)))
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hL
    obtain ⟨e₂⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU (by omega : 1 ≤ 3 * m)
      (Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)) hK
    exact innerDiag_of_projSU hm (e₁.trans e₂) hdN hd3 hres
  · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := id hL
    have hU : UnitaryFieldData 2 (3 * m) K :=
      ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : 2 < 2 ^ (3 * m) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
    have E : L ⧸ aschbacherSolvableCore 3 L ≃*
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 * m) K 3 := e₁
    by_cases hout : InducesOuterTheta d L
    · rcases inducesKindSU3_diagonal_or_field L hU hq hd3 hout E with hdg | hf
      · exact Or.inr (.su3 hU hq hdg)
      · exfalso
        have hC := KFacts.isoSUThree_barCentralizer_of_inducesStdKind hmo hL hd3 (.su3 hU hq hf)
        refine false_of_card_dvd hres (card_of_isoSUThree hC) ?_
        exact not_dvd_unitary (two_le_two_pow hm)
    · exact Or.inl (.su3 hU hq ((inducesKindSU3_inner_iff L hU hq E d).mpr ⟨hdN, hout⟩))

theorem innerDiag_of_g2
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (3 * m))
    (E : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup .G2 K)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hout : InducesOuterTheta d L
  · exfalso
    obtain ⟨-, k, _, _, hk, ⟨φ⟩⟩ := KFacts.barCentralizer_mulEquiv_g2 (by omega) hK hd3 hout E
    exact card_perfectResidual_g2_ne hm hk ((card_inSubgroup_perfectResidual_eq φ).symm.trans hres)
  · have := Fintype.ofFinite K
    have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := 3 * m)
      (by rw [← Nat.card_eq_fintype_card, hK])
    have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Or.inl (.g2 K hK3 hK4 ⟨E, (inducesKind_inner_iff L _ E d).mpr ⟨hdN, hout⟩⟩)

theorem exists_barCentralizer_mulEquiv_reeGamma' {X : Subgroup G}
    {a : G} {k : ℕ} (hk1 : 1 ≤ k) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * k + 1))
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* ReeTag.F4.reeGamma K k) (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a X) :
    ∃ (b : ℕ) (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' ReeTag.F4.prime),
      Nat.card k' = 2 ^ (2 * b + 1) ∧ 3 * (2 * b + 1) = 2 * k + 1 ∧
        Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* ReeTag.F4.reeGamma k' b) :=
  Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index hk1 hK e ha3 hout


theorem innerDiag_of_trialityD4
    (hEv : KF89D4SecondCentEven) {m : ℕ}
    (hL : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) m)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hL
  by_cases hout : InducesOuterTheta d L
  · exfalso
    set τ := inducedAutHom L E ⟨d, hdN⟩ with hτ
    have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L E hdN hd3
    have hτin : ¬ IsInnerAut τ := (not_isInnerAut_inducedAutHom_iff L E hdN).mpr hout
    have hCτ : barCentralizer (Subgroup.zpowers d) L ≃* Sec4.autFix τ :=
      (MulEquiv.subgroupCongr (barCentralizer_zpowers_eq_autFix hdN)).trans
        (autFixCongrEquiv E _).symm
    have hq := two_le_two_pow hm1
    by_cases hstd : Sec4.IsStdGraphFieldConj σ τ
    · obtain ⟨β, hβ⟩ := hstd
      obtain ⟨k, _, _, hk, ⟨φ⟩⟩ :=
        isoGTwoEven_barCentralizer_of_conj_fieldActor hm1 hK hσ E hdN β hβ
      exact card_perfectResidual_g2_ne hm1 hk
        ((card_inSubgroup_perfectResidual_eq φ).symm.trans hres)
    · rcases Nat.even_or_odd m with hev | hodd
      · have hP := hEv m hev hm1 K σ hK hσ τ hτ3 hτin hstd
        exact false_of_card_dvd hres
          (card_of_isoPGLThree hm1 (isoPGLThree_of_mulEquiv hCτ hP)) (not_dvd_linear hq)
      · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ
          hK hσ τ hτ3 hτin with hs | ⟨-, -, -, -, -, -, hP⟩
        · exact hstd hs
        · exact false_of_card_dvd hres
            (card_of_isoPGUThree hm1 (Item82OneProof.isoPGUThree_of_mulEquiv hCτ hP))
            (not_dvd_unitary hq)
  · refine Or.inl (.triality m hm1 K hK σ hσ ⟨E, hdN, ?_⟩)
    show IsInnerAut _
    by_contra hni
    exact hout ((not_isInnerAut_inducedAutHom_iff L E hdN).mp hni)

theorem innerDiag_of_ree {m : ℕ} (hm : 1 ≤ m)
    (hL : IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) m)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
      (2 ^ (3 * m)) ^ 3 * ((2 ^ (3 * m)) ^ 2 - 1) * ((2 ^ (3 * m)) ^ 3 + 1)) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  obtain ⟨k, hk, hkm, ⟨e₀⟩⟩ := hL
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk
  obtain ⟨-, k', hk'1, hkk', K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  set E := e₀.trans e₁
  by_cases hout : InducesOuterTheta d L
  · exfalso
    obtain ⟨b, k'', _, _, _, hk'', hrel, ⟨φ⟩⟩ :=
      exists_barCentralizer_mulEquiv_reeGamma' hk'1 hK E hd3 hout
    have hb : 2 * b + 1 = m := by omega
    have hC := Item86ResProof.card_of_mulEquiv_reeGamma b k'' hk'' φ
    rw [hb, Item86ResProof.ordTwistedF4_eq_factored' (two_le_two_pow hm)] at hC
    have h := card_inSubgroup_perfectResidual_dvd (barCentralizer (Subgroup.zpowers d) L)
    rw [hres, hC, mul_comm 3 m, pow_mul] at h
    exact not_dvd_ree (two_le_two_pow hm) h
  · exact Or.inl (.largeRee k' hk'1 K hK ⟨E, (inducesKind_inner_iff L _ E d).mpr ⟨hdN, hout⟩⟩)


theorem innerDiag_of_isGammaIndex (hEv : KF89D4SecondCentEven) {A : Subgroup G} {m : ℕ}
    (hdm : IsGammaIndex A L d m) (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1) :
    InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hdN
    ⟨1, by rw [pow_one]; exact hd3⟩
  obtain ⟨-, -, hm, hcase⟩ := Item87Proof.isGammaIndex_cases hdm
  rcases hcase with ⟨hRee, hSU⟩ | ⟨hL2, ⟨ι⟩⟩
  · have hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
        (2 ^ (3 * m)) ^ 3 * ((2 ^ (3 * m)) ^ 2 - 1) * ((2 ^ (3 * m)) ^ 3 + 1) := by
      rw [← himg]
      exact card_of_isoSUThree hSU
    exact innerDiag_of_ree hm hRee hdN hd3 hres
  · have hres : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) L)) =
        2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
      rw [← himg, Nat.card_congr ι.toEquiv]
      exact Item87Proof.card_projSL_two_three hm
    rcases hL2 with hD | ⟨q, hq2, hqe, hG⟩ | hU | hS | hSp
    · exact innerDiag_of_trialityD4 hEv hD hdN hd3 hres
    · obtain ⟨K, _, _, hK, ⟨E⟩⟩ := Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG
      exact innerDiag_of_g2 hm hK E hdN hd3 hres
    · obtain ⟨e₁⟩ := hU
      exact innerDiag_of_projSU hm e₁ hdN hd3 hres
    · exact innerDiag_of_isoSUThree hm hS hdN hd3 hres
    · obtain ⟨e₁⟩ := hSp
      exact innerDiag_of_projSp hm e₁ hdN hd3 hres

end Item812Res8


theorem pair89GammaInner_of (h45 : Sec4.Item4_5) (hEv : KF89D4SecondCentEven) :
    Pair89GammaInner := by
  intro G _ _ A c L a b X n h p hp d hd
  obtain ⟨e, Le⟩ := p
  obtain ⟨heA, he1, hLe, -, -, -⟩ := hp
  obtain ⟨m, hdm⟩ := hd
  have hAel := h.mem_partTwoF.1
  have h3 : ∀ u ∈ A, u ^ 3 = 1 := hAel.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3 u u.2)⟩
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz e heA)
  have hAN := Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp
    (h3 e heA) he1 hA3 hAe Le hLe
  exact Item812Res8.innerDiag_of_isGammaIndex hEv hdm (hAN hdm.1) (h3 d hdm.1)

theorem pair89GammaInner_of_y0 (h45 : Sec4.Item4_5) (hY0 : KF89D4SecondCentY0Even) :
    Pair89GammaInner :=
  pair89GammaInner_of h45 (kF89D4SecondCentEven_of_y0 hY0)

end CFSG.RankThree.PartTwo.Sec8
