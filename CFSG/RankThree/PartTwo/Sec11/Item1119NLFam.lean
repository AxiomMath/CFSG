module

public import CFSG.RankThree.PartTwo.Sec11.Item1119NLSL2
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
public import CFSG.RankThree.PartTwo.Sec11.Item119
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentCore
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

section Fam


theorem isSL2_G2 {Z : Type} [Group Z] [Finite Z]
    (hZq : ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo Z q)
    {α : MulAut Z} {J : Subgroup Z} (hα3 : α ^ 3 = 1)
    (hJα : J ∈ thetaComponentsIn (Sec4.Item426.fixSub α))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : IsSL2 J := by
  obtain ⟨q, hq, ⟨e0⟩⟩ := hZq
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.G2 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, ⟨e0⟩⟩, Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424G2_holds Z hZ α J hα3 hno hJα hJT
  obtain ⟨z, rfl⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := hα3
  rcases KS11Lie3Proof.splitFamily_g2 Z hZ with hZ' | hno
  swap
  · exact (hno z J hz3 hJα hJT).elim
  obtain ⟨K, _, _, hK3, hK4, e, hezM, hB⟩ := KS11Lie4Proof.exists_g2_threeB
    (KS11Lie4Proof.g2ThreeConjSL2_of_minus KS11Lie7Proof.g2ThreeConjSL2Minus_holds)
    (KS11Lie4Proof.g2ThreeACent_of_minus KS11Lie7Proof.g2ThreeACentMinus_holds)
    KS11Lie4Proof.g2ThreeBCent_holds hZ' hz3 hJα hJT
  have hJS : J = (KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom := hB.eq hJα
  obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  subst hJS
  exact ⟨K, inferInstance, inferInstance, hK4,
    ⟨(Item1120V0Bar.G2eComapMulEquiv e (KS11Lie4Proof.g2ShortSL2 K)).trans e₂.symm⟩⟩

theorem isSL2_D4 {Z : Type} [Group Z] [Finite Z]
    (hZq : ∃ n : ℕ, Sec8.IsoTrialityD4 Z n)
    {α : MulAut Z} {J : Subgroup Z} (hα3 : α ^ 3 = 1)
    (hJα : J ∈ thetaComponentsIn (Sec4.Item426.fixSub α))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : IsSL2 J := by
  obtain ⟨n, qT, hq, hp2, hn, ⟨e0⟩⟩ := hZq
  have hn1 : 1 ≤ n := by
    rw [← hn]
    exact qT.exponent_pos
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 qT hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hcomm : Nonempty (Z ≃* _root_.commutator Z) :=
    Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf
  have hZeven : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid), q'.p = 2 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨qT, hq, hp2, ⟨e0⟩⟩, hcomm⟩
  have hZc : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨qT, hq, ⟨e0⟩⟩, hcomm⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424D4Even_holds Z hZeven α J hα3 hno hJα hJT
  obtain ⟨z, rfl⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := hα3
  have hcen : Subgroup.center Z = ⊥ := KS11Lie3Proof.center_eq_bot_d4 Z hZc
  have hcent : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (MonoidHom.mem_ker.mp hx)
    rw [hcen, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  have hz3' : z ^ 3 = 1 := hcent (by rw [map_pow, hz3, map_one])
  obtain ⟨K, _, _, σK, hKcard, hσK, ⟨E⟩⟩ :=
    Item1118Res3Proof.exists_d4_model_pow e0 hcomm.some
  rw [hp2, hn] at hKcard hσK
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hσK3 : σK ^ 3 = 1 := by
    apply RingEquiv.ext
    intro c
    haveI : Fintype K := Fintype.ofFinite K
    have h1 : σK (σK (σK c)) = c := by
      rw [hσK, hσK, hσK, ← pow_mul, ← pow_mul]
      have h2 : 2 ^ n * (2 ^ n * 2 ^ n) = Fintype.card K := by
        rw [← Nat.card_eq_fintype_card, hKcard]
        ring
      rw [h2, FiniteField.pow_card]
    exact h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σK.toRingHom) :=
    Item1120V0Bar.isSimpleGroup_graphFixedRootGroup_d4 (ℓ := 2) hn1 hKcard hσK
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    have hT := KS11Lie2Proof.hasType424_of_mem hJα hJT
    rw [map_one, Sec4.Item426.fixSub_one] at hT
    exact KS11Lie4Proof.not_hasType424_d4 hσK3
      ((hT.of_mulEquiv Subgroup.topEquiv).of_mulEquiv E)
  have hez3 : E z ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
  have hez1 : E z ≠ 1 := fun h => hz1 (E.injective (h.trans (map_one E).symm))
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ n) σK hKcard hσK h3 (E z) hez3 hez1
  set e' : Z ≃* graphFixedRootGroup TwistTag.D4 K σK.toRingHom := E.trans (MulAut.conj g)
    with he'
  have hmem : e' z ∈ KS11Lie4Proof.d4ShortSL2 K σK.toRingHom ∨ e' z ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 K σK.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) := hg
  obtain ⟨-, hB⟩ := KS11Lie4Proof.threeBAt_d4 KS11Lie6Proof.d4ThreeACent_holds
    KS11Lie6Proof.d4ThreeBCent_holds hKcard hσK h3 hσK3 e' hz3' hz1 hmem hJα hJT
  have hJS : J = (KS11Lie4Proof.d4ShortSL2 K σK.toRingHom).comap e'.toMonoidHom :=
    hB.eq hJα
  obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 (K := K) hσK3
  have hFin : Finite (orbitField TwistTag.D4 K σK.toRingHom
      KS11Lie4Proof.d4Outer) := Subtype.finite
  have hF4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σK.toRingHom
      KS11Lie4Proof.d4Outer) := by
    rw [KS11Lie4Proof.natCard_orbitField_d4Outer hσK3, hKcard]
    have : 2 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  subst hJS
  exact ⟨_, inferInstance, hFin, hF4,
    ⟨(Item1120V0Bar.G2eComapMulEquiv e' (KS11Lie4Proof.d4ShortSL2 K σK.toRingHom)).trans
      e₂.symm⟩⟩

end Fam

theorem isSL2_slPi_two {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) : IsSL2 (slPi π 2 (p ^ f) Kf) := by
  have := hKf.finite
  have : Fact p.Prime := ⟨hKf.prime⟩
  cases π
  · have hcard : Nat.card Kf = (p ^ f) ^ 2 := hKf.card
    have : CharP Kf p := hKf.unitary.charP
    have hq' : p ^ f % 3 = 2 := hq
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := Kf) (r := p) (f := f) hcard
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield (F := Kf) (p := p) (f := f) hcard
    exact ⟨_, inferInstance, inferInstance, by rw [hF]; omega, ⟨e.symm⟩⟩
  · have hcard : Nat.card Kf = p ^ f := hKf.card
    have hq' : p ^ f % 3 = 1 := hq
    exact ⟨Kf, inferInstance, inferInstance, by rw [hcard]; omega, ⟨statedSLEquiv 2 Kf⟩⟩

theorem isSL2_L3 {G : Type} [Group G] [Finite G] {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K)) :
    IsSL2 ((K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) := by
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := KS11LieProof.exists_model hY hcN hc3 hK
  obtain ⟨h₀, hh₀, e, -, -, hαc, hKblock⟩ :=
    KS11LieProof.core_block hcN hc3 hK hT hKf hq hq2 φ
  have hblk := KS11LieProof.block_mem_image hcN hc3 hK hT hKf hq hq2 φ hh₀ hαc hKblock
  have himg := KS11LieProof.exists_block_of_mem hKf φ hh₀ hKblock
  obtain ⟨F, _, _, hF4, ⟨e2⟩⟩ := isSL2_slPi_two hKf hq hq2
  set J := (K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hJ
  have hmapJ : J.map φ.toMonoidHom = (KS11LieProof.blockProj hKf hh₀).range := by
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hj
      obtain ⟨B, hB⟩ := himg y (Subgroup.mem_subgroupOf.mp hy)
      exact ⟨B, hB.symm⟩
    · rintro ⟨B, rfl⟩
      obtain ⟨y, hyK, hy⟩ := hblk B
      exact ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) y,
        ⟨y, Subgroup.mem_subgroupOf.mpr hyK, rfl⟩, hy⟩
  have e1 : J ≃* (KS11LieProof.blockProj hKf hh₀).range :=
    (φ.subgroupMap J).trans (MulEquiv.subgroupCongr hmapJ)
  exact ⟨F, inferInstance, inferInstance, hF4,
    ⟨e1.trans ((MonoidHom.ofInjective (KS11LieProof.blockProj_injective hKf hh₀)).symm.trans e2)⟩⟩

end CFSG.RankThree.PartTwo.Sec11.Item1119NL

end
