module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
import CFSG.GH74.Generic.GKFCover
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise MatrixGroups

section Named

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ExclSL2 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M →
    ∀ X ∈ thetaComponentsIn M, Y ≤ X → X = delta A LB X →
      ∀ p : ℕ, p.Prime → 5 < p →
        Nonempty (↥X ⧸ Sec4.oTwoP p ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) →
          CFSG.pCore p (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥

end Named

section Tools

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem nonempty_quotient_mulEquiv_of_le {S : Type*} [Group S] [IsSimpleGroup S]
    {N K : Subgroup X} [N.Normal] [K.Normal] (hNK : N ≤ K) (hK : K ≠ ⊤) (e : X ⧸ N ≃* S) :
    Nonempty (X ⧸ K ≃* S) := by
  set f : S →* X ⧸ K :=
    (QuotientGroup.map N K (MonoidHom.id X) hNK).comp e.symm.toMonoidHom with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    refine ⟨e (x : X ⧸ N), ?_⟩
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hfi : Function.Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exfalso
      apply hK
      rw [eq_top_iff]
      intro x _
      obtain ⟨s, hs⟩ := hfs (x : X ⧸ K)
      have h1 : f s = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top s)
      rw [h1] at hs
      exact (QuotientGroup.eq_one_iff x).mp hs.symm
  exact ⟨(MulEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩

theorem isQuasisimple_projSL_three_three :
    IsQuasisimple (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv Sec4.Census.sl3EquivProjSL
    Sec4.Census.isQuasisimple_SL3_three

theorem isSimpleGroup_projSL_three_three :
    IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) := by
  have hq := Sec4.Census.isQuasisimple_SL3_three
  have : IsSimpleGroup (SL(3, ZMod 3) ⧸ Subgroup.center SL(3, ZMod 3)) := hq.2.1
  have e : SL(3, ZMod 3) ⧸ Subgroup.center SL(3, ZMod 3) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1) :=
    ((QuotientGroup.quotientMulEquivOfEq Sec4.Census.center_SL3_three).trans
      QuotientGroup.quotientBot).trans Sec4.Census.sl3EquivProjSL
  exact e.symm.isSimpleGroup

theorem card_center_eq_one_of_projSL_three_three {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) :
    Nat.card (Subgroup.center Q) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ePSL : CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1) ≃* PSL(3, ZMod 3) :=
    Sec4.Census.sl3EquivProjSL.symm.trans
      ((QuotientGroup.quotientBot.symm).trans
        (QuotientGroup.quotientMulEquivOfEq Sec4.Census.center_SL3_three.symm))
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hQ (e.trans ePSL)
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (k := ZMod 3) (n := 3) le_rfl (by rw [ZMod.card]) (by rw [ZMod.card]; omega)
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier PSL(3, ZMod 3)) = 1 := by
    rw [← Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess PSL(3, ZMod 3)).toEquiv,
      Nat.card_congr eM.toEquiv, ZMod.card, show Nat.gcd 3 (3 - 1) = 1 by norm_num,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 1) ≃ ZMod 1), Nat.card_zmod]
  rw [h2] at h1
  exact Nat.dvd_one.mp h1

theorem isPGroup_two_Q8D8 : IsPGroup 2 Sec4.Q8D8 := by
  have h64 : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 2 ^ 6 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
      DihedralGroup.nat_card]
    norm_num
  exact (IsPGroup.of_card h64).to_quotient _

theorem nontrivial_Q8D8 : Nontrivial Sec4.Q8D8 := by
  have h64 : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 64 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
      DihedralGroup.nat_card]
  have hord : orderOf ((QuaternionGroup.a 2, DihedralGroup.r 2) :
      QuaternionGroup 2 × DihedralGroup 4) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have hk : Nat.card Sec4.q8D8Kernel = 2 := by
    rw [Sec4.q8D8Kernel, Nat.card_zpowers, hord]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Sec4.q8D8Kernel
  rw [h64, hk] at h
  have hq : Nat.card Sec4.Q8D8 = 32 := by
    change Nat.card ((QuaternionGroup 2 × DihedralGroup 4) ⧸ Sec4.q8D8Kernel) = 32
    omega
  rw [← Finite.one_lt_card_iff_nontrivial, hq]
  norm_num

end Tools

section Case4

variable {X : Type} [Group X] [Finite X]

theorem isQuasisimple_of_case444 (hXp : Group.IsPerfect X)
    (hXq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (h4 : Nonempty (X ⧸ Sec4.oTwoP 3 X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) ∨
      Sec4.IsExtOf (X ⧸ Sec4.oTwoP 3 X) (alternatingGroup (Fin 5)) Sec4.Q8D8) :
    IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 X with hθdef
  set Zc := Subgroup.center (X ⧸ θ) with hZc
  set K := Zc.comap (QuotientGroup.mk' θ) with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
  have : IsSimpleGroup ((X ⧸ θ) ⧸ Zc) := hXq.2.1
  set eK := quotientComapEquiv θ Zc with heK
  have hKsimp : IsSimpleGroup (X ⧸ K) := eK.isSimpleGroup
  have hKtop : K ≠ ⊤ := by
    intro h
    have : Nontrivial (X ⧸ K) := hKsimp.toNontrivial
    exact (QuotientGroup.nontrivial_iff.mp this) h
  have hOK : Sec4.oTwoP 3 X ≤ K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance (Sec4.isSolvable_oTwoP 3)
  have hKcard : Nat.card K = Nat.card Zc * Nat.card θ := by
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index Zc
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    have hidx : K.index = Zc.index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective θ)
    have hpos : 0 < Zc.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    rw [← h2] at h3
    rw [h3] at h1
    have h4 : Nat.card K * Zc.index = (Nat.card Zc * Nat.card θ) * Zc.index := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  have hZ3 : ¬ 3 ∣ Nat.card Zc := by
    rcases h4 with h4a | hext
    ·
      obtain ⟨e4⟩ := h4a
      have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) :=
        isSimpleGroup_projSL_three_three
      obtain ⟨eS⟩ := nonempty_quotient_mulEquiv_of_le hOK hKtop e4
      have h1 := card_center_eq_one_of_projSL_three_three hXq (eK.symm.trans eS)
      rw [h1]
      norm_num
    ·
      obtain ⟨B, hBn, ⟨eB⟩, ⟨eA⟩⟩ := hext
      set Bt := B.comap (QuotientGroup.mk' (Sec4.oTwoP 3 X)) with hBt
      have hBtn : Bt.Normal := Subgroup.Normal.comap hBn _
      have hB2 : IsPGroup 2 B := isPGroup_two_Q8D8.of_equiv eB.symm
      have hBts : Group.IsSolvable Bt := by
        have : Group.IsNilpotent B := hB2.isNilpotent
        exact Sec4.isSolvable_comap_mk' (Sec4.isSolvable_oTwoP 3) inferInstance
      have hBtK : Bt ≤ K := Sec4.Census.le_of_isSolvable_of_normal hBtn hBts
      have eA' : X ⧸ Bt ≃* alternatingGroup (Fin 5) :=
        (quotientComapEquiv (Sec4.oTwoP 3 X) B).trans eA
      obtain ⟨eS⟩ := nonempty_quotient_mulEquiv_of_le hBtK hKtop eA'
      set e5 := eK.symm.trans eS
      have h := CFSG.ComponentClassification.RankTwoAlt.card_ker_dvd_two_five
        hXq.1.commutator_eq_top
        (CFSG.ComponentClassification.RankTwoAlt.quotCenterHom_surjective e5)
        (CFSG.ComponentClassification.RankTwoAlt.ker_quotCenterHom e5).le
      rw [CFSG.ComponentClassification.RankTwoAlt.ker_quotCenterHom] at h
      intro h3
      have := Nat.le_of_dvd (by norm_num) (h3.trans h)
      omega
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hZ3 h
    · exact hθ.2.2.1 h
  have hV : CFSG.pCore 3 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
    set V := CFSG.pCore 3 (X ⧸ CFSG.pCore 2 X) with hVdef
    have hVmap : (Sec4.oTwoP 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = V :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) V
    have hV3 : ¬ 3 ∣ Nat.card V := by
      intro h3
      apply hK3
      rw [← hVmap] at h3
      exact (h3.trans (Subgroup.card_map_dvd _ _)).trans (Subgroup.card_dvd_of_le hOK)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := X ⧸ CFSG.pCore 2 X))
    have hk0 : k = 0 := by
      by_contra hk0
      apply hV3
      rw [hk]
      exact dvd_pow_self 3 hk0
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq V hk
  have hO23 : Sec4.oTwoP 3 X = CFSG.pCore 2 X := by
    rw [Sec4.oTwoP, hV, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have eq23 : X ⧸ Sec4.oTwoP 3 X ≃* X ⧸ CFSG.pCore 2 X := QuotientGroup.quotientMulEquivOfEq hO23
  rcases h4 with h4a | hext
  · obtain ⟨e4⟩ := h4a
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (eq23.symm.trans e4).symm
      isQuasisimple_projSL_three_three
  ·
    exfalso
    obtain ⟨B, hBn, ⟨eB⟩, -⟩ := hext
    set B' := B.map eq23.toMonoidHom with hB'
    have hB'n : B'.Normal := hBn.map _ eq23.surjective
    have hB2 : IsPGroup 2 B := isPGroup_two_Q8D8.of_equiv eB.symm
    have hB'2 : IsPGroup 2 B' := hB2.map _
    have hB'le : B' ≤ CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) := le_sSup ⟨hB'n, hB'2⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective _ eq23.injective] at hB'le
    have : Nontrivial Sec4.Q8D8 := nontrivial_Q8D8
    have hBnt : Nontrivial B := eB.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot B).mp hBnt hB'le

end Case4

section Excl

variable {G : Type} [Group G] [Finite G]

theorem step152Excl_of {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hSL2 : Step152ExclSL2 A LB) : Step152Excl A LB := by
  intro Y hY M hM hYM hF X hX hYX hΔ hcase
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  rcases hcase with ⟨p, hp, hp5, ⟨e3⟩⟩ | h4
  · have : Fact p.Prime := ⟨hp⟩
    have hV := hSL2 Y hY M hM hYM hF X hX hYX hΔ p hp hp5 ⟨e3⟩
    have hOp : Sec4.oTwoP p ↥X = CFSG.pCore 2 ↥X := by
      rw [Sec4.oTwoP, hV, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    have e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* SL(2, ZMod p) :=
      (QuotientGroup.quotientMulEquivOfEq hOp).symm.trans e3
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (Sec4.Census.isQuasisimple_SL2 (p := p) (by omega))
  · exact isQuasisimple_of_case444 hXp hXq h4

@[expose] noncomputable def Step152ExclSL2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ExclSL2 A (lB A)

theorem step152ExclR_of (hSL2 : Step152ExclSL2R) :
    Step152ExclR :=
  fun G _ _ A c L hR => step152Excl_of (hSL2 G A c L hR)

end Excl

end CFSG.RankThree.PartTwo.Sec15
