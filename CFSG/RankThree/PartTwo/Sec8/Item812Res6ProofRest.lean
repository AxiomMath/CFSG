module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofTrivial
public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace Item812Res6

theorem perfectResidual_ne_bot_of_le {H : Type} [Group H] {P : Subgroup H}
    (hP : Group.IsPerfect P) (hne : P ≠ ⊥) : perfectResidual H ≠ ⊥ := by
  intro h0
  apply hne
  have hle := Item87Res2Proof.le_perfectResidual_of_isPerfect hP
  rwa [h0, le_bot_iff] at hle

theorem perfectResidual_ne_bot_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : perfectResidual B ≠ ⊥) : perfectResidual A ≠ ⊥ := by
  intro h0
  apply h
  rw [← KFacts.perfectResidual_map_mulEquiv e, h0, Subgroup.map_bot]

theorem inSubgroup_perfectResidual_ne_bot {H : Type} [Group H] {C : Subgroup H}
    (h : perfectResidual C ≠ ⊥) : inSubgroup perfectResidual C ≠ ⊥ := by
  intro h0
  apply h
  rw [inSubgroup] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h0

theorem perfectResidual_ne_bot_of_isoSUThree {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (h : IsoSUThree X (2 ^ m)) : perfectResidual X ≠ ⊥ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨hq, -⟩ := Item87Proof.isQuasisimple_statedSU_three hK hm
  have : Nontrivial (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K) :=
    LocalCores.isQuasisimple_nontrivial hq
  exact perfectResidual_ne_bot_of_mulEquiv e
    (Item87Res2Proof.perfectResidual_ne_bot_of_isPerfect hq.1)

theorem perfectResidual_ne_bot_of_isoPGUThree {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (h : IsoPGUThree X (2 ^ m)) : perfectResidual X ≠ ⊥ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 m K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  set S := CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K with hS
  have hle : S ≤ glPi false 3 (2 ^ m) K := slPi_le_glPi (π := false) (fun _ => hU)
  obtain ⟨hq, -⟩ := Item87Proof.isQuasisimple_statedSU_three hK hm
  have hnt : Nontrivial S := LocalCores.isQuasisimple_nontrivial hq
  set M := projImage (glPi false 3 (2 ^ m) K) with hM
  let f : S →* M := (Matrix.ProjGenLinGroup.mk.comp S.subtype).codRestrict M
    (fun s => ⟨s, hle s.2, rfl⟩)
  have hP : Group.IsPerfect f.range :=
    hq.1.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hne : f.range ≠ ⊥ := by
    intro h0
    have hcen : ∀ s : S, (s : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      intro s
      have hs : f s ∈ f.range := ⟨s, rfl⟩
      rw [h0, Subgroup.mem_bot] at hs
      have hs' : Matrix.ProjGenLinGroup.mk (s : GL (Fin 3) K) = 1 := congrArg Subtype.val hs
      exact Matrix.ProjGenLinGroup.mk_eq_one.mp hs'
    have hcomm : ∀ s t : S, s * t = t * s := by
      intro s t
      apply Subtype.ext
      exact ((Subgroup.mem_center_iff.mp (hcen s)) t).symm
    have hbot : commutator S = ⊥ := (commutator_eq_bot_iff S).mpr ⟨⟨hcomm⟩⟩
    have htop : commutator S = ⊤ := hq.1.1
    obtain ⟨s, hs1⟩ := exists_ne (1 : S)
    have hs : s ∈ commutator S := by rw [htop]; exact Subgroup.mem_top s
    rw [hbot, Subgroup.mem_bot] at hs
    exact hs1 hs
  exact perfectResidual_ne_bot_of_mulEquiv e (perfectResidual_ne_bot_of_le hP hne)

theorem perfectResidual_reeGamma_ne_bot {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    perfectResidual (ReeTag.F4.reeGamma k b) ≠ ⊥ := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    set R := reeFixed ReeTag.F4 k 0 with hR
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hperf : Group.IsPerfect (commutator R) := hT.isPerfect hk2
    have hne : commutator R ≠ ⊥ := by
      intro h0
      obtain ⟨x, hx, y, hy, hxy⟩ := hT.nonabelian
      rw [h0, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one] at hxy
      exact hxy rfl
    exact perfectResidual_ne_bot_of_mulEquiv (ReeTag.reeFixedEquivReeGamma k 0).symm
      (perfectResidual_ne_bot_of_le hperf hne)
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have h4096 := Item812Res2.card_reeGamma_ge hk
    have : Nontrivial (ReeTag.F4.reeGamma k b) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact Item87Res2Proof.perfectResidual_ne_bot_of_isPerfect hperf

end Item812Res6

open Item812Res6


namespace Item812Res6

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}

theorem perfectResidual_ne_bot_of_projSU {m : ℕ} (hm : 2 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * m)) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    perfectResidual (barCentralizer (Subgroup.zpowers x) L) ≠ ⊥ := by
  have hout : InducesOuterTheta x L := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
  have h3m : 1 ≤ 3 * m := by omega
  have hU := unitaryFieldData_galoisField 2 (3 * m) h3m
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  rcases Nat.even_or_odd m with hme | hmo
  ·
    have hme3 : Even (3 * m) := hme.mul_left 3
    have hq := Item82OneProof.two_pow_mod_three_of_even hme3
    set E := e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)
    rcases KFacts.inducesKindPSU3_diagonal_or_field (h := hU) L hq2 hx3 hout E with hd | hf
    · exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd hx3).elim
    · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq2 hx3 ⟨E, hf⟩
      obtain rfl : f₀ = m := by omega
      exact perfectResidual_ne_bot_of_isoPGUThree hm hC
  ·
    have hmo3 : Odd (3 * m) := Nat.odd_mul.mpr ⟨by decide, hmo⟩
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)).symm
        (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
        CFSG.Open.ordTwistedA 2 (2 ^ (3 * m)) :=
      (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
    have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
    rcases hk with hk | hk
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, hq, hkK⟩ | hO
      · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq hx3 hkK
        obtain rfl : f₀ = m := by omega
        exact perfectResidual_ne_bot_of_isoPGUThree hm hC
      · exact (hodd hO).elim
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, -, hkK⟩ | hO
      · exact (KFacts.not_inducesKindPSU3_graphField hK hkK).elim
      · exact (hodd hO).elim

theorem perfectResidual_ne_bot_of_isoSUThree_quot {m : ℕ} (hm : 2 ≤ m)
    (hL : IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m))) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    perfectResidual (barCentralizer (Subgroup.zpowers x) L) ≠ ⊥ := by
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hL
    obtain ⟨e₂⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU (by omega : 1 ≤ 3 * m)
      (Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)) hK
    exact perfectResidual_ne_bot_of_projSU hm (e₁.trans e₂) hx3 hk
  · rcases hk with hk | hk
    · exact perfectResidual_ne_bot_of_isoSUThree hm
        (KFacts.isoSUThree_barCentralizer_of_inducesStdKind hmo hL hx3 hk)
    · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree (by omega)
        (KFacts.three_dvd_two_pow_three_mul_add_one hmo) hL hk).elim

end Item812Res6


theorem kF87INontrivRest_holds : KF87INontrivRest := by
  intro G _ _ L x m hm htype hU3 hx3 hk
  refine inSubgroup_perfectResidual_ne_bot ?_
  rcases htype with ⟨k, hk', hkm, ⟨e₀⟩⟩ | hU | hS
  ·
    have hout : InducesOuterTheta x L := by
      rcases hk with h | h
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
    obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
    obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) hx3 hout
    exact perfectResidual_ne_bot_of_mulEquiv φ (perfectResidual_reeGamma_ne_bot hk₀)
  ·
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · obtain rfl : m = 1 := by omega
        exact (hU3 (Or.inl hU)).elim
      · exact h
    obtain ⟨e₁⟩ := hU
    exact Item812Res6.perfectResidual_ne_bot_of_projSU hm2 e₁ hx3 hk
  ·
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · obtain rfl : m = 1 := by omega
        exact (hU3 (Or.inr hS)).elim
      · exact h
    exact Item812Res6.perfectResidual_ne_bot_of_isoSUThree_quot hm2 hS hx3 hk


theorem kF87INontriv_holds : KF87INontriv :=
  kF87INontriv_of kFG2TwoNonsolv_holds kF87INontrivRest_holds

end CFSG.RankThree.PartTwo.Sec8
