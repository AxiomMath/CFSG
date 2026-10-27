module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProof
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def InnerCensus223 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (E D : Subgroup (MulAut Y)) (Kb : Subgroup Y) (m : ℕ),
    Sec4.IsList46 Y → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
    E ≤ (MulAut.conj : Y →* MulAut Y).range → D ≤ E → 3 ^ 2 ≤ Nat.card D →
    (∀ d ∈ D, ∀ k ∈ Kb, d k = k) →
    (∀ y : Y, (∀ d ∈ D, d y = y) → ∀ k ∈ Kb, y * k * y⁻¹ ∈ Kb) →
    Nonempty (Kb ≃* projSL 2 (GaloisField 2 m)) → 1 < m → Odd m →
    ∃ k : ℕ, Odd k ∧ Nonempty (Y ≃* projSU 4 2 k)

namespace Item223CensusProof

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_iff_of_mem {X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer X ↔
      Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hx⟩) = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    subst hyx'
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem map_ker_thetaAct {X A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (X : Set G)) :
    (Sec4.thetaAct hAN).ker.map A.subtype = A ⊓ Sec4.thetaQuotCentralizer X := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (mem_thetaQuotCentralizer_iff_of_mem (hAN a.2)).mpr ha⟩
  · rintro ⟨hxA, hxC⟩
    exact ⟨⟨x, hxA⟩, (mem_thetaQuotCentralizer_iff_of_mem (hAN hxA)).mp hxC, rfl⟩

theorem card_range_thetaAct {X A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card (Sec4.thetaAct hAN).range *
      Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = Nat.card A := by
  rw [← map_ker_thetaAct hAN, Subgroup.card_map_of_injective A.subtype_injective,
    ← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index]

theorem thetaAct_mk {X B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (X : Set G)) (b : B)
    (l : X) :
    Sec4.thetaAct hBN b (l : X ⧸ aschbacherSolvableCore 3 X) =
      ((⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) l).mp l.2⟩ : X) :
        X ⧸ aschbacherSolvableCore 3 X) := by
  rw [Sec4.thetaAct_apply, Sec4.thetaQuotMulAut_mk]
  rfl

end Item223CensusProof

open Item223CensusProof

theorem inspection223ListInner_of_census (h : InnerCensus223) : Inspection223ListInner := by
  intro G _ _ X A B K m hL hAe hA81 hAN hAC hin hBA hB27 hKX hKC hKN hK hm1 hmo
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hAN
  have hE := Sec4.isElemAbelian_range_thetaAct hAN hAe
  have hEcard : Nat.card (Sec4.thetaAct hAN).range = 3 ^ 3 := by
    have h1 := card_range_thetaAct hAN
    rw [hAC, hA81] at h1
    omega
  have hEinn := Sec4.range_thetaAct_le_inner hAN hin
  have hDE : (Sec4.thetaAct hBN).range ≤ (Sec4.thetaAct hAN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBA b.2⟩, rfl⟩
  have hDcard : 3 ^ 2 ≤ Nat.card (Sec4.thetaAct hBN).range := by
    have h1 := card_range_thetaAct hBN
    have h2 : Nat.card (B ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ 3 := by
      rw [← hAC]
      exact Subgroup.card_le_of_le (inf_le_inf_right _ hBA)
    have hpos : 0 < Nat.card (Sec4.thetaAct hBN).range := Nat.card_pos
    rw [hB27] at h1
    by_contra hlt
    have h3 : Nat.card (Sec4.thetaAct hBN).range *
        Nat.card (B ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ 8 * 3 :=
      Nat.mul_le_mul (by omega) h2
    omega
  obtain ⟨eK⟩ := hK
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := isSimpleGroup_projSL_two (by omega)
  have : IsSimpleGroup K := eK.isSimpleGroup
  have hKp : Group.IsPerfect K := isPerfect_of_mulEquiv_projSL (by omega) eK
  set ι : K.subgroupOf X →* X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype with hιdef
  have hι : Function.Injective ι := Item223KFactsProof.injective_mk_comp_subtype hKX hKp
  let eKb : ι.range ≃* projSL 2 (GaloisField 2 m) :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hKX).trans eK)
  have hfix : ∀ d ∈ (Sec4.thetaAct hBN).range, ∀ k ∈ ι.range, d k = k := by
    rintro _ ⟨b, rfl⟩ _ ⟨x, rfl⟩
    rw [hιdef, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      thetaAct_mk]
    congr 1
    apply Subtype.ext
    have hxB := Subgroup.mem_centralizer_iff.mp (hKC (Subgroup.mem_subgroupOf.mp x.2)) b b.2
    change (b : G) * ((x : X) : G) * (b : G)⁻¹ = ((x : X) : G)
    rw [hxB, mul_inv_cancel_right]
  have hnorm : ∀ y : X ⧸ aschbacherSolvableCore 3 X,
      (∀ d ∈ (Sec4.thetaAct hBN).range, d y = y) → ∀ k ∈ ι.range, y * k * y⁻¹ ∈ ι.range := by
    intro z hz k hk
    have hfixz : ∀ b : B, Item223KFactsProof.barAct hBN b z = z := fun b => hz _ ⟨b, rfl⟩
    have hB3 : IsPGroup 3 B := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.of_card hB27
    obtain ⟨y, rfl, hyC⟩ := Item223KFactsProof.exists_lift_of_fixed hBN hB3 z hfixz
    obtain ⟨x, rfl⟩ := hk
    have hyk : (y : G) * ((x : X) : G) * (y : G)⁻¹ ∈ K :=
      hKN y ⟨y.2, hyC⟩ _ (Subgroup.mem_subgroupOf.mp x.2)
    refine ⟨⟨y * (x : X) * y⁻¹, Subgroup.mem_subgroupOf.mpr hyk⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 X) (y * (x : X) * y⁻¹) =
      (y : X ⧸ aschbacherSolvableCore 3 X) * ι x * (y : X ⧸ aschbacherSolvableCore 3 X)⁻¹
    rw [map_mul, map_mul, map_inv]
    rfl
  exact h _ _ _ ι.range m hL hE hEcard hEinn hDE hDcard hfix hnorm ⟨eKb⟩ hm1 hmo

end CFSG.RankThree.PartTwo.Sec21
