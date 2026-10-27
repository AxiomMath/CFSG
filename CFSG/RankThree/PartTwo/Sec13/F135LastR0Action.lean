module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13

theorem r0_phi_eq_one_iff {G : Type} [Group G] [Finite G] {L M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (m : M) :
    ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hM) m = 1 ↔
      (m : G) ∈ Sec4.thetaQuotCentralizer L := by
  unfold Sec4.thetaQuotCentralizer
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨⟨(m : G), hM m.2⟩, MonoidHom.mem_ker.mpr h, rfl⟩
  · rintro ⟨y, hy, hym⟩
    have hy' : y = ⟨(m : G), hM m.2⟩ := Subtype.ext hym
    subst hy'
    exact MonoidHom.mem_ker.mp hy

theorem r0_card_map_le_nine {P T : Type} [Group P] [Group T] [Finite T]
    (Q' : Subgroup P) (hQ' : IsPGroup 3 Q') (φ : P →* T) (hT : Nat.card T = 5040) :
    Nat.card (Q'.map φ) ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hQ'.map φ)
  have hdvd : Nat.card (Q'.map φ) ∣ 5040 := by
    have h := Subgroup.card_subgroup_dvd_card (Q'.map φ)
    rwa [hT] at h
  rw [hn] at hdvd ⊢
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · exfalso
    have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 h
    exact absurd (dvd_trans h27 hdvd) (by decide)

theorem r0_nine_le_card_map {G : Type} [Group G] [Finite G] {C A M : Subgroup G} {T : Type}
    [Group T] (φ : M →* T) (hφ : ∀ m : M, φ m = 1 ↔ (m : G) ∈ C) (hAM : A ≤ M)
    (hA27 : Nat.card A = 27) (hAker : Nat.card (A ⊓ C : Subgroup G) ≤ 3) :
    9 ≤ Nat.card ((A.subgroupOf M).map φ) := by
  have hcardA' : Nat.card (A.subgroupOf M) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hA27]
  have hrange : (φ.comp (A.subgroupOf M).subtype).range = (A.subgroupOf M).map φ := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hker : Nat.card (φ.comp (A.subgroupOf M).subtype).ker ≤ 3 := by
    have hmem : ∀ x : (φ.comp (A.subgroupOf M).subtype).ker, ((x.1.1 : M) : G) ∈ A ⊓ C := by
      intro x
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp x.1.2, ?_⟩
      exact (hφ x.1.1).mp (MonoidHom.mem_ker.mp x.2)
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : (φ.comp (A.subgroupOf M).subtype).ker => (⟨((x.1.1 : M) : G), hmem x⟩ : ↥(A ⊓ C)))
      ?_) hAker
    intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hxy'
  have key : Nat.card (φ.comp (A.subgroupOf M).subtype).ker *
      Nat.card (φ.comp (A.subgroupOf M).subtype).range = 27 := by
    rw [Subgroup.card_ker_mul_card_range, hcardA']
  rw [hrange] at key
  by_contra hlt
  push_neg at hlt
  have h8 : Nat.card (φ.comp (A.subgroupOf M).subtype).ker *
      Nat.card ((A.subgroupOf M).map φ) ≤ 3 * 8 :=
    Nat.mul_le_mul hker (by omega)
  rw [key] at h8
  norm_num at h8

theorem exists_mul_mem_thetaQuotCentralizer {G : Type} [Group G] [Finite G] {L A Q M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (hAQ : A ≤ Q) (hQM : Q ≤ M) (hQ : IsPGroup 3 Q)
    (hcardAut : Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 5040)
    (hA27 : Nat.card A = 27)
    (hAker : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≤ 3) :
    ∀ q ∈ Q, ∃ a ∈ A, a⁻¹ * q ∈ Sec4.thetaQuotCentralizer L := by
  intro q hq
  haveI : Finite (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  have hAM : A ≤ M := hAQ.trans hQM
  have hAQ' : A.subgroupOf M ≤ Q.subgroupOf M :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (hAQ (Subgroup.mem_subgroupOf.mp hx))
  have hQ' : IsPGroup 3 (Q.subgroupOf M) := hQ.comap_subtype
  let φ : M →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hM)
  have hφ : ∀ m : M, φ m = 1 ↔ (m : G) ∈ Sec4.thetaQuotCentralizer L :=
    fun m => r0_phi_eq_one_iff hM m
  have hle1 : Nat.card ((Q.subgroupOf M).map φ) ≤ 9 :=
    r0_card_map_le_nine (Q.subgroupOf M) hQ' φ hcardAut
  have hle2 : 9 ≤ Nat.card ((A.subgroupOf M).map φ) :=
    r0_nine_le_card_map φ hφ hAM hA27 hAker
  have heq : (A.subgroupOf M).map φ = (Q.subgroupOf M).map φ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hAQ') (hle1.trans hle2)
  obtain ⟨m, hmq⟩ : ∃ m : M, (m : G) = q := ⟨⟨q, hQM hq⟩, rfl⟩
  have hmQ : m ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr (by rw [hmq]; exact hq)
  have hmem : φ m ∈ (A.subgroupOf M).map φ := by
    rw [heq]
    exact Subgroup.mem_map_of_mem φ hmQ
  obtain ⟨a', ha'A, ha'φ⟩ := Subgroup.mem_map.mp hmem
  have hone : φ (a'⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, ha'φ, inv_mul_cancel]
  have hcoe : ((a'⁻¹ * m : M) : G) = ((a' : M) : G)⁻¹ * q := by
    rw [← hmq]
    simp
  have hfin : ((a' : M) : G)⁻¹ * q ∈ Sec4.thetaQuotCentralizer L := by
    rw [← hcoe]
    exact (hφ _).mp hone
  exact ⟨((a' : M) : G), Subgroup.mem_subgroupOf.mp ha'A, hfin⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
