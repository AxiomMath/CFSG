module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21.Item211Proof

namespace Res424Six

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

omit [Finite G] in
theorem aOne_le_of_closure {a c d : G} (hAeq : A = Subgroup.closure {a, c, d}) (ha : a ∈ A)
    (hc : c ∈ A) (hd : d ∈ A) {S : Subgroup (QuotX L A)}
    (haS : piX L A ⟨a, Subgroup.mem_sup_right ha⟩ ∈ S)
    (hcS : piX L A ⟨c, Subgroup.mem_sup_right hc⟩ ∈ S)
    (hdS : piX L A ⟨d, Subgroup.mem_sup_right hd⟩ ∈ S) : aOne L A ≤ S := by
  have hcl : Subgroup.closure ({a, c, d} : Set G) ≤ (S.comap (piX L A)).map (L ⊔ A).subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨⟨x, Subgroup.mem_sup_right ha⟩, haS, rfl⟩
    · exact ⟨⟨x, Subgroup.mem_sup_right hc⟩, hcS, rfl⟩
    · exact ⟨⟨x, Subgroup.mem_sup_right hd⟩, hdS, rfl⟩
  have hle := hAeq.le.trans hcl
  intro x hx
  obtain ⟨g, hgA, rfl⟩ := exists_eq_piX_of_mem_aOne hx
  obtain ⟨y, hy, hyg⟩ := hle hgA
  have : y = ⟨g, Subgroup.mem_sup_right hgA⟩ := Subtype.ext hyg
  rw [← this]
  exact hy

theorem mem_zpowers_of_piX (hA : IsPGroup 3 A) {x y : G} (hxA : x ∈ A) (hyA : y ∈ A)
    (h : piX L A ⟨y, Subgroup.mem_sup_right hyA⟩ ∈
      Subgroup.zpowers (piX L A ⟨x, Subgroup.mem_sup_right hxA⟩)) :
    y ∈ Subgroup.zpowers x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : aEquiv (L := L) hA (⟨x, hxA⟩ ^ k) = aEquiv (L := L) hA ⟨y, hyA⟩ := by
    apply Subtype.ext
    rw [map_zpow, Subgroup.coe_zpow, aEquiv_apply, aEquiv_apply]
    exact hk
  have h2 := congrArg Subtype.val ((aEquiv (L := L) hA).injective h1)
  rw [Subgroup.coe_zpow] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem inducesStdKind_lOne_of
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {Φ₀ : Sec21.lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : Sec21.lBar L) : QuotX L A) =
      piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {x : G} (hxA : x ∈ A) {k : KFacts.AutKind} (h : KFacts.InducesStdKind L x k) :
    KFacts.InducesStdKind (lOne L A) (piX L A ⟨x, Subgroup.mem_sup_right hxA⟩) k := by
  refine inducesStdKind_of_intertwine (lEquivTheta Φ₀).symm (mem_normalizer_lOne hAL _)
    (fun hx z => ?_) h
  apply (lEquivTheta Φ₀).injective
  rw [MulEquiv.apply_symm_apply, lEquivTheta_conj hΦ₀ hxA hx (mem_normalizer_lOne hAL _)
    ((lEquivTheta Φ₀).symm z), MulEquiv.apply_symm_apply]

theorem exists_lift_normalizer (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {n : QuotX L A} (hnL : n ∈ lOne L A)
    (hnN : n ∈ Subgroup.normalizer ((aOne L A : Subgroup (QuotX L A)) : Set (QuotX L A))) :
    ∃ (l : G) (hl : l ∈ L ⊔ A), l ∈ L ∧ l ∈ Subgroup.normalizer (A : Set G) ∧
      piX L A ⟨l, hl⟩ = n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM := isPGroup_subgroupOf (L := L) hA
  have : Fact (IsPGroup 3 (A.subgroupOf (L ⊔ A))) := ⟨hAM⟩
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hNdef
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := ↥(L ⊔ A)) Nat.prime_three).2.2.1
  have hNorm : Subgroup.normalizer
      (((A.subgroupOf (L ⊔ A)).map (QuotientGroup.mk' N) : Subgroup _) : Set _) =
      (Subgroup.normalizer ((A.subgroupOf (L ⊔ A) : Subgroup ↥(L ⊔ A)) : Set ↥(L ⊔ A))).map
        (QuotientGroup.mk' N) :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf (L ⊔ A)) N inferInstance hcop
  have hnN' : n ∈ Subgroup.normalizer
      (((A.subgroupOf (L ⊔ A)).map (QuotientGroup.mk' N) : Subgroup _) : Set _) := hnN
  rw [hNorm] at hnN'
  obtain ⟨h, hh, rfl⟩ := hnN'
  have hθL := theta_le_subgroupOf hA hAL
  have hhL : h ∈ L.subgroupOf (L ⊔ A) := by
    obtain ⟨l, hl, hlh⟩ := hnL
    have hlt : l⁻¹ * h ∈ N := by
      rw [← QuotientGroup.eq]
      exact hlh
    have := (L.subgroupOf (L ⊔ A)).mul_mem hl (hθL hlt)
    simpa using this
  refine ⟨h, h.2, Subgroup.mem_subgroupOf.mp hhL, ?_, rfl⟩
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have h1 := (Subgroup.mem_normalizer_iff.mp hh ⟨x, Subgroup.mem_sup_right hx⟩).mp
    (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_subgroupOf.mp h1

theorem false_of_isSolvable {a c : G} {K : Subgroup G} (h : Config424 G A L a c K)
    (hsol : Group.IsSolvable ↥(lOne L A ⊓
      Subgroup.centralizer {piX L A ⟨c, Subgroup.mem_sup_right h.c_mem⟩})) : False := by
  have hKLA : K ≤ L ⊔ A := h.K_le_L.trans le_sup_left
  let φ : K →* QuotX L A := (piX L A).comp (Subgroup.inclusion hKLA)
  have hrange : φ.range ≤ lOne L A ⊓
      Subgroup.centralizer {piX L A ⟨c, Subgroup.mem_sup_right h.c_mem⟩} := by
    rintro _ ⟨k, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨Subgroup.inclusion hKLA k,
      Subgroup.mem_subgroupOf.mpr (h.K_le_L k.2), rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change piX L A (Subgroup.inclusion hKLA k) * piX L A ⟨c, Subgroup.mem_sup_right h.c_mem⟩ =
      piX L A ⟨c, Subgroup.mem_sup_right h.c_mem⟩ * piX L A (Subgroup.inclusion hKLA k)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.commute_c_of_mem_K k.2)
  have hsolR : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hrange)
  have : Group.IsPerfect K := h.isPerfect_K
  have hperfR : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hR1 : ∀ k : K, φ k = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨k, hk⟩ := hne
    have : Nontrivial φ.range :=
      ⟨⟨⟨φ k, k, rfl⟩, 1, fun h' => hk (congrArg Subtype.val h')⟩⟩
    exact Group.IsPerfect.not_isSolvable φ.range hsolR
  set θ := aschbacherSolvableCore 3 ↥(L ⊔ A) with hθdef
  have hmemθ : ∀ k : K, Subgroup.inclusion hKLA k ∈ θ := fun k =>
    (QuotientGroup.eq_one_iff _).mp (hR1 k)
  let ψ : K →* θ := (Subgroup.inclusion hKLA).codRestrict θ hmemθ
  have hψinj : Function.Injective ψ := fun x y hxy =>
    Subgroup.inclusion_injective hKLA (congrArg Subtype.val hxy)
  have hθsol : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥(L ⊔ A)) Nat.prime_three).1
  have hKsol : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hψinj
  have h3 := h.three_dvd_card_K
  have : Nontrivial K := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos h3
    omega
  exact Group.IsPerfect.not_isSolvable K hKsol

end Res424Six

end CFSG.RankThree.PartTwo.Sec4
