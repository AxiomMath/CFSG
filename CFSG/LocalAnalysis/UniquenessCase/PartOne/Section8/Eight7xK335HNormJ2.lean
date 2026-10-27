module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNorm
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem k335hj_disjoint_zpowers {X : Type} [Group X] {Z : Subgroup X} {t : X}
    (ht : t ^ 3 = 1) (htZ : t ∉ Z) : Disjoint Z (Subgroup.zpowers t) := by
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ Z.one_mem)
  have hord : orderOf t = 3 := orderOf_eq_prime ht ht1
  have hcardz : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, hord]
  rw [Subgroup.disjoint_def]
  intro x hxZ hxt
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    (H := (Z ⊓ Subgroup.zpowers t).subgroupOf (Subgroup.zpowers t))
    (hp := ⟨by rw [hcardz]; exact Nat.prime_three⟩) with h | h
  · have hdisj : Disjoint (Z ⊓ Subgroup.zpowers t) (Subgroup.zpowers t) :=
      Subgroup.subgroupOf_eq_bot.mp h
    exact Subgroup.disjoint_def.mp hdisj ⟨hxZ, hxt⟩ hxt
  · have hle : Subgroup.zpowers t ≤ Z ⊓ Subgroup.zpowers t := Subgroup.subgroupOf_eq_top.mp h
    exact (htZ ((Subgroup.mem_inf.mp (hle (Subgroup.mem_zpowers t))).1)).elim

private theorem k335hj_exists_second {X : Type} [Group X] [Finite X] {P Q : Subgroup X}
    (hcardP : Nat.card P = 27) (hexp : Monoid.exponent ↥P = 3)
    (hZcard : Nat.card (Subgroup.center ↥P) = 3) (hQ : Nat.card Q = 9) :
    ∃ Q' : Subgroup X, Q' ≤ P ∧ Nat.card Q' = 9 ∧ Q' ≠ Q := by
  classical
  set Z : Subgroup X := (Subgroup.center ↥P).map P.subtype with hZdef
  have hZc : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective P.subtype_injective]
    exact hZcard
  have hZP : Z ≤ P := fun z hz => by
    obtain ⟨y, -, rfl⟩ := hz
    exact y.2
  have hZcomm : ∀ z ∈ Z, ∀ g ∈ P, g * z = z * g := by
    rintro _ ⟨y, hy, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)
  have hx : ∃ x ∈ P, x ∉ Q ∧ x ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hsub : (P : Set X) ⊆ (Q : Set X) ∪ (Z : Set X) := fun x hx => by
      by_cases hxQ : x ∈ Q
      · exact Or.inl hxQ
      · exact Or.inr (hcon x hx hxQ)
    have h1 : Nat.card P ≤ Nat.card Q + Nat.card Z := by
      calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
        _ ≤ ((Q : Set X) ∪ (Z : Set X)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (Q : Set X).ncard + (Z : Set X).ncard := Set.ncard_union_le _ _
        _ = Nat.card Q + Nat.card Z := by
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
          rfl
    omega
  obtain ⟨x, hxP, hxQ, hxZ⟩ := hx
  have hx3 : x ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨x, hxP⟩ : ↥P)
    rw [hexp] at h
    exact congrArg Subtype.val h
  have hdisj := k335hj_disjoint_zpowers hx3 hxZ
  have hx1 : x ≠ 1 := fun h => hxQ (h ▸ Q.one_mem)
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro z
    have key : ∀ w ∈ Z, x * w * x⁻¹ = w := fun w hw => by
      rw [hZcomm w hw x hxP]
      group
    constructor
    · intro hz
      rw [key z hz]
      exact hz
    · intro hz
      have h2 : x⁻¹ * (x * z * x⁻¹) * x = x * z * x⁻¹ := by
        rw [hZcomm _ hz x⁻¹ (P.inv_mem hxP)]
        group
      have h3 : x⁻¹ * (x * z * x⁻¹) * x = z := by group
      rw [← h3, h2]
      exact hz
  have hcard' : Nat.card (Z ⊔ Subgroup.zpowers x : Subgroup X) = 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z _ hnorm hdisj, hZc,
      hxcard]
  refine ⟨Z ⊔ Subgroup.zpowers x, sup_le hZP (Subgroup.zpowers_le.mpr hxP), hcard', ?_⟩
  intro h
  exact hxQ (h ▸ (le_sup_right : Subgroup.zpowers x ≤ Z ⊔ Subgroup.zpowers x)
    (Subgroup.mem_zpowers x))

theorem k335SporNormAt_J2 :
    K335SporNormAt .J2 := by
  intro X _ _ hX S Q hS hQS hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hpg, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [Subgroup.relIndex_top_right] at hdvd
  let P : Sylow 3 X := hpg.toSylow hdvd
  have hPS : (P : Subgroup X) = S := rfl
  obtain ⟨⟨⟨⟨-, -, -, hZcard⟩, hcardP, hexp⟩, -⟩, hTrans, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨Q', hQ'S, hQ'card, hne⟩ := k335hj_exists_second (P := S) (Q := Q) hcardP hexp hZcard hQ
  obtain ⟨x, hx, hxQ⟩ := hTrans Q ⟨hQS, hQ⟩ Q' ⟨hQ'S, hQ'card⟩
  refine ⟨x, hx, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : CFSG.conjugate Q x ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hcon y hy
  have heq : CFSG.conjugate Q x = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective])
  exact hne (hxQ.trans heq)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
