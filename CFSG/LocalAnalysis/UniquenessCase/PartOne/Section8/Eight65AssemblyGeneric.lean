module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65WeakClosureGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65K332Inversion
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65CyclicSylowThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65K332Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65K332CaseOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

private theorem exists_isSylowOf_ge_chain {Γ : Type} [Group Γ] [Finite Γ]
    {p : ℕ} [Fact p.Prime] {K E : Subgroup Γ} (hEK : E ≤ K) (hE : IsPGroup p ↥E) :
    ∃ P : Subgroup Γ, CFSG.ABGLocalTools.IsSylowOf p P K ∧ E ≤ P := by
  obtain ⟨T, hT⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hEK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem exists_t_of_inverts_subgroupOf {G : Type} [Group G] {X Z C : Subgroup G}
    (hZC : Z ≤ C) (hC : C ≤ Subgroup.centralizer (X : Set G)) (n : ↥C)
    (hn : ∀ z ∈ Z.subgroupOf C, n * z * n⁻¹ = z⁻¹) :
    ∃ t : G, (∀ x ∈ X, t * x * t⁻¹ = x) ∧ ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
  refine ⟨(n : G), ?_, ?_⟩
  · intro x hx
    have hcomm : (n : G) * x = x * (n : G) :=
      ((Subgroup.mem_centralizer_iff.mp (hC n.2)) x hx).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · intro z hz
    have hz' : (⟨z, hZC hz⟩ : ↥C) ∈ Z.subgroupOf C := Subgroup.mem_subgroupOf.mpr hz
    have h := congrArg (fun w : ↥C => (w : G)) (hn ⟨z, hZC hz⟩ hz')
    simpa using h

theorem exists_inverting_of_K332
    (hK : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hJ2 : ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .J2 → SylowCenterInverted Y)
    (hU33 : ∀ (Y : Type) [Group Y] [Finite Y],
      CFSG.Blueprint.LieModel Y .PSU 3 3 1 → SylowCenterInverted Y)
    (hG2 : ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime →
      CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterInverted Y)
    {G : Type} [Group G] [Finite G] {D : Data G} {X Q Z : Subgroup G}
    (hrk : CFSG.Open.pRank 3 D.M ≤ 3) (hZU : Z ∈ uniqueSet D.M)
    (hXcard : Nat.card X = 3) (hQX : Q ≤ Subgroup.centralizer (X : Set G))
    (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3)
    (hW : ∀ m ∈ D.M, CFSG.conjugate Z m ≤ Subgroup.normalizer (Z : Set G) →
      CFSG.conjugate Z m = Z)
    (hO3 : ∀ O : Subgroup G, Q ≤ Subgroup.normalizer (O : Set G) →
      Nat.Coprime 3 (Nat.card O) → O ≤ D.M)
    (hXnotM : ¬ Subgroup.normalizer (X : Set G) ≤ D.M) :
    ∃ t : G, (∀ x ∈ X, t * x * t⁻¹ = x) ∧ ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hZC : Z ≤ C := hZQ.trans hQX
  have hX0 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set G)) :=
    isWeaklyClosedIn_normalizer_of_uniqueSet hZU hW
  have hKC : CFSG.Open.IsKGroup ↥C := isKGroup_centralizer_of_ne_bot D.standing hX0
  have hwcC : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (Z.subgroupOf C)
      (Subgroup.normalizer ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C)) :=
    isWeaklyClosedIn_subgroupOf_normalizer hZC hwc
  have hrkC : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 3 :=
    pRank_top_le_three_of_mem_uniqueSet hZU hZC hZcard hrk
  have hZ'card : Nat.card (Z.subgroupOf C) = 3 := by
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  rcases exists_inverts_or_pRank_one_of_K332 hK hJ2 hU33 hG2 hKC hZ'card hwcC hrkC with
    ⟨n, -, hn⟩ | hrank1
  · exact exists_t_of_inverts_subgroupOf hZC (le_refl C) n hn
  · set K' : Subgroup ↥C :=
      Subgroup.normalClosure ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C) with hK'def
    have hKn : K'.Normal := Subgroup.normalClosure_normal
    have hZK : Z.subgroupOf C ≤ K' := Subgroup.subset_normalClosure
    have hZ'p : IsPGroup 3 ↥(Z.subgroupOf C) :=
      IsPGroup.of_card (n := 1) (by rw [hZ'card]; norm_num)
    obtain ⟨S, hS, hZS⟩ := exists_isSylowOf_ge_chain hZK hZ'p
    rcases exists_inverts_or_le_pPrimeCore_sup hKn hZK hZ'card hS hZS hrank1 with
      ⟨n, -, hn⟩ | hKS
    · exact exists_t_of_inverts_subgroupOf hZC (le_refl C) n hn
    · have hCM : C ≤ D.M :=
        centralizer_le_of_normalClosure_le_pPrimeCore_sup (C := C) (S := S) hZU hO3 hQX hZQ
          hZcard hwc hS.isPGroup hZS hKS
      exact absurd (normalizer_le_of_centralizer_le_of_mem_uniqueSet_of_le hZU hZC hCM) hXnotM

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
