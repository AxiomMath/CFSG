module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iQuasi
public import CFSG.RankThree.PartTwo.Sec21.Hering233iExcAbs
public import CFSG.RankThree.PartTwo.Sec21.Hering233iTwoInv
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G]

open Item21EarlyProof Item21Early2Proof in
theorem isQuasisimple_of_exception [Finite G] (h44 : Sec4.Item4_4)
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAS : A ∈ partTwoS G) {B : Subgroup G}
    (hBA : B ≤ A) (hB3 : Nat.card B = 3) {b : G} (hBb : B = Subgroup.zpowers b) (hbA : b ∈ A)
    (hb1 : b ≠ 1) {X₀ : Subgroup G} (hX₀ : X₀ ∈ thetaComponentsAt 3 b)
    (hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G)) (hA27 : Nat.card A = 27)
    {X : Subgroup G} (hXX₀ : X ≤ X₀)
    (eX : Nonempty (X ≃* projSL 2 (GaloisField 2 2)))
    {w : G} (hXw : ∀ x ∈ X, x * w = w * x) (hw2 : orderOf w = 2) {a r₁ r₂ r₃ : G} (haA : a ∈ A)
    (haX : a ∈ X)
    (ha1 : a ≠ 1)
    (hcover : ∀ h ∈ A, h ∉ B → ∃ i : Fin 4, ![a, r₁, r₂, r₃] i ∈ B ⊔ Subgroup.zpowers h)
    (h₁ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ X₀, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₁ = r₁ * d →
      d * w = w * d)
    (h₂ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ X₀, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₂ = r₂ * d →
      d * w = w * d)
    (h₃ : ∀ q : ℕ, q.Prime → 3 < q → ∀ d ∈ X₀, (∃ k : ℕ, d ^ q ^ k = 1) → d * r₃ = r₃ * d →
      d * w = w * d) : IsQuasisimple X₀ := by
  have hLp : Group.IsPerfect X₀ := Sec6.isPerfect_of_mem_thetaComponentsAt hX₀
  have hLq : IsQuasisimple (X₀ ⧸ aschbacherSolvableCore 3 X₀) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hX₀
  have hX₀C : X₀ ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hX₀
  have hL4 : SectionFourHyp X₀ := by
    have hne : X₀ ≠ ⊤ := fun h =>
      Sec6.centralizer_ne_top_of_ne_one hG hb1 (top_le_iff.mp (h ▸ hX₀C))
    exact hG.sectionFourHyp hne
  have hAe : IsElemAbelian 3 A := hAS.1.1
  obtain ⟨eX⟩ := eX
  haveI : IsSimpleGroup X := by
    haveI := isSimpleGroup_projSL_two (m := 2) le_rfl
    exact eX.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eX
  have hXnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x :=
    ⟨x, x.2, y, y.2, fun h => hxy (Subtype.ext h)⟩
  obtain ⟨u, v, hu1, hv1, huv, hu2, hv2⟩ := exists_two_involutions_projSL 2 (by norm_num)
  have hact := exists_act_of_simple hAX₀ hXX₀ hXnc haA haX ha1
  have hO2 := pCore_two_le_center_of_act hAS hbA hb1 hX₀ hAX₀ hact
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := X₀)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 X₀ with hT
  haveI : IsSimpleGroup ((X₀ ⧸ T) ⧸ Subgroup.center (X₀ ⧸ T)) := hLq.2.1
  haveI : IsSimpleGroup (X₀ ⧸ centerPre T) := (centerPreEquiv T).isSimpleGroup
  have hO3 : CFSG.pCore 3 X₀ ≤ Subgroup.center X₀ := pCore_three_le_center T hT3
  let eK : X.subgroupOf X₀ ≃* X := Subgroup.subgroupOfEquivOfLe hXX₀
  haveI : IsSimpleGroup (X.subgroupOf X₀) := eK.isSimpleGroup
  let lift : ∀ {x : G}, x ∈ X → X₀ := fun {x} hx => ⟨x, hXX₀ hx⟩
  have hlift : ∀ {x : G} (hx : x ∈ X), lift hx ∈ X.subgroupOf X₀ := fun hx =>
    Subgroup.mem_subgroupOf.mpr hx
  have hne1 : ∀ {x : G} (hx : x ∈ X), x ≠ 1 → lift hx ≠ 1 := fun hx hx1 h =>
    hx1 (congrArg Subtype.val h)
  have hu1' : ((eX.symm u : X) : G) ≠ 1 := fun h => hu1 (by
    simpa using congrArg eX (Subtype.ext h : eX.symm u = 1))
  have hv1' : ((eX.symm v : X) : G) ≠ 1 := fun h => hv1 (by
    simpa using congrArg eX (Subtype.ext h : eX.symm v = 1))
  refine isQuasisimple_of_item44 h44 hL4 hLq hO2 (S := X.subgroupOf X₀)
    ⟨lift x.2, hlift x.2, lift y.2, hlift y.2,
      fun h => hxy (Subtype.ext (congrArg (fun z : X₀ => (z : G)) h))⟩
    (u := lift (eX.symm u).2) (v := lift (eX.symm v).2) (hlift (eX.symm u).2)
    (hlift (eX.symm v).2) (hne1 (eX.symm u).2 hu1') (hne1 (eX.symm v).2 hv1')
    (fun h => huv (eX.symm.injective (Subtype.ext (congrArg (fun z : X₀ => (z : G)) h))))
    (Subtype.ext (by
      have := congrArg (fun z : X => (z : G)) (show eX.symm u * eX.symm u = 1 by
        rw [← map_mul, hu2, map_one])
      simpa using this))
    (Subtype.ext (by
      have := congrArg (fun z : X => (z : G)) (show eX.symm v * eX.symm v = 1 by
        rw [← map_mul, hv2, map_one])
      simpa using this)) ?_
  intro hO2' hQ p hp hpS
  exfalso
  have hBL : ∀ b' ∈ B, ∀ x ∈ X₀, b' * x = x * b' := by
    intro b' hb' x hx
    rw [hBb] at hb'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hc : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp (hX₀C hx)).symm
    exact (hc.zpow_left n).eq
  exact false_of_exceptional_q hG.localRank_lt (isSolvable_centerPre T hTs) hO2' hO3 hAX₀ hAe
    hA27 hBA hB3 hBL hXX₀ hXnc hXw hw2 haX ha1 hcover h₁ h₂ h₃ p hp hpS

end CFSG.RankThree.PartTwo.Sec21.Hering233i
