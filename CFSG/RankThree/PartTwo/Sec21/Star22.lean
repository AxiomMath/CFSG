module

public import CFSG.RankThree.PartTwo.Sec21.Item229URoots

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly (IsElemAbelian)
open URoots (V3 centerVec movedVec)
open Matrix

abbrev IsBodyDiag (v : V3) : Prop := ∀ i : Fin 3, v i ≠ 0

@[expose] def swapReflList : List (GL (Fin 3) (ZMod 3)) := [p01, m01, p12, m12, p02, m02]

theorem mem_swapReflList_of_mem_swapRefl {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl) :
    x ∈ swapReflList := by
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [swapReflList]

theorem isBodyDiag_of_fixed_swapRefl : ∀ M ∈ swapReflList, ∀ N ∈ swapReflList, M * N ≠ N * M →
    ∀ v : V3, v ≠ 0 → (M : Mat3) *ᵥ v = v → (N : Mat3) *ᵥ v = v → IsBodyDiag v := by
  decide +kernel

@[expose] def crossVec (u w : V3) : V3 :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

@[expose] def fixVec (M N : Mat3) : V3 := crossVec (centerVec M) (centerVec N)

abbrev CommPairFacts (M N : Mat3) : Prop :=
  M *ᵥ fixVec M N = fixVec M N ∧ N *ᵥ fixVec M N = fixVec M N ∧
    centerVec M + centerVec N ≠ 0 ∧
    (∀ v : V3, ∃ k a b : ZMod 3, v = k • fixVec M N + a • centerVec M + b • centerVec N) ∧
    (∀ c k : ZMod 3, ¬ IsBodyDiag (c • (centerVec M + centerVec N) + k • fixVec M N))

theorem commPairFacts_of_mem_swapRefl : ∀ M ∈ swapReflList, ∀ N ∈ swapReflList, M ≠ N →
    M * N = N * M → CommPairFacts (M : Mat3) (N : Mat3) := by
  decide +kernel

variable {G : Type} [Group G]

theorem le_normalizer_of_forall_mul_mem {X S : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ S, x * y * x⁻¹ ∈ S) : X ≤ Subgroup.normalizer (S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h x hx y, fun hy => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this

theorem le_normalizer_kOf [Finite G] {A : Subgroup G} (hAc : IsMulCommutative A)
    (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    A ≤ Subgroup.normalizer (kOf A φ : Set G) := by
  refine le_normalizer_of_forall_mul_mem fun a ha x hx => ?_
  have hw : wConj A ⟨a, Subgroup.le_normalizer ha⟩ = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [wConj_apply, MulAut.one_apply]
    have hab : a * (b : G) = b * a := congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ b)
    change a * (b : G) * a⁻¹ = b
    rw [hab, mul_inv_cancel_right]
  exact conj_mem_kOf hK ⟨a, Subgroup.le_normalizer ha⟩ hφ (by rw [hw, one_mul, mul_one]) hx

theorem apply_eq_of_mem_starOf_of_le_centralizer {A X : Subgroup G} {φ : MulAut A}
    (hφ : φ ∈ starOf A X) {a : A} (ha : X ≤ Subgroup.centralizer ({(a : G)} : Set G)) :
    φ a = a := by
  obtain ⟨w, hw, rfl⟩ := hφ
  have hwX : (w : G) ∈ X := Subgroup.mem_subgroupOf.mp hw
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (ha hwX)
  apply Subtype.ext
  change (w : G) * a * (w : G)⁻¹ = a
  rw [hc, mul_inv_cancel_right]

theorem isBodyDiag_of_pair [Finite G] (h222 : Item222) {A : Subgroup G} (hA : Sec21Std G A)
    (hA27 : Nat.card A = 3 ^ 3) (f : Multiplicative V3 ≃* A)
    (hD : coordGL f '' dStar A = swapRefl) {E' V L' : Subgroup G} {c' : G}
    (hE' : E' ∈ collectionIn (partTwoE G) A) (hV : V ∈ fourGroups E')
    (hcL : (c', L') ∈ lThreeStarPairs A E' V) (hc'A : c' ∈ A) :
    IsBodyDiag (Multiplicative.toAdd (f.symm ⟨c', hc'A⟩)) := by
  have hpair' : Sec21Pair G A E' V c' L' := ⟨hA, hE', hV, hcL⟩
  obtain ⟨hgen, ⟨φ0, hφ0L, hφ0D⟩, hcase⟩ := h222 G A E' V c' L' hpair'
  have hS3 : Nonempty (starOf A L' ≃* Equiv.Perm (Fin 3)) := by
    rcases hcase φ0 hφ0L hφ0D with ⟨-, n, -, -, -, -, he⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
        ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
    · exact he
    · exact (not_dihedral_of_image_eq_swapRefl f hD hgen e).elim
    · exact (not_dihedral_of_image_eq_swapRefl f hD hgen e).elim
    · exact (not_dihedral_of_image_eq_swapRefl f hD hgen e).elim
    · rw [hA27] at h81
      norm_num at h81
  obtain ⟨e⟩ := hS3
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ (starOf A L' : Set (MulAut A)) ∩ dStar A,
      ∃ y ∈ (starOf A L' : Set (MulAut A)) ∩ dStar A, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hcomm : ((starOf A L' : Set (MulAut A)) ∩ dStar A).Pairwise Commute :=
      fun x hx y hy _ => hcon x hx y hy
    have hab := Subgroup.isMulCommutative_closure hcomm
    rw [← hgen] at hab
    exact not_isMulCommutative_perm_three (isMulCommutative_of_mulEquiv e hab)
  have hLc : L' ≤ Subgroup.centralizer ({c'} : Set G) := by
    obtain ⟨L₀, -, hL₀⟩ := (lZeroStarAt_subset A c') hcL.2.2.1
    change L₀.map (Subgroup.centralizer ({c'} : Set G)).subtype = L' at hL₀
    rw [← hL₀]
    exact Subgroup.map_subtype_le _
  set v : V3 := Multiplicative.toAdd (f.symm ⟨c', hc'A⟩) with hvdef
  have hv : ∀ φ ∈ starOf A L', ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ v = v := by
    intro φ hφ
    rw [coordGL_mulVec, coordLin3_apply, hvdef, ofAdd_toAdd, MulEquiv.apply_symm_apply,
      apply_eq_of_mem_starOf_of_le_centralizer hφ hLc]
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : f.symm ⟨c', hc'A⟩ = 1 := by
      rw [← ofAdd_toAdd (f.symm _), ← hvdef, h0, ofAdd_zero]
    have h2 : (⟨c', hc'A⟩ : A) = 1 := by
      rw [← f.apply_symm_apply ⟨c', hc'A⟩, h1, map_one]
    exact hcL.2.1 (congrArg Subtype.val h2)
  have hsw : ∀ d ∈ dStar A, coordGL f d ∈ swapReflList := fun d hd =>
    mem_swapReflList_of_mem_swapRefl (hD ▸ ⟨d, hd, rfl⟩)
  exact isBodyDiag_of_fixed_swapRefl _ (hsw x hx.2) _ (hsw y hy.2)
    (fun h => hxy (coordGL_injective f (by rw [map_mul, map_mul]; exact h))) v hv0
    (hv x hx.1) (hv y hy.1)

theorem mem_collectionIn_self [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) :
    A ∈ collectionIn (partTwoE G) A := by
  obtain ⟨hE, hEA⟩ := hpair.mem_E
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hE.2.1]; norm_num)
  exact ⟨hEeq ▸ hE, le_rfl⟩

theorem exists_bodyDiag_of_fourGroup [Finite G] (h612 : Item612Sec21) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (f : Multiplicative V3 ≃* A) (hD : coordGL f '' dStar A = swapRefl) {V : Subgroup G}
    (hV : V ∈ fourGroups A) :
    ∃ a : A, (a : G) ∈ Subgroup.centralizer (V : Set G) ∧
      IsBodyDiag (Multiplicative.toAdd (f.symm a)) := by
  have hAE := mem_collectionIn_self hpair hA27
  obtain ⟨⟨c', L'⟩, hcL⟩ := h612 G A hpair.toSec21Std A hAE V hV
  have hc'A : c' ∈ A := hcL.1.1
  exact ⟨⟨c', hc'A⟩, hcL.1.2,
    isBodyDiag_of_pair h222 hpair.toSec21Std hA27 f hD hAE hV hcL hc'A⟩

end CFSG.RankThree.PartTwo.Sec21
