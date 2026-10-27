module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Congruence
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: class-function helpers

The Brauer--Suzuki machinery for Lemma 1.3 (Gorenstein 4.4.6) and the
index-two class-function identities used by Sections 1--2.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

/-! ## Brauer--Suzuki machinery for Lemma 1.3 (Gorenstein 4.4.6) -/

/-- The summand of an induced class function: `δ(x⁻¹·g·x)` when `x⁻¹·g·x ∈ H`,
else `0`. -/
@[expose] public noncomputable def inducedSummand {G : Type u} [Group G] {H : Subgroup G}
    (δ : ClassFunction (↥H)) (g x : G) : ℂ := by
  classical
  exact if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0

/-- If `g ∈ T` (a TI-set with normalizer `H`) and `x ∉ H`, then `x⁻¹·g·x ∉ T`. -/
public lemma not_mem_conj_of_TI {G : Type u} [Group G] {H : Subgroup G} {T : Set G}
    (hTI : IsTISet T) (hnorm : Subgroup.normalizer T = H) {g x : G} (hgT : g ∈ T) (hx : x ∉ H) :
    x⁻¹ * g * x ∉ T := by
  intro hxT
  have hgxT : g ∈ (fun t : G => x * t * x⁻¹) '' T := ⟨x⁻¹ * g * x, hxT, by group⟩
  have hne : T ∩ (fun t : G => x * t * x⁻¹) '' T ≠ ∅ := by
    intro hEq
    have hg : g ∈ T ∩ (fun t : G => x * t * x⁻¹) '' T := ⟨hgT, hgxT⟩
    rw [hEq] at hg
    simp at hg
  have hxnotnorm : x ∉ Subgroup.normalizer T := by
    intro hxn
    exact hx (by rw [← hnorm]; exact hxn)
  have hxneq : (fun t : G => x * t * x⁻¹) '' T ≠ T := by
    intro hEq
    exact hxnotnorm (by
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      exact hEq)
  rcases hTI x with hEq | hDisj
  · exact hxneq hEq
  · exact hne hDisj

/-- An induced-class-function summand vanishes at points outside the normalizer
of the TI-set `T` on which `δ` is supported. -/
public lemma inducedSummand_zero_of_not_normalizer {G : Type u} [Group G]
    {H0 H : Subgroup G} {T : Set G} (hTI : IsTISet T) (hnorm : Subgroup.normalizer T = H)
    (δ : ClassFunction (↥H0)) (hδT : supportedOn δ {x : ↥H0 | (x : G) ∈ T})
    {g x : G} (hgT : g ∈ T) (hx : x ∉ H) :
    inducedSummand δ g x = 0 := by
  by_cases hx0 : x⁻¹ * g * x ∈ H0
  · have hnotT : x⁻¹ * g * x ∉ T := not_mem_conj_of_TI hTI hnorm hgT hx
    have hδ0 : δ ⟨x⁻¹ * g * x, hx0⟩ = 0 := hδT ⟨x⁻¹ * g * x, hx0⟩ (fun hT => hnotT hT)
    rw [inducedSummand]
    simp [hx0, hδ0]
  · rw [inducedSummand]
    simp [hx0]

/-- For `g ∈ T`, the induced-function sum over `G` restricts to the sum over `H`. -/
public lemma induced_sum_eq_sum_subgroup {G : Type u} [Group G] [Fintype G]
    {H0 H : Subgroup G} {T : Set G} (hTI : IsTISet T) (hnorm : Subgroup.normalizer T = H)
    (δ : ClassFunction (↥H0)) (hδT : supportedOn δ {x : ↥H0 | (x : G) ∈ T})
    {g : G} (hgT : g ∈ T) :
    (∑ x : G, inducedSummand δ g x) = ∑ x : ↥H, inducedSummand δ g (x : G) := by
  classical
  exact sum_eq_sum_subgroup_of_vanishes H (fun x => inducedSummand δ g x)
    (fun x hx => inducedSummand_zero_of_not_normalizer hTI hnorm δ hδT hgT hx)

/-- A pairing summand vanishes for `z` outside the normalizer of the TI-set. -/
public lemma pairingSummand_zero_of_not_normalizer {G : Type u} [Group G]
    {H0 H : Subgroup G} {T : Set G} (hTI : IsTISet T) (hnorm : Subgroup.normalizer T = H)
    (δ1 δ2 : ClassFunction (↥H0))
    (hδ1T : supportedOn δ1 {x : ↥H0 | (x : G) ∈ T})
    (hδ2T : supportedOn δ2 {x : ↥H0 | (x : G) ∈ T})
    {z : G} (hz : z ∉ H) (h : ↥H0) :
    pairingSummand H0 δ1 δ2 z h = 0 := by
  by_cases hz0 : z⁻¹ * (h : G) * z ∈ H0
  · by_contra hne
    have hδ1nz : δ1 h ≠ 0 := by
      intro h1
      apply hne
      rw [pairingSummand]
      simp [hz0, h1]
    have h1T : (h : G) ∈ T := by
      by_contra hnotT
      exact hδ1nz (hδ1T h hnotT)
    have hδ2nz : δ2 ⟨z⁻¹ * (h : G) * z, hz0⟩ ≠ 0 := by
      intro h2
      apply hne
      rw [pairingSummand]
      simp [hz0, h2]
    have h2T : z⁻¹ * (h : G) * z ∈ T := by
      by_contra hnotT
      exact hδ2nz (hδ2T ⟨z⁻¹ * (h : G) * z, hz0⟩ hnotT)
    have hzT : (h : G) ∈ (fun t : G => z * t * z⁻¹) '' T :=
      ⟨z⁻¹ * (h : G) * z, h2T, by group⟩
    have hneT : T ∩ (fun t : G => z * t * z⁻¹) '' T ≠ ∅ := by
      intro hEq
      have hg : (h : G) ∈ T ∩ (fun t : G => z * t * z⁻¹) '' T := ⟨h1T, hzT⟩
      rw [hEq] at hg
      simp at hg
    have hznotnorm : z ∉ Subgroup.normalizer T := by
      intro hzn
      exact hz (by rw [← hnorm]; exact hzn)
    have hzneq : (fun t : G => z * t * z⁻¹) '' T ≠ T := by
      intro hEq
      exact hznotnorm (by
        rw [Subgroup.mem_normalizer_iff_conj_image_eq]
        exact hEq)
    rcases hTI z with hEq | hDisj
    · exact hzneq hEq
    · exact hneT hDisj
  · rw [pairingSummand]
    simp [hz0]

/-- The pairing sum over `G` restricts to the sum over `H` (TI-set argument). -/
public lemma pairing_sum_eq_sum_subgroup {G : Type u} [Group G] [Fintype G]
    {H0 H : Subgroup G} {T : Set G} (hTI : IsTISet T) (hnorm : Subgroup.normalizer T = H)
    (δ1 δ2 : ClassFunction (↥H0))
    (hδ1T : supportedOn δ1 {x : ↥H0 | (x : G) ∈ T})
    (hδ2T : supportedOn δ2 {x : ↥H0 | (x : G) ∈ T}) :
    (∑ z : G, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 z h) =
      ∑ z : ↥H, ∑ h : ↥H0, pairingSummand H0 δ1 δ2 (z : G) h := by
  classical
  exact sum_eq_sum_subgroup_of_vanishes H
    (fun z : G => ∑ h : ↥H0, pairingSummand H0 δ1 δ2 z h) (fun z hz => by
      apply Finset.sum_eq_zero
      intro h hh
      exact pairingSummand_zero_of_not_normalizer hTI hnorm δ1 δ2 hδ1T hδ2T hz h)

/-- A class function on a subgroup is conjugation-invariant under subgroup elements
(flat form). -/
public theorem classFunction_conj_subtype {G : Type u} [Group G] (H0 : Subgroup G)
    (ν : ClassFunction (↥H0)) (hνc : IsClassFunction ν) (a b : G)
    (ha : a ∈ H0) (hb : b ∈ H0) :
    ν ⟨a⁻¹ * b * a, H0.mul_mem (H0.mul_mem (H0.inv_mem ha) hb) ha⟩ = ν ⟨b, hb⟩ := by
  have hc := hνc ⟨b, hb⟩ ⟨a⁻¹, H0.inv_mem ha⟩
  have hval : (⟨a⁻¹, H0.inv_mem ha⟩ * ⟨b, hb⟩ * ⟨a⁻¹, H0.inv_mem ha⟩⁻¹ : ↥H0) =
      ⟨a⁻¹ * b * a, H0.mul_mem (H0.mul_mem (H0.inv_mem ha) hb) ha⟩ := by
    ext
    change (a⁻¹ * b * (a⁻¹)⁻¹) = a⁻¹ * b * a
    group
  rw [hval] at hc
  exact hc

/-- A finite group with a subgroup of index two splits into the subgroup and its
left translate `s⁻¹·K`: `∑ f = ∑_{k∈K} f k + ∑_{k∈K} f (s⁻¹·k)`. -/
public theorem sum_split_index_two {H : Type u} [Group H] [Fintype H] (K : Subgroup H)
    (hindex : K.index = 2) {s : H} (hs : s ∉ K) (f : H → ℂ) :
    (∑ x : H, f x) = (∑ k : ↥K, f (k : H)) + ∑ k : ↥K, f (s⁻¹ * (k : H)) := by
  classical
  have hiff : ∀ x : H, s * x ∈ K ↔ x ∉ K := by
    intro x
    rw [Subgroup.mul_mem_iff_of_index_two hindex]
    simp [hs]
  have hcover : ∀ x : H, (s * x ∈ K) ∨ (x ∈ K) := by
    intro x
    by_cases hx : x ∈ K
    · right; exact hx
    · left; exact (hiff x).mpr hx
  let S1 : Finset H := Finset.univ.filter (fun x : H => x ∈ K)
  let S2 : Finset H := Finset.univ.filter (fun x : H => s * x ∈ K)
  have hdisj : _root_.Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (hiff x).mp (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
  have hunion : S1 ∪ S2 = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    rcases hcover x with hx | hx
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩))
  calc
    (∑ x : H, f x) = ∑ x ∈ S1 ∪ S2, f x := by
      rw [hunion]
    _ = (∑ x ∈ S1, f x) + ∑ x ∈ S2, f x := Finset.sum_union hdisj
    _ = (∑ k : ↥K, f (k : H)) + ∑ k : ↥K, f (s⁻¹ * (k : H)) := by
      congr 1
      · refine Finset.sum_bij
          (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : ↥K)) ?_ ?_ ?_ ?_
        · intro x hx
          simp
        · intro a₁ ha₁ a₂ ha₂ hEq
          exact congrArg Subtype.val hEq
        · intro k hk
          refine ⟨(k : H), Finset.mem_filter.mpr ⟨Finset.mem_univ (k : H), k.2⟩, ?_⟩
          exact Subtype.ext rfl
        · intro x hx
          simp
      · refine Finset.sum_bij
          (fun x hx => (⟨s * x, (Finset.mem_filter.mp hx).2⟩ : ↥K)) ?_ ?_ ?_ ?_
        · intro x hx
          simp
        · intro a₁ ha₁ a₂ ha₂ hEq
          exact mul_left_cancel (congrArg Subtype.val hEq)
        · intro k hk
          refine ⟨s⁻¹ * (k : H), Finset.mem_filter.mpr ⟨Finset.mem_univ (s⁻¹ * (k : H)), ?_⟩, ?_⟩
          · have hk'' : s * (s⁻¹ * (k : H)) = k := by group
            simp [hk'']
          · ext
            group
        · intro x hx
          simp

/-- Remark 1.4, first assertion: for `|H : H0| = 2` and `s ∉ H0`,
`ν^H = ν + ν^s` on `H0` (where `ν^s(h) = ν(s·h·s⁻¹)`). -/
public theorem inducedFromSub_eq_add_conj_index_two {G : Type u} [Group G] [Fintype G]
    (H0 H : Subgroup G) (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    {s : G} (hs : s ∈ H) (hs_not : s ∉ H0) (ν : ClassFunction (↥H0))
    (hνc : IsClassFunction ν) {h : G} (hh : h ∈ H0) (hsh : s * h * s⁻¹ ∈ H0) :
    (inducedFromSub hH0 ν) ⟨h, hH0 hh⟩ = ν ⟨h, hh⟩ + ν ⟨s * h * s⁻¹, hsh⟩ := by
  classical
  let K : Subgroup (↥H) := H0.subgroupOf H
  let ν' : ClassFunction (↥K) := fun x => ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  let s' : ↥H := ⟨s, hs⟩
  have hsK : s' ∉ K := by
    intro hK
    exact hs_not (Subgroup.mem_subgroupOf.mp hK)
  have hcard : (Nat.card (↥K) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.card_pos (α := ↥K)))
  have hxK : ∀ x : ↥H, x⁻¹ * ⟨h, hH0 hh⟩ * x ∈ K := by
    intro x
    have hiff1 : x⁻¹ * (⟨h, hH0 hh⟩ * x) ∈ K ↔ (x⁻¹ ∈ K ↔ ⟨h, hH0 hh⟩ * x ∈ K) :=
      Subgroup.mul_mem_iff_of_index_two hindex (a := x⁻¹) (b := ⟨h, hH0 hh⟩ * x)
    have hiff2 : ⟨h, hH0 hh⟩ * x ∈ K ↔ (⟨h, hH0 hh⟩ ∈ K ↔ x ∈ K) :=
      Subgroup.mul_mem_iff_of_index_two hindex (a := ⟨h, hH0 hh⟩) (b := x)
    have hhK : ⟨h, hH0 hh⟩ ∈ K := Subgroup.mem_subgroupOf.mpr hh
    have hxinv : x⁻¹ ∈ K ↔ x ∈ K := Subgroup.inv_mem_iff K
    rw [mul_assoc, hiff1, hiff2, hxinv]
    simp [hhK]
  have hsplit :
      (∑ x : ↥H, ν' ⟨x⁻¹ * ⟨h, hH0 hh⟩ * x, hxK x⟩) =
        (∑ k : ↥K, ν' ⟨(k : ↥H)⁻¹ * ⟨h, hH0 hh⟩ * (k : ↥H), hxK (k : ↥H)⟩) +
          ∑ k : ↥K, ν' ⟨(s'⁻¹ * (k : ↥H))⁻¹ * ⟨h, hH0 hh⟩ * (s'⁻¹ * (k : ↥H)),
            hxK (s'⁻¹ * (k : ↥H))⟩ := by
    exact sum_split_index_two (H := ↥H) (K := K) hindex (s := s') hsK
      (fun x : ↥H => ν' ⟨x⁻¹ * ⟨h, hH0 hh⟩ * x, hxK x⟩)
  have hsum1 :
      (∑ k : ↥K, ν' ⟨(k : ↥H)⁻¹ * ⟨h, hH0 hh⟩ * (k : ↥H), hxK (k : ↥H)⟩) =
        (Nat.card (↥K) : ℂ) * ν ⟨h, hh⟩ := by
    calc
      (∑ k : ↥K, ν' ⟨(k : ↥H)⁻¹ * ⟨h, hH0 hh⟩ * (k : ↥H), hxK (k : ↥H)⟩)
          = ∑ k : ↥K, ν ⟨h, hh⟩ := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hc := classFunction_conj_subtype H0 ν hνc (k : G) h
                (Subgroup.mem_subgroupOf.mp k.2) hh
              simpa [ν'] using hc
      _ = (Nat.card (↥K) : ℂ) * ν ⟨h, hh⟩ := by
              simp [Finset.sum_const, Nat.card_eq_fintype_card]
  have hsum2 :
      (∑ k : ↥K, ν' ⟨(s'⁻¹ * (k : ↥H))⁻¹ * ⟨h, hH0 hh⟩ * (s'⁻¹ * (k : ↥H)),
          hxK (s'⁻¹ * (k : ↥H))⟩) =
        (Nat.card (↥K) : ℂ) * ν ⟨s * h * s⁻¹, hsh⟩ := by
    calc
      (∑ k : ↥K, ν' ⟨(s'⁻¹ * (k : ↥H))⁻¹ * ⟨h, hH0 hh⟩ * (s'⁻¹ * (k : ↥H)),
          hxK (s'⁻¹ * (k : ↥H))⟩)
          = ∑ k : ↥K, ν ⟨s * h * s⁻¹, hsh⟩ := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hc := classFunction_conj_subtype H0 ν hνc (k : G) (s * h * s⁻¹)
                (Subgroup.mem_subgroupOf.mp k.2) hsh
              have hsub' : (⟨((⟨(s'⁻¹ * (k : ↥H))⁻¹ * ⟨h, hH0 hh⟩ * (s'⁻¹ * (k : ↥H)),
                    hxK (s'⁻¹ * (k : ↥H))⟩ : ↥K) : G),
                    Subgroup.mem_subgroupOf.mp (hxK (s'⁻¹ * (k : ↥H)))⟩ : ↥H0) =
                  ⟨(k : G)⁻¹ * (s * h * s⁻¹) * (k : G),
                    H0.mul_mem (H0.mul_mem (H0.inv_mem (Subgroup.mem_subgroupOf.mp k.2)) hsh)
                      (Subgroup.mem_subgroupOf.mp k.2)⟩ := by
                apply Subtype.ext
                simp [s']
                group
              simpa [ν'] using (congrArg ν hsub').trans hc
      _ = (Nat.card (↥K) : ℂ) * ν ⟨s * h * s⁻¹, hsh⟩ := by
              simp [Finset.sum_const, Nat.card_eq_fintype_card]
  calc
    (inducedFromSub hH0 ν) ⟨h, hH0 hh⟩
        = (Nat.card (↥K) : ℂ)⁻¹ * ∑ x : ↥H, ν' ⟨x⁻¹ * ⟨h, hH0 hh⟩ * x, hxK x⟩ := by
            unfold inducedFromSub inducedClassFunction
            simp [hxK, ν', K]
    _ = (Nat.card (↥K) : ℂ)⁻¹ *
          ((Nat.card (↥K) : ℂ) * ν ⟨h, hh⟩ +
            (Nat.card (↥K) : ℂ) * ν ⟨s * h * s⁻¹, hsh⟩) := by
            rw [hsplit, hsum1, hsum2]
    _ = ν ⟨h, hh⟩ + ν ⟨s * h * s⁻¹, hsh⟩ := by
            field_simp [hcard]


/-- Frobenius reciprocity for `inducedFromSub`: `(δ^{H}, χ)_H = (δ, χ|_H0)_H0`. -/
public theorem frobenius_reciprocity_inducedFromSub {G : Type u} [Group G] [Fintype G]
    {H0 H : Subgroup G} (hH0 : H0 ≤ H) (δ : ClassFunction (↥H0))
    {χ : ClassFunction (↥H)} (hχ : IsClassFunction χ) :
    scalarProduct (↥H) (inducedFromSub hH0 δ) χ =
      scalarProduct (↥H0) δ (fun x : ↥H0 => χ ⟨(x : G), hH0 x.2⟩) := by
  classical
  let K : Subgroup (↥H) := H0.subgroupOf H
  let eK : ↥K ≃ ↥H0 :=
    { toFun := fun k => ⟨(k : G), Subgroup.mem_subgroupOf.mp k.2⟩
      invFun := fun x => ⟨⟨(x : G), hH0 x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
      left_inv := by intro k; ext; rfl
      right_inv := by intro x; ext; rfl }
  let δ' : ClassFunction (↥K) := fun x => δ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  have hmain := frobenius_reciprocity (G := ↥H) (H := K) δ' hχ
  have hLHS : inducedClassFunction K δ' = inducedFromSub hH0 δ := by
    rfl
  have hRHS : scalarProduct (↥K) δ' (fun x : ↥K => χ (x : ↥H)) =
      scalarProduct (↥H0) δ (fun x : ↥H0 => χ ⟨(x : G), hH0 x.2⟩) := by
    unfold scalarProduct
    congr 1
    · have hc : (Nat.card (↥K) : ℂ) = (Nat.card (↥H0) : ℂ) := by
        exact_mod_cast (Nat.card_congr eK)
      rw [hc]
    · refine Fintype.sum_equiv eK
        (fun x : ↥K => δ' x * star (χ (x : ↥H)))
        (fun x : ↥H0 => δ x * star (χ ⟨(x : G), hH0 x.2⟩)) ?_
      intro k
      rfl
  rw [← hLHS, hmain, hRHS]


/-- Conjugation by `s` on `H0`, given `s·H0·s⁻¹ ≤ H0`. -/
@[expose] public def conjMonoidHom {G : Type u} [Group G] (H0 : Subgroup G) (s : G)
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) : ↥H0 →* ↥H0 where
  toFun x := ⟨s * (x : G) * s⁻¹, hsH0 x⟩
  map_one' := by
    ext
    change s * (1 : G) * s⁻¹ = 1
    group
  map_mul' x y := by
    ext
    change s * ((x : G) * (y : G)) * s⁻¹ = s * (x : G) * s⁻¹ * (s * (y : G) * s⁻¹)
    group

/-- The `s`-conjugate of a class function: `ν^s(h) = ν(s·h·s⁻¹)`. -/
@[expose] public def conjChar {G : Type u} [Group G] (H0 : Subgroup G) {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) (ν : ClassFunction (↥H0)) :
    ClassFunction (↥H0) :=
  fun x => ν (conjMonoidHom H0 s hsH0 x)

/-- For `|H : H0| = 2`, `H0` is closed under conjugation by elements of `H`. -/
public theorem conj_mem_of_index_two {G : Type u} [Group G] (H0 H : Subgroup G)
    (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    (a : ↥H) (x : ↥H0) : (a : G)⁻¹ * (x : G) * (a : G) ∈ H0 := by
  let K : Subgroup (↥H) := H0.subgroupOf H
  change (a : ↥H)⁻¹ * (⟨(x : G), hH0 x.2⟩ : ↥H) * (a : ↥H) ∈ K
  rw [mul_assoc]
  have hiff1 : (a : ↥H)⁻¹ * (⟨(x : G), hH0 x.2⟩ * (a : ↥H)) ∈ K ↔
      ((a : ↥H)⁻¹ ∈ K ↔ ⟨(x : G), hH0 x.2⟩ * (a : ↥H) ∈ K) :=
    Subgroup.mul_mem_iff_of_index_two hindex (a := (a : ↥H)⁻¹)
      (b := ⟨(x : G), hH0 x.2⟩ * (a : ↥H))
  have hiff2 : ⟨(x : G), hH0 x.2⟩ * (a : ↥H) ∈ K ↔
      (⟨(x : G), hH0 x.2⟩ ∈ K ↔ (a : ↥H) ∈ K) :=
    Subgroup.mul_mem_iff_of_index_two hindex (a := ⟨(x : G), hH0 x.2⟩) (b := a)
  have hxK : ⟨(x : G), hH0 x.2⟩ ∈ K := Subgroup.mem_subgroupOf.mpr x.2
  have hainv : (a : ↥H)⁻¹ ∈ K ↔ (a : ↥H) ∈ K := Subgroup.inv_mem_iff K
  rw [hiff1, hiff2]
  simp [hxK, hainv]

/-- The induced function vanishes outside `H0` (which is normal of index two). -/
public theorem inducedFromSub_eq_zero_of_not_mem {G : Type u} [Group G] [Fintype G]
    (H0 H : Subgroup G) (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    {ν : ClassFunction (↥H0)} {x : ↥H} (hx : (x : G) ∉ H0) :
    inducedFromSub hH0 ν x = 0 := by
  classical
  let K : Subgroup (↥H) := H0.subgroupOf H
  have hnot : ∀ y : ↥H, ¬ (y : ↥H)⁻¹ * x * (y : ↥H) ∈ K := by
    intro y hy
    have hiff1 : (y : ↥H)⁻¹ * (x * (y : ↥H)) ∈ K ↔
        ((y : ↥H)⁻¹ ∈ K ↔ x * (y : ↥H) ∈ K) :=
      Subgroup.mul_mem_iff_of_index_two hindex (a := (y : ↥H)⁻¹) (b := x * (y : ↥H))
    have hiff2 : x * (y : ↥H) ∈ K ↔ (x ∈ K ↔ (y : ↥H) ∈ K) :=
      Subgroup.mul_mem_iff_of_index_two hindex (a := x) (b := y)
    have hyK : (y : ↥H)⁻¹ ∈ K ↔ (y : ↥H) ∈ K := Subgroup.inv_mem_iff K
    have hxK' : x ∈ K ↔ (y : ↥H)⁻¹ * x * (y : ↥H) ∈ K := by
      rw [mul_assoc, hiff1, hiff2, hyK]
      tauto
    exact hx (Subgroup.mem_subgroupOf.mp (hxK'.mpr hy))
  unfold inducedFromSub
  unfold inducedClassFunction
  simp [hnot, K]

/-- The conjugate of a character is a character. -/
public theorem isCharacter_conjChar {G : Type u} [Group G] (H0 : Subgroup G) {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) {ν : ClassFunction (↥H0)}
    (hν : IsCharacter ν) : IsCharacter (conjChar H0 hsH0 ν) := by
  rcases hν with ⟨n, ρ, hχeq⟩
  refine ⟨n, { toFun := fun g => ρ (conjMonoidHom H0 s hsH0 g)
               map_one' := by
                 refine LinearMap.ext ?_
                 intro v
                 have hc1 : conjMonoidHom H0 s hsH0 1 = (1 : ↥H0) := by
                   ext
                   change s * (1 : G) * s⁻¹ = 1
                   group
                 calc
                   (ρ (conjMonoidHom H0 s hsH0 1)) v = (ρ 1) v := by rw [hc1]
                   _ = v := by
                     simpa using
                       (congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) ρ.map_one')
               map_mul' := by
                 intro g h
                 refine LinearMap.ext ?_
                 intro v
                 have hcm : conjMonoidHom H0 s hsH0 (g * h) =
                     conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h := by
                   ext
                   change s * ((g : G) * (h : G)) * s⁻¹ = (s * (g : G) * s⁻¹) * (s * (h : G) * s⁻¹)
                   group
                 have hρm : ρ (conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h) =
                     ρ (conjMonoidHom H0 s hsH0 g) * ρ (conjMonoidHom H0 s hsH0 h) :=
                   ρ.map_mul' _ _
                 calc
                   (ρ (conjMonoidHom H0 s hsH0 (g * h))) v
                       = (ρ (conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h)) v := by rw [hcm]
                   _ = (ρ (conjMonoidHom H0 s hsH0 g) * ρ (conjMonoidHom H0 s hsH0 h)) v := by rw [hρm]
               }, ?_⟩
  ext x
  change ν (conjMonoidHom H0 s hsH0 x) = (LinearMap.trace ℂ (Fin n → ℂ)) (ρ (conjMonoidHom H0 s hsH0 x))
  rw [hχeq]
  rfl

/-- `|ν^s| = |ν|` (in `g⁻¹`-form): conjugation is an isometry of the inner product. -/
public theorem norm_inv_conjChar {G : Type u} [Group G] [Fintype G] (H0 : Subgroup G)
    {s : G} (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0)
    (hsH0_inv : ∀ x : ↥H0, s⁻¹ * (x : G) * s ∈ H0)
    (ν : ClassFunction (↥H0)) :
    scalarProductInv (↥H0) (conjChar H0 hsH0 ν) (conjChar H0 hsH0 ν) = scalarProductInv (↥H0) ν ν := by
  classical
  let c : ↥H0 ≃ ↥H0 :=
    { toFun := conjMonoidHom H0 s hsH0
      invFun := conjMonoidHom H0 (s⁻¹) (fun x : ↥H0 => by
        convert hsH0_inv x using 1
        group)
      left_inv := by
        intro x
        ext
        change s⁻¹ * (s * (x : G) * s⁻¹) * (s⁻¹)⁻¹ = x
        group
      right_inv := by
        intro x
        ext
        change s * (s⁻¹ * (x : G) * (s⁻¹)⁻¹) * s⁻¹ = x
        group }
  unfold scalarProductInv
  congr 1
  refine Fintype.sum_equiv c (fun x : ↥H0 => conjChar H0 hsH0 ν x * conjChar H0 hsH0 ν x⁻¹)
    (fun x : ↥H0 => ν x * ν x⁻¹) ?_
  intro x
  have hc : conjMonoidHom H0 s hsH0 x⁻¹ = (conjMonoidHom H0 s hsH0 x)⁻¹ := by
    ext
    change s * ((x⁻¹ : ↥H0) : G) * s⁻¹ = (s * ((x : ↥H0) : G) * s⁻¹)⁻¹
    change s * ((x : ↥H0) : G)⁻¹ * s⁻¹ = (s * ((x : ↥H0) : G) * s⁻¹)⁻¹
    group
  simp [conjChar, hc, c]

/-- The `s`-conjugate of an irreducible character is irreducible (via the norm-one
criterion and the isometry of conjugation). -/
public theorem isIrreducibleCharacter_conjChar {G : Type u} [Group G] [Fintype G]
    (H0 : Subgroup G) {s : G}
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0)
    (hsH0_inv : ∀ x : ↥H0, s⁻¹ * (x : G) * s ∈ H0)
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν) :
    IsIrreducibleCharacter (conjChar H0 hsH0 ν) := by
  refine isIrreducibleCharacter_of_norm_one_inv (isCharacter_conjChar H0 hsH0 ?hchar) ?hnorm
  · rcases hν with ⟨n, ρ, hρ, hχeq⟩
    exact ⟨n, ρ, hχeq⟩
  · rw [norm_inv_conjChar H0 hsH0 hsH0_inv ν]
    exact isIrreducible_norm_inv_one hν

/-- For `|H : H0| = 2`, `|ν^H|² = 1` when `ν^s ≠ ν` (in `g⁻¹`-form). -/
public theorem scalarProductInv_ind_index_two {G : Type u} [Group G] [Fintype G]
    (H0 H : Subgroup G) (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    {s : G} (hs : s ∈ H) (hs_not : s ∉ H0)
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν)
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0)
    (hνs_ne : conjChar H0 hsH0 ν ≠ ν) :
    scalarProductInv (↥H) (inducedFromSub hH0 ν) (inducedFromSub hH0 ν) = 1 := by
  classical
  let K : Subgroup (↥H) := H0.subgroupOf H
  let s' : ↥H := ⟨s, hs⟩
  let ν' : ClassFunction (↥K) := fun x => ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  let νs : ClassFunction (↥H0) := conjChar H0 hsH0 ν
  let νs' : ClassFunction (↥K) := fun x => νs ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  have hsK : s' ∉ K := by
    intro hK
    exact hs_not (Subgroup.mem_subgroupOf.mp hK)
  have hconj : ∀ (a : ↥H) (x : ↥H0), (a : G)⁻¹ * (x : G) * (a : G) ∈ H0 :=
    conj_mem_of_index_two H0 H hH0 hindex
  have hsH0_inv : ∀ x : ↥H0, s'⁻¹ * (x : G) * s' ∈ H0 := by
    intro x
    simpa using hconj s' x
  have hpart1 : ∀ k : ↥K,
      (inducedFromSub hH0 ν) (k : ↥H) = ν' k + νs' k := by
    intro k
    have hk : (k : G) ∈ H0 := Subgroup.mem_subgroupOf.mp k.2
    have hsk : s * (k : G) * s⁻¹ ∈ H0 := hsH0 ⟨(k : G), hk⟩
    have h := inducedFromSub_eq_add_conj_index_two H0 H hH0 hindex hs hs_not ν
      (irreducibleCharacter_isClassFunction hν) hk hsk
    simpa [ν', νs', νs, conjChar, conjMonoidHom, hsk] using h
  have hpart1inv : ∀ k : ↥K,
      (inducedFromSub hH0 ν) (k⁻¹ : ↥H) = ν' k⁻¹ + νs' k⁻¹ := by
    intro k
    exact hpart1 (k⁻¹)
  have hzero : ∀ k : ↥K, (inducedFromSub hH0 ν) (s'⁻¹ * (k : ↥H)) = 0 := by
    intro k
    apply inducedFromSub_eq_zero_of_not_mem H0 H hH0 hindex
    intro hx
    have h1 : (s' : G)⁻¹ = (s' : G)⁻¹ * (k : G) * (k : G)⁻¹ := by group
    have this : (s' : G)⁻¹ ∈ H0 := by
      rw [h1]
      exact H0.mul_mem hx (H0.inv_mem (Subgroup.mem_subgroupOf.mp k.2))
    have hsK_inv : s'⁻¹ ∉ K := by
      intro hK
      exact hsK ((Subgroup.inv_mem_iff K).mp hK)
    exact hsK_inv (Subgroup.mem_subgroupOf.mpr this)
  have hsplit := sum_split_index_two (H := ↥H) (K := K) hindex (s := s') hsK
      (fun x : ↥H => (inducedFromSub hH0 ν) x * (inducedFromSub hH0 ν) (x⁻¹))
  have hsumK :
      (∑ k : ↥K, (inducedFromSub hH0 ν) (k : ↥H) * (inducedFromSub hH0 ν) ((k : ↥H)⁻¹)) =
        (∑ k : ↥K, (ν' k + νs' k) * (ν' k⁻¹ + νs' k⁻¹)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hpart1 k, hpart1inv k]
  have hsum_expand :
      (∑ k : ↥K, (ν' k + νs' k) * (ν' k⁻¹ + νs' k⁻¹)) =
        (∑ k : ↥K, ν' k * ν' k⁻¹) + (∑ k : ↥K, ν' k * νs' k⁻¹) +
          (∑ k : ↥K, νs' k * ν' k⁻¹) + (∑ k : ↥K, νs' k * νs' k⁻¹) := by
    simp [Finset.sum_add_distrib, mul_add, add_mul]
    ring
  let eK : ↥K ≃ ↥H0 :=
    { toFun := fun k => ⟨(k : G), Subgroup.mem_subgroupOf.mp k.2⟩
      invFun := fun x => ⟨⟨(x : G), hH0 x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
      left_inv := by intro k; ext; rfl
      right_inv := by intro x; ext; rfl }
  have hcard0 : (Nat.card (↥H0) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥H0)).ne'
  have hsum1 : (∑ k : ↥K, ν' k * ν' k⁻¹) = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν ν := by
    calc
      (∑ k : ↥K, ν' k * ν' k⁻¹) = ∑ x : ↥H0, ν x * ν x⁻¹ := by
        refine Fintype.sum_equiv eK (fun k => ν' k * ν' k⁻¹) (fun x => ν x * ν x⁻¹) ?_
        intro k
        rfl
      _ = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν ν := by
        rw [scalarProductInv]
        rw [← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
  have hsum2 : (∑ k : ↥K, ν' k * νs' k⁻¹) = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν νs := by
    calc
      (∑ k : ↥K, ν' k * νs' k⁻¹) = ∑ x : ↥H0, ν x * νs x⁻¹ := by
        refine Fintype.sum_equiv eK (fun k => ν' k * νs' k⁻¹) (fun x => ν x * νs x⁻¹) ?_
        intro k
        rfl
      _ = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν νs := by
        rw [scalarProductInv]
        rw [← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
  have hsum3 : (∑ k : ↥K, νs' k * ν' k⁻¹) = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs ν := by
    calc
      (∑ k : ↥K, νs' k * ν' k⁻¹) = ∑ x : ↥H0, νs x * ν x⁻¹ := by
        refine Fintype.sum_equiv eK (fun k => νs' k * ν' k⁻¹) (fun x => νs x * ν x⁻¹) ?_
        intro k
        rfl
      _ = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs ν := by
        rw [scalarProductInv]
        rw [← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
  have hsum4 : (∑ k : ↥K, νs' k * νs' k⁻¹) = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs νs := by
    calc
      (∑ k : ↥K, νs' k * νs' k⁻¹) = ∑ x : ↥H0, νs x * νs x⁻¹ := by
        refine Fintype.sum_equiv eK (fun k => νs' k * νs' k⁻¹) (fun x => νs x * νs x⁻¹) ?_
        intro k
        rfl
      _ = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs νs := by
        rw [scalarProductInv]
        rw [← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
  have hνs_char : IsCharacter νs := by
    rcases hν with ⟨n, ρ, hρ, hχeq⟩
    exact isCharacter_conjChar H0 hsH0 ⟨n, ρ, hχeq⟩
  have hνs_norm : scalarProductInv (↥H0) νs νs = 1 := by
    rw [norm_inv_conjChar H0 hsH0 hsH0_inv ν]
    exact isIrreducible_norm_inv_one hν
  have hνs : IsIrreducibleCharacter νs :=
    isIrreducibleCharacter_of_norm_one_inv hνs_char hνs_norm
  have hν_ne : ν ≠ νs := by
    simpa [νs] using hνs_ne.symm
  have hcard : (Nat.card (↥H) : ℂ) = (2 : ℂ) * (Nat.card (↥H0) : ℂ) := by
    -- |H| = |K|·index = 2·|K| = 2·|H0|
    have h1 : Nat.card (↥H) = Nat.card (↥K) * K.index := by
      simpa using (Subgroup.card_mul_index K).symm
    have h2 : Nat.card (↥K) = Nat.card (↥H0) := by
      exact Nat.card_congr eK
    rw [h1, h2, hindex]
    rw [Nat.cast_mul]
    ring
  calc
    scalarProductInv (↥H) (inducedFromSub hH0 ν) (inducedFromSub hH0 ν)
        = (Nat.card (↥H) : ℂ)⁻¹ *
            ((∑ k : ↥K, ν' k * ν' k⁻¹) + (∑ k : ↥K, ν' k * νs' k⁻¹) +
              (∑ k : ↥K, νs' k * ν' k⁻¹) + (∑ k : ↥K, νs' k * νs' k⁻¹)) := by
            rw [scalarProductInv]
            rw [hsplit]
            rw [hsumK]
            simp [hzero]
            rw [hsum_expand]
    _ = (Nat.card (↥H) : ℂ)⁻¹ *
          ((Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν ν +
            (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν νs +
            (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs ν +
            (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) νs νs) := by
            rw [hsum1, hsum2, hsum3, hsum4]
    _ = (Nat.card (↥H) : ℂ)⁻¹ * ((Nat.card (↥H0) : ℂ) * (1 + 0 + 0 + 1)) := by
            congr 1
            rw [isIrreducible_norm_inv_one hν,
              isIrreducible_orthogonal_inv hν hνs hν_ne,
              isIrreducible_orthogonal_inv hνs hν hν_ne.symm,
              isIrreducible_norm_inv_one hνs]
            ring
    _ = 1 := by
            rw [hcard]
            field_simp [hcard0]
            ring

/-- For `|H : H0| = 2`, `|ν^H|² = 2` when `ν^s = ν` (in `g⁻¹`-form):
Remark 1.4's `ν^H = σ₁ + σ₂` case. -/
public theorem scalarProductInv_ind_index_two_of_fixed {G : Type u} [Group G] [Fintype G]
    (H0 H : Subgroup G) (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    {s : G} (hs : s ∈ H) (hs_not : s ∉ H0)
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν)
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0)
    (hνs_eq : conjChar H0 hsH0 ν = ν) :
    scalarProductInv (↥H) (inducedFromSub hH0 ν) (inducedFromSub hH0 ν) = 2 := by
  classical
  let K : Subgroup (↥H) := H0.subgroupOf H
  let s' : ↥H := ⟨s, hs⟩
  let ν' : ClassFunction (↥K) := fun x => ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  let νs : ClassFunction (↥H0) := conjChar H0 hsH0 ν
  let νs' : ClassFunction (↥K) := fun x => νs ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  have hsK : s' ∉ K := by
    intro hK
    exact hs_not (Subgroup.mem_subgroupOf.mp hK)
  have hpart1 : ∀ k : ↥K,
      (inducedFromSub hH0 ν) (k : ↥H) = ν' k + νs' k := by
    intro k
    have hk : (k : G) ∈ H0 := Subgroup.mem_subgroupOf.mp k.2
    have hsk : s * (k : G) * s⁻¹ ∈ H0 := hsH0 ⟨(k : G), hk⟩
    have h := inducedFromSub_eq_add_conj_index_two H0 H hH0 hindex hs hs_not ν
      (irreducibleCharacter_isClassFunction hν) hk hsk
    simpa [ν', νs', νs, conjChar, conjMonoidHom, hsk] using h
  have hνs_eq' : νs' = ν' := by
    funext k
    simp [ν', νs', νs, conjChar, conjMonoidHom, hνs_eq]
  have hpart1' : ∀ k : ↥K, (inducedFromSub hH0 ν) (k : ↥H) = 2 * ν' k := by
    intro k
    calc
      (inducedFromSub hH0 ν) (k : ↥H) = ν' k + νs' k := hpart1 k
      _ = ν' k + ν' k := by rw [hνs_eq']
      _ = 2 * ν' k := by ring
  have hpart1inv : ∀ k : ↥K, (inducedFromSub hH0 ν) (k⁻¹ : ↥H) = 2 * ν' k⁻¹ := by
    intro k
    exact hpart1' (k⁻¹)
  have hzero : ∀ k : ↥K, (inducedFromSub hH0 ν) (s'⁻¹ * (k : ↥H)) = 0 := by
    intro k
    apply inducedFromSub_eq_zero_of_not_mem H0 H hH0 hindex
    intro hx
    have h1 : (s' : G)⁻¹ = (s' : G)⁻¹ * (k : G) * (k : G)⁻¹ := by group
    have this : (s' : G)⁻¹ ∈ H0 := by
      rw [h1]
      exact H0.mul_mem hx (H0.inv_mem (Subgroup.mem_subgroupOf.mp k.2))
    have hsK_inv : s'⁻¹ ∉ K := by
      intro hK
      exact hsK ((Subgroup.inv_mem_iff K).mp hK)
    exact hsK_inv (Subgroup.mem_subgroupOf.mpr this)
  have hsplit := sum_split_index_two (H := ↥H) (K := K) hindex (s := s') hsK
      (fun x : ↥H => (inducedFromSub hH0 ν) x * (inducedFromSub hH0 ν) (x⁻¹))
  let eK : ↥K ≃ ↥H0 :=
    { toFun := fun k => ⟨(k : G), Subgroup.mem_subgroupOf.mp k.2⟩
      invFun := fun x => ⟨⟨(x : G), hH0 x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
      left_inv := by intro k; ext; rfl
      right_inv := by intro x; ext; rfl }
  have hcard0 : (Nat.card (↥H0) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥H0)).ne'
  have hsumK :
      (∑ k : ↥K, (inducedFromSub hH0 ν) (k : ↥H) * (inducedFromSub hH0 ν) ((k : ↥H)⁻¹)) =
        (∑ k : ↥K, (2 * ν' k) * (2 * ν' k⁻¹)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hpart1' k, hpart1inv k]
  have hsum : (∑ k : ↥K, (2 * ν' k) * (2 * ν' k⁻¹)) =
      (4 : ℂ) * (Nat.card (↥H0) : ℂ) := by
    calc
      (∑ k : ↥K, (2 * ν' k) * (2 * ν' k⁻¹))
          = (4 : ℂ) * (∑ k : ↥K, ν' k * ν' k⁻¹) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ = (4 : ℂ) * ((Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν ν) := by
              congr 1
              calc
                (∑ k : ↥K, ν' k * ν' k⁻¹) = ∑ x : ↥H0, ν x * ν x⁻¹ := by
                  refine Fintype.sum_equiv eK (fun k => ν' k * ν' k⁻¹) (fun x => ν x * ν x⁻¹) ?_
                  intro k
                  rfl
                _ = (Nat.card (↥H0) : ℂ) * scalarProductInv (↥H0) ν ν := by
                  rw [scalarProductInv]
                  rw [← mul_assoc, mul_inv_cancel₀ hcard0, one_mul]
      _ = (4 : ℂ) * (Nat.card (↥H0) : ℂ) := by
              rw [isIrreducible_norm_inv_one hν]
              ring
  have hcard : (Nat.card (↥H) : ℂ) = (2 : ℂ) * (Nat.card (↥H0) : ℂ) := by
    have h1 : Nat.card (↥H) = Nat.card (↥K) * K.index := by
      simpa using (Subgroup.card_mul_index K).symm
    have h2 : Nat.card (↥K) = Nat.card (↥H0) := by
      exact Nat.card_congr eK
    rw [h1, h2, hindex]
    rw [Nat.cast_mul]
    ring
  calc
    scalarProductInv (↥H) (inducedFromSub hH0 ν) (inducedFromSub hH0 ν)
        = (Nat.card (↥H) : ℂ)⁻¹ *
            ((∑ k : ↥K, (inducedFromSub hH0 ν) (k : ↥H) * (inducedFromSub hH0 ν) ((k : ↥H)⁻¹)) +
              ∑ k : ↥K, (inducedFromSub hH0 ν) (s'⁻¹ * (k : ↥H)) *
                (inducedFromSub hH0 ν) ((s'⁻¹ * (k : ↥H))⁻¹)) := by
            rw [scalarProductInv]
            rw [hsplit]
    _ = (Nat.card (↥H) : ℂ)⁻¹ *
          ((∑ k : ↥K, (2 * ν' k) * (2 * ν' k⁻¹)) + 0) := by
            rw [hsumK]
            simp [hzero]
    _ = (Nat.card (↥H) : ℂ)⁻¹ * ((4 : ℂ) * (Nat.card (↥H0) : ℂ)) := by
            rw [hsum]
            ring
    _ = 2 := by
            rw [hcard]
            field_simp [hcard0]
            ring

/-- For `|H : H0| = 2`, the induced class function of an irreducible character is a
character: it is the character of the explicit index-two induced representation. -/
public theorem isCharacter_ind_index_two {G : Type u} [Group G] [Fintype G]
    (H0 H : Subgroup G) (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2)
    {s : G} (hs : s ∈ H) (hs_not : s ∉ H0)
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν)
    (hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0) :
    IsCharacter (inducedFromSub hH0 ν) := by
  classical
  have hν' : IsIrreducibleCharacter ν := hν
  rcases hν with ⟨n, ρ, hρ, hχeq⟩
  let V := Fin n → ℂ
  let ρs : Representation ℂ (↥H0) V :=
    { toFun := fun g => ρ (conjMonoidHom H0 s hsH0 g)
      map_one' := by
        refine LinearMap.ext ?_
        intro v
        have hc1 : conjMonoidHom H0 s hsH0 1 = (1 : ↥H0) := by
          ext
          change s * (1 : G) * s⁻¹ = 1
          group
        calc
          (ρ (conjMonoidHom H0 s hsH0 1)) v = (ρ 1) v := by rw [hc1]
          _ = v := by
            simpa using
              (congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) ρ.map_one')
      map_mul' := by
        intro g h
        refine LinearMap.ext ?_
        intro v
        have hcm : conjMonoidHom H0 s hsH0 (g * h) =
            conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h := by
          ext
          change s * ((g : G) * (h : G)) * s⁻¹ = (s * (g : G) * s⁻¹) * (s * (h : G) * s⁻¹)
          group
        have hρm : ρ (conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h) =
            ρ (conjMonoidHom H0 s hsH0 g) * ρ (conjMonoidHom H0 s hsH0 h) :=
          ρ.map_mul' _ _
        calc
          (ρ (conjMonoidHom H0 s hsH0 (g * h))) v
              = (ρ (conjMonoidHom H0 s hsH0 g * conjMonoidHom H0 s hsH0 h)) v := by rw [hcm]
          _ = (ρ (conjMonoidHom H0 s hsH0 g) * ρ (conjMonoidHom H0 s hsH0 h)) v := by rw [hρm]
      }
  let K : Subgroup (↥H) := H0.subgroupOf H
  let s' : ↥H := ⟨s, hs⟩
  have hsK : s' ∉ K := by
    intro hK
    exact hs_not (Subgroup.mem_subgroupOf.mp hK)
  have hconj : ∀ (a : ↥H) (x : ↥H0), (a : G)⁻¹ * (x : G) * (a : G) ∈ H0 :=
    conj_mem_of_index_two H0 H hH0 hindex
  have hsK_inv : s'⁻¹ ∉ K := by
    intro hK
    exact hsK ((Subgroup.inv_mem_iff K).mp hK)
  have hkc : ∀ h : ↥H, h ∉ K → s'⁻¹ * h ∈ K := by
    intro h hh
    have hiff : s'⁻¹ * h ∈ K ↔ (s'⁻¹ ∈ K ↔ h ∈ K) :=
      Subgroup.mul_mem_iff_of_index_two hindex (a := s'⁻¹) (b := h)
    rw [hiff]
    simp [hsK_inv, hh]
  have hs2 : s' * s' ∈ K := by
    have hiff := Subgroup.mul_mem_iff_of_index_two hindex (a := s') (b := s')
    rw [hiff]
  have hs2k : ∀ (k : ↥H0), (s' : G) * (s' : G) * (k : G) ∈ H0 := by
    intro k
    exact H0.mul_mem (Subgroup.mem_subgroupOf.mp hs2) k.2
  have hck : ∀ (k : ↥H0), (s' : G) * (k : G) * (s' : G)⁻¹ ∈ H0 := by
    intro k
    simpa using hconj (s'⁻¹) k
  let σfun : (↥H) → (V × V) →ₗ[ℂ] (V × V) := fun h =>
    if hh : h ∈ K then
      (ρ ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩).prodMap
        (ρs ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩)
    else
      let k : ↥H0 := ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩
      ((ρ ⟨(s' : G) * (k : G) * (s' : G)⁻¹, hck k⟩).prodMap
        (ρ ⟨(s' : G) * (s' : G) * (k : G), hs2k k⟩)) ∘ₗ
        (LinearEquiv.prodComm ℂ V V)
  let σ : Representation ℂ (↥H) (V × V) :=
    { toFun := σfun
      map_one' := by
        refine LinearMap.ext ?_
        intro w
        have hρ1 : ∀ p : (1 : G) ∈ H0, ρ ⟨(1 : G), p⟩ = 1 := by
          intro p
          have h : (⟨(1 : G), p⟩ : ↥H0) = 1 := by
            ext
            rfl
          rw [h]
          exact ρ.map_one'
        have hρs1 : ∀ p : (1 : G) ∈ H0, ρs ⟨(1 : G), p⟩ = 1 := by
          intro p
          have h : (⟨(1 : G), p⟩ : ↥H0) = 1 := by
            ext
            rfl
          rw [h]
          exact ρs.map_one'
        have hK1 : (1 : ↥H) ∈ K := K.one_mem
        change σfun 1 w = w
        simp [σfun, hK1, hρ1, hρs1, LinearMap.prodMap_one]
      map_mul' := by
        intro h g
        by_cases hh : h ∈ K <;> by_cases hg : g ∈ K
        · have hhg : h * g ∈ K := K.mul_mem hh hg
          refine LinearMap.ext ?_
          intro w
          change σfun (h * g) w = (σfun h * σfun g) w
          simp [σfun, hh, hg, hhg]
          constructor
          · have hρm : ρ ((⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0)) =
              ρ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                ρ (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0) :=
              ρ.map_mul' _ _
            change ρ ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ w.1 =
              (ρ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                ρ (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0)) w.1
            rw [← hρm]
            have he : (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0) =
                ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ := by
              apply Subtype.ext
              rfl
            rw [he]
          · have hρsm : ρs ((⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0)) =
              ρs (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                ρs (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0) :=
              ρs.map_mul' _ _
            change ρs ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ w.2 =
              (ρs (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                ρs (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0)) w.2
            rw [← hρsm]
            have he : (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) *
                (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0) =
                ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ := by
              apply Subtype.ext
              rfl
            rw [he]
        · have hhg : h * g ∉ K := by
            intro hx
            apply hg
            have : h⁻¹ * (h * g) ∈ K := K.mul_mem (K.inv_mem hh) hx
            simpa [mul_assoc] using this
          refine LinearMap.ext ?_
          intro w
          change σfun (h * g) w = (σfun h * σfun g) w
          simp [σfun, hh, hg, hhg]
          constructor
          · have hb : (g : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * (g : G), Subgroup.mem_subgroupOf.mp (hkc g hg)⟩ using 1
              · change (g : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * (g : G)) * (s' : G)⁻¹
                group
            have ha : (h : G) * (g : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * ((h : G) * (g : G)), Subgroup.mem_subgroupOf.mp (hkc (h * g) hhg)⟩ using 1
              · change (h : G) * (g : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * ((h : G) * (g : G))) * (s' : G)⁻¹
                group
            have hρm : ρ ((⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hb⟩) =
                ρ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) * ρ ⟨(g : G) * (s' : G)⁻¹, hb⟩ :=
              ρ.map_mul' _ _
            have he : (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hb⟩ =
                ⟨(h : G) * (g : G) * (s' : G)⁻¹, ha⟩ := by
              apply Subtype.ext
              change (h : G) * ((g : G) * (s' : G)⁻¹) = (h : G) * (g : G) * (s' : G)⁻¹
              group
            calc
              ρ ⟨(h : G) * (g : G) * (s' : G)⁻¹, ha⟩ w.2
                  = ρ ((⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hb⟩) w.2 := by rw [← he]
              _ = (ρ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) * ρ ⟨(g : G) * (s' : G)⁻¹, hb⟩) w.2 := by rw [hρm]
              _ = ρ (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) (ρ ⟨(g : G) * (s' : G)⁻¹, hb⟩ w.2) := rfl
          · have hρs_eq : ρs (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) =
              ρ ⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ := rfl
            have hc : (s' : G) * (g : G) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * (g : G), Subgroup.mem_subgroupOf.mp (hkc g hg)⟩ using 1
              · change (s' : G) * (g : G) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * (g : G))
                group
            have hd : (s' : G) * ((h : G) * (g : G)) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * ((h : G) * (g : G)), Subgroup.mem_subgroupOf.mp (hkc (h * g) hhg)⟩ using 1
              · change (s' : G) * ((h : G) * (g : G)) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * ((h : G) * (g : G)))
                group
            have hρm : ρ ((⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ : ↥H0) * ⟨(s' : G) * (g : G), hc⟩) =
                ρ ⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ * ρ ⟨(s' : G) * (g : G), hc⟩ :=
              ρ.map_mul' _ _
            have he : (⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ : ↥H0) * ⟨(s' : G) * (g : G), hc⟩ =
                ⟨(s' : G) * ((h : G) * (g : G)), hd⟩ := by
              apply Subtype.ext
              change ((s' : G) * (h : G) * (s' : G)⁻¹) * ((s' : G) * (g : G)) = (s' : G) * ((h : G) * (g : G))
              group
            calc
              ρ ⟨(s' : G) * ((h : G) * (g : G)), hd⟩ w.1
                  = ρ (⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ * ⟨(s' : G) * (g : G), hc⟩) w.1 := by rw [← he]
              _ = (ρ ⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ * ρ ⟨(s' : G) * (g : G), hc⟩) w.1 := by rw [hρm]
              _ = ρ ⟨(s : G) * (h : G) * (s : G)⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ (ρ ⟨(s' : G) * (g : G), hc⟩ w.1) := rfl
              _ = ρs (⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ : ↥H0) (ρ ⟨(s' : G) * (g : G), hc⟩ w.1) := by rw [hρs_eq]
        · have hhg : h * g ∉ K := by
            intro hx
            apply hh
            have : (h * g) * g⁻¹ ∈ K := K.mul_mem hx (K.inv_mem hg)
            simpa [mul_assoc] using this
          refine LinearMap.ext ?_
          intro w
          change σfun (h * g) w = (σfun h * σfun g) w
          simp [σfun, hh, hg, hhg]
          constructor
          · have hρs_eq : ρs (⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ : ↥H0) =
              ρ ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩ := rfl
            have he : (h : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩ using 1
              · change (h : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * (h : G)) * (s' : G)⁻¹
                group
            have hf : (h : G) * (g : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * ((h : G) * (g : G)), Subgroup.mem_subgroupOf.mp (hkc (h * g) hhg)⟩ using 1
              · change (h : G) * (g : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * ((h : G) * (g : G))) * (s' : G)⁻¹
                group
            have hρm : ρ ((⟨(h : G) * (s' : G)⁻¹, he⟩ : ↥H0) * ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩) =
                ρ ⟨(h : G) * (s' : G)⁻¹, he⟩ * ρ ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩ :=
              ρ.map_mul' _ _
            have heq : (⟨(h : G) * (s' : G)⁻¹, he⟩ : ↥H0) * ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩ =
                ⟨(h : G) * (g : G) * (s' : G)⁻¹, hf⟩ := by
              apply Subtype.ext
              change ((h : G) * (s' : G)⁻¹) * ((s' : G) * (g : G) * (s' : G)⁻¹) = (h : G) * (g : G) * (s' : G)⁻¹
              group
            calc
              ρ ⟨(h : G) * (g : G) * (s' : G)⁻¹, hf⟩ w.2
                  = ρ (⟨(h : G) * (s' : G)⁻¹, he⟩ * ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩) w.2 := by rw [← heq]
              _ = (ρ ⟨(h : G) * (s' : G)⁻¹, he⟩ * ρ ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩) w.2 := by rw [hρm]
              _ = ρ ⟨(h : G) * (s' : G)⁻¹, he⟩ (ρ ⟨(s : G) * (g : G) * (s : G)⁻¹, hsH0 ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩⟩ w.2) := rfl
              _ = ρ ⟨(h : G) * (s' : G)⁻¹, he⟩ (ρs ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ w.2) := by rw [hρs_eq]
          · have hg₂ : (s' : G) * (h : G) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩ using 1
              · change (s' : G) * (h : G) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * (h : G))
                group
            have hh₂ : (s' : G) * ((h : G) * (g : G)) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * ((h : G) * (g : G)), Subgroup.mem_subgroupOf.mp (hkc (h * g) hhg)⟩ using 1
              · change (s' : G) * ((h : G) * (g : G)) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * ((h : G) * (g : G)))
                group
            have hρm : ρ ((⟨(s' : G) * (h : G), hg₂⟩ : ↥H0) * ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩) =
                ρ ⟨(s' : G) * (h : G), hg₂⟩ * ρ ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ :=
              ρ.map_mul' _ _
            have heq : (⟨(s' : G) * (h : G), hg₂⟩ : ↥H0) * ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ =
                ⟨(s' : G) * ((h : G) * (g : G)), hh₂⟩ := by
              apply Subtype.ext
              change ((s' : G) * (h : G)) * (g : G) = (s' : G) * ((h : G) * (g : G))
              group
            calc
              ρ ⟨(s' : G) * ((h : G) * (g : G)), hh₂⟩ w.1
                  = ρ (⟨(s' : G) * (h : G), hg₂⟩ * ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩) w.1 := by rw [← heq]
              _ = (ρ ⟨(s' : G) * (h : G), hg₂⟩ * ρ ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩) w.1 := by rw [hρm]
              _ = ρ ⟨(s' : G) * (h : G), hg₂⟩ (ρ ⟨(g : G), Subgroup.mem_subgroupOf.mp hg⟩ w.1) := rfl
        · have hhg : h * g ∈ K := by
            have hk₁ : s'⁻¹ * h ∈ K := hkc h hh
            have hk₂ : s'⁻¹ * g ∈ K := hkc g hg
            have hkg₁ : ((s' : G)⁻¹ * (h : G)) ∈ H0 :=
              Subgroup.mem_subgroupOf.mp hk₁
            have hkg₂ : ((s' : G)⁻¹ * (g : G)) ∈ H0 :=
              Subgroup.mem_subgroupOf.mp hk₂
            have hconj1 : (s' : G)⁻¹ * ((s' : G)⁻¹ * (h : G)) * (s' : G) ∈ H0 :=
              hconj s' ⟨(s' : G)⁻¹ * (h : G), hkg₁⟩
            apply Subgroup.mem_subgroupOf.mpr
            change ((h : G) * (g : G)) ∈ H0
            have hbig : (s' : G) * (s' : G) *
                ((s' : G)⁻¹ * ((s' : G)⁻¹ * (h : G)) * (s' : G)) * ((s' : G)⁻¹ * (g : G)) ∈ H0 := by
              exact H0.mul_mem (H0.mul_mem (Subgroup.mem_subgroupOf.mp hs2) hconj1) hkg₂
            convert hbig using 1
            group
          refine LinearMap.ext ?_
          intro w
          change σfun (h * g) w = (σfun h * σfun g) w
          simp [σfun, hh, hg, hhg]
          constructor
          · have hi : (h : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩ using 1
              · change (h : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * (h : G)) * (s' : G)⁻¹
                group
            have hj : (s' : G) * (g : G) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * (g : G), Subgroup.mem_subgroupOf.mp (hkc g hg)⟩ using 1
              · change (s' : G) * (g : G) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * (g : G))
                group
            have hρm : ρ ((⟨(h : G) * (s' : G)⁻¹, hi⟩ : ↥H0) * ⟨(s' : G) * (g : G), hj⟩) =
                ρ ⟨(h : G) * (s' : G)⁻¹, hi⟩ * ρ ⟨(s' : G) * (g : G), hj⟩ :=
              ρ.map_mul' _ _
            have heq : (⟨(h : G) * (s' : G)⁻¹, hi⟩ : ↥H0) * ⟨(s' : G) * (g : G), hj⟩ =
                ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ := by
              apply Subtype.ext
              change ((h : G) * (s' : G)⁻¹) * ((s' : G) * (g : G)) = (h : G) * (g : G)
              group
            calc
              ρ ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ w.1
                  = ρ (⟨(h : G) * (s' : G)⁻¹, hi⟩ * ⟨(s' : G) * (g : G), hj⟩) w.1 := by rw [← heq]
              _ = (ρ ⟨(h : G) * (s' : G)⁻¹, hi⟩ * ρ ⟨(s' : G) * (g : G), hj⟩) w.1 := by rw [hρm]
              _ = ρ ⟨(h : G) * (s' : G)⁻¹, hi⟩ (ρ ⟨(s' : G) * (g : G), hj⟩ w.1) := rfl
          · have hρs_eq : ρs (⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ : ↥H0) =
              ρ ⟨(s : G) * ((h : G) * (g : G)) * (s : G)⁻¹,
                hsH0 ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩⟩ := rfl
            have hk₂ : (s' : G) * (h : G) ∈ H0 := by
              convert hs2k ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩ using 1
              · change (s' : G) * (h : G) = (s' : G) * (s' : G) * ((s' : G)⁻¹ * (h : G))
                group
            have hl : (g : G) * (s' : G)⁻¹ ∈ H0 := by
              convert hck ⟨(s' : G)⁻¹ * (g : G), Subgroup.mem_subgroupOf.mp (hkc g hg)⟩ using 1
              · change (g : G) * (s' : G)⁻¹ = (s' : G) * ((s' : G)⁻¹ * (g : G)) * (s' : G)⁻¹
                group
            have hρm : ρ ((⟨(s' : G) * (h : G), hk₂⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hl⟩) =
                ρ ⟨(s' : G) * (h : G), hk₂⟩ * ρ ⟨(g : G) * (s' : G)⁻¹, hl⟩ :=
              ρ.map_mul' _ _
            have heq : (⟨(s' : G) * (h : G), hk₂⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hl⟩ =
                ⟨(s : G) * ((h : G) * (g : G)) * (s : G)⁻¹, hsH0 ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩⟩ := by
              apply Subtype.ext
              change ((s' : G) * (h : G)) * ((g : G) * (s' : G)⁻¹) = (s' : G) * ((h : G) * (g : G)) * (s' : G)⁻¹
              group
            calc
              ρs (⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩ : ↥H0) w.2
                  = ρ ⟨(s : G) * ((h : G) * (g : G)) * (s : G)⁻¹,
                      hsH0 ⟨(h : G) * (g : G), Subgroup.mem_subgroupOf.mp hhg⟩⟩ w.2 := by rw [hρs_eq]
              _ = ρ ((⟨(s' : G) * (h : G), hk₂⟩ : ↥H0) * ⟨(g : G) * (s' : G)⁻¹, hl⟩) w.2 := by rw [← heq]
              _ = (ρ (⟨(s' : G) * (h : G), hk₂⟩ : ↥H0) * ρ ⟨(g : G) * (s' : G)⁻¹, hl⟩) w.2 := by rw [hρm]
              _ = ρ (⟨(s' : G) * (h : G), hk₂⟩ : ↥H0) (ρ ⟨(g : G) * (s' : G)⁻¹, hl⟩ w.2) := rfl

      }
  let eDom : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
    (finSumFinEquiv).trans (Equiv.cast (by rw [two_mul]))
  let e : (V × V) ≃ₗ[ℂ] (Fin (2 * n) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℂ ℂ).symm).trans
      ((LinearEquiv.funCongrLeft ℂ ℂ eDom).symm)
  let σ' : Representation ℂ (↥H) (Fin (2 * n) → ℂ) :=
    { toFun := fun h => e.conj (σ h)
      map_one' := by
        refine LinearMap.ext ?_
        intro v
        have hσ1 : σfun 1 = 1 := by
          simpa [σ] using σ.map_one'
        calc
          e.conj (σ 1) v = e.conj (σfun 1) v := rfl
          _ = e.conj 1 v := by rw [hσ1]
          _ = v := by simp
      map_mul' := by
        intro a b
        have hm : σfun (a * b) = σfun a * σfun b := by
          simpa [σ] using σ.map_mul' a b
        calc
          e.conj (σ (a * b)) = e.conj (σfun (a * b)) := rfl
          _ = e.conj (σfun a * σfun b) := by rw [hm]
          _ = e.conj (σ a * σ b) := rfl
          _ = (e.conj (σ a)).comp (e.conj (σ b)) := by
                exact LinearEquiv.conj_comp e (σ b) (σ a)
          _ = e.conj (σ a) * e.conj (σ b) := rfl
      }
  have htrace_swap : ∀ (f g : V →ₗ[ℂ] V),
      LinearMap.trace ℂ (V × V) ((f.prodMap g) ∘ₗ (LinearEquiv.prodComm ℂ V V : V × V →ₗ[ℂ] V × V)) = 0 := by
    intro f g
    have hdecomp : (f.prodMap g) ∘ₗ (LinearEquiv.prodComm ℂ V V : V × V →ₗ[ℂ] V × V) =
        ((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V) +
          ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V) := by
      refine LinearMap.ext ?_
      intro x
      cases x with
      | mk v w =>
        simp [LinearMap.prodMap_apply, LinearMap.comp_apply, LinearEquiv.prodComm_apply]
    have ht1 : LinearMap.trace ℂ (V × V) ((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V) = 0 := by
      calc
        LinearMap.trace ℂ (V × V) ((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V)
            = LinearMap.trace ℂ V (LinearMap.snd ℂ V V ∘ₗ (LinearMap.inl ℂ V V ∘ₗ f)) := by
                rw [← LinearMap.trace_comp_comm' (f := LinearMap.snd ℂ V V) (g := LinearMap.inl ℂ V V ∘ₗ f)]
        _ = LinearMap.trace ℂ V ((LinearMap.snd ℂ V V ∘ₗ LinearMap.inl ℂ V V) ∘ₗ f) := by
                rw [← LinearMap.comp_assoc]
        _ = LinearMap.trace ℂ V ((0 : V →ₗ[ℂ] V) ∘ₗ f) := by
                rw [LinearMap.snd_comp_inl]
        _ = 0 := by
                simp
    have ht2 : LinearMap.trace ℂ (V × V) ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V) = 0 := by
      calc
        LinearMap.trace ℂ (V × V) ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V)
            = LinearMap.trace ℂ V (LinearMap.fst ℂ V V ∘ₗ (LinearMap.inr ℂ V V ∘ₗ g)) := by
                rw [← LinearMap.trace_comp_comm' (f := LinearMap.fst ℂ V V) (g := LinearMap.inr ℂ V V ∘ₗ g)]
        _ = LinearMap.trace ℂ V ((LinearMap.fst ℂ V V ∘ₗ LinearMap.inr ℂ V V) ∘ₗ g) := by
                rw [← LinearMap.comp_assoc]
        _ = LinearMap.trace ℂ V ((0 : V →ₗ[ℂ] V) ∘ₗ g) := by
                rw [LinearMap.fst_comp_inr]
        _ = 0 := by
                simp
    calc
      LinearMap.trace ℂ (V × V) ((f.prodMap g) ∘ₗ (LinearEquiv.prodComm ℂ V V : V × V →ₗ[ℂ] V × V))
          = LinearMap.trace ℂ (V × V) (((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V) +
              ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V)) := by
              rw [hdecomp]
      _ = LinearMap.trace ℂ (V × V) ((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V) +
          LinearMap.trace ℂ (V × V) ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V) := by
              exact (map_add (LinearMap.trace ℂ (V × V))
                ((LinearMap.inl ℂ V V ∘ₗ f) ∘ₗ LinearMap.snd ℂ V V)
                ((LinearMap.inr ℂ V V ∘ₗ g) ∘ₗ LinearMap.fst ℂ V V))
      _ = 0 := by
              rw [ht1, ht2]
              simp
  have htr_in : ∀ (h : ↥H) (hh : h ∈ K),
      LinearMap.trace ℂ (V × V) (σ h) = ν ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ +
        ν ⟨s * (h : G) * s⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ := by
    intro h hh
    calc
      LinearMap.trace ℂ (V × V) (σ h)
          = LinearMap.trace ℂ V (ρ ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩) +
            LinearMap.trace ℂ V (ρs ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩) := by
              simp [σ, σfun, hh, LinearMap.trace_prodMap']
      _ = ν ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ +
          ν ⟨s * (h : G) * s⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ := by
              congr 1
              · rw [hχeq]
                rfl
              · rw [hχeq]
                rfl
  have htr_swap : ∀ h : ↥H, h ∉ K → LinearMap.trace ℂ (V × V) (σ h) = 0 := by
    intro h hh
    calc
      LinearMap.trace ℂ (V × V) (σ h)
          = LinearMap.trace ℂ (V × V)
              ((ρ ⟨(s' : G) * (((s' : G)⁻¹ * (h : G)) : G) * (s' : G)⁻¹,
                  hck ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩⟩).prodMap
                (ρ ⟨(s' : G) * (s' : G) * ((s' : G)⁻¹ * (h : G)),
                  hs2k ⟨(s' : G)⁻¹ * (h : G), Subgroup.mem_subgroupOf.mp (hkc h hh)⟩⟩) ∘ₗ
                  (LinearEquiv.prodComm ℂ V V : V × V →ₗ[ℂ] V × V)) := by
              simp [σ, σfun, hh]
      _ = 0 := by
              exact htrace_swap _ _
  refine ⟨2 * n, σ', ?_⟩
  ext h
  by_cases hh : h ∈ K
  · calc
      (inducedFromSub hH0 ν) h = ν ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩ +
          ν ⟨s * (h : G) * s⁻¹, hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩⟩ := by
              exact inducedFromSub_eq_add_conj_index_two H0 H hH0 hindex hs hs_not ν
                (irreducibleCharacter_isClassFunction hν') (h := (h : G))
                (hh := Subgroup.mem_subgroupOf.mp hh)
                (hsh := hsH0 ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩)
      _ = LinearMap.trace ℂ (V × V) (σ h) := (htr_in h hh).symm
      _ = LinearMap.trace ℂ (Fin (2 * n) → ℂ) (σ' h) := by
              change LinearMap.trace ℂ (V × V) (σ h) = LinearMap.trace ℂ (Fin (2 * n) → ℂ) (e.conj (σ h))
              exact (LinearMap.trace_conj' (σ h) e).symm
      _ = σ'.character h := rfl
  · calc
      (inducedFromSub hH0 ν) h = 0 := by
              exact inducedFromSub_eq_zero_of_not_mem H0 H hH0 hindex (ν := ν) (x := h)
                (by
                  intro hx
                  exact hh (Subgroup.mem_subgroupOf.mpr hx))
      _ = LinearMap.trace ℂ (V × V) (σ h) := (htr_swap h hh).symm
      _ = LinearMap.trace ℂ (Fin (2 * n) → ℂ) (σ' h) := by
              change LinearMap.trace ℂ (V × V) (σ h) = LinearMap.trace ℂ (Fin (2 * n) → ℂ) (e.conj (σ h))
              exact (LinearMap.trace_conj' (σ h) e).symm
      _ = σ'.character h := rfl
/-- Remark 1.4: index-two induction: `ν^H = ν + ν^s` on `H0`; if `ν^s ≠ ν`
then `ν^H` is irreducible. -/
public theorem remark_1_4 {G : Type u} [Group G] [Fintype G] {H0 H : Subgroup G}
    (hH0 : H0 ≤ H) (hindex : (H0.subgroupOf H).index = 2) {s : G}
    (hs : s ∈ H) (hs_not : s ∉ H0) {ν : ClassFunction (↥H0)}
    (hν : IsIrreducibleCharacter ν) :
    (∀ h : G, (hh : h ∈ H0) → (hsh : s * h * s⁻¹ ∈ H0) →
      (inducedFromSub hH0 ν) ⟨h, hH0 hh⟩ =
        ν ⟨h, hh⟩ + ν ⟨s * h * s⁻¹, hsh⟩) ∧
    ((¬ ∀ h : G, (hh : h ∈ H0) → (hsh : s * h * s⁻¹ ∈ H0) →
        ν ⟨s * h * s⁻¹, hsh⟩ = ν ⟨h, hh⟩) →
      IsIrreducibleCharacter (inducedFromSub hH0 ν)) := by
  constructor
  · intro h hh hsh
    exact inducedFromSub_eq_add_conj_index_two H0 H hH0 hindex hs hs_not ν
      (irreducibleCharacter_isClassFunction hν) hh hsh
  · intro hνs_ne
    have hsH0 : ∀ x : ↥H0, s * (x : G) * s⁻¹ ∈ H0 := by
      intro x
      simpa using conj_mem_of_index_two H0 H hH0 hindex (a := ⟨s⁻¹, H.inv_mem hs⟩) x
    have hνs_ne' : conjChar H0 hsH0 ν ≠ ν := by
      intro hEq
      apply hνs_ne
      intro h hh hsh
      have hc := congrFun hEq ⟨h, hh⟩
      have hcv : conjChar H0 hsH0 ν ⟨h, hh⟩ = ν ⟨s * h * s⁻¹, hsh⟩ := rfl
      exact hcv.trans hc
    refine isIrreducibleCharacter_of_norm_one_inv ?hchar ?hnorm
    · exact isCharacter_ind_index_two H0 H hH0 hindex hs hs_not hν hsH0
    · exact scalarProductInv_ind_index_two H0 H hH0 hindex hs hs_not hν hsH0 hνs_ne'
/-- Remark 1.5: generalized characters with `|δ| = |ε| = 2`, equal degrees
and zero inner product are disjoint. -/
public theorem remark_1_5 {G : Type u} [Group G] [Fintype G] {δ ε : ClassFunction G}
    (hδ : IsGeneralizedCharacter δ) (hε : IsGeneralizedCharacter ε)
    (hδ2 : normSq G δ = 2) (hε2 : normSq G ε = 2)
    (hdeg : δ 1 = ε 1) (horth : scalarProduct G δ ε = 0) :
    Theory.Character.Disjoint δ ε := by
  classical
  unfold Theory.Character.Disjoint
  intro χ hχ hχδ
  by_contra hχε
  rcases char_decomp_generalized hδ with ⟨ι₁, _, χs₁, ms₁, hirr₁, hdist₁, hδsum⟩
  rcases char_decomp_generalized hε with ⟨ι₂, _, χs₂, ms₂, hirr₂, hdist₂, hεsum⟩
  have hsq₁ : (∑ i, ((ms₁ i : ℤ) : ℂ)^2) = ((2 : ℕ) : ℂ) := by
    rw [← decomp_scalarProduct hirr₁ hdist₁]
    rw [← hδsum]
    simpa [normSq] using hδ2
  have hsq₂ : (∑ i, ((ms₂ i : ℤ) : ℂ)^2) = ((2 : ℕ) : ℂ) := by
    rw [← decomp_scalarProduct hirr₂ hdist₂]
    rw [← hεsum]
    simpa [normSq] using hε2
  have hmem₁ : ∀ i, ms₁ i = 0 ∨ ms₁ i = 1 ∨ ms₁ i = -1 :=
    int_sq_sum_mem (k := 2) (by norm_num) hsq₁
  have hmem₂ : ∀ i, ms₂ i = 0 ∨ ms₂ i = 1 ∨ ms₂ i = -1 :=
    int_sq_sum_mem (k := 2) (by norm_num) hsq₂
  rcases decomp_scalarProduct_irreducible hirr₁ hdist₁ hχ
      (by simpa [hδsum] using hχδ) with ⟨i₁, hχi₁, hχδ'⟩
  rcases decomp_scalarProduct_irreducible hirr₂ hdist₂ hχ
      (by simpa [hεsum] using hχε) with ⟨i₂, hχi₂, hχε'⟩
  let a : ℤ := ms₁ i₁
  let b : ℤ := ms₂ i₂
  have ha : (a : ℂ) = scalarProduct G χ δ := by
    simpa [a, ← hδsum] using hχδ'.symm
  have hb : (b : ℂ) = scalarProduct G χ ε := by
    simpa [b, ← hεsum] using hχε'.symm
  have ha_c_ne : (a : ℂ) ≠ 0 := by simpa [ha] using hχδ
  have hb_c_ne : (b : ℂ) ≠ 0 := by simpa [hb] using hχε
  have ha_mem : a = 1 ∨ a = -1 := by
    rcases hmem₁ i₁ with h | h | h
    · exfalso
      exact ha_c_ne (by simp [a, h])
    · exact Or.inl h
    · exact Or.inr h
  have hb_mem : b = 1 ∨ b = -1 := by
    rcases hmem₂ i₂ with h | h | h
    · exfalso
      exact hb_c_ne (by simp [b, h])
    · exact Or.inl h
    · exact Or.inr h
  have ha_sq : (a : ℂ)^2 = 1 := by
    rcases ha_mem with h | h <;> simp [h]
  have hb_sq : (b : ℂ)^2 = 1 := by
    rcases hb_mem with h | h <;> simp [h]
  have hδδ : scalarProduct G δ δ = (2 : ℂ) := by simpa [normSq] using hδ2
  have hεε : scalarProduct G ε ε = (2 : ℂ) := by simpa [normSq] using hε2
  have hχχ : scalarProduct G χ χ = 1 := irreducible_scalarProduct_self hχ
  have hδχ : scalarProduct G δ χ = (a : ℂ) := by
    calc
      scalarProduct G δ χ = star (scalarProduct G χ δ) := by
        rw [← scalarProduct_conj χ δ]
      _ = (a : ℂ) := by
        rw [← ha]
        norm_num
  have hχδ : scalarProduct G χ δ = (a : ℂ) := ha.symm
  have hχε : scalarProduct G χ ε = (b : ℂ) := hb.symm
  have hεχ : scalarProduct G ε χ = (b : ℂ) := by
    rw [← scalarProduct_conj χ ε, hχε]
    norm_num
  have hsub (r s : ℤ) (φ ψ : ClassFunction G) :
      scalarProduct G (φ - (r : ℂ) • χ) (ψ - (s : ℂ) • χ) =
        scalarProduct G φ ψ - scalarProduct G φ χ * (s : ℂ) -
          (r : ℂ) * scalarProduct G χ ψ +
            (r : ℂ) * scalarProduct G χ χ * (s : ℂ) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    convert scalarProduct_expand_four (G := G) 1 (-(r : ℂ)) 1 (-(s : ℂ)) φ χ ψ χ using 1 <;>
      simp <;> ring
  let δ₁ : ClassFunction G := δ - (a : ℂ) • χ
  let ε₁ : ClassFunction G := ε - (b : ℂ) • χ
  have hδ₁gen : IsGeneralizedCharacter δ₁ := by
    rcases ha_mem with h | h
    · simpa [δ₁, a, h] using
        isGeneralizedCharacter_sub_char hδ (isCharacter_of_isIrreducibleCharacter hχ)
    · simpa [δ₁, a, h] using
        isGeneralizedCharacter_add_char hδ (isCharacter_of_isIrreducibleCharacter hχ)
  have hε₁gen : IsGeneralizedCharacter ε₁ := by
    rcases hb_mem with h | h
    · simpa [ε₁, b, h] using
        isGeneralizedCharacter_sub_char hε (isCharacter_of_isIrreducibleCharacter hχ)
    · simpa [ε₁, b, h] using
        isGeneralizedCharacter_add_char hε (isCharacter_of_isIrreducibleCharacter hχ)
  have hδ₁₁ : scalarProduct G δ₁ δ₁ = 1 := by
    rw [hsub, hδδ, hδχ, hχδ, hχχ]
    ring_nf
    rw [ha_sq]
    norm_num
  have hε₁₁ : scalarProduct G ε₁ ε₁ = 1 := by
    rw [hsub, hεε, hεχ, hχε, hχχ]
    ring_nf
    rw [hb_sq]
    norm_num
  have hδ₁ε₁ : scalarProduct G δ₁ ε₁ = -((a : ℂ) * (b : ℂ)) := by
    rw [hsub, horth, hδχ, hχε, hχχ]
    ring
  have hδ₁ε₁_ne : scalarProduct G δ₁ ε₁ ≠ 0 := by
    rw [hδ₁ε₁]
    exact neg_ne_zero.mpr (mul_ne_zero ha_c_ne hb_c_ne)
  rcases norm_one_signed_irreducible hδ₁gen hδ₁₁ with ⟨ξ, hξ, hξcase⟩
  rcases norm_one_signed_irreducible hε₁gen hε₁₁ with ⟨η, hη, hηcase⟩
  have hξη_ne : scalarProduct G ξ η ≠ 0 := by
    intro hz
    rcases hξcase with hξ' | hξ' <;> rcases hηcase with hη' | hη'
    all_goals rw [hξ', hη'] at hδ₁ε₁_ne
    all_goals simp [scalarProduct_neg_left, scalarProduct_neg_right, hz] at hδ₁ε₁_ne
  have hξη_eq : ξ = η := by
    by_contra hne
    exact hξη_ne (irreducible_scalarProduct_of_ne hξ hη hne)
  have hηcase' : ε₁ = ξ ∨ ε₁ = -ξ := by
    rw [← hξη_eq] at hηcase
    exact hηcase
  have signed (ψ : ClassFunction G) (hcase : ψ = ξ ∨ ψ = -ξ) :
      ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ψ = (c : ℂ) • ξ := by
    rcases hcase with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  rcases signed δ₁ hξcase with ⟨c, hc, hδc⟩
  rcases signed ε₁ hηcase' with ⟨d, hd, hεd⟩
  have habcd : (a : ℂ) * (b : ℂ) + (c : ℂ) * (d : ℂ) = 0 := by
    rw [hδc, hεd] at hδ₁ε₁
    simp [scalarProduct_smul_left, scalarProduct_smul_right,
      irreducible_scalarProduct_self hξ] at hδ₁ε₁
    linear_combination hδ₁ε₁
  have hdegree : (c : ℂ) * ξ 1 + (a : ℂ) * χ 1 =
      (d : ℂ) * ξ 1 + (b : ℂ) * χ 1 := by
    calc
      (c : ℂ) * ξ 1 + (a : ℂ) * χ 1 = δ 1 := by
        have hδ_recover : δ = δ₁ + (a : ℂ) • χ := by
          ext x
          simp [δ₁]
        rw [hδ_recover, hδc]
        simp
      _ = ε 1 := hdeg
      _ = (d : ℂ) * ξ 1 + (b : ℂ) * χ 1 := by
        have hε_recover : ε = ε₁ + (b : ℂ) • χ := by
          ext x
          simp [ε₁]
        rw [hε_recover, hεd]
        simp
  have ha_cases : (a : ℂ) = 1 ∨ (a : ℂ) = -1 := by
    rcases ha_mem with h | h <;> simp [h]
  have hb_cases : (b : ℂ) = 1 ∨ (b : ℂ) = -1 := by
    rcases hb_mem with h | h <;> simp [h]
  have hc_cases : (c : ℂ) = 1 ∨ (c : ℂ) = -1 := by
    rcases hc with h | h <;> simp [h]
  have hd_cases : (d : ℂ) = 1 ∨ (d : ℂ) = -1 := by
    rcases hd with h | h <;> simp [h]
  have sign_contradiction {a b c d x y : ℂ}
      (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
      (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
      (hprod : a * b + c * d = 0)
      (hdegree : c * x + a * y = d * x + b * y)
      (hx : x ≠ 0) (hy : y ≠ 0) : False := by
    have hzero {z : ℂ} (hz : z = -z) : z = 0 := by
      have h2 : (2 : ℂ) * z = 0 := by
        calc
          (2 : ℂ) * z = z + z := by rw [two_mul]
          _ = z + (-z) := by nth_rw 2 [hz]
          _ = 0 := add_neg_cancel z
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    all_goals (try norm_num at hprod)
    all_goals norm_num at hdegree
    all_goals first
      | exact hx (hzero hdegree)
      | exact hx (hzero hdegree.symm)
      | exact hy (hzero hdegree)
      | exact hy (hzero hdegree.symm)
  exact sign_contradiction ha_cases hb_cases hc_cases hd_cases habcd hdegree
    (irreducible_char_one_ne_zero hξ) (irreducible_char_one_ne_zero hχ)


/-- Lemma 1.6 for characters: for an involution `t` and `u ∈ C_G(t)`,
`χ(tu) ≡ χ(u)` (mod 2).

The proof runs the trace computation with the projections
`P₁ = (1 + ρt)/2`, `Pm = (1 - ρt)/2` on the representation space:
`χ(tu) - χ(u) = trace(ρt·ρu) - trace(ρu) = -2·trace(ρu·Pm)`, and
every eigenvalue of `ρu·Pm` is either `0` or an eigenvalue of `ρu`
(hence a root of unity), so the trace is an algebraic integer. -/
public theorem character_congr_mod_two_of_involution {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsCharacter χ) {t u : G}
    (ht : IsInvolution t) (hu : t * u = u * t) :
    CongruentModTwo (χ (t * u)) (χ u) := by
  classical
  unfold IsCharacter at hχ
  rcases hχ with ⟨n, ρ, hχeq⟩
  let V : Type := Fin n → ℂ
  let ρt : V →ₗ[ℂ] V := ρ t
  let ρu : V →ₗ[ℂ] V := ρ u
  have ht2 : t * t = 1 := by simpa [pow_two] using ht.2
  have hρt2 : ρt * ρt = 1 := by
    change (ρ t) * (ρ t) = 1
    rw [← map_mul, ht2, map_one]
  have hρcomm : ρt * ρu = ρu * ρt := by
    change (ρ t) * (ρ u) = (ρ u) * (ρ t)
    rw [← map_mul, ← map_mul]
    rw [hu]
  let P₁ : V →ₗ[ℂ] V := (2 : ℂ)⁻¹ • (1 + ρt)
  let Pm : V →ₗ[ℂ] V := (2 : ℂ)⁻¹ • (1 - ρt)
  have hPsum : P₁ + Pm = 1 := by
    calc
      P₁ + Pm = (2 : ℂ)⁻¹ • (1 + ρt) + (2 : ℂ)⁻¹ • (1 - ρt) := rfl
      _ = (2 : ℂ)⁻¹ • ((1 + ρt) + (1 - ρt)) := by rw [← smul_add]
      _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • (1 : V →ₗ[ℂ] V)) := by
        congr 1
        rw [two_smul]
        abel
      _ = 1 := by
        rw [smul_smul]
        norm_num
  have hρtP₁ : ρt * P₁ = P₁ := by
    calc
      ρt * P₁ = ρt * ((2 : ℂ)⁻¹ • (1 + ρt)) := rfl
      _ = (2 : ℂ)⁻¹ • (ρt * (1 + ρt)) := by rw [mul_smul_comm]
      _ = (2 : ℂ)⁻¹ • (ρt * 1 + ρt * ρt) := by rw [mul_add]
      _ = (2 : ℂ)⁻¹ • (ρt + 1) := by rw [mul_one, hρt2]
      _ = (2 : ℂ)⁻¹ • (1 + ρt) := by rw [add_comm]
  have hρtPm : ρt * Pm = -Pm := by
    calc
      ρt * Pm = ρt * ((2 : ℂ)⁻¹ • (1 - ρt)) := rfl
      _ = (2 : ℂ)⁻¹ • (ρt * (1 - ρt)) := by rw [mul_smul_comm]
      _ = (2 : ℂ)⁻¹ • (ρt * 1 - ρt * ρt) := by rw [mul_sub]
      _ = (2 : ℂ)⁻¹ • (ρt - 1) := by rw [mul_one, hρt2]
      _ = -((2 : ℂ)⁻¹ • (1 - ρt)) := by
        rw [← neg_sub]
        rw [smul_neg]
  have hQ2 : (1 - ρt) * (1 - ρt) = (2 : ℂ) • (1 - ρt) := by
    calc
      (1 - ρt) * (1 - ρt) = 1 * (1 - ρt) - ρt * (1 - ρt) := by rw [sub_mul]
      _ = (1 - ρt) - (ρt * 1 - ρt * ρt) := by rw [one_mul, mul_sub]
      _ = (1 - ρt) - (ρt - 1) := by rw [mul_one, hρt2]
      _ = (1 - ρt) + (1 - ρt) := by abel
      _ = (2 : ℂ) • (1 - ρt) := by rw [two_smul]
  have hPmidem : Pm * Pm = Pm := by
    calc
      Pm * Pm = ((2 : ℂ)⁻¹ • (1 - ρt)) * ((2 : ℂ)⁻¹ • (1 - ρt)) := rfl
      _ = (2 : ℂ)⁻¹ • ((1 - ρt) * ((2 : ℂ)⁻¹ • (1 - ρt))) := by rw [smul_mul_assoc]
      _ = (2 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ((1 - ρt) * (1 - ρt))) := by rw [mul_smul_comm]
      _ = (2 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ((2 : ℂ) • (1 - ρt))) := by rw [hQ2]
      _ = (2 : ℂ)⁻¹ • (1 - ρt) := by
        rw [smul_smul, smul_smul]
        norm_num
  have hPmcomm : ρu * Pm = Pm * ρu := by
    calc
      ρu * Pm = ρu * ((2 : ℂ)⁻¹ • (1 - ρt)) := rfl
      _ = (2 : ℂ)⁻¹ • (ρu * (1 - ρt)) := by rw [mul_smul_comm]
      _ = (2 : ℂ)⁻¹ • (ρu * 1 - ρu * ρt) := by rw [mul_sub]
      _ = (2 : ℂ)⁻¹ • (ρu - ρu * ρt) := by rw [mul_one]
      _ = (2 : ℂ)⁻¹ • (ρu - ρt * ρu) := by rw [hρcomm]
      _ = (2 : ℂ)⁻¹ • ((1 - ρt) * ρu) := by
        rw [sub_mul, one_mul]
      _ = ((2 : ℂ)⁻¹ • (1 - ρt)) * ρu := by rw [← smul_mul_assoc]
  have htr2 : (LinearMap.trace ℂ V) ρu =
      (LinearMap.trace ℂ V) (ρu * P₁) + (LinearMap.trace ℂ V) (ρu * Pm) := by
    calc
      (LinearMap.trace ℂ V) ρu = (LinearMap.trace ℂ V) (ρu * (P₁ + Pm)) := by
        rw [hPsum]
        simp
      _ = (LinearMap.trace ℂ V) (ρu * P₁ + ρu * Pm) := by rw [mul_add]
      _ = (LinearMap.trace ℂ V) (ρu * P₁) + (LinearMap.trace ℂ V) (ρu * Pm) := by
        exact (LinearMap.trace ℂ V).map_add _ _
  have htr1 : (LinearMap.trace ℂ V) (ρt * ρu) =
      (LinearMap.trace ℂ V) (ρu * P₁) - (LinearMap.trace ℂ V) (ρu * Pm) := by
    calc
      (LinearMap.trace ℂ V) (ρt * ρu) = (LinearMap.trace ℂ V) ((ρt * ρu) * (P₁ + Pm)) := by
        rw [hPsum]
        simp
      _ = (LinearMap.trace ℂ V) ((ρt * ρu) * P₁ + (ρt * ρu) * Pm) := by rw [mul_add]
      _ = (LinearMap.trace ℂ V) ((ρt * ρu) * P₁) + (LinearMap.trace ℂ V) ((ρt * ρu) * Pm) := by
        exact (LinearMap.trace ℂ V).map_add _ _
      _ = (LinearMap.trace ℂ V) ((ρu * ρt) * P₁) + (LinearMap.trace ℂ V) ((ρu * ρt) * Pm) := by
        rw [hρcomm]
      _ = (LinearMap.trace ℂ V) (ρu * (ρt * P₁)) + (LinearMap.trace ℂ V) (ρu * (ρt * Pm)) := by
        rw [mul_assoc, mul_assoc]
      _ = (LinearMap.trace ℂ V) (ρu * P₁) + (LinearMap.trace ℂ V) (ρu * (-Pm)) := by
        rw [hρtP₁, hρtPm]
      _ = (LinearMap.trace ℂ V) (ρu * P₁) - (LinearMap.trace ℂ V) (ρu * Pm) := by
        have hmulneg : ρu * -Pm = -(ρu * Pm) := mul_neg ρu Pm
        rw [sub_eq_add_neg, hmulneg, ← (LinearMap.trace ℂ V).map_neg (ρu * Pm)]
  have hdiff : χ (t * u) - χ u = -2 * (LinearMap.trace ℂ V) (ρu * Pm) := by
    rw [hχeq]
    change (LinearMap.trace ℂ V) (ρ (t * u)) - (LinearMap.trace ℂ V) (ρ u) =
      -2 * (LinearMap.trace ℂ V) (ρu * Pm)
    calc
      (LinearMap.trace ℂ V) (ρ (t * u)) - (LinearMap.trace ℂ V) (ρ u)
          = (LinearMap.trace ℂ V) (ρt * ρu) - (LinearMap.trace ℂ V) ρu := by rw [map_mul]
      _ = ((LinearMap.trace ℂ V) (ρu * P₁) - (LinearMap.trace ℂ V) (ρu * Pm))
            - ((LinearMap.trace ℂ V) (ρu * P₁) + (LinearMap.trace ℂ V) (ρu * Pm)) := by
            rw [htr1, htr2]
      _ = -2 * (LinearMap.trace ℂ V) (ρu * Pm) := by ring
  have hρu_pow : ρu ^ orderOf u = 1 := by
    change (ρ u) ^ orderOf u = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hint : IsIntegral ℤ ((LinearMap.trace ℂ V) (ρu * Pm)) := by
    refine trace_isIntegral_of_forall_eigenvalue (ρu * Pm) ?_
    intro z hz
    rcases hasEigenvalue_of_mul_hasEigenvalue hPmcomm hPmidem hz with hz0 | hzev
    · rw [hz0]
      exact isIntegral_zero
    · exact eigen_value_isIntegral_of_pow_eq_one (orderOf_pos u) hρu_pow hzev
  change ∃ w : ℂ, IsIntegral ℤ w ∧ χ (t * u) - χ u = 2 * w
  refine ⟨-((LinearMap.trace ℂ V) (ρu * Pm)), hint.neg, ?_⟩
  rw [hdiff]
  ring

/-- Lemma 1.6: for a generalized character `φ`, an involution `t` and a
`2'`-element `u ∈ C_G(t)`, `φ(tu) ≡ φ(u)` (mod 2). -/
public theorem lemma_1_6 {G : Type u} [Group G] [Fintype G] (φ : ClassFunction G)
    (hφ : IsGeneralizedCharacter φ) {t u : G}
    (ht : IsInvolution t) (hu : u ∈ centralizerIn (⊤ : Subgroup G) t)
    (_hu2' : Nat.Coprime 2 (orderOf u)) :
    CongruentModTwo (φ (t * u)) (φ u) := by
  classical
  unfold IsGeneralizedCharacter at hφ
  rcases hφ with ⟨χ, ψ, hχ, hψ, hφeq⟩
  have htcomm : t * u = u * t := by
    have huc : u ∈ Subgroup.centralizer ({t} : Set G) := by
      have hu' : u ∈ (⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) := by
        simpa [centralizerIn] using hu
      exact ((Subgroup.mem_inf).1 hu').2
    exact (Subgroup.mem_centralizer_iff.mp huc) t (by simp)
  have hχcong : CongruentModTwo (χ (t * u)) (χ u) :=
    character_congr_mod_two_of_involution hχ ht htcomm
  have hψcong : CongruentModTwo (ψ (t * u)) (ψ u) :=
    character_congr_mod_two_of_involution hψ ht htcomm
  rw [hφeq]
  simpa [Pi.sub_apply] using CongruentModTwo.sub hχcong hψcong

/-- Lemma 1.8: mod-2 linear independence of irreducible characters of a
`2'`-group. -/
public theorem lemma_1_8 {B : Type u} [Group B] [Fintype B] (hB2' : Nat.Coprime 2 (Nat.card B))
    {I : Type u} [Fintype I] {β : I → ClassFunction B} {c : I → ℂ}
    (hβ : ∀ i, IsIrreducibleCharacter (β i))
    (hβdist : Pairwise fun i j => β i ≠ β j)
    (hc : ∀ i, IsIntegral ℤ (c i))
    (h0 : ∀ b : B, CongruentModTwo (∑ i, c i * β i b) 0) :
    ∀ i, CongruentModTwo (c i) 0 := by
  classical
  intro j
  unfold IsIrreducibleCharacter at hβ
  rcases hβ j with ⟨nj, ρj, hρj, hβj⟩
  let βsum : ClassFunction B := fun b => ∑ i, c i * β i b
  have h2ndvd : ¬ 2 ∣ Nat.card B := by
    intro h2
    have hg : (2 : ℕ).gcd (Nat.card B) = 1 := hB2'.gcd_eq_one
    have h2g : 2 ∣ (2 : ℕ).gcd (Nat.card B) := Nat.dvd_gcd (dvd_refl 2) h2
    rw [hg] at h2g
    norm_num at h2g
  have hodd : Odd (Nat.card B) := by
    rw [Nat.odd_iff]
    have hcases : Nat.card B % 2 = 0 ∨ Nat.card B % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · exfalso
      exact h2ndvd (Nat.dvd_of_mod_eq_zero h0)
    · exact h1
  -- `cⱼ ≡ |B|·cⱼ` because `|B|` is odd
  have hcB : CongruentModTwo (c j) ((Nat.card B : ℂ) * c j) :=
    CongruentModTwo.symm (CongruentModTwo.odd_mul_congr hodd (hc j))
  -- orthonormality
  have horth : ∀ i, characterProduct B (β i) (β j) = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      have hself : characterProduct B (β j) (β j) = 1 :=
        irreducibleCharacter_self (hβ j)
      simp [hself]
    · have horth' : characterProduct B (β i) (β j) = 0 :=
        irreducibleCharacters_orthogonal (hβ i) (hβ j) (hβdist hij)
      simp [horth', hij]
  -- bilinearity
  have hbilin : characterProduct B βsum (β j) =
      ∑ i, c i * characterProduct B (β i) (β j) := by
    calc
      characterProduct B βsum (β j)
          = characterProduct B (∑ i, c i • β i) (β j) := by
            congr 1
            ext b
            simp [βsum]
      _ = ∑ i, c i * characterProduct B (β i) (β j) := by
            refine Finset.induction_on Finset.univ ?_ ?_
            · simp [characterProduct]
            · intro i s hi hs
              rw [Finset.sum_insert hi, characterProduct_add_left,
                characterProduct_smul_left, Finset.sum_insert hi]
              rw [hs]
  have hββj : characterProduct B βsum (β j) = c j := by
    calc
      characterProduct B βsum (β j) = ∑ i, c i * (if i = j then 1 else 0) := by
        rw [hbilin]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [horth i]
      _ = c j := by
        calc
          ∑ i, c i * (if i = j then 1 else 0) = ∑ i, (if i = j then c i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hij : i = j <;> simp [hij]
          _ = c j := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro i hi hij
              simp [hij]
            · intro hj
              simp at hj
  -- `|B|·cⱼ = Σ_b βsum(b)·βⱼ(b⁻¹)`
  have hBβ : (Nat.card B : ℂ) * c j = ∑ b : B, βsum b * (β j) b⁻¹ := by
    calc
      (Nat.card B : ℂ) * c j = (Nat.card B : ℂ) * characterProduct B βsum (β j) := by
        rw [hββj]
      _ = (Nat.card B : ℂ) * ((Nat.card B : ℂ)⁻¹ * ∑ b : B, βsum b * (β j) b⁻¹) := by
        rfl
      _ = ∑ b : B, βsum b * (β j) b⁻¹ := by
        rw [← mul_assoc, mul_inv_cancel₀, one_mul]
        exact Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  -- each term is `≡ 0` since `βsum(b) ≡ 0` and character values are integral
  have hterm : ∀ b : B, CongruentModTwo (βsum b * (β j) b⁻¹) 0 := by
    intro b
    exact CongruentModTwo.mul_zero_left (h0 b)
      (by simpa [hβj] using character_value_isIntegral ρj (b⁻¹))
  have hsum0 : CongruentModTwo (∑ b : B, βsum b * (β j) b⁻¹) 0 := by
    exact CongruentModTwo.sum_zero hterm
  have hB0 : CongruentModTwo ((Nat.card B : ℂ) * c j) 0 := by
    rw [hBβ]
    exact hsum0
  exact CongruentModTwo.trans hcB hB0

end CFSG.BenderGlauberman
