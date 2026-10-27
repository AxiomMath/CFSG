module

public import CFSG.Monster.B.Geometry.Gate

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

theorem subset_of_longest_mem_parabolic {K I : Set ι} {w : W} (hw : IsLongest cs K w)
    (hI : w ∈ cs.parabolic I) : K ⊆ I := fun _ hi =>
  (simple_mem_parabolic_iff cs).mp
    (cs.simple_mem_parabolic_of_isLeftDescent hI (hw.isLeftDescent hi))

theorem mem_foundation_iff {k : ℕ} {x y : C} :
    y ∈ foundation cs δ k x ↔ ∃ J : Set ι, J.encard ≤ k ∧ y ∈ residue cs δ J x := by
  simp [foundation]

theorem mem_residueFoundation_iff {J : Set ι} {x y : C} :
    y ∈ residueFoundation cs δ J x ↔
      ∃ I : Set ι, (I ⊆ J ∧ I.encard ≤ 2) ∧ y ∈ residue cs δ I x := by
  simp [residueFoundation]

theorem residue_subset_foundation {k : ℕ} {J : Set ι} (hJ : J.encard ≤ k) (x : C) :
    residue cs δ J x ⊆ foundation cs δ k x := fun _ hy =>
  mem_foundation_iff.mpr ⟨J, hJ, hy⟩

theorem self_mem_foundation (k : ℕ) (x : C) : x ∈ foundation cs δ k x :=
  residue_subset_foundation (J := ∅) (by simp) x (self_mem_residue _ x)

theorem residueFoundation_subset_foundation (J : Set ι) (x : C) :
    residueFoundation cs δ J x ⊆ foundation cs δ 2 x := by
  intro y hy
  obtain ⟨I, ⟨-, hI⟩, hy⟩ := mem_residueFoundation_iff.mp hy
  exact mem_foundation_iff.mpr ⟨I, by exact_mod_cast hI, hy⟩

theorem residueFoundation_subset_residue (J : Set ι) (x : C) :
    residueFoundation cs δ J x ⊆ residue cs δ J x := by
  intro y hy
  obtain ⟨I, ⟨hIJ, -⟩, hy⟩ := mem_residueFoundation_iff.mp hy
  exact residue_mono hIJ x hy

theorem IsWeylIsometry.mem_residue (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {X : Set C} {X' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) {x y : C} (hx : x ∈ X) (hy : y ∈ X) {J : Set ι}
    (hyJ : y ∈ residue cs δ J x) : φ y ∈ residue cs δ' J (φ x) := by
  rw [mem_residue_iff_mem_parabolic hδ'] at *
  rw [hφ.2 x hx y hy]
  exact (mem_residue_iff_mem_parabolic hδ).mp hyJ

theorem IsWeylIsometry.mem_residue_iff (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {X : Set C} {X' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) {x y : C} (hx : x ∈ X) (hy : y ∈ X) {J : Set ι} :
    φ y ∈ residue cs δ' J (φ x) ↔ y ∈ residue cs δ J x := by
  rw [mem_residue_iff_mem_parabolic hδ', mem_residue_iff_mem_parabolic hδ, hφ.2 x hx y hy]

theorem IsWeylIsometry.injOn (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {X : Set C} {X' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) : Set.InjOn φ X := fun y hy z hz h => by
  have := hφ.2 y hy z hz
  rw [h, hδ'.eq_one_self, eq_comm, hδ.eq_one_iff] at this
  exact this

theorem isWeylIsometry_of (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {X : Set C} {X' : Set C'} {φ : C → C'}
    (hmaps : Set.MapsTo φ X X') (hsurj : Set.SurjOn φ X X')
    (hd : ∀ y ∈ X, ∀ z ∈ X, δ' (φ y) (φ z) = δ y z) : IsWeylIsometry δ δ' X X' φ := by
  refine ⟨⟨hmaps, fun y hy z hz h => ?_, hsurj⟩, hd⟩
  have := hd y hy z hz
  rw [h, hδ'.eq_one_self, eq_comm, hδ.eq_one_iff] at this
  exact this

theorem IsWeylIsometry.isTypeIso {X : Set C} {X' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) : IsTypeIso cs δ δ' X X' φ :=
  ⟨hφ.1, fun y hy z hz i => by rw [hφ.2 y hy z hz]⟩

section Four

variable (hS : Nat.card ι = 4)
include hS

theorem finite_of_card_eq_four : Finite ι :=
  Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)

theorem encard_univ_of_card_eq_four : (Set.univ : Set ι).encard = 4 := by
  have := finite_of_card_eq_four hS
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, hS]
  rfl

theorem exists_ncard_three_superset {J : Set ι} (hJ : J.encard ≤ 3) :
    ∃ K : Set ι, J ⊆ K ∧ K.ncard = 3 := by
  have := finite_of_card_eq_four hS
  obtain ⟨K, hJK, -, hK⟩ := Set.exists_superset_subset_encard_eq (Set.subset_univ J) hJ
    (by rw [encard_univ_of_card_eq_four hS]; norm_num)
  refine ⟨K, hJK, ?_⟩
  rw [← Set.Finite.cast_ncard_eq (Set.toFinite K)] at hK
  exact_mod_cast hK

theorem encard_inter_le_two {J K : Set ι} (hJ : J.ncard = 3) (hK : K.ncard = 3)
    (hJK : J ≠ K) : (J ∩ K).encard ≤ 2 := by
  have := finite_of_card_eq_four hS
  have hss : J ∩ K ⊂ J := by
    refine ⟨Set.inter_subset_left, fun h => hJK ?_⟩
    have hJK' : J ⊆ K := fun i hi => (h hi).2
    exact Set.eq_of_subset_of_ncard_le hJK' (by rw [hJ, hK]) (Set.toFinite K)
  have hlt := Set.ncard_lt_ncard hss (Set.toFinite J)
  rw [← Set.Finite.cast_ncard_eq (Set.toFinite _)]
  have : (J ∩ K).ncard ≤ 2 := by omega
  exact_mod_cast this

end Four

section Setting

variable [Finite W]

theorem not_mem_foundation_two (hδ : IsWeylDistanceBuilding cs δ) (hS : Nat.card ι = 4) {x d : C}
    (hxd : δ x d = longest cs Set.univ) : d ∉ foundation cs δ 2 x := by
  intro h
  obtain ⟨I, hI, hdI⟩ := mem_foundation_iff.mp h
  have hmem := (mem_residue_iff_mem_parabolic hδ).mp hdI
  rw [hxd] at hmem
  have hsub := subset_of_longest_mem_parabolic isLongest_univ hmem
  have := Set.encard_le_encard hsub
  rw [encard_univ_of_card_eq_four hS] at this
  have h2 : (I.encard : ℕ∞) ≤ 2 := by exact_mod_cast hI
  have := this.trans h2
  norm_num at this

theorem oppChamber_longest_not_mem_residueFoundation (hδ : IsWeylDistanceBuilding cs δ) {x d : C}
    (hxd : δ x d = longest cs Set.univ) {J : Set ι} (hJ : J.ncard = 3) :
    oppChamber cs δ x d (longest cs J) ∉ residueFoundation cs δ J x := by
  intro h
  obtain ⟨I, ⟨hIJ, hI⟩, hpI⟩ := mem_residueFoundation_iff.mp h
  have hmem := (mem_residue_iff_mem_parabolic hδ).mp hpI
  rw [(oppChamber_spec hδ hxd _).1] at hmem
  have hsub := subset_of_longest_mem_parabolic (isLongest_of_finite J) hmem
  have hJI : J = I := le_antisymm hsub hIJ
  subst hJI
  have hJf : J.Finite := Set.finite_of_ncard_ne_zero (by rw [hJ]; norm_num)
  rw [← hJf.cast_ncard_eq, hJ] at hI
  norm_num at hI

end Setting

end CFSG.Monster.B.Geometry

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

omit [Group W] in
theorem IsWeylIsometry.mono {X Y : Set C} {X' Y' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) (hYX : Y ⊆ X) (hY : Set.BijOn φ Y Y') :
    IsWeylIsometry δ δ' Y Y' φ :=
  ⟨hY, fun y hy z hz => hφ.2 y (hYX hy) z (hYX hz)⟩

theorem IsWeylIsometry.bijOn_residue (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {X : Set C} {X' : Set C'} {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' X X' φ) {x : C} {x' : C'} (hx : x ∈ X) (hφx : φ x = x')
    {J : Set ι} (hRX : residue cs δ J x ⊆ X) (hRX' : residue cs δ' J x' ⊆ X') :
    Set.BijOn φ (residue cs δ J x) (residue cs δ' J x') := by
  refine ⟨fun y hy => ?_, hφ.1.injOn.mono hRX, fun y' hy' => ?_⟩
  · rw [← hφx]
    exact hφ.mem_residue hδ hδ' hx (hRX hy) hy
  · obtain ⟨y, hy, rfl⟩ := hφ.1.surjOn (hRX' hy')
    rw [← hφx, hφ.mem_residue_iff hδ hδ' hx hy] at hy'
    exact ⟨y, hy', rfl⟩

theorem exists_isProjection_oppChamber [Finite W] (hδ : IsWeylDistanceBuilding cs δ) {x d : C}
    (hxd : δ x d = longest cs Set.univ) (J : Set ι) (t : W) :
    ∃ v ∈ cs.parabolic J,
      IsProjection cs δ (residue cs δ J x) (oppChamber cs δ x d t) (oppChamber cs δ x d v) := by
  obtain ⟨q, hq⟩ := exists_isProjection hδ J x (oppChamber cs δ x d t)
  obtain ⟨hmul, -⟩ := hq.gate hδ (self_mem_residue J x)
  have hqx : δ q x ∈ cs.parabolic J :=
    mem_parabolic_of_mem_residue hδ hq.1 (self_mem_residue J x)
  set v := (δ q x)⁻¹
  have hv : v ∈ cs.parabolic J := inv_mem hqx
  have hap := isApartmentMap_oppChamber hδ hxd
  have hmem : oppChamber cs δ x d v ∈ residue cs δ J x := by
    rw [mem_residue_iff_mem_parabolic hδ, (oppChamber_spec hδ hxd v).1]
    exact hv
  have heq : δ (oppChamber cs δ x d t) (oppChamber cs δ x d v) =
      δ (oppChamber cs δ x d t) q := by
    have h1 : δ (oppChamber cs δ x d t) x = t⁻¹ := by
      rw [dist_inv hδ, (oppChamber_spec hδ hxd t).1]
    have h2 : δ (oppChamber cs δ x d t) q = t⁻¹ * (δ q x)⁻¹ := by
      rw [← h1, hmul, mul_inv_cancel_right]
    rw [hap, h2]
  refine ⟨v, hv, ?_⟩
  by_cases hqv : oppChamber cs δ x d v = q
  · rw [hqv]
    exact hq
  · exfalso
    have := hq.2 _ hmem hqv
    rw [heq] at this
    exact lt_irrefl _ this

section Main

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  (hS : Nat.card ι = 4) {x d : C} {x' d' : C'} (hxd : δ x d = longest cs Set.univ)
  (hxd' : δ' x' d' = longest cs Set.univ) {φ : C → C'}
  (hφ : IsWeylIsometry δ δ' (foundation cs δ 2 x ∪ {d}) (foundation cs δ' 2 x' ∪ {d'}) φ)
  (hφx : φ x = x') (hφd : φ d = d')
include hδ hδ' hS hxd hxd' hφ hφx hφd

theorem bijOn_residueFoundation (J : Set ι) :
    Set.BijOn φ (residueFoundation cs δ J x) (residueFoundation cs δ' J x') := by
  have hx : x ∈ foundation cs δ 2 x ∪ {d} := Or.inl (self_mem_foundation 2 x)
  refine ⟨fun y hy => ?_, hφ.1.injOn.mono fun y hy =>
    Or.inl (residueFoundation_subset_foundation J x hy), fun y' hy' => ?_⟩
  · obtain ⟨I, hI, hyI⟩ := mem_residueFoundation_iff.mp hy
    have hyX : y ∈ foundation cs δ 2 x ∪ {d} :=
      Or.inl (residueFoundation_subset_foundation J x hy)
    have := hφ.mem_residue hδ hδ' hx hyX hyI
    rw [hφx] at this
    exact mem_residueFoundation_iff.mpr ⟨I, hI, this⟩
  · obtain ⟨I, hI, hyI⟩ := mem_residueFoundation_iff.mp hy'
    have hy'X : y' ∈ foundation cs δ' 2 x' ∪ {d'} :=
      Or.inl (residueFoundation_subset_foundation J x' hy')
    obtain ⟨y, hy, rfl⟩ := hφ.1.surjOn hy'X
    have hyd : y ≠ d := by
      rintro rfl
      rw [hφd] at hy'
      exact not_mem_foundation_two hδ' hS hxd' (residueFoundation_subset_foundation J x' hy')
    have hy2 : y ∈ foundation cs δ 2 x := hy.resolve_right hyd
    rw [← hφx, hφ.mem_residue_iff hδ hδ' hx hy] at hyI
    exact ⟨y, mem_residueFoundation_iff.mpr ⟨I, hI, hyI⟩, rfl⟩

theorem isWeylIsometry_localMap {J : Set ι} {f : C → C'}
    (hfF : ∀ y ∈ residueFoundation cs δ J x, f y = φ y)
    (hfp : f (oppChamber cs δ x d (longest cs J)) = oppChamber cs δ' x' d' (longest cs J)) :
    IsWeylIsometry δ δ'
      (residueFoundation cs δ J x ∪ {oppChamber cs δ x d (longest cs J)})
      (residueFoundation cs δ' J x' ∪ {oppChamber cs δ' x' d' (longest cs J)}) f := by
  set p := oppChamber cs δ x d (longest cs J) with hp
  set p' := oppChamber cs δ' x' d' (longest cs J) with hp'
  have hbij := bijOn_residueFoundation hδ hδ' hS hxd hxd' hφ hφx hφd J
  have hproj := isProjection_oppChamber_longest hδ hxd J
  have hproj' := isProjection_oppChamber_longest hδ' hxd' J
  have key : ∀ y ∈ residueFoundation cs δ J x, δ' p' (φ y) = δ p y := by
    intro y hy
    have hyR := residueFoundation_subset_residue J x hy
    have hyR' := residueFoundation_subset_residue J x' (hbij.mapsTo hy)
    obtain ⟨h1, -⟩ := hproj.gate hδ hyR
    obtain ⟨h2, -⟩ := hproj'.gate hδ' hyR'
    have h3 : δ' d' (φ y) = δ d y := by
      rw [← hφd]
      exact hφ.2 d (Or.inr rfl) y (Or.inl (residueFoundation_subset_foundation J x hy))
    have h4 : δ d p = δ' d' p' := by
      rw [dist_inv hδ, dist_inv hδ', (oppChamber_spec hδ hxd _).2,
        (oppChamber_spec hδ' hxd' _).2]
    rw [h3, h1, h4] at h2
    exact (mul_left_cancel h2).symm
  refine isWeylIsometry_of hδ hδ' ?_ ?_ ?_
  · rintro y (hy | hy)
    · rw [hfF y hy]
      exact Or.inl (hbij.mapsTo hy)
    · rw [Set.mem_singleton_iff.mp hy, hfp]
      exact Or.inr rfl
  · rintro y' (hy' | hy')
    · obtain ⟨y, hy, rfl⟩ := hbij.surjOn hy'
      exact ⟨y, Or.inl hy, hfF y hy⟩
    · exact ⟨p, Or.inr rfl, by rw [hfp, Set.mem_singleton_iff.mp hy']⟩
  · rintro y (hy | hy) z (hz | hz)
    · rw [hfF y hy, hfF z hz]
      exact hφ.2 y (Or.inl (residueFoundation_subset_foundation J x hy)) z
        (Or.inl (residueFoundation_subset_foundation J x hz))
    · rw [Set.mem_singleton_iff.mp hz, hfF y hy, hfp, dist_inv hδ', key y hy, ← dist_inv hδ]
    · rw [Set.mem_singleton_iff.mp hy, hfF z hz, hfp, key z hz]
    · rw [Set.mem_singleton_iff.mp hy, Set.mem_singleton_iff.mp hz, hfp, hδ.eq_one_self,
        hδ'.eq_one_self]

end Main

theorem mem_foundation_three_iff (hS : Nat.card ι = 4) {x y : C} :
    y ∈ foundation cs δ 3 x ↔ ∃ J : Set ι, J.ncard = 3 ∧ y ∈ residue cs δ J x := by
  have := finite_of_card_eq_four hS
  rw [mem_foundation_iff]
  constructor
  · rintro ⟨J, hJ, hy⟩
    obtain ⟨K, hJK, hK⟩ := exists_ncard_three_superset hS (by exact_mod_cast hJ)
    exact ⟨K, hK, residue_mono hJK x hy⟩
  · rintro ⟨J, hJ, hy⟩
    refine ⟨J, ?_, hy⟩
    rw [← Set.Finite.cast_ncard_eq (Set.toFinite J), hJ]

theorem spherical_foundation_three_and_apartment_extension [Finite W]
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
    (hS : Nat.card ι = 4) (hext : Ext₃ cs δ δ') {x d : C} {x' d' : C'}
    (hxd : δ x d = longest cs Set.univ) (hxd' : δ' x' d' = longest cs Set.univ) {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' (foundation cs δ 2 x ∪ {d}) (foundation cs δ' 2 x' ∪ {d'}) φ)
    (hφx : φ x = x') (hφd : φ d = d') :
    (IsApartment δ (Set.range (oppChamber cs δ x d)) ∧
      ∀ b : W → C, IsApartmentMap δ b → x ∈ Set.range b → d ∈ Set.range b →
        Set.range b = Set.range (oppChamber cs δ x d)) ∧
    (IsApartment δ' (Set.range (oppChamber cs δ' x' d')) ∧
      ∀ b : W → C', IsApartmentMap δ' b → x' ∈ Set.range b → d' ∈ Set.range b →
        Set.range b = Set.range (oppChamber cs δ' x' d')) ∧
    ∃ Φ : C → C',
      IsWeylIsometry δ δ' (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x d))
        (foundation cs δ' 3 x' ∪ Set.range (oppChamber cs δ' x' d')) Φ ∧
      Set.EqOn Φ φ (foundation cs δ 2 x ∪ {d}) ∧
      (∀ Ψ : C → C', IsWeylIsometry δ δ' (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x d))
          (foundation cs δ' 3 x' ∪ Set.range (oppChamber cs δ' x' d')) Ψ →
        Set.EqOn Ψ φ (foundation cs δ 2 x ∪ {d}) →
        Set.EqOn Ψ Φ (foundation cs δ 3 x ∪ Set.range (oppChamber cs δ x d))) ∧
      (∀ J : Set ι, J.encard ≤ 3 →
        IsTypeIso cs δ δ' (residue cs δ J x) (residue cs δ' J x') Φ) ∧
      ∀ u : W, Φ (oppChamber cs δ x d u) = oppChamber cs δ' x' d' u := by
  classical
  refine ⟨⟨isApartment_range_oppChamber hδ hxd, fun b hb hx hd =>
    range_eq_of_isApartmentMap hδ hxd hb hx hd⟩, ⟨isApartment_range_oppChamber hδ' hxd',
    fun b hb hx hd => range_eq_of_isApartmentMap hδ' hxd' hb hx hd⟩, ?_⟩
  set a := oppChamber cs δ x d with ha
  set a' := oppChamber cs δ' x' d' with ha'
  have hap := isApartmentMap_oppChamber hδ hxd
  have hap' := isApartmentMap_oppChamber hδ' hxd'
  have hx₀ : x ∈ foundation cs δ 2 x ∪ {d} := Or.inl (self_mem_foundation 2 x)
  let f : Set ι → C → C' := fun J y => if y = a (longest cs J) then a' (longest cs J) else φ y
  have hxF : ∀ J : Set ι, x ∈ residueFoundation cs δ J x := fun J =>
    mem_residueFoundation_iff.mpr ⟨∅, ⟨Set.empty_subset J, by simp⟩, self_mem_residue _ x⟩
  have hfF : ∀ J : Set ι, J.ncard = 3 → ∀ y ∈ residueFoundation cs δ J x, f J y = φ y :=
    fun J hJ y hy => ite_eq_right fun (h : y = a (longest cs J)) =>
      oppChamber_longest_not_mem_residueFoundation hδ hxd hJ (by subst h; exact hy)
  have hfp : ∀ J : Set ι, f J (a (longest cs J)) = a' (longest cs J) := fun J => ite_eq_left rfl
  have hloc : ∀ J : Set ι, J.ncard = 3 → IsWeylIsometry δ δ'
      (residueFoundation cs δ J x ∪ {a (longest cs J)})
      (residueFoundation cs δ' J x' ∪ {a' (longest cs J)}) (f J) := fun J hJ =>
    isWeylIsometry_localMap hδ hδ' hS hxd hxd' hφ hφx hφd (hfF J hJ) (hfp J)
  have hpJ : ∀ J : Set ι, a (longest cs J) ∈ residue cs δ J x := fun J =>
    (isProjection_oppChamber_longest hδ hxd J).1
  have hpJ' : ∀ J : Set ι, a' (longest cs J) ∈ residue cs δ' J x' := fun J =>
    (isProjection_oppChamber_longest hδ' hxd' J).1
  have hextJ := fun (J : Set ι) (hJ : J.ncard = 3) =>
    hext J hJ x (a (longest cs J)) x' (a' (longest cs J)) (hpJ J) (hpJ' J)
      (oppChamber_spec hδ hxd _).1 (oppChamber_spec hδ' hxd' _).1 (f J) (hloc J hJ)
      ((hfF J hJ x (hxF J)).trans hφx) (hfp J)
  have hex : ∀ J : Set ι, ∃ F : C → C', J.ncard = 3 →
      IsTypeIso cs δ δ' (residue cs δ J x) (residue cs δ' J x') F ∧
        IsWeylIsometry δ δ' (residue cs δ J x) (residue cs δ' J x') F ∧
          Set.EqOn F (f J) (residueFoundation cs δ J x ∪ {a (longest cs J)}) := by
    intro J
    by_cases hJ : J.ncard = 3
    · obtain ⟨F, hF⟩ := (hextJ J hJ).1
      exact ⟨F, fun _ => hF⟩
    · exact ⟨φ, fun h => absurd h hJ⟩
  choose α hα using hex
  have hαT := fun J (hJ : J.ncard = 3) => (hα J hJ).1
  have hαI := fun J (hJ : J.ncard = 3) => (hα J hJ).2.1
  have hαE := fun J (hJ : J.ncard = 3) => (hα J hJ).2.2
  have hαF : ∀ J : Set ι, J.ncard = 3 → ∀ y ∈ residueFoundation cs δ J x, α J y = φ y :=
    fun J hJ y hy => (hαE J hJ (Or.inl hy)).trans (hfF J hJ y hy)
  have hαx : ∀ J : Set ι, J.ncard = 3 → α J x = x' := fun J hJ =>
    (hαF J hJ x (hxF J)).trans hφx
  have hαp : ∀ J : Set ι, J.ncard = 3 → α J (a (longest cs J)) = a' (longest cs J) :=
    fun J hJ => (hαE J hJ (Or.inr rfl)).trans (hfp J)
  have hcons : ∀ J K : Set ι, J.ncard = 3 → K.ncard = 3 → ∀ y ∈ residue cs δ J x,
      y ∈ residue cs δ K x → α J y = α K y := by
    intro J K hJ hK y hyJ hyK
    by_cases hJK : J = K
    · rw [hJK]
    have hI := encard_inter_le_two hS hJ hK hJK
    have hyI : y ∈ residue cs δ (J ∩ K) x := by
      rw [← residue_inter hδ]
      exact ⟨hyJ, hyK⟩
    rw [hαF J hJ y (mem_residueFoundation_iff.mpr ⟨J ∩ K, ⟨Set.inter_subset_left, hI⟩, hyI⟩),
      hαF K hK y (mem_residueFoundation_iff.mpr ⟨J ∩ K, ⟨Set.inter_subset_right, hI⟩, hyI⟩)]
  have hαA : ∀ J : Set ι, J.ncard = 3 → ∀ u ∈ cs.parabolic J, α J (a u) = a' u := by
    intro J hJ u hu
    have hJl := isLongest_of_finite (cs := cs) J
    have hau : a u ∈ residue cs δ J x := by
      rw [mem_residue_iff_mem_parabolic hδ, (oppChamber_spec hδ hxd u).1]
      exact hu
    have h1 : δ' x' (α J (a u)) = u := by
      rw [← hαx J hJ, (hαI J hJ).2 x (self_mem_residue J x) (a u) hau,
        (oppChamber_spec hδ hxd u).1]
    have h2 : δ' (α J (a u)) (a' (longest cs J)) = u⁻¹ * longest cs J := by
      rw [← hαp J hJ, (hαI J hJ).2 (a u) hau _ (hpJ J), hap]
    exact eq_of_dist_eq_of_length_add hδ' (hJl.length_inv_mul hu) h1 h2
      (oppChamber_spec hδ' hxd' u).1 (by rw [hap'])
  let Φ : C → C' := fun y =>
    if h : ∃ J : Set ι, J.ncard = 3 ∧ y ∈ residue cs δ J x then α h.choose y else a' (δ x y)
  have hΦR : ∀ J : Set ι, J.ncard = 3 → ∀ y ∈ residue cs δ J x, Φ y = α J y := by
    intro J hJ y hy
    have h : ∃ J : Set ι, J.ncard = 3 ∧ y ∈ residue cs δ J x := ⟨J, hJ, hy⟩
    change (if h : ∃ J : Set ι, J.ncard = 3 ∧ y ∈ residue cs δ J x then α h.choose y
      else a' (δ x y)) = α J y
    rw [dite_eq_left h]
    exact hcons _ J h.choose_spec.1 hJ y h.choose_spec.2 hy
  have hΦA : ∀ u : W, Φ (a u) = a' u := by
    intro u
    by_cases h : ∃ J : Set ι, J.ncard = 3 ∧ a u ∈ residue cs δ J x
    · obtain ⟨J, hJ, hJu⟩ := h
      rw [hΦR J hJ _ hJu]
      refine hαA J hJ u ?_
      rw [mem_residue_iff_mem_parabolic hδ, (oppChamber_spec hδ hxd u).1] at hJu
      exact hJu
    · change (if h : ∃ J : Set ι, J.ncard = 3 ∧ a u ∈ residue cs δ J x then α h.choose (a u)
        else a' (δ x (a u))) = a' u
      rw [dite_eq_right h, (oppChamber_spec hδ hxd u).1]
  have hRR : ∀ A B : Set ι, A.ncard = 3 → B.ncard = 3 → ∀ y ∈ residue cs δ A x,
      ∀ z ∈ residue cs δ B x, δ' (Φ y) (Φ z) = δ y z := by
    intro A B hA hB y hy z hz
    obtain ⟨q, hq⟩ := exists_isProjection hδ B x y
    have hqA : q ∈ residue cs δ A x := hq.mem_residue_of_mem hδ hy
    obtain ⟨hmul, hlen⟩ := hq.gate hδ hz
    have h1 : δ' (Φ y) (Φ q) = δ y q := by
      rw [hΦR A hA y hy, hΦR A hA q hqA]
      exact (hαI A hA).2 y hy q hqA
    have h2 : δ' (Φ q) (Φ z) = δ q z := by
      rw [hΦR B hB q hq.1, hΦR B hB z hz]
      exact (hαI B hB).2 q hq.1 z hz
    rw [dist_eq_mul_of_length_add hδ' (y := Φ q) (by rw [h1, h2, ← hmul, hlen]), h1, h2, hmul]
  have hAR : ∀ J : Set ι, J.ncard = 3 → ∀ t : W, ∀ z ∈ residue cs δ J x,
      δ' (Φ (a t)) (Φ z) = δ (a t) z := by
    intro J hJ t z hz
    obtain ⟨v, hv, hq⟩ := exists_isProjection_oppChamber hδ hxd J t
    obtain ⟨hmul, hlen⟩ := hq.gate hδ hz
    have h1 : δ' (Φ (a t)) (Φ (a v)) = δ (a t) (a v) := by
      rw [hΦA, hΦA, hap, hap']
    have h2 : δ' (Φ (a v)) (Φ z) = δ (a v) z := by
      rw [hΦR J hJ _ hq.1, hΦR J hJ z hz]
      exact (hαI J hJ).2 _ hq.1 z hz
    rw [dist_eq_mul_of_length_add hδ' (y := Φ (a v)) (by rw [h1, h2, ← hmul, hlen]), h1, h2, hmul]
  have hdist : ∀ y ∈ foundation cs δ 3 x ∪ Set.range a, ∀ z ∈ foundation cs δ 3 x ∪ Set.range a,
      δ' (Φ y) (Φ z) = δ y z := by
    rintro y (hy | ⟨t, rfl⟩) z (hz | ⟨t', rfl⟩)
    · obtain ⟨A, hA, hyA⟩ := (mem_foundation_three_iff hS).mp hy
      obtain ⟨B, hB, hzB⟩ := (mem_foundation_three_iff hS).mp hz
      exact hRR A B hA hB y hyA z hzB
    · obtain ⟨A, hA, hyA⟩ := (mem_foundation_three_iff hS).mp hy
      rw [dist_inv hδ', hAR A hA t' y hyA, ← dist_inv hδ]
    · obtain ⟨B, hB, hzB⟩ := (mem_foundation_three_iff hS).mp hz
      exact hAR B hB t z hzB
    · rw [hΦA, hΦA, hap, hap']
  have hiso : IsWeylIsometry δ δ' (foundation cs δ 3 x ∪ Set.range a)
      (foundation cs δ' 3 x' ∪ Set.range a') Φ := by
    refine isWeylIsometry_of hδ hδ' ?_ ?_ hdist
    · rintro y (hy | ⟨t, rfl⟩)
      · obtain ⟨A, hA, hyA⟩ := (mem_foundation_three_iff hS).mp hy
        rw [hΦR A hA y hyA]
        exact Or.inl ((mem_foundation_three_iff hS).mpr ⟨A, hA, (hαT A hA).1.mapsTo hyA⟩)
      · rw [hΦA]
        exact Or.inr ⟨t, rfl⟩
    · rintro y' (hy' | ⟨t, rfl⟩)
      · obtain ⟨A, hA, hyA⟩ := (mem_foundation_three_iff hS).mp hy'
        obtain ⟨y, hy, rfl⟩ := (hαT A hA).1.surjOn hyA
        exact ⟨y, Or.inl ((mem_foundation_three_iff hS).mpr ⟨A, hA, hy⟩), hΦR A hA y hy⟩
      · exact ⟨a t, Or.inr ⟨t, rfl⟩, hΦA t⟩
  have hΦx : Φ x = x' := by
    obtain ⟨K, -, hK⟩ := exists_ncard_three_superset hS (J := ∅) (by simp)
    rw [hΦR K hK x (self_mem_residue K x), hαx K hK]
  have hdom3 : ∀ J : Set ι, J.encard ≤ 3 →
      residue cs δ J x ⊆ foundation cs δ 3 x ∪ Set.range a := fun J hJ =>
    (residue_subset_foundation (by exact_mod_cast hJ) x).trans Set.subset_union_left
  have hdom3' : ∀ J : Set ι, J.encard ≤ 3 →
      residue cs δ' J x' ⊆ foundation cs δ' 3 x' ∪ Set.range a' := fun J hJ =>
    (residue_subset_foundation (by exact_mod_cast hJ) x').trans Set.subset_union_left
  have hxdom : x ∈ foundation cs δ 3 x ∪ Set.range a := Or.inl (self_mem_foundation 3 x)
  refine ⟨Φ, hiso, ?_, ?_, ?_, hΦA⟩
  ·
    rintro y (hy | hy)
    · obtain ⟨I, hI, hyI⟩ := mem_foundation_iff.mp hy
      obtain ⟨K, hIK, hK⟩ := exists_ncard_three_superset hS (J := I)
        (le_trans (by exact_mod_cast hI) (by norm_num))
      have hyK := residue_mono hIK x hyI
      rw [hΦR K hK y hyK]
      exact hαF K hK y (mem_residueFoundation_iff.mpr ⟨I, ⟨hIK, by exact_mod_cast hI⟩, hyI⟩)
    · rw [Set.mem_singleton_iff.mp hy, hφd]
      have h1 := hΦA (longest cs Set.univ)
      have h2 : a (longest cs Set.univ) = d := oppChamber_longest hδ hxd
      have h3 : a' (longest cs Set.univ) = d' := oppChamber_longest hδ' hxd'
      rw [h2, h3] at h1
      exact h1
  ·
    intro Ψ hΨ hΨφ
    have hΨx : Ψ x = x' := (hΨφ hx₀).trans hφx
    have hΨd : Ψ d = d' := (hΨφ (Or.inr rfl)).trans hφd
    have hddom : d ∈ foundation cs δ 3 x ∪ Set.range a :=
      Or.inr ⟨longest cs Set.univ, oppChamber_longest hδ hxd⟩
    have hΨA : ∀ u : W, Ψ (a u) = a' u := by
      intro u
      have hu : a u ∈ foundation cs δ 3 x ∪ Set.range a := Or.inr ⟨u, rfl⟩
      refine eq_oppChamber hδ' hxd' ?_ ?_
      · rw [← hΨx, hΨ.2 x hxdom _ hu, (oppChamber_spec hδ hxd u).1]
      · rw [← hΨd, hΨ.2 _ hu d hddom, (oppChamber_spec hδ hxd u).2]
    rintro y (hy | ⟨t, rfl⟩)
    · obtain ⟨K, hK, hyK⟩ := (mem_foundation_three_iff hS).mp hy
      have hK3 : K.encard ≤ 3 := by
        have := finite_of_card_eq_four hS
        rw [← Set.Finite.cast_ncard_eq (Set.toFinite K), hK]
        rfl
      have hbij := hΨ.bijOn_residue hδ hδ' hxdom hΨx (hdom3 K hK3) (hdom3' K hK3)
      have hΨK : IsTypeIso cs δ δ' (residue cs δ K x) (residue cs δ' K x') Ψ :=
        (hΨ.mono (hdom3 K hK3) hbij).isTypeIso
      have hΨf : Set.EqOn Ψ (f K) (residueFoundation cs δ K x ∪ {a (longest cs K)}) := by
        rintro z (hz | hz)
        · rw [hfF K hK z hz]
          exact hΨφ (Or.inl (residueFoundation_subset_foundation K x hz))
        · rw [Set.mem_singleton_iff.mp hz, hfp, hΨA]
      have := (hextJ K hK).2 Ψ (α K) hΨK (hαT K hK) hΨf (hαE K hK) hyK
      rw [this, hΦR K hK y hyK]
    · rw [hΨA, hΦA]
  ·
    intro J hJ
    exact (hiso.mono (hdom3 J hJ) (hiso.bijOn_residue hδ hδ' hxdom hΦx (hdom3 J hJ)
      (hdom3' J hJ))).isTypeIso

end CFSG.Monster.B.Geometry
