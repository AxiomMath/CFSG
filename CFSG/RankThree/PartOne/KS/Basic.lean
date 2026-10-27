module

public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.LocalRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem exists_section_of_quotient_subgroup {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (L : Subgroup (X ⧸ N)) :
    ∃ (H : Subgroup X) (K : Subgroup H) (_ : K.Normal),
      Nonempty ((H ⧸ K) ≃* (L ⧸ center L)) := by
  let φ0 : (L.comap (QuotientGroup.mk' N)) →* L := (QuotientGroup.mk' N).subgroupComap L
  have hφ0 : Function.Surjective φ0 := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ N)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [Subgroup.mem_comap]
    change (x : X ⧸ N) ∈ L
    rw [hx]
    exact l.2
  let φ : (L.comap (QuotientGroup.mk' N)) →* (L ⧸ center L) :=
    (QuotientGroup.mk' (center L)).comp φ0
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hφ0
  exact ⟨_, φ.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩⟩

@[expose] def SectionsForceEvenRankFour (A : Type) [Group A] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (K : Subgroup H) [K.Normal],
    Nonempty ((H ⧸ K) ≃* A) → 4 ≤ evenRank G

@[expose] def SimplePresentationMSectionsForceEvenRankFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (K : Subgroup H) [K.Normal]
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty ((H ⧸ K) ≃* T) → Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.M) → 4 ≤ evenRank G

theorem planeLocalCoreOdd_of_not_sq_dvd {T : Type*} [Group T] {p : ℕ}
    (h : ¬ p ^ 2 ∣ Nat.card (MulAut T)) : PlaneLocalCoreOdd p T := by
  intro B _ A _ _ hAcard _ _ _
  have hdvd := Subgroup.card_subgroup_dvd_card A
  rw [hAcard] at hdvd
  exact absurd hdvd h

theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ center T := by rw [h]; exact Subgroup.mem_top a
    exact ((Subgroup.mem_center_iff.mp ha) b).symm

theorem card_mulAut_eq_mul_card_outer {T : Type*} [Group T] [Finite T] (hc : center T = ⊥) :
    Nat.card (MulAut T) =
      Nat.card T * Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner T) = Nat.card T :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).toEquiv).symm
  rw [h1, h2, mul_comm]

@[expose] def AlmostSimplePlaneOdd (p : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal], Nonempty (K ≃* A) →
    centralizer (K : Set H) = ⊥ → ∀ E : Subgroup H, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      ∀ t ∈ E, t ≠ 1 → ¬ 2 ∣ Nat.card (localCoreProduct p E t)

theorem map_subtype_thetaT_eq {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) (hA : ∃ a ∈ A, a ≠ 1) :
    (thetaT p A).map B.subtype = autThetaT p B (A.map B.subtype) := by
  refine le_antisymm (map_subtype_thetaT_le hp B A) ?_
  intro x hx
  obtain ⟨a, haA, ha1⟩ := hA
  simp only [autThetaT, Subgroup.mem_iInf] at hx
  have hxa : x ∈ (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B))).map B.subtype := by
    rw [map_subtype_theta_centralizer hp B a]
    exact hx (B.subtype a) (Subgroup.mem_map_of_mem _ haA)
      (fun h => ha1 (Subtype.ext (by simpa using h)))
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hxa
  refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
  simp only [thetaT, Subgroup.mem_iInf]
  intro b hbA hb1
  have hxb : B.subtype y ∈ (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({b} : Set B))).map B.subtype := by
    rw [map_subtype_theta_centralizer hp B b]
    exact hx (B.subtype b) (Subgroup.mem_map_of_mem _ hbA)
      (fun h => hb1 (Subtype.ext (by simpa using h)))
  obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hxb
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem autPlaneProduct_eq_map_localCoreProduct {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (B : Subgroup M) (A : Subgroup B) (t : B) (hA : ∃ a ∈ A, a ≠ 1) :
    autPlaneProduct p B (A.map B.subtype) (t : M) =
      (localCoreProduct p A t).map B.subtype := by
  rw [localCoreProduct, Subgroup.map_sup, Subgroup.map_commutator,
    map_subtype_theta_centralizer hp B t, map_subtype_thetaT_eq hp B A hA, autPlaneProduct]

theorem planeLocalCoreOdd_of_almostSimple {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) {A : Type} [Group A] (e : T ≃* A) {p : ℕ}
    (hp : p.Prime) (h : AlmostSimplePlaneOdd p A) : PlaneLocalCoreOdd p T := by
  have hc : center T = ⊥ := center_eq_bot_of_simple hnab
  have hinj := conj_injective_of_center_eq_bot hc
  intro B hB A' hA'B hA' hA'card t htA' ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA'
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner T).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal T
  let K : Subgroup B := (MulAut.conj : T →* MulAut T).range.subgroupOf B
  have : K.Normal :=
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal T).subgroupOf B
  have hKA : Nonempty (K ≃* A) :=
    ⟨((Subgroup.subgroupOfEquivOfLe hB).trans
      (MonoidHom.ofInjective hinj).symm).trans e⟩
  have hKc : centralizer (K : Set B) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hcomm : ∀ x : T, (b : MulAut T) * MulAut.conj x = MulAut.conj x * (b : MulAut T) := by
      intro x
      have hmem : (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) ∈ K := ⟨x, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hb _ hmem
      exact congrArg Subtype.val this.symm
    have hx : ∀ x : T, (b : MulAut T) x = x := by
      intro x
      have hxc : x⁻¹ * (b : MulAut T) x ∈ center T := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h1 := congrArg (fun f : MulAut T => f ((b : MulAut T).symm z)) (hcomm x)
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.apply_symm_apply] at h1
        calc z * (x⁻¹ * (b : MulAut T) x) = x⁻¹ * ((x * z * x⁻¹) * (b : MulAut T) x) := by group
          _ = x⁻¹ * (((b : MulAut T) x * z * ((b : MulAut T) x)⁻¹) * (b : MulAut T) x) := by
            rw [← h1]
          _ = x⁻¹ * (b : MulAut T) x * z := by group
      rw [hc, Subgroup.mem_bot] at hxc
      calc (b : MulAut T) x = x * (x⁻¹ * (b : MulAut T) x) := by group
        _ = x := by rw [hxc, mul_one]
    ext x
    exact hx x
  have hEA : IsElementaryAbelian p (A'.subgroupOf B) := IsElementaryAbelian.subgroupOf hA'B
  have hEcard : Nat.card (A'.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'B).toEquiv, hA'card]
  have htB : (⟨t, hA'B htA'⟩ : B) ∈ A'.subgroupOf B := htA'
  have ht1' : (⟨t, hA'B htA'⟩ : B) ≠ 1 := fun h' => ht1 (congrArg Subtype.val h')
  have hodd := h B K hKA hKc (A'.subgroupOf B) hEA hEcard _ htB ht1'
  have hne : ∃ a ∈ A'.subgroupOf B, a ≠ 1 := ⟨_, htB, ht1'⟩
  have heq := autPlaneProduct_eq_map_localCoreProduct hp B (A'.subgroupOf B)
    ⟨t, hA'B htA'⟩ hne
  rw [Subgroup.map_subgroupOf_eq_of_le hA'B] at heq
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd

end CFSG.RankThree.PartOne
