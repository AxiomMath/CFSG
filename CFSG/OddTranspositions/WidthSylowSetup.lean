module

public import CFSG.OddTranspositions.Width
public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type*} [Group G] {D : Set G}

theorem sylow_inter_commute_of_setup (hS : Setup G D) (T : Sylow 2 G) {a b : G}
    (haT : a ∈ (T : Set G)) (hbT : b ∈ (T : Set G)) (haD : a ∈ D) (hbD : b ∈ D)
    (hne : a ≠ b) : Commute a b :=
  hS.oddT.commute_of_isPGroup T.isPGroup' haD hbD haT hbT

theorem exists_sylow_of_pairwise_commuting_of_setup (hS : Setup G D) {S : Finset G}
    (hSD : (↑S : Set G) ⊆ D)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Commute x y) :
    ∃ T : Sylow 2 G, (↑S : Set G) ⊆ (T : Set G) := by
  classical
  let H : Subgroup G := Subgroup.closure (↑S : Set G)
  have hpair : ((↑S : Set G)).Pairwise Commute := by
    intro x hx y hy hxy
    exact hcomm x hx y hy hxy
  haveI : IsMulCommutative H := Subgroup.isMulCommutative_closure hpair
  have hsq : ∀ x : H, x ^ 2 = 1 := by
    have hsq_mem : ∀ g (hg : g ∈ H), (⟨g, hg⟩ : H) ^ 2 = 1 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
        apply Subtype.ext
        simpa [pow_two] using hS.oddT.mul_self_eq_one (hSD hy)
      | one => simp
      | mul y z hy hz ihy ihz =>
        change ((⟨y, hy⟩ : H) * ⟨z, hz⟩) ^ 2 = 1
        have hc : Commute (⟨y, hy⟩ : H) ⟨z, hz⟩ :=
          (IsMulCommutative.is_comm (M := H)).comm _ _
        rw [hc.mul_pow, ihy, ihz, mul_one]
      | inv y hy ihy =>
        change (⟨y, hy⟩ : H)⁻¹ ^ 2 = 1
        rw [inv_pow, ihy, inv_one]
    intro x
    exact hsq_mem (x : G) x.2
  have hexp : Monoid.exponent H ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  have hP2 : IsPGroup 2 H := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  obtain ⟨T, hT⟩ := hP2.exists_le_sylow
  exact ⟨T, fun x hx => hT (Subgroup.subset_closure hx)⟩

theorem widthLe_iff_sylow_of_setup [Finite G] (hS : Setup G D) (n : ℕ) :
    WidthLe D n ↔ ∀ T : Sylow 2 G, ((T : Set G) ∩ D).ncard ≤ n := by
  classical
  constructor
  · intro h T
    unfold WidthLe at h
    let s : Set G := (T : Set G) ∩ D
    have hs : s.Finite := Set.toFinite s
    let S : Finset G := hs.toFinset
    have hDS : (↑S : Set G) ⊆ D := by
      intro x hx
      exact (hs.mem_toFinset.mp hx).2
    have hcomm : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Commute x y := by
      intro x hx y hy hxy
      have hx' : x ∈ s := hs.mem_toFinset.mp hx
      have hy' : y ∈ s := hs.mem_toFinset.mp hy
      exact sylow_inter_commute_of_setup hS T hx'.1 hy'.1 hx'.2 hy'.2 hxy
    have hle := h S hDS hcomm
    change s.ncard ≤ n
    rw [Set.ncard_eq_toFinset_card s hs]
    exact hle
  · intro h
    unfold WidthLe
    intro S hSD hcomm
    obtain ⟨T, hST⟩ := exists_sylow_of_pairwise_commuting_of_setup hS hSD hcomm
    have hle : S.card ≤ ((T : Set G) ∩ D).ncard := by
      have hsub : (↑S : Set G) ⊆ (T : Set G) ∩ D := fun x hx => ⟨hST hx, hSD hx⟩
      have h1 : ((↑S : Set G)).ncard ≤ ((T : Set G) ∩ D).ncard := Set.ncard_le_ncard hsub
      rwa [Set.ncard_coe_finset] at h1
    exact hle.trans (h T)

theorem widthLe_of_sylow_bound [Finite G] (hS : Setup G D) {n : ℕ}
    (h : ∀ T : Sylow 2 G, ((T : Set G) ∩ D).ncard ≤ n) : WidthLe D n :=
  (widthLe_iff_sylow_of_setup hS n).mpr h

end CFSG.OddTranspositions
