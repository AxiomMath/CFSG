module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KGroupBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91riso_orderOf_eq {G K : Type*} [Group G] [Group K] (φ : G →* K)
    (hinj : Function.Injective φ) (c : G) (hZ : center K = zpowers (φ c)) :
    orderOf c = Nat.card (center K) := by
  rw [hZ, Nat.card_zpowers]
  exact (orderOf_injective φ hinj c).symm

private theorem k91riso_ker_eq_bot {G K P : Type*} [Group G] [Group K] [Group P] (φ : G →* K)
    (hinj : Function.Injective φ) (c : G) (hZ : center K = zpowers (φ c)) (ψ : G →* P)
    (hψc : orderOf (ψ c) = Nat.card (center K)) (h : ψ.ker.map φ ≤ center K) : ψ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hgK : φ g ∈ zpowers (φ c) := hZ ▸ h (Subgroup.mem_map_of_mem φ hg)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hgK
  have hgc : g = c ^ m := hinj (by rw [map_zpow, hm])
  have h1 : ψ c ^ m = 1 := by rw [← map_zpow, ← hgc]; exact MonoidHom.mem_ker.mp hg
  have h2 : (orderOf c : ℤ) ∣ m := by
    rw [k91riso_orderOf_eq φ hinj c hZ, ← hψc]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hgc, orderOf_dvd_iff_zpow_eq_one.mp h2]
  exact Subgroup.one_mem _

theorem nonempty_mulEquiv_of_cover {G K P : Type*} [Group G] [Group K] [Group P] [Finite G]
    (hq : CFSG.IsQuasisimple K) (φ : G →* K) (hφ : Function.Surjective φ)
    (hcard : Nat.card G ≤ Nat.card K) (c : G) (hZ : center K = zpowers (φ c)) (ψ : G →* P)
    (hψ : Function.Surjective ψ) (hψc : orderOf (ψ c) = Nat.card (center K))
    (hZ1 : Nat.card (center K) ≠ 1) : Nonempty (K ≃* P) := by
  have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le hcard
  rcases normal_eq_top_or_le_center_of_isQuasisimple hq (ψ.normal_ker.map φ hφ) with h | h
  · exfalso
    have hker : ψ.ker = ⊤ := by
      apply Subgroup.map_injective hbij.1
      rw [h, Subgroup.map_top_of_surjective φ hφ]
    have hc : c ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top c
    exact hZ1 (by rw [← hψc, MonoidHom.mem_ker.mp hc, orderOf_one])
  · have hinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).mp (k91riso_ker_eq_bot φ hbij.1 c hZ ψ hψc h)
    exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩)⟩

private theorem k91rab_commutator_eq_top {G K : Type*} [Group G] [Group K] [Finite G]
    (hK : commutator K = ⊤) (φ : G →* K) (hφ : Function.Surjective φ)
    (hcard : Nat.card G ≤ Nat.card K) : commutator G = ⊤ := by
  apply Subgroup.map_injective (hφ.bijective_of_nat_card_le hcard).1
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hφ, ← _root_.commutator_def, hK,
    Subgroup.map_top_of_surjective φ hφ]

theorem false_of_cover_abel {G K : Type*} [Group G] [Group K] [Finite G]
    (hK : commutator K = ⊤) (φ : G →* K) (hφ : Function.Surjective φ)
    (hcard : Nat.card G ≤ Nat.card K) (χ : G →* Multiplicative (ZMod 6)) (hχ : χ ≠ 1) :
    False := by
  have hG := k91rab_commutator_eq_top hK φ hφ hcard
  refine hχ (MonoidHom.ext fun g => ?_)
  have hg : g ∈ χ.ker :=
    Abelianization.commutator_subset_ker χ (hG ▸ Subgroup.mem_top g)
  exact MonoidHom.mem_ker.mp hg

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
