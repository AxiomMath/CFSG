module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RAMax
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RCenJ

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

structure RData {G : Type} [Group G] (b : G) {L : Subgroup G} (z : Fin 3 → ↥L)
    (J B₂ A R : Subgroup G) : Prop where
  b2 : B2Package b z B₂
  aStar : AStar b z B₂ A
  le : R ≤ B₂
  card : Nat.card R = 9
  b₁_mem : GGFF.zs z 0 ∈ R
  comm : ∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ Subgroup.zpowers (GGFF.zs z 0)
  nonc : ∃ r ∈ R, b * r * b⁻¹ * r⁻¹ ≠ 1
  cenJ : ∀ r ∈ R, ∀ x ∈ J, r * x = x * r
  A_le : A ≤ Subgroup.centralizer (R : Set G)
  A_max : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (R : Set G) → IsPGroup 3 P → A ≤ P → P = A

theorem exists_rData {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A : Subgroup G} {τ c : G}
    (hJ : JData n L z J) (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c)
    (hS : SylowData b B₂ A c)
    (hT : ∀ P : Sylow 3 G, ¬ ((P : Subgroup G) ≤ Subgroup.centralizer ({GGFF.zs z 0} : Set G))) :
    ∃ R : Subgroup G, RData b z J B₂ A R := by
  obtain ⟨R, hRB, hR9, hR1, hRc, hRn, hRJ⟩ := exists_rCenJ h hJ hB₂
  refine ⟨R, ?_⟩
  exact
    { b2 := hB₂
      aStar := hA
      le := hRB
      card := hR9
      b₁_mem := hR1
      comm := hRc
      nonc := hRn
      cenJ := hRJ
      A_le := fun x hx => Subgroup.mem_centralizer_iff.mpr fun r hr =>
        Subgroup.mem_centralizer_iff.mp (hA.le_cen hx) r (hRB hr)
      A_max := aStar_max_of_R h hB₂ hA hτc hS hT hRB hR9 hR1 hRc hRn }

end CFSG.StandardType.FF81.PropOne

end
