module

public import CFSG.Quasithin.Background.FFC4NatS3
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.Open

theorem nonempty_mulEquiv_perm_of_s3 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {U : Subgroup V} (hH6 : Nat.card ↥H = 6) (hU4 : Nat.card U = 4)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1) :
    Nonempty (↥H ≃* Equiv.Perm (Fin 3)) := by
  have hUK : IsKleinFour ↥U := isKleinFour_of_card_four hU4 fun u => Subtype.ext (hV u)
  have hstab : H ≤ stabSub U := le_stabSub_of_invariant hUinv
  have hρinj : Function.Injective (resG hstab) := resG_injective hstab hfaith
  have hMA : Nat.card (MulAut ↥U) ≤ 6 := card_mulAut_le_six hU4
  have hρbij : Function.Bijective (resG hstab) :=
    hρinj.bijective_of_nat_card_le (by rw [hH6]; exact hMA)
  exact ⟨(MulEquiv.ofBijective (resG hstab) hρbij).trans
    (CFSG.GorensteinWalter.kleinFourAutSymmetricThreeEquiv ↥U)⟩

theorem commV_invariant_self {V : Type} [CommGroup V] (X : Subgroup (MulAut V)) :
    ∀ g ∈ X, ∀ u ∈ commV X, g u ∈ commV X := fun _ hg _ hu =>
  commV_invariant (fun _ hx => X.mul_mem (X.mul_mem hg hx) (X.inv_mem hg)) hu

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

theorem good_of_case2 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} (h : B56Case2 H) : GoodFactor H := by
  obtain ⟨⟨e⟩, ⟨hsup, hinf⟩, hc4⟩ := h
  have hH6 : Nat.card ↥H = 6 := by rw [Nat.card_congr e.toEquiv, card_perm_three]
  have hU4 : Nat.card (commV H) = 4 := by simpa using hc4
  have hUinv : ∀ g ∈ H, ∀ u ∈ commV H, g u ∈ commV H := commV_invariant_self H
  have hfaith : ∀ g ∈ H, (∀ u ∈ commV H, g u = u) → g = 1 := by
    intro g hg hu
    ext v
    have hv : v ∈ commV H ⊔ fixV H := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, hu y hy, hz g hg]
    rfl
  have hCinv : ∀ g ∈ H, ∀ c ∈ fixV H, g c ∈ fixV H := fun g hg c hc => by
    rw [hc g hg]; exact hc
  obtain ⟨π, hπ, -⟩ := exists_natural_s3 hW hH6 hU4 hUinv hfaith
  have hnat := binaryNaturalSL_two_of_s3 hW hH6 hU4 hUinv hfaith hCinv hinf
  rw [hsup] at hnat
  refine ⟨Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, by simp,
    ⟨(MulEquiv.ofBijective π hπ).symm⟩⟩, Or.inl ⟨hsup.symm, Or.inl ⟨1, hnat⟩⟩⟩

section Split

variable {V : Type} [CommGroup V] [Finite V]

namespace B58Split

variable {G A G₁ G₂ F : Subgroup (MulAut V)} (h : B58Split G A G₁ G₂ F)

omit [Finite V] in
include h in
theorem card_G₁ : Nat.card ↥G₁ = 6 := by
  obtain ⟨e⟩ := h.iso
  rw [Nat.card_congr e.toEquiv, card_sl2_two]

omit [Finite V] in
include h in
theorem faithful_G₁ : ∀ a ∈ G₁, (∀ u ∈ commV G₁, a u = u) → a = 1 := by
  intro a ha hu
  ext v
  have hv : v ∈ commV G₁ ⊔ fixV G₁ := by rw [h.dec_sup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, hu y hy, hz a ha]
  rfl

include h in
theorem case2 (hV : ∀ v : V, v ^ 2 = 1) (hG₂ : G₂ = ⊥) : B56Case2 G := by
  have hGG : G = G₁ := by
    rw [← h.sup, hG₂, sup_bot_eq]
  subst hGG
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_of_s3 hV h.card_G₁ h.card_comm (commV_invariant_self _)
    h.faithful_G₁
  exact ⟨⟨e⟩, ⟨h.dec_sup, h.dec_inf⟩, by simpa using h.card_comm⟩

include h in
theorem pieceG₁ (hV : ∀ v : V, v ^ 2 = 1) :
    B56FactorList ↥G₁ ∧ B56Piece G₁ (commV G₁ ⊔ fixV G) (fixV G) := by
  obtain ⟨e⟩ := h.iso
  have hCinv : ∀ g ∈ G₁, ∀ c ∈ fixV G, g c ∈ fixV G := fun g hg c hc => by
    rw [hc g (h.G₁_le hg)]; exact hc
  have hUC : commV G₁ ⊓ fixV G = ⊥ := by
    rw [eq_bot_iff, ← h.dec_inf]
    exact inf_le_inf_left _ (B1.fixV_le_fixV h.G₁_le)
  refine ⟨Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, by simp,
    ⟨e.trans (specialLinearGroupEquivStatedSL 2 (ZMod 2))⟩⟩, Or.inl ⟨rfl, Or.inl ⟨1, ?_⟩⟩⟩
  exact binaryNaturalSL_two_of_s3 hV h.card_G₁ h.card_comm (commV_invariant_self G₁) h.faithful_G₁ hCinv hUC

end B58Split

end Split

end FFC

end CFSG.Quasithin
