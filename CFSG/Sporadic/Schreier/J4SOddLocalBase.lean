
module

public import CFSG.Sporadic.Schreier.J4SOddCheckBase
public import CFSG.Sporadic.Schreier.J4SOddLemmas
public import CFSG.Sporadic.Schreier.J4SThreeBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.Local
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

theorem card_inf_centralizer_mul_ncard {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (g : G) :
    Nat.card (L ⊓ Subgroup.centralizer {g} : Subgroup G) *
      {m | ∃ k ∈ L, m = k * g * k⁻¹}.ncard = Nat.card L := by
  let _ : MulAction L G := MulAction.compHom G (MulAut.conj.comp L.subtype)
  have hsmul : ∀ (k : L) (m : G), k • m = (k : G) * m * (k : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit L g = {m | ∃ k ∈ L, m = k * g * k⁻¹} := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, hsmul k g⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, hsmul _ g⟩
  have hstab : Nat.card (MulAction.stabilizer L g) =
      Nat.card (L ⊓ Subgroup.centralizer {g} : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, Subgroup.mem_inf.2 ⟨s.1.2, ?_⟩⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    · have h1 : s.1 • g = g := MulAction.mem_stabilizer_iff.1 s.2
      rw [hsmul] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (s.1 : G) * g = s.1 * g * (s.1 : G)⁻¹ * s.1 := by group
        _ = g * s.1 := by rw [h1]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2
      change (s : G) * g * (s : G)⁻¹ = g
      rw [h2, mul_inv_cancel_right]
  rw [← hstab, ← horb, ← MulAction.index_stabilizer, Subgroup.card_mul_index]

section Local

variable {t : J}

theorem conj_mem_centralizer_oddCoreImage {k : J} (hkN : ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hkC : k ∈ Subgroup.centralizer {t}) {b : J}
    (hb : b ∈ N ⊓ Subgroup.centralizer (oddCoreImage (Subgroup.centralizer {t}) : Set J)) :
    k * b * k⁻¹ ∈ N ⊓ Subgroup.centralizer (oddCoreImage (Subgroup.centralizer {t}) : Set J) := by
  obtain ⟨hbN, hbR⟩ := Subgroup.mem_inf.1 hb
  refine Subgroup.mem_inf.2 ⟨hkN b hbN, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have hr' : k⁻¹ * r * k⁻¹⁻¹ ∈ oddCoreImage (Subgroup.centralizer {t}) :=
    oddCoreImage_conj _ (Subgroup.inv_mem _ hkC) hr
  have h1 := Subgroup.mem_centralizer_iff.1 hbR _ hr'
  rw [inv_inv] at h1
  calc r * (k * b * k⁻¹) = k * ((k⁻¹ * r * k) * b) * k⁻¹ := by group
    _ = k * (b * (k⁻¹ * r * k)) * k⁻¹ := by rw [h1]
    _ = k * b * k⁻¹ * r := by group

end Local

theorem isConj_of_orbit {s t : J} (h : ∃ g : J, ∃ k ∈ K, t = g⁻¹ * (k⁻¹ * s * k) * g) :
    IsConj s t := by
  obtain ⟨g, k, -, rfl⟩ := h
  exact isConj_iff.2 ⟨g⁻¹ * k⁻¹, by group⟩

theorem orderOf_of_isConj {s t : J} (h : IsConj s t) : orderOf t = orderOf s := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [show c * s * c⁻¹ = MulAut.conj c s by rw [MulAut.conj_apply], MulEquiv.orderOf_eq]

end CFSG.Sporadic.J4Schreier
