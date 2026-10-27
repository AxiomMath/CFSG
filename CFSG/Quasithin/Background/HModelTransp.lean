module

public import CFSG.Quasithin.Background.HB82Base
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H.ZTrans

open CFSG.Open

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem isElemAbelian_map_hom {G G' : Type*} [Group G] [Group G'] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* G') : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem map_le_normalizer_congrHom (e : V ≃* W) {H X : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    X.map (congrHom e) ≤ Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W)) :
      Set (MulAut W)) :=
  (Subgroup.map_mono hXN).trans (Subgroup.le_normalizer_map (congrHom e))

theorem card_fixV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    Nat.card ↥(fixV (X.map (congrHom e))) = Nat.card ↥(fixV X) := by
  rw [fixV_map_congrHom, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem congrHom_self_apply (c x : MulAut W) : congrHom c x = MulAut.conj c x := by
  ext w
  rfl

theorem map_congrHom_self_eq_conj (c : MulAut W) (X : Subgroup (MulAut W)) :
    X.map (congrHom c) = X.map (MulAut.conj c).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (congrHom_self_apply c x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, congrHom_self_apply c x⟩

theorem map_congrHom_of_mem_normalizer {H₀ : Subgroup (MulAut W)} {c : MulAut W}
    (hc : c ∈ Subgroup.normalizer (H₀ : Set (MulAut W))) : H₀.map (congrHom c) = H₀ := by
  rw [map_congrHom_self_eq_conj]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hc x).1 hx
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hc) y).1 hy
      rwa [inv_inv] at h
    · show c * (c⁻¹ * y * c) * c⁻¹ = y
      group

theorem perfectCore_inf_stab_map [Finite V] [Finite W] (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom e) =
      perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))) := by
  rw [← perfectCore_map_congrHom, map_inf_stab_congrHom]

theorem pCoreOf_le_comm_of_map (e : V ≃* W) {P X : Subgroup (MulAut V)}
    (h : pCoreOf 2 (P.map (congrHom e)) ≤ ⁅X.map (congrHom e), P.map (congrHom e)⁆) :
    pCoreOf 2 P ≤ ⁅X, P⁆ := by
  rw [pCoreOf_map_congrHom, ← Subgroup.map_commutator] at h
  exact (Subgroup.map_le_map_iff_of_injective (congrHom_injective e)).1 h

theorem map_congrHom_symm_map (e : V ≃* W) (A : Subgroup (MulAut V)) :
    (A.map (congrHom e)).map (congrHom e.symm) = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x v
  simp

theorem isPSL_of_mulEquiv' {X Y : Type} [Group X] [Group Y] {n p f : ℕ} (e : X ≃* Y)
    (h : IsPSL n p f Y) : IsPSL n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

end CFSG.Quasithin.H.ZTrans
