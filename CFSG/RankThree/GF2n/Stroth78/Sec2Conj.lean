module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Literature.GL52Transport

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem centralizer_map_conj (a : G) (g : G) :
    Subgroup.centralizer ({g * a * g⁻¹} : Set G) =
      (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom := by
  rw [← MulAut.conj_apply g a]
  exact (CFSG.Literature.GL52.map_centralizer_singleton (MulAut.conj g) a).symm

theorem fStar_map_conj (M : Subgroup G) (g : G) :
    fStar (M.map (MulAut.conj g).toMonoidHom) =
      (fStar M).map (MulAut.conj g).toMonoidHom := by
  let φ : G ≃* G := MulAut.conj g
  let e : ↥M ≃* ↥(M.map φ.toMonoidHom) := M.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomp : (M.map φ.toMonoidHom).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp M.subtype := by
    ext x
    rfl
  have h := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  unfold fStar
  rw [← h, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem QaOf_eq_map_of_isConj (S : Setting z E F) {a : G} (h : IsConj z a) :
    ∃ g : G, QaOf a = (Q z).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨c, hc⟩ := h
  have ha : a = (c : G) * z * (c : G)⁻¹ := by
    have hcz : (c : G) * z = a * (c : G) := hc.eq
    calc
      a = a * (c : G) * (c : G)⁻¹ := by group
      _ = (c : G) * z * (c : G)⁻¹ := by rw [← hcz]
  refine ⟨(c : G), ?_⟩
  show fStar (Subgroup.centralizer ({a} : Set G)) =
    (fStar (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj (c : G)).toMonoidHom
  rw [ha, centralizer_map_conj z (c : G), fStar_map_conj]

theorem card_QaOf_eq (S : Setting z E F) {a : G} (h : IsConj z a) :
    Nat.card (QaOf a) = Nat.card (Q z) := by
  obtain ⟨g, hg⟩ := QaOf_eq_map_of_isConj S h
  rw [hg, Subgroup.card_map_of_injective (K := Q z)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

theorem centerIn_QaOf_eq_map (S : Setting z E F) {a : G} (h : IsConj z a) :
    ∃ g : G, centerIn (QaOf a) = (ZQ z).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := QaOf_eq_map_of_isConj S h
  refine ⟨g, ?_⟩
  let φ : G ≃* G := MulAut.conj g
  have hg' : QaOf a = (Q z).map φ.toMonoidHom := hg
  have hC : Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) =
      (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
    (CFSG.Literature.GL52.map_centralizer_subgroup φ (Q z)).symm
  calc
    centerIn (QaOf a) = QaOf a ⊓ Subgroup.centralizer (QaOf a : Set G) := rfl
    _ = (Q z).map φ.toMonoidHom ⊓
          Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) := by rw [hg']
    _ = (Q z).map φ.toMonoidHom ⊓
          (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom := by rw [hC]
    _ = ((Q z) ⊓ Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
          (Subgroup.map_inf_eq (Q z) (Subgroup.centralizer (Q z : Set G)) φ.toMonoidHom
            φ.injective).symm
    _ = (ZQ z).map φ.toMonoidHom := rfl

theorem card_centerIn_QaOf (S : Setting z E F) {a : G} (h : IsConj z a) :
    Nat.card (centerIn (QaOf a)) = 2 * Nat.card E := by
  obtain ⟨g, hg⟩ := centerIn_QaOf_eq_map S h
  rw [hg, Subgroup.card_map_of_injective (K := ZQ z)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective, ZQ_card S, Nat.mul_comm]

end CFSG.RankThree.GF2n.Stroth78
