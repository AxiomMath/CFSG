module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Conj
public import CFSG.RankThree.GF2n.Stroth78.Sec2Three

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar fStar_cent fStar_le fStar_normal)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem QaOf_isPGroup (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    IsPGroup 2 (QaOf a) := by
  obtain ⟨g, hg⟩ := QaOf_eq_map_of_isConj S hconj
  rw [hg]
  exact (Q_isPGroup S).map (MulAut.conj g).toMonoidHom

theorem zpowers_mem_centerIn_QaOf (S : Setting z E F) (a : G) :
    Subgroup.zpowers a ≤ centerIn (QaOf a) := by
  refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨mem_QaOf_self a, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp
    (fStar_le (Subgroup.centralizer ({a} : Set G)) hy) a (Set.mem_singleton a)).symm

theorem QaOf_eq_map_of_conj_eq (S : Setting z E F) {a g : G}
    (hg : g * z * g⁻¹ = a) :
    QaOf a = (Q z).map (MulAut.conj g).toMonoidHom := by
  have hcent : Subgroup.centralizer ({a} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact centralizer_map_conj z g
  show fStar (Subgroup.centralizer ({a} : Set G)) = _
  rw [hcent, fStar_map_conj]
  rfl

theorem centerIn_QaOf_eq_map_of_conj_eq (S : Setting z E F) {a g : G}
    (hg : g * z * g⁻¹ = a) :
    centerIn (QaOf a) = (ZQ z).map (MulAut.conj g).toMonoidHom := by
  let φ : G ≃* G := MulAut.conj g
  have hQa := QaOf_eq_map_of_conj_eq S hg
  have hC : Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) =
      (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
    (CFSG.Literature.GL52.map_centralizer_subgroup φ (Q z)).symm
  calc
    centerIn (QaOf a) = QaOf a ⊓ Subgroup.centralizer (QaOf a : Set G) := rfl
    _ = (Q z).map φ.toMonoidHom ⊓
          Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) := by rw [hQa]
    _ = (Q z).map φ.toMonoidHom ⊓
          (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom := by rw [hC]
    _ = ((Q z) ⊓ Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
          (Subgroup.map_inf_eq (Q z) (Subgroup.centralizer (Q z : Set G)) φ.toMonoidHom
            φ.injective).symm
    _ = (ZQ z).map φ.toMonoidHom := rfl

theorem mem_centralizer_QaOf_iff (S : Setting z E F) {a g x : G}
    (hg : g * z * g⁻¹ = a) :
    x ∈ Subgroup.centralizer ({a} : Set G) ↔ g⁻¹ * x * g ∈ H z := by
  have hC : Subgroup.centralizer ({a} : Set G) =
      (H z).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact centralizer_map_conj z g
  rw [hC, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end CFSG.RankThree.GF2n.Stroth78
