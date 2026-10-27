module

public import CFSG.LocalAnalysis.StandardType.GGResICellBasic

public section
namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFH_cons {R : Type} [CommRing R] {N : ℕ}
    (T : Fin N → Vector R (N + 1)) (k j : Fin N) (ws : List (Fin N)) :
    ggFH T (k, j :: ws) = ggFRefl T j (ggFH T (k, ws)) := rfl

theorem ggFC_cons {R : Type} [CommRing R] {N : ℕ}
    (T : Fin N → Vector R (N + 1)) (k j : Fin N) (ws : List (Fin N)) :
    ggFC T (k, j :: ws) = ggFDRefl T j (ggFC T (k, ws)) := by
  simp [ggFC, ggFDWord, List.reverse_cons, List.foldl_append]

abbrev GGResQTwoFactorDataEq {R : Type} [CommRing R] {N : ℕ}
    (H H' : Vector R (N + 1)) (C C' : Vector R N) : Prop :=
  ((∀ m : Fin N, H.get m.castSucc = H'.get m.castSucc) ∧
    ∀ o : Fin N, C.get o = C'.get o) ∨
  ((∀ m : Fin N, H.get m.castSucc = -H'.get m.castSucc) ∧
    ∀ o : Fin N, C.get o = -C'.get o)

theorem ggFRefMat_eq_of_raw_factors {R : Type} [CommRing R] {N : ℕ}
    {T : Fin N → Vector R (N + 1)} {t t' : Fin N × List (Fin N)}
    (h : GGResQTwoFactorDataEq (ggFH T t) (ggFH T t') (ggFC T t) (ggFC T t')) :
    ggFRefMat T t = ggFRefMat T t' := by
  rw [ggFRefMat_eq_map, ggFRefMat_eq_map]
  apply List.map_congr_left
  intro l _
  apply List.map_congr_left
  intro m _
  rcases h with ⟨hh, hc⟩ | ⟨hh, hc⟩
  · have he : ggFDualAt T (ggFC T t) l = ggFDualAt T (ggFC T t') l :=
      Finset.sum_congr rfl fun o _ => by rw [hc o]
    rw [hh m, he]
  · have he : ggFDualAt T (ggFC T t) l = -ggFDualAt T (ggFC T t') l := by
      change (∑ o : Fin N, (ggFC T t).get o * (T o).get l.castSucc) =
        -(∑ o : Fin N, (ggFC T t').get o * (T o).get l.castSucc)
      calc
        _ = ∑ o : Fin N, -((ggFC T t').get o * (T o).get l.castSucc) :=
          Finset.sum_congr rfl fun o _ => by rw [hc o, neg_mul]
        _ = _ := Finset.sum_neg_distrib _
    rw [hh m, he, neg_mul_neg]

end CFSG.StandardType
