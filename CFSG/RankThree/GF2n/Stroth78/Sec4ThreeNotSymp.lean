module

public import CFSG.Fischer.Classification.Defs

import CFSG.Fischer.Classification.SymplecticTypeTransport
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUModel
import CFSG.Timmesfeld.Transvection.QTwoFischer

public section

namespace CFSG.RankThree.GF2n.Stroth78

open Matrix CFSG.ClassicalGroups.Unitary CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.Timmesfeld.Transvection.QTwo

theorem not_isSymplecticType_transvections {A : Matrix (Fin 6) (Fin 6) K}
    (hA : IsNondegenerateHermitian A) : ¬ IsSymplecticType (Transvections A) := by
  intro h
  obtain ⟨B, hB⟩ := exists_isometry hA
  let f : PSU A →* PSU (1 : Matrix (Fin 6) (Fin 6) K) := (psuEquivOf hB).symm
  have hsymm : f '' Transvections A = Transvections (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [← image_transvections hB]
    exact image_symm_image (psuEquivOf hB) (Transvections (1 : Matrix (Fin 6) (Fin 6) K))
  have h1 : IsSymplecticType (Transvections (1 : Matrix (Fin 6) (Fin 6) K)) := by
    have := h.image f
    rwa [hsymm] at this
  let g : PSU (1 : Matrix (Fin 6) (Fin 6) K) →* U2 6 := psuOneEquivU2
  have hg : g '' Transvections (1 : Matrix (Fin 6) (Fin 6) K) = DU 6 :=
    psuOneEquivU2_image
  have h2 : IsSymplecticType (DU 6) := by
    have := h1.image g
    rwa [hg] at this
  exact not_isSymplecticType_DU (by norm_num) h2

theorem not_isSymplecticType_of_F22 {Y : Type} [Group Y] {F : Set Y} (h : F22 Y F) :
    ¬ IsSymplecticType F := by
  rintro hs
  obtain ⟨-, e, he, Hm, hHm, iso, himg⟩ := h
  have hloc := (hs.localImages e).image (iso : LocalQuotient F e →* PSU Hm)
  have himg' : ((iso : LocalQuotient F e →* PSU Hm) '' LocalImages F e) =
      Transvections Hm := himg
  rw [himg'] at hloc
  exact not_isSymplecticType_transvections hHm hloc

theorem not_isSymplecticType_of_F23 {Y : Type} [Group Y] {F : Set Y} (h : F23 Y F) :
    ¬ IsSymplecticType F := by
  rintro hs
  obtain ⟨-, e, he, h22⟩ := h
  exact not_isSymplecticType_of_F22 h22 (hs.localImages e)

theorem not_isSymplecticType_of_F24 {Y : Type} [Group Y] {F : Set Y} (h : F24 Y F) :
    ¬ IsSymplecticType F := by
  rintro hs
  obtain ⟨-, e, he, h23⟩ := h
  exact not_isSymplecticType_of_F23 h23 (hs.localImages e)

theorem hasType_not_isSymplecticType {X : Type} [Group X] {E : Set X} {k : Fin 3}
    (h : HasType k X E) : ¬ IsSymplecticType E := by
  fin_cases k
  · exact not_isSymplecticType_of_F22 h
  · exact not_isSymplecticType_of_F23 h
  · exact not_isSymplecticType_of_F24 h

end CFSG.RankThree.GF2n.Stroth78
