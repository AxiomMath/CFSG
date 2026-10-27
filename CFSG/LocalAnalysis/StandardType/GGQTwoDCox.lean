module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxPat

public section

namespace CFSG.StandardType.QTwo

theorem qtwo_exists_conj_of_card_lt {m : ℕ} (hm : 4 ≤ m) {T : Finset (Fin m)}
    (hT : (dSuppSet T).card < m) :
    ∃ w : (ggCoxeterMatrixD m).Group, ∀ t ∈ T,
      w * (ggCoxeterMatrixD m).simple t * w⁻¹ ∈ qtwoParabRefl m := by
  obtain ⟨e, he⟩ := dEven_equiv hm
  obtain ⟨c, hc⟩ := exists_coord_not_mem_of_card_lt hT
  let z : Fin m := ⟨0, by omega⟩
  let π : Equiv.Perm (Fin m) := Equiv.swap c z
  refine ⟨dPermW e π, fun t ht => dPermW_conj_simple_mem hm he π t ?_ ?_⟩
  · intro h0
    have hπz : π (OrthTorus.simpleLo t) = z := Fin.ext (by simpa [z] using h0)
    have hne : OrthTorus.simpleLo t ≠ c :=
      fun h => hc (by simpa [h] using simpleLo_mem_dSuppSet ht)
    apply hne
    have h' := hπz
    change Equiv.swap c z (OrthTorus.simpleLo t) = z at h'
    rw [Equiv.swap_apply_eq_iff] at h'
    simpa using h'
  · intro h0
    have hπz : π (OrthTorus.simpleHi t) = z := Fin.ext (by simpa [z] using h0)
    have hne : OrthTorus.simpleHi t ≠ c :=
      fun h => hc (by simpa [h] using simpleHi_mem_dSuppSet ht)
    apply hne
    have h' := hπz
    change Equiv.swap c z (OrthTorus.simpleHi t) = z at h'
    rw [Equiv.swap_apply_eq_iff] at h'
    simpa using h'

theorem qtwo_exists_conj_into_parab_pairA3 {m : ℕ} (hm : 5 ≤ m) {T : Finset (Fin m)}
    (hT : (∃ i j, i ≠ j ∧ T = {i, j}) ∨
      (∃ i j k, ggCoxeterMatrixD m i j = 3 ∧ ggCoxeterMatrixD m j k = 3 ∧
        ggCoxeterMatrixD m i k = 2 ∧ T = {i, j, k})) :
    ∃ w : (ggCoxeterMatrixD m).Group, ∀ t ∈ T,
      w * (ggCoxeterMatrixD m).simple t * w⁻¹ ∈ qtwoParabRefl m := by
  rcases hT with ⟨i, j, -, hT⟩ | ⟨i, j, k, h1, h2, -, hT⟩
  · exact qtwo_exists_conj_of_card_lt (by omega)
      (lt_of_le_of_lt (dSuppSet_card_le_of_pair hT) (by omega))
  · exact qtwo_exists_conj_of_card_lt (by omega)
      (lt_of_le_of_lt (dSuppSet_card_le_of_A3 (by omega) h1 h2 hT) (by omega))

theorem qtwo_exists_conj_into_parab {m : ℕ} (hm : 7 ≤ m) {T : Finset (Fin m)}
    (hT : QTwoPattern m T) :
    ∃ w : (ggCoxeterMatrixD m).Group, ∀ t ∈ T,
      w * (ggCoxeterMatrixD m).simple t * w⁻¹ ∈ qtwoParabRefl m :=
  qtwo_exists_conj_of_card_lt (by omega)
    (lt_of_le_of_lt (dSuppSet_card_le (by omega) hT) (by omega))

theorem qtwoParabConj : QTwoParabConj :=
  fun _ hm _ hT => qtwo_exists_conj_into_parab hm hT

end CFSG.StandardType.QTwo

end
