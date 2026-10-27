
module

public import CFSG.Sporadic.Ly.Action
public import CFSG.RankThree.Native.LyOperatorData

@[expose] public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix

@[expose] def lyA0 : Equiv.Perm (Fin lyN) := MulAction.toPerm (a : J)

@[expose] def lyA1 : Equiv.Perm (Fin lyN) := MulAction.toPerm (b : J)

@[expose] def lyP : Subgroup (Equiv.Perm (Fin lyN)) := Subgroup.closure {lyA0, lyA1}

@[expose] def lyPhi : J →* Equiv.Perm (Fin lyN) := MulAction.toPermHom J (Fin lyN)

theorem lyPhi_apply (g : J) (i : Fin lyN) : lyPhi g i = g • i := rfl

theorem lyPhi_a : lyPhi a = lyA0 := rfl

theorem lyPhi_b : lyPhi b = lyA1 := rfl

theorem lyPhi_range : lyPhi.range = lyP := by
  rw [MonoidHom.range_eq_map, ← closure_ab, MonoidHom.map_closure, lyP, Set.image_pair, lyPhi_a,
    lyPhi_b]

theorem lyPhi_mem (g : J) : lyPhi g ∈ lyP := by
  rw [← lyPhi_range]
  exact ⟨g, rfl⟩

@[expose] def lyPhiP : J →* lyP := lyPhi.codRestrict lyP lyPhi_mem

theorem lyPhiP_apply (g : J) : (lyPhiP g : Equiv.Perm (Fin lyN)) = lyPhi g := rfl

theorem lyPhiP_surjective : Function.Surjective lyPhiP := by
  rintro ⟨p, hp⟩
  rw [← lyPhi_range] at hp
  obtain ⟨g, rfl⟩ := hp
  exact ⟨g, rfl⟩

end CFSG.RankThree.Native
