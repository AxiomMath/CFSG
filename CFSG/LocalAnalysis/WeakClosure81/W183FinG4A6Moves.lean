module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6S6
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6DynA
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6MovesModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem w183finG4A6_br2DynkinMoves_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) : Br2DynkinMoves M (w183finG4A6AutS6 e) := by
  classical
  obtain ⟨f, hf_inj, hf_aut, hf_surj, -, hf_s6⟩ := w183finG4A6_exists_model e
  intro P₀ hP₀ A hA_le hA_el hA8 _ τ hτP hτacts hτA
  have hX₀map : (w183finG4A6AutS6 e).map f = A6Facts.s6 := by
    ext y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact (hf_s6 γ).1 hγ
    · intro hy
      obtain ⟨γ, hγ⟩ := hf_surj y (A6Facts.s6_le_autA6 hy)
      exact ⟨γ, (hf_s6 γ).2 (hγ ▸ hy), hγ⟩
  have hP₀' : IsSylowIn 2 (P₀.map f) A6Facts.s6 := by
    have h := w183finG4A6_isSylowIn_map f hf_inj hP₀
    rwa [hX₀map] at h
  have hA' : A.map f ≤ P₀.map f := Subgroup.map_mono hA_le
  have hA_el' : IsElemAbelian 2 (A.map f) := hA_el.map f
  have hA8' : 8 ≤ Nat.card (A.map f) := by
    rw [Subgroup.card_map_of_injective hf_inj]
    exact hA8
  have hτ's6 : f τ ∉ A6Facts.s6 := by
    intro h
    exact w183finG4A6_not_mem_autS6_of_acts e τ hτacts ((hf_s6 τ).2 h)
  have hτ'P : f τ ∈ Subgroup.normalizer ((P₀.map f : Subgroup (Equiv.Perm (Fin 10))) :
      Set (Equiv.Perm (Fin 10))) := Subgroup.le_normalizer_map f ⟨τ, hτP, rfl⟩
  have hnot := w183finG4A6_model_dynkin_moves (P₀.map f) (A.map f) hP₀' hA' hA_el' hA8'
    (f τ) (hf_aut τ) hτ's6 hτ'P
  exact hnot (Subgroup.le_normalizer_map f ⟨τ, hτA, rfl⟩)

end CFSG.LocalAnalysis.WeakClosure81

end
