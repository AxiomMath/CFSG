module

public import CFSG.LocalAnalysis.UniquenessCase.K340.Vocab
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_conjSetOf_self (X F : Subgroup G) : F ∈ conjSetOf X F := by
  refine ⟨1, X.one_mem, ?_⟩
  simp [MulAut.one_def]

private theorem le_conjClosure_self (X F : Subgroup G) : F ≤ conjClosure X F := by
  rw [conjClosure]
  exact le_iSup₂_of_le F (mem_conjSetOf_self X F) le_rfl

private theorem conj_mul_eq_commutator_mul (u f : G) : u * f * u⁻¹ = ⁅u, f⁆ * f := by
  rw [commutatorElement_def]
  group

private theorem map_conj_le_of_commutator_le {K X F : Subgroup G}
    (h : ∀ x ∈ X, ⁅K, F.map (MulAut.conj x).toMonoidHom⁆ ≤ F)
    {u : G} (hu : u ∈ K) :
    (conjClosure X F).map (MulAut.conj u).toMonoidHom ≤ conjClosure X F := by
  have hgen : ∀ x ∈ X,
      (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj u).toMonoidHom ≤
        conjClosure X F := by
    intro x hx
    have hFx : F.map (MulAut.conj x).toMonoidHom ≤ conjClosure X F := by
      rw [conjClosure]
      exact le_iSup₂_of_le (F.map (MulAut.conj x).toMonoidHom) ⟨x, hx, rfl⟩ le_rfl
    have hle : (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj u).toMonoidHom ≤
        F ⊔ F.map (MulAut.conj x).toMonoidHom := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.mp hf
      change MulAut.conj u (MulAut.conj x f₀) ∈ F ⊔ F.map (MulAut.conj x).toMonoidHom
      rw [MulAut.conj_apply, MulAut.conj_apply, conj_mul_eq_commutator_mul]
      refine Subgroup.mul_mem_sup (h x hx ?_) ?_
      · exact Subgroup.commutator_mem_commutator hu
          (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hf₀)
      · exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hf₀
    exact le_trans hle (sup_le (le_conjClosure_self X F) hFx)
  rw [conjClosure, Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  obtain ⟨x, hx, rfl⟩ := hK
  exact hgen x hx

theorem le_normalizer_conjClosure_of_commutator_le {K X F : Subgroup G}
    (h : ∀ x ∈ X, ⁅K, F.map (MulAut.conj x).toMonoidHom⁆ ≤ F) :
    K ≤ Subgroup.normalizer (conjClosure X F : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun u hu c hc => ?_
  exact map_conj_le_of_commutator_le h hu
    (Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hc)

theorem not_thompsonJ_le_pCore_of {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T)
    (hJQ : ¬ thompsonJ T ≤ CFSG.Open.pCoreOf 2 H) :
    ¬ CFSG.Quasithin.thompsonJ (P : Subgroup ↥H) ≤ CFSG.pCore 2 ↥H := by
  intro hJ
  apply hJQ
  have hm : (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)).map H.subtype ≤
      (CFSG.pCore 2 ↥H).map H.subtype := Subgroup.map_mono hJ
  rw [map_thompsonJ_sylow P hP] at hm
  simpa only [CFSG.Open.pCoreOf] using hm

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
