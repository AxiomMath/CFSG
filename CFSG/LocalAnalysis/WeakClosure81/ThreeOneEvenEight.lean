module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneEightCert
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneEightE
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneEight
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneSmall
public import CFSG.Permutation.BurnsideSchur.RegularCyclic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

private theorem isSylowIn_map_of_injective {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Function.Injective f) {p : ℕ} {P H : Subgroup G}
    (h : IsSylowIn p P H) : IsSylowIn p (P.map f) (H.map f) := by
  refine ⟨Subgroup.map_mono h.le, h.isPGroup.map f, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective P H hf]
  exact h.not_dvd_relIndex

theorem eq_alternatingGroup_or_isE8L3 {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = 8) {S K : Subgroup (Perm Ω)}
    (hK : K ≤ alternatingGroup Ω) (hS : IsSylowIn 2 S (alternatingGroup Ω)) (hSK : S ≤ K)
    (h2 : MulAction.IsMultiplyPretransitive K Ω 2) : K = alternatingGroup Ω ∨ IsE8L3 K := by
  classical
  let e : Ω ≃ Fin 8 := Fintype.equivFinOfCardEq hΩ
  let φ : Perm Ω ≃* Perm (Fin 8) := e.permCongrHom
  let K8 : Subgroup (Perm (Fin 8)) := K.map φ.toMonoidHom
  let S8 : Subgroup (Perm (Fin 8)) := S.map φ.toMonoidHom
  have hAgmap : (alternatingGroup Ω).map φ.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [Subgroup.map_equiv_eq_comap_symm' (f := φ) (K := alternatingGroup Ω)]
    ext x
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup,
      Equiv.Perm.mem_alternatingGroup]
    have hsign : Perm.sign (φ.symm x) = Perm.sign x := by
      simpa [φ, Equiv.permCongrHom_symm] using Equiv.Perm.sign_permCongr e.symm x
    change Perm.sign (φ.symm x) = 1 ↔ Perm.sign x = 1
    rw [hsign]
  have hS8 : IsSylowIn 2 S8 (alternatingGroup (Fin 8)) := by
    have h := isSylowIn_map_of_injective (f := φ.toMonoidHom) φ.injective hS
    rw [hAgmap] at h
    simpa [S8] using h
  have hK8 : K8 ≤ alternatingGroup (Fin 8) := by
    calc K8 = K.map φ.toMonoidHom := rfl
      _ ≤ (alternatingGroup Ω).map φ.toMonoidHom := Subgroup.map_mono hK
      _ = alternatingGroup (Fin 8) := hAgmap
  have hSK8 : S8 ≤ K8 := by
    simpa [S8, K8] using Subgroup.map_mono hSK
  have hcardK8 : Nat.card K8 = Nat.card K := by
    simpa [K8] using Subgroup.card_map_of_injective (K := K) (f := φ.toMonoidHom) φ.injective
  have h56 : 56 ∣ Nat.card K := by
    have h := card_mul_pred_dvd_card (Ω := Ω) (by omega) h2
    simpa [hΩ] using h
  have hcases : Nat.card K8 = 1344 ∨ Nat.card K8 = 20160 := by
    rcases card_mem_of_le_alternatingGroup_eight (S := S8) (K := K8) hK8 hS8 hSK8 with
      h | h | h | h | h
    · exfalso
      rw [← hcardK8, h] at h56
      norm_num at h56
    · exfalso
      rw [← hcardK8, h] at h56
      norm_num at h56
    · exfalso
      rw [← hcardK8, h] at h56
      norm_num at h56
    · exact Or.inl h
    · exact Or.inr h
  have hKback : K8.map φ.symm.toMonoidHom = K := by
    have h := (Subgroup.map_symm_eq_iff_map_eq (H := K8) (K := K) (e := φ)).mpr rfl
    simpa using h
  have hcardAg : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rcases hcases with h1344 | h20160
  · right
    have h2_8 : MulAction.IsMultiplyPretransitive K8 (Fin 8) 2 := by
      have h :=
        (CFSG.BurnsideSchur.isMultiplyPretransitive_map_permCongrHom_iff e K 2).mpr h2
      simpa [K8, φ] using h
    have hne : K8 ≠ alternatingGroup (Fin 8) := by
      intro heq
      have hc : Nat.card K8 = Nat.card (alternatingGroup (Fin 8)) := by rw [heq]
      rw [h1344, hcardAg] at hc
      norm_num at hc
    obtain ⟨Q8, hQ8K, hQ8norm, hQ8two, hQ8cent⟩ :=
      exists_le_inf_centralizer_le (S := S8) (K := K8) hK8 hS8 hSK8 hne
    have hElem := isElemAbelian_of_isMultiplyPretransitive (Ω := Fin 8) (by norm_num)
      h2_8 hQ8K hQ8norm hQ8two hQ8cent
    have hE8 : IsE8L3 K8 :=
      isE8L3_of_isElemAbelian h1344 hQ8K hQ8norm hElem.1 hElem.2 hQ8cent
    have hmap := hE8.map φ.symm.toMonoidHom φ.symm.injective
    rwa [hKback] at hmap
  · left
    have hK8eq : K8 = alternatingGroup (Fin 8) :=
      Subgroup.eq_of_le_of_card_ge hK8 (by rw [h20160, hcardAg])
    calc K = K8.map φ.symm.toMonoidHom := hKback.symm
      _ = (alternatingGroup (Fin 8)).map φ.symm.toMonoidHom := by rw [hK8eq]
      _ = alternatingGroup Ω :=
        (Subgroup.map_symm_eq_iff_map_eq (H := alternatingGroup (Fin 8))
          (K := alternatingGroup Ω) (e := φ)).mpr hAgmap

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
