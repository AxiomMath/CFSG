module

public import CFSG.LocalAnalysis.StandardType.GGHalfSlOn
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

private theorem exists_perm_image_eq {n : ℕ} {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ π : Equiv.Perm (Fin n), π '' (A : Set (Fin n)) = (B : Set (Fin n)) := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq A B h
  refine ⟨π, ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hπ]
    exact Finset.mem_map_of_mem π.toEmbedding ha
  · intro hx
    rw [← hπ] at hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx
    exact ⟨a, ha, by simpa using hax⟩

theorem exists_mulEquiv_slOn_compl (m : ℕ) (P : Fin (m + 1 + 1)) :
    Nonempty (↥(slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}) ≃*
      SpecialLinearGroup (Fin (m + 1)) F2) := by
  classical
  let A : Finset (Fin (m + 1 + 1 + 1)) :=
    Finset.univ.filter (fun i => i ≠ P.castSucc ∧ i ≠ P.succ)
  let B : Finset (Fin (m + 1 + 1 + 1)) :=
    (Finset.univ : Finset (Fin (m + 1))).image (fun k => (k.succ.succ : Fin (m + 1 + 1 + 1)))
  have hAcard : A.card = m + 1 := by
    have hA' : A = ({P.castSucc, P.succ} : Finset (Fin (m + 1 + 1 + 1)))ᶜ := by
      ext i
      dsimp only [A]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    rw [hA', Finset.card_compl,
      Finset.card_pair (show P.castSucc < P.succ from Fin.castSucc_lt_succ).ne,
      Fintype.card_fin]
    omega
  have hinj : Function.Injective
      (fun k : Fin (m + 1) => (k.succ.succ : Fin (m + 1 + 1 + 1))) :=
    fun a b h => Fin.succ_injective _ (Fin.succ_injective _ h)
  have hBcard : B.card = m + 1 := by
    dsimp only [B]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hAset : (A : Set (Fin (m + 1 + 1 + 1))) = {i | i ≠ P.castSucc ∧ i ≠ P.succ} := by
    ext i
    dsimp only [A]
    simp
  have hBset : (B : Set (Fin (m + 1 + 1 + 1))) = {i | 2 ≤ i.val} := by
    ext i
    dsimp only [B]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩
      simp only [Fin.val_succ]
      omega
    · intro hi
      refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
      ext
      simp only [Fin.val_succ]
      omega
  obtain ⟨π, hπ⟩ := exists_perm_image_eq (A := A) (B := B) (by rw [hAcard, hBcard])
  have himg : π '' {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} =
      {i | 2 ≤ i.val} := by
    rw [← hAset, hπ, hBset]
  have hmap : (slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}).map
      (MulAut.conj (slPerm gf2_two π)).toMonoidHom =
      slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val} := by
    rw [slOn_map_conj_slPerm, himg]
  have hinjconj : Function.Injective (MulAut.conj (slPerm gf2_two π)).toMonoidHom :=
    fun _ _ hab => MulEquiv.injective _ hab
  exact ⟨(Subgroup.equivMapOfInjective _ _ hinjconj).trans
    ((MulEquiv.subgroupCongr hmap).trans
      ((MulEquiv.subgroupCongr (range_slLower2Hom m).symm).trans
        (MonoidHom.ofInjective (slLower2Hom_injective m)).symm))⟩

end GGHalf

end CFSG.StandardType

end
