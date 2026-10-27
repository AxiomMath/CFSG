module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordHA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordHB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_isoMod_trans {L : Subgroup (MulAut W)} {A B C : Subgroup W}
    (hAB : H.Pair.IsoMod L A B) (hBC : H.Pair.IsoMod L B C) : H.Pair.IsoMod L A C := by
  obtain ⟨e₁, he₁⟩ := hAB
  obtain ⟨e₂, he₂⟩ := hBC
  refine ⟨e₁.trans e₂, fun l hl w hw => ?_⟩
  have hmem : l ((e₁ w : B) : W) ∈ B := he₁ l hl w hw ▸ (e₁ ⟨l w, hw⟩).2
  have h1 : e₁ ⟨l w, hw⟩ = ⟨l ((e₁ w : B) : W), hmem⟩ := Subtype.ext (he₁ l hl w hw)
  calc ((e₁.trans e₂) ⟨l w, hw⟩ : W) = (e₂ (e₁ ⟨l w, hw⟩) : W) := rfl
    _ = (e₂ ⟨l ((e₁ w : B) : W), hmem⟩ : W) := by rw [h1]
    _ = l ((e₂ (e₁ w)) : W) := he₂ l hl (e₁ w) hmem
    _ = l (((e₁.trans e₂) w : C) : W) := rfl

theorem s16h_e3_l3_homog {W : Type} [CommGroup W] [Finite W] {L Y : Subgroup (MulAut W)}
    {I : Fin 3 → Subgroup W} (hirr : ∀ i, I i ∈ irrSet L) (hfix : ∀ i, I i ⊓ fixV L = ⊥)
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥)
    (hU : (⊥ ⊔ ⨆ i, I i) = commSub ⊤ L)
    (hY : Y ≤ normalizer (L : Set (MulAut W)))
    (htrans : ∀ J₁ ∈ irrSet L, ∀ J₂ ∈ irrSet L, ∃ g ∈ Y, J₂ = J₁.map g.toMonoidHom)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hiso : H.Pair.IsoMod L (I i) (I j)) : H.Pair.IsoMod L (I i) (I k) := by
  by_contra hnot
  have hInv : ∀ m, H.Pair.IsInv L (I m) := fun m => (hirr m).2.2.1
  have hnotik : ¬ H.Pair.IsoMod L (I k) (I i) :=
    fun h => hnot (H.Pair.IsoMod.symm (hInv k) h)
  have hnotkj : ¬ H.Pair.IsoMod L (I k) (I j) :=
    fun h => hnotik (s16h_e3_isoMod_trans h (H.Pair.IsoMod.symm (hInv i) hiso))
  obtain ⟨g, hgY, hg⟩ := htrans (I k) (hirr k) (I i) (hirr i)
  have hgnorm : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := hY hgY
  have hgnorm' : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.inv_mem _ hgnorm
  have hJmem : (I j).map g⁻¹.toMonoidHom ∈ irrSet L :=
    CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
      (fun x hx => inv_conj_mem_of_mem_normalizer hgnorm hx)
      (fun x hx => conj_mem_of_mem_normalizer hgnorm hx) (hirr j)
  have hJiso : H.Pair.IsoMod L ((I j).map g⁻¹.toMonoidHom) (I k) := by
    have h1 : H.Pair.IsoMod L ((I j).map g⁻¹.toMonoidHom) ((I i).map g⁻¹.toMonoidHom) :=
      s16h_e3_isoMod_map hgnorm' (H.Pair.IsoMod.symm (hInv i) hiso)
    have h2 : (I i).map g⁻¹.toMonoidHom = I k := by
      rw [hg, Subgroup.map_map]
      have hcomp : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
        ext w; simp
      rw [hcomp, Subgroup.map_id]
    rwa [h2] at h1
  have hJeq : (I j).map g⁻¹.toMonoidHom = I k :=
    s16h_e3_eq_of_iso_of_irr hij hik hjk hirr hfix hind hU hnotik hnotkj hJmem hJiso
  have hgi : (I i).map g⁻¹.toMonoidHom = I k := by
    rw [hg, Subgroup.map_map]
    have hcomp : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
      ext w; simp
    rw [hcomp, Subgroup.map_id]
  have hji : I j = I i := by
    have h1 : ((I j).map g⁻¹.toMonoidHom).map g.toMonoidHom =
        ((I i).map g⁻¹.toMonoidHom).map g.toMonoidHom := by rw [hJeq, hgi]
    rw [Subgroup.map_map, Subgroup.map_map] at h1
    have hcomp : g.toMonoidHom.comp g⁻¹.toMonoidHom = MonoidHom.id W := by
      ext w; simp
    rw [hcomp, Subgroup.map_id, Subgroup.map_id] at h1
    exact h1
  have hIij_inf : I i ⊓ I j = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf le_rfl ((le_iSup (fun _ : j ≠ i => I j) (Ne.symm hij)).trans
      (le_iSup (fun n : Fin 3 => ⨆ (_ : n ≠ i), I n) j))) ?_
    simpa only [bot_sup_eq] using hind i
  have hIirr : H.Pair.IsIrr L (I i) := by
    have h := (hirr i).2
    rw [hfix i] at h
    exact ⟨h.1.ne', fun U hU hUi => h.2.2.2 U hUi bot_le hU⟩
  exact hIirr.1 (by
    have : I i ⊓ I j = I i := by rw [hji.symm, inf_idem]
    rw [← this]
    exact hIij_inf)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
