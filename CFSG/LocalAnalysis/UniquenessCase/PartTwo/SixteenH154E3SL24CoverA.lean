module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ID
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_normalizer_cent_Z_aux (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hnZ : ∀ z ∈ commSub ⊤ L ⊓ fixV L, n z = z) :
    ∃ l ∈ L, ∀ u ∈ commSub ⊤ L, n u = l u := by
  obtain ⟨ψ, π, hπ, hact, hZcorr⟩ := s16h_sl24_cover_model hW hrow hZ4
  have hnU : n ∈ stabSub (commSub ⊤ L) :=
    StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := n) (by intro u; simp) hn
  let nU : MulAut ↥(commSub ⊤ L) := resHom (commSub ⊤ L) ⟨n, hnU⟩
  let nM : MulAut Orth3 := MulAut.congr ψ nU
  have horth3L := s16h_sl24_cover_orth3L_eq_map_autSub (L := L) hπ hact
  have hnU_norm : nU ∈ Subgroup.normalizer
      (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) :=
    s16h_sl24_cover_resHom_normalizer (L := L) hn hnU
  have hnM_norm : nM ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) := by
    rw [horth3L]
    exact Subgroup.le_normalizer_map (MulAut.congr ψ).toMonoidHom ⟨nU, hnU_norm, rfl⟩
  have hnM_Z : ∀ z ∈ orth3Z, nM z = z := by
    intro z hz
    have hmem : ((ψ.symm z : ↥(commSub ⊤ L)) : W) ∈ commSub ⊤ L ⊓ fixV L :=
      ⟨(ψ.symm z).2, (hZcorr (ψ.symm z)).mpr (by simpa using hz)⟩
    have hfix : n ((ψ.symm z : ↥(commSub ⊤ L)) : W) =
        ((ψ.symm z : ↥(commSub ⊤ L)) : W) := hnZ _ hmem
    have hnUfix : nU (ψ.symm z) = ψ.symm z := by
      apply Subtype.ext
      simp only [nU, resHom_apply, hfix]
    show ψ (nU (ψ.symm z)) = z
    rw [hnUfix, MulEquiv.apply_symm_apply]
  have hnM_L : nM ∈ orth3L := s16h_orth3_kernel_Z hnM_norm hnM_Z
  rw [horth3L] at hnM_L
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hnM_L
  obtain ⟨g, hgL, hgφ⟩ := mem_autSub.mp hφ
  have hnU_eq : nU = resHom (commSub ⊤ L) g := by
    apply (MulAut.congr ψ).injective
    rw [hgφ]
    exact hφeq.symm
  refine ⟨(g : MulAut W), hgL, fun u hu => ?_⟩
  have hval : nU ⟨u, hu⟩ = resHom (commSub ⊤ L) g ⟨u, hu⟩ := by rw [hnU_eq]
  simpa [nU, resHom_apply] using
    congrArg (fun x : ↥(commSub ⊤ L) => (x : W)) hval

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
