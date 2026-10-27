module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3InvA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.eq_one_of_kBar_fix (h : ThreeNat A L T) {k : MulAut W}
    (hk : k ∈ s1t3KBar A L) (hfix : ∀ J ∈ irrSet L, J.map k.toMonoidHom = J) : k = 1 := by
  have hkA : k ∈ A := hk.1
  have hkC : k ∈ Subgroup.centralizer (L : Set (MulAut W)) := hk.2
  have hkN : k ∈ Subgroup.normalizer (L : Set (MulAut W)) := h.normal hkA
  have hfixVmap : (fixV L).map k.toMonoidHom = fixV L :=
    s16t3_inv_map_fixV_normalizer (E := L) hkN
  have hkfixV : ∀ w : W, k w ∈ fixV L ↔ w ∈ fixV L := by
    intro w
    have h1 : k w ∈ (fixV L).map k.toMonoidHom ↔ w ∈ fixV L :=
      Subgroup.mem_map_iff_mem (f := k.toMonoidHom) (x := w) k.injective
    rw [hfixVmap] at h1
    exact h1
  have hJu : ∀ J ∈ irrSet L, ∀ u : ↥J, k (u : W) * (u : W)⁻¹ ∈ fixV L := by
    intro J hJ
    have hJnat : SumOfNatShape L J (J ⊓ fixV L) 1 := h.natural_of_mem_irrSet hJ
    let φ : ↥J ≃* ↥J :=
      { toFun := fun u => ⟨k (u : W), by
          have h : k (u : W) ∈ J.map k.toMonoidHom := ⟨(u : W), u.2, rfl⟩
          rwa [hfix J hJ] at h⟩
        invFun := fun u => ⟨k⁻¹ (u : W), by
          have h : (u : W) ∈ J.map k.toMonoidHom := by rw [hfix J hJ]; exact u.2
          obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 h
          have hvv : k⁻¹ (u : W) = v := by
            rw [← hvu]; exact MulAut.inv_apply_self W k v
          rw [hvv]; exact hv⟩
        left_inv := fun u => Subtype.ext (MulAut.inv_apply_self W k (u : W))
        right_inv := fun u => Subtype.ext (MulAut.apply_inv_self W k (u : W))
        map_mul' := fun u v => Subtype.ext (map_mul k (u : W) (v : W)) }
    have hφval : ∀ u : ↥J, ((φ u : ↥J) : W) = k (u : W) := fun u => rfl
    have hZ : ∀ u : ↥J,
        ((φ u : ↥J) : W) ∈ J ⊓ fixV L ↔ (u : W) ∈ J ⊓ fixV L := by
      intro u
      have h1 : ((φ u : ↥J) : W) = k (u : W) := hφval u
      constructor
      · rintro ⟨-, hf⟩
        exact ⟨u.2, (hkfixV (u : W)).1 (h1 ▸ hf)⟩
      · rintro ⟨-, hf⟩
        exact ⟨(φ u).2, h1.symm ▸ (hkfixV (u : W)).2 hf⟩
    have hφ : ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
        ((φ ⟨l (u : W), hu⟩ : ↥J) : W) * (l ((φ u : ↥J) : W))⁻¹ ∈ J ⊓ fixV L := by
      intro l hl u hu
      have h1 : ((φ ⟨l (u : W), hu⟩ : ↥J) : W) = k (l (u : W)) := hφval _
      have h2 : ((φ u : ↥J) : W) = k (u : W) := hφval u
      have hcomm : k * l = l * k := ((Subgroup.mem_centralizer_iff.1 hkC) l hl).symm
      have hklu : k (l (u : W)) = l (k (u : W)) := by
        have := congrArg (fun m : MulAut W => m (u : W)) hcomm
        simpa [MulAut.mul_apply] using this
      rw [h1, h2, hklu, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hres := SumOfNatShape.eq_of_equivariant h.quasi hJnat φ hZ hφ
    intro u
    have hmem := (Subgroup.mem_inf.1 (hres u)).2
    rwa [hφval u] at hmem
  let S : Subgroup W := (fixV L).comap (commHom k)
  have hSle : ∀ w : W, w ∈ S ↔ k w * w⁻¹ ∈ fixV L := by
    intro w
    show commHom k w ∈ fixV L ↔ k w * w⁻¹ ∈ fixV L
    rw [commHom_apply]
  have hZS : fixV L ≤ S := by
    intro z hz
    rw [hSle z]
    exact Subgroup.mul_mem _ ((hkfixV z).2 hz) (Subgroup.inv_mem _ hz)
  have hJS : ∀ J ∈ irrSet L, J ≤ S := by
    intro J hJ u hu
    rw [hSle u]
    exact hJu J hJ ⟨u, hu⟩
  have htopS : (⊤ : Subgroup W) ≤ S := by
    obtain ⟨I, hZI, -, hsup, hnat⟩ := s16t3_summands h.sum
    rw [← hsup]
    refine sup_le hZS ?_
    refine iSup_le fun i => ?_
    obtain ⟨hIr, -, hIZ⟩ := s16t3_commSub_mem_irrSet_of_natural h.quasi (hZI i) (hnat i)
    calc I i = commSub (I i) L ⊔ fixV L := hIZ.symm
      _ ≤ S := sup_le (hJS (commSub (I i) L) hIr) hZS
  have hSeqTop : S = ⊤ := le_antisymm le_top htopS
  exact h.faithful k hkA
    (fun w => (hSle w).1 (by rw [hSeqTop]; exact Subgroup.mem_top w))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
