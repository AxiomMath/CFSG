module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1ABAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenHyper

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_e3_irrSet_L3_le_commSub {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet L) :
    I ≤ commSub (⊤ : Subgroup W) L := by
  calc I = commSub I L := hI.1.symm
    _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl

private theorem s16h_e3_matrix_fixed_by_gl_eq_zero
    (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : ∀ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M = M) :
    M = 0 := by
  ext j k
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
    fin_cases j
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  have hv : (Matrix.transvection i j (1 : ZMod 2) * M) i k = M i k := by
    have := congrFun (congrFun (h (Matrix.GeneralLinearGroup.transvection i j hij 1)) i) k
    simpa using this
  rw [Matrix.transvection_mul_apply_same] at hv
  have hv' : M i k + M j k = M i k + 0 := by simpa using hv
  exact (add_left_cancel_iff).mp hv'

theorem s16h_e3_fixV_inf_commSub_eq_bot {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U) :
    fixV L ⊓ commSub (⊤ : Subgroup W) L = ⊥ := by
  rw [hU, eq_bot_iff]
  intro u hu
  obtain ⟨hfix, hU'⟩ := hu
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := Multiplicative.toAdd (C.ψ ⟨u, hU'⟩)
  have hM : ∀ l : ↥L, (C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M = M := by
    intro l
    have hlu : (l : MulAut W) u ∈ U := by
      rw [hfix (l : MulAut W) l.2]; exact hU'
    have heq : (⟨(l : MulAut W) u, hlu⟩ : ↥U) = ⟨u, hU'⟩ := by
      exact Subtype.ext (hfix (l : MulAut W) l.2)
    have hψ := C.equivariant l u hU' hlu
    rw [heq] at hψ
    have h2 : M = (C.ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M := by
      have := congrArg Multiplicative.toAdd hψ
      simpa [M] using this
    exact h2.symm
  have hGL : ∀ g : GL (Fin 3) (ZMod 2),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M = M := by
    intro g
    obtain ⟨l, rfl⟩ := C.ρ.surjective g
    exact hM l
  have hM0 : M = 0 := s16h_e3_matrix_fixed_by_gl_eq_zero M hGL
  have h1 : C.ψ ⟨u, hU'⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    exact hM0
  have h2 : (⟨u, hU'⟩ : ↥U) = 1 := by
    apply C.ψ.injective
    simpa using h1
  simpa using congrArg Subtype.val h2

private theorem s16h_l3MatImage_isMin {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U) {I : Subgroup W} (hI : I ∈ irrSet L) :
    s16h_IsMinLeftInvMat (s16h_l3MatImage C I) := by
  have hIle : I ≤ U := by
    rw [← hU]
    exact s16h_e3_irrSet_L3_le_commSub hI
  obtain ⟨hcomm, hirr⟩ := hI
  have hIfix : I ⊓ fixV L = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hmem : w ∈ fixV L ⊓ commSub (⊤ : Subgroup W) L := ⟨hw.2, hU ▸ hIle hw.1⟩
    rw [s16h_e3_fixV_inf_commSub_eq_bot hU C] at hmem
    exact hmem
  have hirr' : IsIrrOn L I ⊥ := by rwa [hIfix] at hirr
  have hIne : I ≠ ⊥ := bot_lt_iff_ne_bot.mp hirr'.1
  refine ⟨?_, ?_, ?_⟩
  · intro hbot
    obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIne
    have hwneW : (w : W) ≠ 1 := fun h => hwne (Subtype.ext h)
    let u : ↥U := ⟨(w : W), hIle w.2⟩
    have hu_ne : u ≠ 1 := fun h => hwneW (congrArg Subtype.val h)
    have hm_ne : Multiplicative.toAdd (C.ψ u) ≠ 0 := by
      intro h0
      have h1 : C.ψ u = 1 := by
        calc C.ψ u = Multiplicative.ofAdd (Multiplicative.toAdd (C.ψ u)) :=
              (ofAdd_toAdd _).symm
          _ = Multiplicative.ofAdd 0 := by rw [h0]
          _ = 1 := by rw [ofAdd_zero]
      exact hu_ne (C.ψ.injective (by rw [h1, map_one]))
    have hu_mem : Multiplicative.toAdd (C.ψ u) ∈ s16h_l3MatImage C I :=
      (s16h_l3MatImage_mem_iff C).mpr ⟨u, w.2, (ofAdd_toAdd _).symm⟩
    rw [hbot] at hu_mem
    exact hm_ne (by simpa using hu_mem)
  · intro g m hm
    rw [s16h_l3MatImage_mem_iff] at hm ⊢
    obtain ⟨u, huI, rfl⟩ := hm
    obtain ⟨l, rfl⟩ := C.ρ.surjective g
    refine ⟨⟨(l : MulAut W) (u : W), hIle (hirr'.2.1 l l.2 (u : W) huI)⟩,
      hirr'.2.1 l l.2 (u : W) huI, ?_⟩
    exact C.equivariant l (u : W) u.2 _
  · intro K hKle hKinv
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · right
      set IK : Subgroup W := I ⊓ s16h_l3Preimage C K with hIK
      have hIKstab : StableUnder L IK := by
        intro l hl w hw
        obtain ⟨hwI, hwpre⟩ := hw
        change w ∈ s16h_l3Preimage C K at hwpre
        rw [s16h_l3Preimage_mem_iff] at hwpre
        obtain ⟨hwU, hwK⟩ := hwpre
        have hluI : (l : MulAut W) w ∈ I := hirr'.2.1 l hl w hwI
        refine ⟨hluI, ?_⟩
        change (l : MulAut W) w ∈ s16h_l3Preimage C K
        rw [s16h_l3Preimage_mem_iff]
        refine ⟨hIle hluI, ?_⟩
        have heq := C.equivariant (⟨l, hl⟩ : ↥L) w hwU (hIle hluI)
        rw [heq, toAdd_ofAdd]
        exact hKinv (C.ρ ⟨l, hl⟩)
          (Multiplicative.toAdd (C.ψ ⟨w, hwU⟩)) hwK
      rcases hirr'.2.2.2 IK hIKstab bot_le inf_le_left with h | h
      · exfalso
        rcases AddSubgroup.ne_bot_iff_exists_ne_zero.mp hKbot with ⟨m, hmne⟩
        have hmK : (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ K := m.2
        have hmne' : (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 := by simpa using hmne
        have hmI : (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ s16h_l3MatImage C I := hKle hmK
        rw [s16h_l3MatImage_mem_iff] at hmI
        obtain ⟨u, huI, hψ⟩ := hmI
        have huPre : (u : W) ∈ s16h_l3Preimage C K := by
          rw [s16h_l3Preimage_mem_iff]
          refine ⟨u.2, ?_⟩
          have hsub : (⟨(u : W), u.2⟩ : ↥U) = u := Subtype.ext rfl
          rw [hsub, hψ]
          simpa using hmK
        have huIK : (u : W) ∈ IK := ⟨huI, huPre⟩
        rw [h] at huIK
        rw [Subgroup.mem_bot] at huIK
        have hu1 : u = 1 := Subtype.ext huIK
        have hm0 : (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
          have h1 : Multiplicative.ofAdd (m : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
            rw [← hψ, hu1, map_one]
          have := congrArg Multiplicative.toAdd h1
          simpa using this
        exact hmne' hm0
      · have hpre : I ≤ s16h_l3Preimage C K := by
          rw [← h]
          exact inf_le_right
        apply le_antisymm hKle
        intro m hm
        rw [s16h_l3MatImage_mem_iff] at hm
        obtain ⟨u, huI, hψ⟩ := hm
        have huPre : (u : W) ∈ s16h_l3Preimage C K := hpre huI
        rw [s16h_l3Preimage_mem_iff] at huPre
        obtain ⟨hwU, hK⟩ := huPre
        have hsub : (⟨(u : W), hwU⟩ : ↥U) = u := Subtype.ext rfl
        rw [hsub, hψ] at hK
        simpa using hK

private theorem s16h_l3Preimage_mem_irrSet {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U)
    {J : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))} (hJ : s16h_IsMinLeftInvMat J) :
    s16h_l3Preimage C J ∈ irrSet L := by
  obtain ⟨hJne, hJinv, hJmin⟩ := hJ
  set I : Subgroup W := s16h_l3Preimage C J with hIdef
  have hIle : I ≤ U := by
    intro w hw
    rw [hIdef, s16h_l3Preimage_mem_iff] at hw
    exact hw.choose
  have hUstab : StableUnder L U := by
    rw [← hU]
    intro a ha c hc
    exact s16c167_commSub_stable (C := (⊤ : Subgroup W)) (X := L) (g := a)
      (fun c _ => trivial) (fun x hx => L.mul_mem (L.mul_mem ha hx) (L.inv_mem ha)) hc
  have hIstab : StableUnder L I := by
    intro l hl w hw
    rw [hIdef, s16h_l3Preimage_mem_iff] at hw ⊢
    obtain ⟨hwU, hwK⟩ := hw
    have hlwU : (l : MulAut W) w ∈ U := hUstab l hl w hwU
    refine ⟨hlwU, ?_⟩
    have heq := C.equivariant (⟨l, hl⟩ : ↥L) w hwU hlwU
    rw [heq, toAdd_ofAdd]
    exact hJinv (C.ρ ⟨l, hl⟩)
      (Multiplicative.toAdd (C.ψ ⟨w, hwU⟩)) hwK
  have hIfixbot : I ⊓ fixV L = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hmem : w ∈ fixV L ⊓ commSub (⊤ : Subgroup W) L := ⟨hw.2, hU ▸ hIle hw.1⟩
    rw [s16h_e3_fixV_inf_commSub_eq_bot hU C] at hmem
    exact hmem
  have hIimage : s16h_l3MatImage C I = J := by
    rw [hIdef, s16h_l3MatImage_preimage]
  have hIne : I ≠ ⊥ := by
    intro hbot
    apply hJne
    rw [← s16h_l3MatImage_preimage C J, ← hIdef, hbot, s16h_l3MatImage_bot]
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · exact commSub_le_of_invariant hIstab
    · have hCIstab : StableUnder L (commSub I L) := by
        intro l hl c hc
        exact s16c167_commSub_stable (C := I) (X := L) (g := l)
          (fun c hc => hIstab l hl c hc)
          (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) hc
      have hCIleI : commSub I L ≤ I := commSub_le_of_invariant hIstab
      have hCIleU : commSub I L ≤ U := hCIleI.trans hIle
      have hKinv : ∀ (g : GL (Fin 3) (ZMod 2)) m, m ∈ s16h_l3MatImage C (commSub I L) →
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m ∈ s16h_l3MatImage C (commSub I L) := by
        intro g m hm
        rw [s16h_l3MatImage_mem_iff] at hm ⊢
        obtain ⟨u, huCI, rfl⟩ := hm
        obtain ⟨l, rfl⟩ := C.ρ.surjective g
        have hluCI : (l : MulAut W) (u : W) ∈ commSub I L :=
          hCIstab l l.2 (u : W) huCI
        refine ⟨⟨(l : MulAut W) (u : W), hCIleU hluCI⟩, hluCI, ?_⟩
        exact C.equivariant ⟨l, l.2⟩ (u : W) u.2 (hCIleU hluCI)
      have hKle : s16h_l3MatImage C (commSub I L) ≤ J := by
        rw [← hIimage]
        exact s16h_l3MatImage_mono C hCIleI
      rcases hJmin (s16h_l3MatImage C (commSub I L)) hKle hKinv with hKbot | hKJ
      · exfalso
        have hCIbot : commSub I L = ⊥ := by
          have h1 : s16h_l3Preimage C (s16h_l3MatImage C (commSub I L)) = commSub I L :=
            s16h_l3Preimage_image C hCIleU
          rw [hKbot, s16h_l3Preimage_bot] at h1
          exact h1.symm
        have hfix : I ≤ fixV L := (commSub_eq_bot_iff).mp hCIbot
        apply hIne
        rw [eq_bot_iff]
        intro w hw
        have : w ∈ I ⊓ fixV L := ⟨hw, hfix hw⟩
        rwa [hIfixbot] at this
      · have h1 : s16h_l3Preimage C (s16h_l3MatImage C (commSub I L)) = commSub I L :=
          s16h_l3Preimage_image C hCIleU
        rw [hKJ, ← hIimage, s16h_l3Preimage_image C hIle] at h1
        exact h1.le
  · rw [hIfixbot]
    refine ⟨bot_lt_iff_ne_bot.mpr hIne, hIstab, ?_, ?_⟩
    · intro l hl w hw
      rw [Subgroup.mem_bot] at hw
      subst hw
      simp
    · intro J' hJ'stab hNle hJ'le
      have hJ'U : J' ≤ U := hJ'le.trans hIle
      have hKinv : ∀ (g : GL (Fin 3) (ZMod 2)) m, m ∈ s16h_l3MatImage C J' →
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m ∈ s16h_l3MatImage C J' := by
        intro g m hm
        rw [s16h_l3MatImage_mem_iff] at hm ⊢
        obtain ⟨u, huJ', rfl⟩ := hm
        obtain ⟨l, rfl⟩ := C.ρ.surjective g
        have hluJ' : (l : MulAut W) (u : W) ∈ J' := hJ'stab l l.2 (u : W) huJ'
        refine ⟨⟨(l : MulAut W) (u : W), hJ'U hluJ'⟩, hluJ', ?_⟩
        exact C.equivariant ⟨l, l.2⟩ (u : W) u.2 (hJ'U hluJ')
      have hKle : s16h_l3MatImage C J' ≤ J := by
        rw [← hIimage]
        exact s16h_l3MatImage_mono C hJ'le
      rcases hJmin (s16h_l3MatImage C J') hKle hKinv with hKbot | hKJ
      · left
        have h1 : s16h_l3Preimage C (s16h_l3MatImage C J') = J' :=
          s16h_l3Preimage_image C hJ'U
        rw [hKbot, s16h_l3Preimage_bot] at h1
        exact h1.symm
      · right
        have h1 : s16h_l3Preimage C (s16h_l3MatImage C J') = J' :=
          s16h_l3Preimage_image C hJ'U
        rw [hKJ, ← hIimage, s16h_l3Preimage_image C hIle] at h1
        exact h1.symm

theorem s16h_e3_irrSet_L3_equiv_minLeftInv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : commSub (⊤ : Subgroup W) L = U)
    (C : s16h_L3Coord L U) :
    Nonempty (↥(irrSet L) ≃ {I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) //
      s16h_IsMinLeftInvMat I}) := by
  exact ⟨{
    toFun := fun I => ⟨s16h_l3MatImage C I.1, s16h_l3MatImage_isMin hU C I.2⟩
    invFun := fun J => ⟨s16h_l3Preimage C J.1, s16h_l3Preimage_mem_irrSet hU C J.2⟩
    left_inv := by
      intro I
      apply Subtype.ext
      exact s16h_l3Preimage_image C (by
        rw [← hU]
        exact s16h_e3_irrSet_L3_le_commSub I.2)
    right_inv := by
      intro J
      apply Subtype.ext
      exact s16h_l3MatImage_preimage C J.1 }⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
