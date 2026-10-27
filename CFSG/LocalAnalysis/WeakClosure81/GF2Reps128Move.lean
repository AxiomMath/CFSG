module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem dMinDeg_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) : dMinDeg A = dMinDeg B := by
  unfold dMinDeg
  congr 1
  ext n
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.comp e.symm.toMonoidHom, fun h => hf (MonoidHom.ext fun a => ?_)⟩
    have := congrArg (fun g : B →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) => g (e a)) h
    simpa using this
  · rintro ⟨f, hf⟩
    refine ⟨f.comp e.toMonoidHom, fun h => hf (MonoidHom.ext fun b => ?_)⟩
    have := congrArg (fun g : A →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) => g (e.symm b)) h
    simpa using this

variable {W : Type} [CommGroup W] [Finite W]

theorem dMinDeg_le_of_map_ne (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hIt : I.map t.toMonoidHom ≠ I) : dMinDeg ↥L ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  set C := fixV H with hC
  have hg : ∀ x ∈ H, t * x * t⁻¹ ∈ H := hn t ht
  have hg' : ∀ x ∈ H, t⁻¹ * x * t ∈ H := by
    intro x hx
    have := hn t⁻¹ (Y.inv_mem ht) x hx
    simpa using this
  have htI : I.map t.toMonoidHom ∈ irrSet H := map_mem_irrSet hg hg' hI
  have hirrI := isIrrOn_sup_fixV hI
  have hirrtI := isIrrOn_sup_fixV htI
  have hstabI : StableUnder H (I ⊔ C) := hirrI.2.1
  have hstabtI : StableUnder H (I.map t.toMonoidHom ⊔ C) := hirrtI.2.1
  have hmeet : (I ⊔ C) ⊓ (I.map t.toMonoidHom ⊔ C) = C := by
    rcases hirrI.2.2.2 _ (stableUnder_inf hstabI hstabtI) (le_inf le_sup_right le_sup_right)
        inf_le_left with h | h
    · exact h
    · exfalso
      have hle : I ⊔ C ≤ I.map t.toMonoidHom ⊔ C := by
        rw [← h]
        exact inf_le_right
      rcases hirrtI.2.2.2 _ hstabI le_sup_right hle with h' | h'
      · exact not_le_fixV_of_mem_irrSet hI (le_sup_left.trans h'.le)
      · apply hIt
        calc I.map t.toMonoidHom = commSub (I.map t.toMonoidHom) H := htI.1.symm
          _ = commSub (I.map t.toMonoidHom ⊔ C) H :=
            (CFSG.Quasithin.commSub_sup_fixV le_rfl).symm
          _ = commSub (I ⊔ C) H := by rw [h']
          _ = commSub I H := CFSG.Quasithin.commSub_sup_fixV le_rfl
          _ = I := hI.1
  set Ct := fixV (Subgroup.zpowers t) with hCt
  have hICt : I ⊓ Ct ≤ I ⊓ C := by
    intro v hv
    refine ⟨hv.1, ?_⟩
    have htv : t v = v := hv.2 t (Subgroup.mem_zpowers t)
    have hvt : v ∈ I.map t.toMonoidHom := ⟨v, hv.1, htv⟩
    have hmem : v ∈ (I ⊔ C) ⊓ (I.map t.toMonoidHom ⊔ C) :=
      ⟨le_sup_left (α := Subgroup W) hv.1, le_sup_left (α := Subgroup W) hvt⟩
    rw [hmeet] at hmem
    exact hmem
  have hrank : rk ↥I ≤ rk ↥(I ⊓ C) + rkIdx Ct := by
    have h1 := rk_sup_add_rk_inf I Ct
    have h2 := rk_add_rkIdx Ct
    have h3 : rk ↥(I ⊔ Ct) ≤ rk W := (rk_mono (le_top : I ⊔ Ct ≤ ⊤)).trans (rk_top).le
    have h4 : rk ↥(I ⊓ Ct) ≤ rk ↥(I ⊓ C) := rk_mono hICt
    omega
  have hex : ∃ X ∈ conjSet L Y, ¬ commSub I X ≤ I ⊓ C := by
    by_contra hall
    push Not at hall
    have hP : ∀ x ∈ H, ∀ u ∈ I, x u * u⁻¹ ∈ I ⊓ C := by
      intro x hx
      rw [hH, iSup_subtype'] at hx
      refine Subgroup.iSup_induction (fun X : conjSet L Y => (X : Subgroup (MulAut W)))
        (C := fun x => ∀ u ∈ I, x u * u⁻¹ ∈ I ⊓ C) hx ?_ ?_ ?_
      · intro X y hy u hu
        exact hall X X.2 (Subgroup.subset_closure ⟨y, hy, u, hu, rfl⟩)
      · intro u _
        simp
      · intro a b ha hb u hu
        have hbu : b u ∈ I := by
          have h1 := (hb u hu).1
          have h2 := I.mul_mem h1 hu
          simpa using h2
        have h3 := (I ⊓ C).mul_mem (ha (b u) hbu) (hb u hu)
        have he : a (b u) * (b u)⁻¹ * (b u * u⁻¹) = (a * b) u * u⁻¹ := by
          rw [MulAut.mul_apply]
          group
        rwa [he] at h3
    apply not_le_fixV_of_mem_irrSet hI
    have hle : commSub I H ≤ I ⊓ C := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, u, hu, rfl⟩
      exact hP x hx u hu
    rw [hI.1] at hle
    exact hle.trans inf_le_right
  obtain ⟨X, hX, hXI⟩ := hex
  have hXH : X ≤ H := by
    rw [hH]
    exact le_iSup₂_of_le X hX le_rfl
  have hSK : StableUnder X I := fun x hx u hu => hI.2.2.1 x (hXH hx) u hu
  have hUK : StableUnder X (I ⊓ C) := fun x hx u hu => hI.2.2.2.1 x (hXH hx) u hu
  have hd : rk ↥(I ⊓ C) + dMinDeg ↥X ≤ rk ↥I := by
    by_contra hlt
    push Not at hlt
    exact hXI (Inputs1719.commSub_le_of_rk_lt_dMinDeg hW inf_le_left hSK hUK hlt)
  obtain ⟨y, hy, rfl⟩ := hX
  have hdeg : dMinDeg ↥(L.map (MulAut.conj y).toMonoidHom) = dMinDeg ↥L :=
    (dMinDeg_congr (L.equivMapOfInjective _ (MulAut.conj y).injective)).symm
  rw [hdeg] at hd
  omega

end CFSG.LocalAnalysis.WeakClosure81
