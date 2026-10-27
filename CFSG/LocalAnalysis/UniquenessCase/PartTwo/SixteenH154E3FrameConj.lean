module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_sumOfNat_map_conj {W : Type} [CommGroup W] (x : MulAut W)
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hN : ∀ H U, N H U ⊥ →
      N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥)
    {H : Subgroup (MulAut W)} {U : Subgroup W} {k : ℕ}
    (h : SumOfNat N H U ⊥ k) :
    SumOfNat N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥ k := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  refine ⟨fun i => (I i).map x.toMonoidHom, fun i => bot_le, ?_, ?_,
    fun i => hN _ _ (hnat i)⟩
  · intro i
    have hle := Subgroup.map_mono (f := x.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq _ _ x.toMonoidHom x.injective, Subgroup.map_sup,
      Subgroup.map_bot] at hle
    simp only [Subgroup.map_iSup x.toMonoidHom] at hle
    simpa using hle
  · have h := congrArg (fun V : Subgroup W => V.map x.toMonoidHom) hsup
    rwa [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup x.toMonoidHom] at h

theorem s16h_e3_frame_sum_conj {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hmap : ∀ (f : MulAut W) (H : Subgroup (MulAut W)) (I : Subgroup W), N H I ⊥ →
      N (H.map (MulAut.conj f).toMonoidHom) (I.map f.toMonoidHom) ⊥) {k : ℕ}
    (hS : SumOfNat N L U ⊥ k) : SumOfNat N L' U' ⊥ k := by
  obtain ⟨t, _, hLt, hUt⟩ := F.swap
  have h := s16h_e3_sumOfNat_map_conj t (fun H U h => hmap t H U h) hS
  simpa only [hLt, hUt] using h

private theorem s16h_e3_conj_surjective {W : Type} [CommGroup W] (x : MulAut W)
    (H : Subgroup (MulAut W)) :
    Function.Surjective
      (Subgroup.equivMapOfInjective H (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective).toMonoidHom := by
  intro y
  exact ⟨(Subgroup.equivMapOfInjective H (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).symm y,
    (Subgroup.equivMapOfInjective H (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).apply_symm_apply y⟩

private theorem s16h_e3_conj_equivariant {W : Type} [CommGroup W] (x : MulAut W)
    (H : Subgroup (MulAut W)) (a : ↥H) (w : W) :
    x.toMonoidHom ((a : MulAut W) w) = (MulAut.conj x a) (x.toMonoidHom w) := by
  change x ((a : MulAut W) w) = (MulAut.conj x a) (x w)
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self]

private theorem s16h_e3_conj_ker {W : Type} [CommGroup W] (x : MulAut W) :
    x.toMonoidHom.ker = ⊥ := by
  ext w
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  exact ⟨fun hw => x.injective (by simpa using hw), fun hw => by simp [hw]⟩

theorem s16h_e3_alt5_conj_stable {W : Type} [CommGroup W] (f : MulAut W)
    (H : Subgroup (MulAut W)) (I : Subgroup W) (h : AlternatingNatural H I ⊥ 5) :
    AlternatingNatural (H.map (MulAut.conj f).toMonoidHom) (I.map f.toMonoidHom) ⊥ 5 := by
  refine s16k_alternatingNatural_map h f.toMonoidHom (s16h_e3_conj_ker f)
    (Subgroup.equivMapOfInjective H (MulAut.conj f).toMonoidHom
      (MulAut.conj f).injective).toMonoidHom (s16h_e3_conj_surjective f H) ?_
  intro a w
  exact s16h_e3_conj_equivariant f H a w

theorem s16h_e3_sl3_conj_stable {W : Type} [CommGroup W] (f : MulAut W)
    (H : Subgroup (MulAut W)) (I : Subgroup W) (h : BinaryNaturalSL H I ⊥ 3 1) :
    BinaryNaturalSL (H.map (MulAut.conj f).toMonoidHom) (I.map f.toMonoidHom) ⊥ 3 1 := by
  refine s16k_binaryNaturalSL_map h f.toMonoidHom (s16h_e3_conj_ker f)
    (Subgroup.equivMapOfInjective H (MulAut.conj f).toMonoidHom
      (MulAut.conj f).injective).toMonoidHom (s16h_e3_conj_surjective f H) ?_
  intro a w
  exact s16h_e3_conj_equivariant f H a w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
