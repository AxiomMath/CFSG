module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Tr2

public section

namespace CFSG.Quasithin.H13.C1294

theorem sl4S_ncard_le : sl4S.ncard ≤ 3 := by
  have hr : sl4S = Set.range (fun i : Fin sl4D.rank =>
      ((⟨sl4n i, CFSG.LieType.Steinberg.n_mem_weylN i⟩ : CFSG.LieType.Steinberg.weylN sl4n sl4H) :
        CFSG.GH74.BNPair.WeylGroup sl4B sl4N)) := rfl
  rw [hr]
  calc (Set.range _).ncard = ((fun i : Fin sl4D.rank =>
        ((⟨sl4n i, CFSG.LieType.Steinberg.n_mem_weylN i⟩ : CFSG.LieType.Steinberg.weylN sl4n sl4H) :
          CFSG.GH74.BNPair.WeylGroup sl4B sl4N)) '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin sl4D.rank)).ncard := Set.ncard_image_le Set.finite_univ
    _ = Nat.card (Fin sl4D.rank) := Set.ncard_univ _
    _ = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl

theorem sl4B_overgroups_ncard_le :
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) | sl4B ≤ P}.ncard ≤ 8 := by
  have hfinS : sl4S.Finite := Set.toFinite _
  have hsub : {P : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) | sl4B ≤ P} ⊆
      (fun J => CFSG.GH74.BNPair.parabolic sl4B sl4N J) '' sl4S.powerset := by
    intro P hP
    obtain ⟨J, hJ, hPJ⟩ := (sl4_overgroup_parabolic P hP).exists
    exact ⟨J, hJ, hPJ.symm⟩
  have hpow : sl4S.powerset.Finite := hfinS.powerset
  calc _ ≤ ((fun J => CFSG.GH74.BNPair.parabolic sl4B sl4N J) '' sl4S.powerset).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ sl4S.powerset.ncard := Set.ncard_image_le hpow
    _ = 2 ^ sl4S.ncard := Set.ncard_powerset sl4S hfinS
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) sl4S_ncard_le
    _ = 8 := by norm_num

theorem Bstd_overgroups_ncard_le {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (e : V4 ≃ₗ[ZMod 2] I) :
    {X : Subgroup (I ≃ₗ[ZMod 2] I) | Bstd e ≤ X}.ncard ≤ 8 := by
  have h := sl4B_overgroups_ncard_le
  rw [sl4B_eq_upperSub] at h
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun X : Subgroup (I ≃ₗ[ZMod 2] I) =>
    X.comap (PsiE e)) ?_ ?_ (Set.toFinite _)) h
  · intro X hX
    show upperSub ≤ X.comap (PsiE e)
    intro g hg
    show PsiE e g ∈ X
    exact hX ((mem_upperSub_iff_Bstd e g).1 hg)
  · intro X _ Y _ hXY
    have hX := Subgroup.map_comap_eq_self_of_surjective (PsiE_surjective e) X
    have hY := Subgroup.map_comap_eq_self_of_surjective (PsiE_surjective e) Y
    rw [← hX, ← hY]
    simp only at hXY
    rw [hXY]

end CFSG.Quasithin.H13.C1294
