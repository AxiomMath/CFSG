module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoCompat
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.PsiDiag
  CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer

noncomputable def SelectedSL2Model.ofGF2Upper {K : Type*} [Group K]
    (D : UniversalRootDatum K) (gamma : Fin D.rank → ℤ) (hroot : gamma ∈ D.roots)
    (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* K)
    (hinj : Function.Injective phi)
    (hupper : (sl2UpperUniSub (GaloisField 2 1)).map phi = D.rootGroup gamma) :
    SelectedSL2Model D (GaloisField 2 1) gamma := by
  classical
  have h2 : Nat.card (D.rootGroup gamma) = 2 := by
    rw [← hupper, Subgroup.card_map_of_injective hinj, card_sl2UpperUniSub,
      GaloisField.card 2 1 (by omega)]
    norm_num
  have hu : ∀ a : (GaloisField 2 1)ˣ, a = 1 := by
    intro a
    let : Fintype (GaloisField 2 1) := Fintype.ofFinite (GaloisField 2 1)
    have hcard : Fintype.card (GaloisField 2 1)ˣ = 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega)]
      norm_num
    have h : a ^ Fintype.card (GaloisField 2 1)ˣ = 1 := pow_card_eq_one
    rwa [hcard, pow_one] at h
  refine SelectedSL2Model.ofRootMap D gamma hroot phi hinj hupper ?_ ?_
  · intro a
    rw [hu a]
    have hd : sl2Diag (1 : (GaloisField 2 1)ˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_sl2Diag]
    rw [hd, map_one]
    exact Subgroup.one_mem _
  · intro h hh
    refine ⟨1, ?_⟩
    intro t
    simp only [one_mul]
    apply ggConj_eq_of_card_two h2
    · simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh gamma hroot
    · rw [← hupper]
      exact Subgroup.mem_map_of_mem phi ⟨t, rfl⟩

@[simp] theorem SelectedSL2Model.ofGF2Upper_phi {K : Type*} [Group K]
    (D : UniversalRootDatum K) (gamma : Fin D.rank → ℤ) (hroot : gamma ∈ D.roots)
    (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* K)
    (hinj : Function.Injective phi)
    (hupper : (sl2UpperUniSub (GaloisField 2 1)).map phi = D.rootGroup gamma) :
    (SelectedSL2Model.ofGF2Upper D gamma hroot phi hinj hupper).phi = phi := by
  unfold SelectedSL2Model.ofGF2Upper
  rfl

theorem SelectedSL2Model.exists_pullback_of_upper_map_eq
    {U K C : Type*} [Group U] [Group K] [Group C] [Finite U]
    (D : UniversalRootDatum U) (E : UniversalRootDatum K)
    {gamma : Fin D.rank → ℤ} {delta : Fin E.rank → ℤ}
    (source : SelectedSL2Model D (GaloisField 2 1) gamma)
    (member : SelectedSL2Model E (GaloisField 2 1) delta)
    (Phi : K →* U) (hPhi : Phi.ker ≤ Subgroup.center K)
    (pi : U →* C) (hpiker : pi.ker ≤ Subgroup.center U)
    (hpiodd : Odd (Nat.card pi.ker)) (u0 : U)
    (hmap : (D.rootGroup gamma).map (pi.comp (MulAut.conj u0).toMonoidHom) =
      (E.rootGroup delta).map (pi.comp Phi)) :
    ∃ model : SelectedSL2Model D (GaloisField 2 1) gamma,
      model.phi = (MulAut.conj u0⁻¹).toMonoidHom.comp (Phi.comp member.phi) ∧
      (MulAut.conj u0).toMonoidHom.comp model.phi = Phi.comp member.phi := by
  have hcardSource : Nat.card (D.rootGroup gamma) = 2 := by
    rw [← source.upper_eq, Subgroup.card_map_of_injective source.injective,
      card_sl2UpperUniSub, GaloisField.card 2 1 (by omega)]
    norm_num
  have hcardMember : Nat.card (E.rootGroup delta) = 2 := by
    rw [← member.upper_eq, Subgroup.card_map_of_injective member.injective,
      card_sl2UpperUniSub, GaloisField.card 2 1 (by omega)]
    norm_num
  have hsource : IsPGroup 2 (D.rootGroup gamma) :=
    IsPGroup.of_card (n := 1) (by simpa using hcardSource)
  have hmember : IsPGroup 2 (E.rootGroup delta) :=
    IsPGroup.of_card (n := 1) (by simpa using hcardMember)
  have hroot : (D.rootGroup gamma).map (MulAut.conj u0).toMonoidHom =
      (E.rootGroup delta).map Phi :=
    CFSG.GroupTheory.eq_of_map_eq_map_of_isPGroup_of_odd_ker pi hpiker hpiodd
      (hsource.map _) (hmember.map _) (by
        rw [Subgroup.map_map, Subgroup.map_map]
        exact hmap)
  let phi := (MulAut.conj u0⁻¹).toMonoidHom.comp (Phi.comp member.phi)
  have hinj : Function.Injective phi := (MulAut.conj u0⁻¹).injective.comp
    (injective_comp_of_ker_le_center member.phi member.injective Phi hPhi)
  have hcancel : (MulAut.conj u0⁻¹).toMonoidHom.comp
      (MulAut.conj u0).toMonoidHom = MonoidHom.id U := by
    ext y
    simp [mul_assoc]
  have hupper : (sl2UpperUniSub (GaloisField 2 1)).map phi = D.rootGroup gamma := by
    have h1 : (sl2UpperUniSub (GaloisField 2 1)).map phi =
        (((sl2UpperUniSub (GaloisField 2 1)).map member.phi).map Phi).map
          (MulAut.conj u0⁻¹).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, member.upper_eq, ← hroot, Subgroup.map_map, hcancel, Subgroup.map_id]
  refine ⟨SelectedSL2Model.ofGF2Upper D gamma source.root_mem phi hinj hupper, ?_, ?_⟩
  · exact SelectedSL2Model.ofGF2Upper_phi D gamma source.root_mem phi hinj hupper
  · rw [SelectedSL2Model.ofGF2Upper_phi]
    ext y
    simp [phi, MulAut.conj_apply, mul_assoc]

end CFSG.StandardType.SelectedRoot
