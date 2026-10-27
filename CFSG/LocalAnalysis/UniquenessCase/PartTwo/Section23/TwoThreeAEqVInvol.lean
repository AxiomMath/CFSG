module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.Holds
public import CFSG.GroupTheory.PerfectCentralizer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Rho

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

theorem isClassicalGroup23_of_isNaturalClassicalModule {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {k : ℕ} (h : IsNaturalClassicalModule H k) :
    IsClassicalGroup23 ↥H k := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨a, hk, h1, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hk, h1⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h1)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr h1)))))))))

private theorem not_centralizes_resHom_of_not_centralizes
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut W) ∈ centSub A' → h ∈ Subgroup.center ↥H)
    {s : MulAut W} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hsA : s ∈ stabSub A')
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    ∃ h ∈ autSub H A',
      resHom A' ⟨s, hsA⟩ * h * (resHom A' ⟨s, hsA⟩)⁻¹ ≠ h := by
  by_contra hcon
  push Not at hcon
  have hcent : resHom A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autSub H A' : Set (MulAut (↥A'))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : resHom A' ⟨s, hsA⟩ * h * (resHom A' ⟨s, hsA⟩)⁻¹ = h := hcon h hh
    calc h * resHom A' ⟨s, hsA⟩ =
        (resHom A' ⟨s, hsA⟩ * h * (resHom A' ⟨s, hsA⟩)⁻¹) * resHom A' ⟨s, hsA⟩ := by
          rw [h1]
      _ = resHom A' ⟨s, hsA⟩ * h := by group
  have hscent : s ∈ Subgroup.centralizer (H : Set (MulAut W)) :=
    centralizes_of_resAut_mem_centralizer hH hHA hCA hsN hsA hcent
  obtain ⟨h, hh, hne⟩ := hnotcent
  apply hne
  have hcomm : h * s = s * h := Subgroup.mem_centralizer_iff.mp hscent h hh
  calc s * h * s⁻¹ = (h * s) * s⁻¹ := by rw [hcomm]
    _ = h := by group

private theorem not_centralizes_quotHom_of_not_centralizes
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCW : ∀ h : ↥H, (h : MulAut W) ∈ centQuot A' → h ∈ Subgroup.center ↥H)
    {s : MulAut W} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hsA : s ∈ stabSub A')
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    ∃ h ∈ autQuot H A',
      quotHom A' ⟨s, hsA⟩ * h * (quotHom A' ⟨s, hsA⟩)⁻¹ ≠ h := by
  by_contra hcon
  push Not at hcon
  have hcent : quotHom A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autQuot H A' : Set (MulAut (W ⧸ A'))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : quotHom A' ⟨s, hsA⟩ * h * (quotHom A' ⟨s, hsA⟩)⁻¹ = h := hcon h hh
    calc h * quotHom A' ⟨s, hsA⟩ =
        (quotHom A' ⟨s, hsA⟩ * h * (quotHom A' ⟨s, hsA⟩)⁻¹) * quotHom A' ⟨s, hsA⟩ := by
          rw [h1]
      _ = quotHom A' ⟨s, hsA⟩ * h := by group
  have hscent : s ∈ Subgroup.centralizer (H : Set (MulAut W)) :=
    centralizes_of_quotHom_mem_centralizer hH hHA hCW hsN hsA hcent
  obtain ⟨h, hh, hne⟩ := hnotcent
  apply hne
  have hcomm : h * s = s * h := Subgroup.mem_centralizer_iff.mp hscent h hh
  calc s * h * s⁻¹ = (h * s) * s⁻¹ := by rw [hcomm]
    _ = h := by group

theorem k_add_two_le_rkIdx_fixV_zpowers
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} (hH : ⁅H, H⁆ = H)
    {A' : Subgroup W} (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut W) ∈ centSub A' → h ∈ Subgroup.center ↥H)
    (hCW : ∀ h : ↥H, (h : MulAut W) ∈ centQuot A' → h ∈ Subgroup.center ↥H)
    {k : ℕ} (hnat : IsNaturalClassicalModule (autSub H A') k)
    (hk : 3 ≤ k ∨ 2 ≤ k ∧ IsOmegaMinus ↥(autSub H A') 4 k)
    {s : MulAut W} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hsA : s ∈ stabSub A') (hs2 : orderOf s = 2)
    (hnotcent : ∃ h ∈ H, s * h * s⁻¹ ≠ h)
    (hsAN : resHom A' ⟨s, hsA⟩ ∈
      Subgroup.normalizer (autSub H A' : Set (MulAut (↥A'))))
    (hs2A : orderOf (resHom A' ⟨s, hsA⟩) = 2)
    (hsBN : quotHom A' ⟨s, hsA⟩ ∈
      Subgroup.normalizer (autQuot H A' : Set (MulAut (W ⧸ A'))))
    (hs2B : orderOf (quotHom A' ⟨s, hsA⟩) = 2)
    (hperfB : ⁅autQuot H A', autQuot H A'⁆ = autQuot H A')
    (hTv : KNoTransv) :
    k + 2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  let sA : MulAut ↥A' := resHom A' ⟨s, hsA⟩
  let sB : MulAut (W ⧸ A') := quotHom A' ⟨s, hsA⟩
  have hnotcentA : ∃ h ∈ autSub H A', sA * h * sA⁻¹ ≠ h :=
    not_centralizes_resHom_of_not_centralizes hH hHA hCA hsN hsA hnotcent
  have hnotcentB : ∃ h ∈ autQuot H A', sB * h * sB⁻¹ ≠ h :=
    not_centralizes_quotHom_of_not_centralizes hH hHA hCW hsN hsA hnotcent
  have hkA : k ≤ rkIdx (fixV (Subgroup.zpowers sA)) :=
    kNatInvol_holds ↥A' (autSub H A') k sA hnat hsAN hs2A hnotcentA
  have hWq : ∀ b : W ⧸ A', b ^ 2 = 1 := by
    intro b
    induction b using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow]; simp [hW w]
  obtain ⟨f, hfsurj, hfker⟩ := exists_surjective_center_quotient hH hHA hCA hCW
  have hkB : 2 ≤ rkIdx (fixV (Subgroup.zpowers sB)) :=
    hTv (W ⧸ A') hWq (autQuot H A') ↥(autSub H A') k sB
      (isClassicalGroup23_of_isNaturalClassicalModule hnat) hk hperfB
      ⟨f, hfsurj, hfker⟩ hsBN hs2B hnotcentB
  have hrank := rkIdx_fixV_zpowers_ge hW s hsA
  have hAsub : autSub (Subgroup.zpowers s) A' = Subgroup.zpowers sA :=
    CFSG.Quasithin.autSub_zpowers (U := A') (x := s) hsA
  have hAquot : autQuot (Subgroup.zpowers s) A' = Subgroup.zpowers sB :=
    autQuot_zpowers (U := A') (x := s) hsA
  rw [hAsub, hAquot] at hrank
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
