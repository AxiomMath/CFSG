module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectSp
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectWr
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectOrth
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthMinus
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNinePSU
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

private theorem w183b5_odd_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem w183b5_isSolvable_fusionZStar (X : Type) [Group X] [Finite X] :
    Group.IsSolvable ↥(fusionZStar X) := by
  have hOeq : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  have hOsolv : Group.IsSolvable ↥(fusionOddCore X) := by
    rw [hOeq]
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _
      (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X)))
  haveI := hOsolv
  have hCsolv : Group.IsSolvable ↥(center (X ⧸ fusionOddCore X)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  haveI := hCsolv
  unfold fusionZStar
  have hle : fusionOddCore X ≤ (center (X ⧸ fusionOddCore X)).comap
      (QuotientGroup.mk' (fusionOddCore X)) := by
    intro y hy
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
    exact one_mem _
  let g : ↥((center (X ⧸ fusionOddCore X)).comap (QuotientGroup.mk' (fusionOddCore X))) →*
      ↥(center (X ⧸ fusionOddCore X)) :=
    ((QuotientGroup.mk' (fusionOddCore X)).comp
      ((center (X ⧸ fusionOddCore X)).comap (QuotientGroup.mk' (fusionOddCore X))).subtype
      ).codRestrict _ fun x => x.2
  refine Group.isSolvable_of_ker_le_range (inclusion hle) g ?_
  intro x hx
  have hx' : QuotientGroup.mk' (fusionOddCore X) (x : X) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact ⟨⟨x, hx'⟩, rfl⟩

private def w183b5_NoFactor (P : (T : Type) → [Group T] → Prop) (Y : Type) [Group Y] : Prop :=
  ∀ (T : Type) [Group T], P T → ¬ E1.IsCompositionFactor Y T

private theorem w183b5_noFactor_of_normal {P : (T : Type) → [Group T] → Prop} {Y : Type}
    [Group Y] (A : Subgroup Y) [A.Normal] (hA : w183b5_NoFactor P ↥A)
    (hQ : w183b5_NoFactor P (Y ⧸ A)) : w183b5_NoFactor P Y :=
  fun T _ hT hcf => (isCompositionFactor_of_normal A hcf).elim (hA T hT) (hQ T hT)

private theorem w183b5_noFactor_of_commute {P : (T : Type) → [Group T] → Prop} {Y : Type}
    [Group Y] [Finite Y]
    (hNonab : ∀ (T : Type) [Group T], P T → ∃ a b : T, a * b ≠ b * a)
    (hcomm : ∀ a b : Y, a * b = b * a) : w183b5_NoFactor P Y := by
  intro T _ hT hcf
  haveI := isCompositionFactor_finite hcf
  obtain ⟨a, b, hab⟩ := hNonab T hT
  exact hab (isCompositionFactor_commute hcomm hcf a b)

private theorem w183b5_noFactor_of_not_dvd {P : (T : Type) → [Group T] → Prop} {Y : Type}
    [Group Y] [Finite Y]
    (h : ∀ (T : Type) [Group T], P T → ¬ Nat.card T ∣ Nat.card Y) : w183b5_NoFactor P Y :=
  fun T _ hT hcf => h T hT (isCompositionFactor_natCard_dvd hcf)

private theorem w183b5_noFactor_of_mulEquiv {P : (T : Type) → [Group T] → Prop} {Y Y' : Type}
    [Group Y] [Group Y'] (e : Y ≃* Y') (h : w183b5_NoFactor P Y) : w183b5_NoFactor P Y' :=
  fun T _ hT hcf => h T hT ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hcf)

private theorem w183b5_noFactor_of_nonSz
    {X : Type} [Group X] [Finite X] {s : X}
    (h : (∃ m n : ℕ,
        (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticTransvection X m n s) ∨
        (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryTransvection X m n s) ∨
        IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) ∨
      (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨ IsThreeCoverOrth6Minus X)
    (P : (T : Type) → [Group T] → Prop)
    (hEven : ∀ (T : Type) [Group T], P T → 2 ∣ Nat.card T)
    (hNonab : ∀ (T : Type) [Group T], P T → ∃ a b : T, a * b ≠ b * a)
    (hSp : ∀ (Y : Type) [Group Y] (m n : ℕ), IsSpGp Y m n → w183b5_NoFactor P Y)
    (hU : ∀ (Y : Type) [Group Y] (m n : ℕ), IsPSUGp Y m n → w183b5_NoFactor P Y)
    (hOrth : ∀ (Y : Type) [Group Y] (m n : ℕ), IsOrthGp Y m n → w183b5_NoFactor P Y)
    (hWr : ∀ (Y : Type) [Group Y] (n m : ℕ), IsL2WrSymGp Y n m → w183b5_NoFactor P Y)
    (hSym : ∀ (Y : Type) [Group Y] (m : ℕ), IsSymGp Y m → w183b5_NoFactor P Y)
    (hSix : ∀ (Y : Type) [Group Y], IsOrth6MinusMod Y → w183b5_NoFactor P Y) :
    w183b5_NoFactor P X := by
  rcases h with ⟨m, n, hc⟩ | ⟨n, hn⟩ | hX
  · have hZ : w183b5_NoFactor P ↥(Subgroup.center X) :=
      w183b5_noFactor_of_commute hNonab fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1)
    rcases hc with ⟨hSp', -⟩ | ⟨hU', -⟩ | hO | hWr'
    · exact w183b5_noFactor_of_normal (Subgroup.center X) hZ (hSp _ m n hSp')
    · exact w183b5_noFactor_of_normal (Subgroup.center X) hZ (hU _ m n hU')
    · exact w183b5_noFactor_of_normal (Subgroup.center X) hZ (hOrth _ m n hO)
    · exact w183b5_noFactor_of_normal (Subgroup.center X) hZ (hWr _ n m hWr')
  · refine w183b5_noFactor_of_normal (fusionOddCore X)
      (w183b5_noFactor_of_not_dvd fun T _ hT hdvd => ?_) (hSym _ n hn)
    have h2 : 2 ∣ Nat.card (fusionOddCore X) := (hEven T hT).trans hdvd
    exact (Nat.not_even_iff_odd.mpr (w183b5_odd_fusionOddCore X))
      (even_iff_two_dvd.mpr h2)
  · obtain ⟨Y, _, φ, hφ, -, hker, hY⟩ := hX
    have hK : w183b5_NoFactor P ↥φ.ker :=
      w183b5_noFactor_of_commute hNonab fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) a.1)
    refine w183b5_noFactor_of_normal φ.ker hK ?_
    exact w183b5_noFactor_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (hSix Y hY)

private theorem w183b5_three_not_dvd_sz (n : ℕ) (hn : Odd n) :
    ¬ 3 ∣ (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hq : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod]
    norm_num [h4]
  have hq2 : (2 ^ (2 * k + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq21 : ((2 ^ (2 * k + 1)) ^ 2 + 1) % 3 = 2 := by
    rw [Nat.add_mod, hq2]
  have hq1 : (2 ^ (2 * k + 1) - 1) % 3 = 1 := by
    have hdecomp : 2 ^ (2 * k + 1) = 3 * (2 ^ (2 * k + 1) / 3) + 2 := by
      have h := Nat.div_add_mod (2 ^ (2 * k + 1)) 3
      rw [hq] at h
      exact h.symm
    have hsub : 2 ^ (2 * k + 1) - 1 = 3 * (2 ^ (2 * k + 1) / 3) + 1 := by omega
    rw [hsub, Nat.mul_add_mod]
  have hA2 : ¬ 3 ∣ (2 ^ (2 * k + 1)) ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, hq2]
    norm_num
  have hA21 : ¬ 3 ∣ (2 ^ (2 * k + 1)) ^ 2 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hq2]
    norm_num
  have hA1 : ¬ 3 ∣ 2 ^ (2 * k + 1) - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, hq1]
    norm_num
  intro h
  rcases Nat.prime_three.dvd_mul.mp h with h' | h'
  · rcases Nat.prime_three.dvd_mul.mp h' with h'' | h''
    · exact hA2 h''
    · exact hA21 h''
  · exact hA1 h'

private theorem w183b5_noFactor_of_sz (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hsz : CFSG.Quasithin.IsSz n (X ⧸ fusionZStar X))
    {T : Type} [Group T] (hNonab : ∃ a b : T, a * b ≠ b * a) (hThree : 3 ∣ Nat.card T) :
    ¬ CFSG.Quasithin.E1.IsCompositionFactor X T := by
  intro hcf
  haveI : Group.IsSolvable ↥(fusionZStar X) := w183b5_isSolvable_fusionZStar X
  rcases isCompositionFactor_of_normal (fusionZStar X) hcf with hZ | hQ
  · obtain ⟨a, b, hab⟩ := hNonab
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      inferInstance hZ a b)
  · have hdvd : Nat.card T ∣ Nat.card (X ⧸ fusionZStar X) :=
      isCompositionFactor_natCard_dvd hQ
    have hmodel : LieModel (X ⧸ fusionZStar X) .twistedB2 0 2 n :=
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hsz⟩))
    have hadm : StatedLieAdmissible .twistedB2 0 2 n := hmodel.admissible
    obtain ⟨-, hM, -⟩ := hO (X ⧸ fusionZStar X) .twistedB2 0 2 n hadm hmodel
    have hcard : Nat.card (X ⧸ fusionZStar X) =
        (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
      rw [show lieOrderDivisor .twistedB2 0 (2 ^ n) = 1 by rfl, mul_one] at hM
      rw [hM]
      rfl
    have h3 : 3 ∣ (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
      rw [← hcard]
      exact hThree.trans hdvd
    obtain ⟨a, ha, K, _, _, hf, _, -⟩ := hsz.2
    exact w183b5_three_not_dvd_sz n ⟨a, hf⟩ h3

private theorem w183b5_socle185_nonab {S : Type} [Group S] (h : Socle185Shape S) :
    ∃ a b : S, a * b ≠ b * a := by
  haveI := Socle185Shape.finite h
  exact Socle185Shape.exists_not_commute h

private theorem w183b5_nonSz_of_alternatives (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] (s : X)
    (h : (∃ m n : ℕ,
        (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticTransvection X m n s) ∨
        (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryTransvection X m n s) ∨
        IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) ∨
      (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨ IsThreeCoverOrth6Minus X)
    {T : Type} [Group T] (hT : CFSG.Quasithin.F6.IsL2 5 2 T ∨ LieModel T .PSp 2 5 1) :
    ¬ CFSG.Quasithin.E1.IsCompositionFactor X T := by
  rcases hT with hL2 | hPSp
  · have hShape : Socle185Shape T :=
      Or.inl ⟨5, 2, by norm_num, by norm_num, by norm_num, hL2⟩
    exact (w183b5_noFactor_of_nonSz h Socle185Shape
      (fun S _ hS => Socle185Shape.two_dvd_card hO hS)
      (fun S _ hS => w183b5_socle185_nonab hS)
      (fun Y _ m n h => noSocle185Factor_of_isSpGp hO h)
      (fun Y _ m n h => noSocle185Factor_of_isPSUGp hO h)
      (fun Y _ m n h => noSocle185Factor_of_isOrthGp hO h)
      (fun Y _ n m h => noSocle185Factor_of_isL2WrSymGp hO h)
      (fun Y _ m h => noSocle185Factor_of_isSymGp hO h)
      (fun Y _ h => noSocle185Factor_of_isOrth6MinusMod hO h)) T hShape
  · have hShape : Psp45Shape T := hPSp
    exact (w183b5_noFactor_of_nonSz h Psp45Shape
      (fun S _ hS => Psp45Shape.two_dvd_card hO hS)
      (fun S _ hS => Psp45Shape.exists_not_commute hO hS)
      (fun Y _ m n h => noPsp45Factor_of_isSpGp hO h)
      (fun Y _ m n h => noPsp45Factor_of_isPSUGp hO h)
      (fun Y _ m n h => noPsp45Factor_of_isOrthGp hO h)
      (fun Y _ n m h => noPsp45Factor_of_isL2WrSymGp hO h)
      (fun Y _ m h => noPsp45Factor_of_isSymGp hO h)
      (fun Y _ h => noPsp45Factor_of_isOrth6MinusMod hO h)) T hShape

theorem not_compFactor_of_listAlternatives (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] {s : X}
    (h : (∃ m n : ℕ, (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticTransvection X m n s) ∨
        (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryTransvection X m n s) ∨
        IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) ∨
      (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨ IsThreeCoverOrth6Minus X ∨
      (∃ n : ℕ, 1 < n ∧ CFSG.Quasithin.IsSz n (X ⧸ fusionZStar X)))
    {T : Type} [Group T] (hT : CFSG.Quasithin.F6.IsL2 5 2 T ∨ LieModel T .PSp 2 5 1) :
    ¬ CFSG.Quasithin.E1.IsCompositionFactor X T := by
  rcases h with hfam | hsym | hsix | ⟨n, hn1, hsz⟩
  · exact w183b5_nonSz_of_alternatives hO s (Or.inl hfam) hT
  · exact w183b5_nonSz_of_alternatives hO s (Or.inr (Or.inl hsym)) hT
  · exact w183b5_nonSz_of_alternatives hO s (Or.inr (Or.inr hsix)) hT
  · rcases hT with hL2 | hPSp
    · have hShape : Socle185Shape T :=
        Or.inl ⟨5, 2, by norm_num, by norm_num, by norm_num, hL2⟩
      refine w183b5_noFactor_of_sz hO hsz ?_ ?_
      · haveI := Socle185Shape.finite hShape
        exact Socle185Shape.exists_not_commute hShape
      · have hmodel : LieModel T .PSL 2 5 2 := Or.inl ⟨by decide, hL2⟩
        obtain ⟨-, hM, -⟩ := hO T .PSL 2 5 2 hL2.1 hmodel
        have hd : lieOrderDivisor .PSL 2 (5 ^ 2) = 2 := by decide
        have hn : lieOrderNumerator .PSL 2 (5 ^ 2) = 15600 := by
          simp [lieOrderNumerator, show Finset.Icc 2 2 = {2} by decide,
            Finset.prod_singleton]
        rw [hd, hn] at hM
        have hcard : Nat.card T = 7800 := by omega
        rw [hcard]
        norm_num
    · refine w183b5_noFactor_of_sz hO hsz (Psp45Shape.exists_not_commute hO hPSp) ?_
      rw [Psp45Shape.card_eq hO hPSp]
      norm_num

end CFSG.LocalAnalysis.WeakClosure81

end
