module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RLine
public import CFSG.RankThree.PartTwo.Sec21.Hering214KG2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec19

section OutStd


theorem normMoveFour_g2 {k : Type} [Field k] [Finite k] [CharP k 2] (h3 : 3 ∣ Nat.card k - 1)
    {h : ↥(adjointGroup .G2 k)} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) : NormMoveFour h := by
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  have hk4 : 4 ≤ Nat.card k := four_le_card_of_cube_root hω hω1
  have hk3 : ringChar k ≠ 3 := by
    rw [ringChar.eq k 2]
    decide
  obtain ⟨y, hy⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds k hk3 hk4 h hh3 hh1
  obtain ⟨ι₀, hι₀, z', hz'⟩ : ∃ ι₀ : Matrix.SpecialLinearGroup (Fin 2) k →*
      ↥(adjointGroup .G2 k), Function.Injective ι₀ ∧ ∃ z', ι₀ z' = y * h * y⁻¹ := by
    rcases hy with hy | hy
    · obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := k)
      exact ⟨(KS11Lie4Proof.g2ShortSL2 k).subtype.comp e.toMonoidHom,
        (Subgroup.subtype_injective _).comp e.injective, e.symm ⟨_, hy⟩, by simp⟩
    · obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := k)
      exact ⟨(KS11Lie4Proof.g2LongSL2 k).subtype.comp e.toMonoidHom,
        (Subgroup.subtype_injective _).comp e.injective, e.symm ⟨_, hy⟩, by simp⟩
  have hz'3 : z' ^ 3 = 1 := by
    apply hι₀
    rw [map_pow, hz', map_one]
    rw [conj_pow, hh3]
    group
  have hz'1 : z' ≠ 1 := by
    rintro rfl
    apply hh1
    rw [map_one] at hz'
    have : h = y⁻¹ * 1 * y := by
      calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
        _ = y⁻¹ * 1 * y := by rw [← hz']
    rw [this]
    group
  have H : NormMoveFour z' := exists_four_sl2 hω hω1 z' hz'3 hz'1
  have H1 : NormMoveFour (ι₀ z') := NormMoveFour.map_injective ι₀ hι₀ H
  rw [hz'] at H1
  exact NormMoveFour.of_conj y h H1

variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem outer_std_four (P : D4Par n F σ) (hev : Even n) {β : MulAut (C0 σ)}
    (hstd : Sec4.IsStdGraphFieldConj σ β) {g : C0 σ} (hg : β g = g) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : FourFixedMoved β (MulAut.conj g) := by
  haveI := P.charP
  have hK2 : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨ι⟩ := Sec8.Item8KFacts3D4.nonempty_autFix_mulEquiv_g2 hK2 hstd
  have hgS : g ∈ Sec4.autFix β := hg
  refine fourFixedMoved_of_subgroup (S := Sec4.autFix β) (fun s hs => hs) hgS ?_
  apply NormMoveFour.of_mulEquiv ι
  have hfin : Finite (fixSubfield σ) := Subtype.finite
  haveI : CharP (fixSubfield σ) 2 :=
    RingHom.charP (fixSubfield σ).subtype Subtype.val_injective 2
  have hkc : Nat.card (fixSubfield σ) = 2 ^ n := P.card_fix
  have h3 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [hkc]
    exact three_dvd_two_pow_sub_one hev
  refine normMoveFour_g2 h3 ?_ ?_
  · rw [← map_pow]
    have : (⟨g, hgS⟩ : ↥(Sec4.autFix β)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  · intro hc
    apply hg1
    have : (⟨g, hgS⟩ : ↥(Sec4.autFix β)) = 1 := ι.injective (hc.trans (map_one ι).symm)
    exact congrArg Subtype.val this

end OutStd

end CFSG.RankThree.PartTwo.Sec21.Hering214
