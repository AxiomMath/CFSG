module

public import CFSG.RankThree.PartTwo.Sec8.Groups
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.LieType.Universal.Symplectic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix
open scoped commutatorElement

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem perfectResidual_eq_top_of_isPerfect {H : Type*} [Group H] (h : Group.IsPerfect H) :
    perfectResidual H = ⊤ := by
  have hD : ∀ n, derivedSeries H n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero H
    | succ n ih =>
      rw [derivedSeries_succ, ih, ← commutator_def]
      exact h.commutator_eq_top
  simp only [perfectResidual, hD, iInf_top]

theorem dvd_card_of_perfectResidual_mulEquiv {H : Type*} [Group H]
    (ι : perfectResidual H ≃* alternatingGroup (Fin 6)) : 360 ∣ Nat.card H := by
  rw [← card_alternatingGroup_six, ← Nat.card_congr ι.toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_eq_of_perfectResidual_mulEquiv {H : Type*} [Group H] (h : Group.IsPerfect H)
    (ι : perfectResidual H ≃* alternatingGroup (Fin 6)) : Nat.card H = 360 := by
  rw [← card_alternatingGroup_six, ← Nat.card_congr ι.toEquiv,
    perfectResidual_eq_top_of_isPerfect h, Subgroup.card_top]

theorem eq_one_of_perfectResidual_mulEquiv_alternatingGroup_six_of_projSp {H : Type*} [Group H]
    {m : ℕ} (hm : 1 ≤ m) (hH : Nonempty (H ≃* projSp 2 (GaloisField 2 m)))
    (hA : Nonempty (perfectResidual H ≃* alternatingGroup (Fin 6))) : m = 1 := by
  obtain ⟨e⟩ := hH
  obtain ⟨ι⟩ := hA
  by_contra hm1
  have hm2 : 2 ≤ m := by omega
  have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm2 : 2 ^ 2 ≤ 2 ^ m)
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hperf : Group.IsPerfect (StatedSp 2 (GaloisField 2 m)) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 (GaloisField 2 m) (by norm_num)
      (Or.inl (Or.inr (hF ▸ hq)))).1
  have hperfH : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective
      (f := ((statedSpEquivProjSpOfCharTwo (GaloisField 2 m)).trans e.symm).toMonoidHom)
      (MulEquiv.surjective _)
  have h360 := card_eq_of_perfectResidual_mulEquiv hperfH ι
  have hcard : Nat.card H = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec21.card_projSp_two hm2,
      CFSG.RankThree.PartTwo.Sec21.ordBC_two_eq (by omega)]
  have h1 : 256 ≤ (2 ^ m) ^ 4 := (Nat.pow_le_pow_left hq 4 : 4 ^ 4 ≤ (2 ^ m) ^ 4)
  have h2' : 16 ≤ (2 ^ m) ^ 2 := (Nat.pow_le_pow_left hq 2 : 4 ^ 2 ≤ (2 ^ m) ^ 2)
  have h2 : 15 ≤ (2 ^ m) ^ 2 - 1 := by omega
  have h3 : 255 ≤ (2 ^ m) ^ 4 - 1 := by omega
  have h4 : 360 < (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
    calc 360 < 256 * (15 * 255) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  omega

theorem not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_isoGTwoEven {H : Type}
    [Group H] {m : ℕ} (hH : Sec8.IsoGTwoEven H m) :
    ¬ Nonempty (perfectResidual H ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hH
  rintro ⟨ι⟩
  have hcard : Nat.card H = (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact (CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1
  have hdvd := dvd_card_of_perfectResidual_mulEquiv ι
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · rw [hcard] at hdvd
      norm_num at hdvd
  · have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm : 2 ^ 2 ≤ 2 ^ m)
    have hK3 : 3 ≤ Nat.card K := by omega
    have hperf := CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K hK3
    have hperfH : Group.IsPerfect H :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have h360 := card_eq_of_perfectResidual_mulEquiv hperfH ι
    have h1 : 4096 ≤ (2 ^ m) ^ 6 := (Nat.pow_le_pow_left hq 6 : 4 ^ 6 ≤ (2 ^ m) ^ 6)
    have h2' : 16 ≤ (2 ^ m) ^ 2 := (Nat.pow_le_pow_left hq 2 : 4 ^ 2 ≤ (2 ^ m) ^ 2)
    have h2 : 1 ≤ (2 ^ m) ^ 6 - 1 := by omega
    have h3 : 1 ≤ (2 ^ m) ^ 2 - 1 := by omega
    have h4 : 4096 ≤ (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) :=
      calc 4096 = 4096 * 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

section PGU

variable {K : Type} [Field K] {m : ℕ}

theorem commutator_glPi_false_le (h : UnitaryFieldData 2 m K) :
    ⁅Sec4.glPi false 3 (2 ^ m) K, Sec4.glPi false 3 (2 ^ m) K⁆ ≤ Sec4.slPi false 3 (2 ^ m) K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Sec4.mem_slPi_iff fun _ => h]
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · have h1 : GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have h2 : ((GeneralLinearGroup.det ⁅a, b⁆ : Kˣ) : K) = 1 := by rw [h1, Units.val_one]
    rwa [GeneralLinearGroup.val_det_apply] at h2

theorem card_ker_mk_slPi_le [Finite K] (h : UnitaryFieldData 2 m K) :
    Nat.card ((Matrix.ProjGenLinGroup.mk.comp (Sec4.slPi false 3 (2 ^ m) K).subtype).ker) ≤
      3 := by
  classical
  have := Fintype.ofFinite K
  set S := Sec4.slPi false 3 (2 ^ m) K
  have hscal : ∀ s : (Matrix.ProjGenLinGroup.mk.comp S.subtype).ker,
      ∃ c : Kˣ, ((s : S) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c ∧
        c ^ 3 = 1 := by
    intro s
    have h1 : ((s : S) : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      have h2 := s.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h2
      exact (QuotientGroup.eq_one_iff _).mp h2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, hc.symm, ?_⟩
    have hdet := ((Sec4.mem_slPi_false h).mp (s : S).2).1
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  choose c hc using hscal
  have hinj : Function.Injective c := by
    intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    rw [(hc s).1, (hc t).1, hst]
  have hle : Nat.card ((Matrix.ProjGenLinGroup.mk.comp S.subtype).ker) ≤
      Nat.card {a : Kˣ // a ^ 3 = 1} :=
    Nat.card_le_card_of_injective (fun s => (⟨c s, (hc s).2⟩ : {a : Kˣ // a ^ 3 = 1}))
      fun s t hst => hinj (congrArg Subtype.val hst)
  have h3 : Nat.card {a : Kˣ // a ^ 3 = 1} ≤ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  exact hle.trans h3

theorem card_slPi_eq_mul (S : Subgroup (GL (Fin 3) K)) :
    Nat.card S = Nat.card ((Matrix.ProjGenLinGroup.mk.comp S.subtype).ker) *
      Nat.card (projImage S) := by
  have h1 : (Matrix.ProjGenLinGroup.mk.comp S.subtype).range = projImage S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]

end PGU

end CFSG.RankThree.PartTwo.KFacts
