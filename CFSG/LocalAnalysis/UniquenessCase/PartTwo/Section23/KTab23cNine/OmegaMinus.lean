module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Generic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusRoot
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.RankThree.PartOne.KC.OrthogonalTailDiagonalRoots

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open Matrix Subgroup
open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.OmegaMinus6Tail
open CFSG.AGLEmbedding.LeviBlock (orthParab)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Hinf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC
open CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem hypVec_inl_zero_ne_zero {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
    (hr : 1 ≤ r) : hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r)) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    have := congrFun (congrArg Prod.fst h) (Sum.inl (⟨0, hr⟩ : Fin r))
    simpa [hypVec, Pi.single_eq_same] using this
  exact one_ne_zero h1

private theorem tailUnipotent_apply_hypVec_inl {A : Type} [AddCommGroup A] [Module K A]
    {r : ℕ} {qA : QuadraticForm K A} (hr : 1 ≤ r)
    {e : ↥(orthElementaryGroup (quadTail r qA))}
    (he : e ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))) :
    e.val (hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) =
      hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r)) :=
  MulAction.mem_stabilizer_iff.mp
    (tailUnipotent_le_stabilizer (r := r) (qA := qA) hr (Subgroup.mem_subgroupOf.mp he))

private theorem conj_apply_hypVec_inl_eq_self {A : Type} [AddCommGroup A] [Module K A]
    {r : ℕ} {qA : QuadraticForm K A} (hr : 1 ≤ r)
    {e g : ↥(orthElementaryGroup (quadTail r qA))}
    (he : e ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)))
    (hg : g.val (hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) =
      hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) :
    (↑(e * g * e⁻¹) : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        (hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) =
      hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r)) := by
  have hx := tailUnipotent_apply_hypVec_inl (K := K) (A := A) (qA := qA) hr he
  have hx' := tailUnipotent_apply_hypVec_inl (K := K) (A := A) (qA := qA) hr (inv_mem he)
  change (e.val * g.val * (e⁻¹).val) (hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) =
    hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx', hg, hx]

private theorem eq_one_of_smul_hypVec_inl_eq_self {A : Type} [AddCommGroup A] [Module K A]
    {r : ℕ} (hr : 1 ≤ r) {c : K}
    (h : c • hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r)) =
      hypVec K A (Sum.inl (⟨0, hr⟩ : Fin r))) : c = 1 :=
  smul_left_injective K (hypVec_inl_zero_ne_zero (K := K) (A := A) hr) (by simpa using h)

private theorem eq_one_of_conj_eq_one {G : Type} [Group G] {e g : G} (h : e * g * e⁻¹ = 1) :
    g = 1 := by
  calc g = e⁻¹ * (e * g * e⁻¹) * e := by group
    _ = e⁻¹ * 1 * e := by rw [h]
    _ = 1 := by group

private theorem minusPhi_apply_hypVec_inl_of_mem_vecStab {k : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(StatedOmega (StatedQuadMinus (k + 3) K b c))}
    (ht : t ∈ vecStab (StatedOmega (StatedQuadMinus (k + 3) K b c)).subtype
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K))) :
    (minusPhi hirr k t).val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2)))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) := by
  let ψ := minusTailIsometry (k + 3) K b c
  let e0 : Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K :=
    Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K)
  let x : (Fin (k + 2) ⊕ Fin (k + 2) → K) × (Fin 2 → K) :=
    hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2)))
  have hψx : ψ x = e0 := by
    simpa [ψ, x, e0] using minusTailIsometry_hypVec_inl (k := k) (i := 0)
  have ht2 : ((t.val : GL (Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2) K) :
      Matrix _ _ K) *ᵥ e0 = e0 := mem_vecStab.mp ht
  have hkey := tailOmegaEquiv_symm_mulVec ψ
    (CFSG.LieType.Universal.Spin.coe_quadMinus (k + 3) K b c)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := k + 3) (by omega) hirr) (minusPhi hirr k t) x
  rw [show minusPhi hirr k = tailOmegaEquiv ψ
      (CFSG.LieType.Universal.Spin.coe_quadMinus (k + 3) K b c)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
        (n := k + 3) (by omega) hirr) from rfl,
    MulEquiv.symm_apply_apply, hψx, ht2] at hkey
  exact ψ.injective (hkey.symm.trans hψx.symm)

private theorem om6m_exists_conj_tailDiag_of_mem_hinf
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hgH : g ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]))
    (hgQ0 : g ∈ orthParab 2 (minusTailForm K b c) ![0, 1])
    (hodd : Odd (orderOf g)) :
    ∃ e ∈ (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))),
      ∃ u : Kˣ, (↑(e * g * e⁻¹) : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) = tailDiag 2 ![u, u⁻¹] 1 := by
  have hgB : g ∈ (tailBorel 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := by
    rw [← om6m_orthParab_inf_eq_tailBorel]
    exact ⟨hgQ0, Subgroup.map_subtype_le _ hgH⟩
  have hodd' : ¬ 2 ∣ orderOf g := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  obtain ⟨e, he, hτT⟩ := om6m_exists_conj_mem_tailTorus hirr hgB hodd'
  have hτH : e * g * e⁻¹ ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]) := by
    have hePα : e ∈ orthParab 2 (minusTailForm K b c) ![0, 2] :=
      (om6m_tailUnipotent_le_orthParab hirr he).2
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22m_le_normalizer_Hinf _ hePα) g).1 hgH
  obtain ⟨-, a, h, -, hdiag⟩ := mem_tailTorus.1 (Subgroup.mem_subgroupOf.1 hτT)
  obtain ⟨ha01, hh1⟩ := om6m_tailDiag_of_mem_hinf hirr hτH hdiag.symm
  have h01u : a 0 * a 1 = 1 := by
    apply Units.ext
    simpa using ha01
  have ha : a = ![a 0, (a 0)⁻¹] := by
    funext i
    fin_cases i
    · simp
    · simpa using eq_inv_of_mul_eq_one_right h01u
  refine ⟨e, he, a 0, ?_⟩
  rw [← hdiag]
  conv_lhs => rw [ha]
  rw [hh1]

private theorem om6m_eq_one_of_mem_hinf_of_fixes (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hgH : g ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]))
    (hgQ0 : g ∈ orthParab 2 (minusTailForm K b c) ![0, 1])
    (hgx : g.val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)))
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨e, he, u, hτdiag⟩ := om6m_exists_conj_tailDiag_of_mem_hinf hirr hgH hgQ0 hodd
  have hτx : (↑(e * g * e⁻¹) : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)))
        (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)) := by
    simpa using conj_apply_hypVec_inl_eq_self (K := K) (A := Fin 2 → K) (r := 2)
      (qA := minusTailForm K b c) (by norm_num) he hgx
  have hux : ((u : Kˣ) : K) • hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)) := by
    have h := hτx
    rw [hτdiag, tailDiag_hypVec_inl] at h
    exact h
  have hu1 : u = 1 := by
    apply Units.ext
    exact eq_one_of_smul_hypVec_inl_eq_self (K := K) (A := Fin 2 → K) (r := 2)
      (by norm_num) (by simpa using hux)
  have hτ1 : e * g * e⁻¹ = 1 := by
    apply Subtype.ext
    rw [hτdiag, hu1]
    have h1 : (![1, (1 : Kˣ)⁻¹] : Fin 2 → Kˣ) = 1 := by
      funext i
      fin_cases i <;> simp
    rw [h1, tailDiag_one_one]
    rfl
  exact eq_one_of_conj_eq_one hτ1

private theorem om6m_minusPhi_mem_of_mem_hinf_vecStab
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(StatedOmega (StatedQuadMinus 3 K b c))}
    (ht : t ∈ Hinf ((orthParab 2 (minusTailForm K b c) ![0, 2]).map
        (minusPhi hirr 0).symm.toMonoidHom) ⊓
      vecStab (StatedOmega (StatedQuadMinus 3 K b c)).subtype
        (Pi.single (Sum.inl (0 : Fin 2)) (1 : K))) :
    minusPhi hirr 0 t ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]) ⊓
        orthParab 2 (minusTailForm K b c) ![0, 1] ∧
      (minusPhi hirr 0 t).val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2))) =
        hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)) := by
  let φ := minusPhi hirr 0
  have hline : t ∈ KTabD.lineStab (StatedOmega (StatedQuadMinus 3 K b c))
      (Pi.single (Sum.inl (0 : Fin 2)) (1 : K)) := by
    rw [KTabD.mem_lineStab]
    exact ⟨1, by simpa using mem_vecStab.mp ht.2⟩
  have hQ0map : (orthParab 2 (minusTailForm K b c) ![0, 1]).map φ.symm.toMonoidHom =
      KTabD.lineStab (StatedOmega (StatedQuadMinus 3 K b c))
        (Pi.single (Sum.inl (0 : Fin 2)) (1 : K)) := by
    simpa [φ] using map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 0
  have hgQ0 : φ t ∈ orthParab 2 (minusTailForm K b c) ![0, 1] := by
    have h : φ t ∈ (KTabD.lineStab (StatedOmega (StatedQuadMinus 3 K b c))
        (Pi.single (Sum.inl (0 : Fin 2)) (1 : K))).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hline
    rw [← hQ0map, Subgroup.map_map,
      show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ from
        MulEquiv.toMonoidHom_comp_toMonoidHom_symm φ, Subgroup.map_id] at h
    exact h
  have hHmap : (Hinf (orthParab 2 (minusTailForm K b c) ![0, 2])).map φ.symm.toMonoidHom =
      Hinf ((orthParab 2 (minusTailForm K b c) ![0, 2]).map φ.symm.toMonoidHom) :=
    Hinf_map φ.symm.toMonoidHom _
  have hgH : φ t ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]) := by
    have h : φ t ∈ (Hinf ((orthParab 2 (minusTailForm K b c) ![0, 2]).map
        φ.symm.toMonoidHom)).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom ht.1
    rw [← hHmap, Subgroup.map_map,
      show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ from
        MulEquiv.toMonoidHom_comp_toMonoidHom_symm φ, Subgroup.map_id] at h
    exact h
  exact ⟨⟨hgH, hgQ0⟩, by
    simpa [φ, hypVec] using minusPhi_apply_hypVec_inl_of_mem_vecStab (k := 0) hirr
      (t := t) (by simpa using ht.2)⟩

theorem om6m_eq_one_of_mem_hinf_vecStab (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(StatedOmega (StatedQuadMinus 3 K b c))}
    (ht : t ∈ Hinf ((orthParab 2 (minusTailForm K b c) ![0, 2]).map
        (minusPhi hirr 0).symm.toMonoidHom) ⊓
      vecStab (StatedOmega (StatedQuadMinus 3 K b c)).subtype
        (Pi.single (Sum.inl (0 : Fin 2)) (1 : K)))
    (hodd : Odd (orderOf t)) : t = 1 := by
  obtain ⟨⟨hgH, hgQ0⟩, hgx⟩ := om6m_minusPhi_mem_of_mem_hinf_vecStab hirr ht
  have hoddg : Odd (orderOf (minusPhi hirr 0 t)) := by
    rw [show orderOf (minusPhi hirr 0 t) = orderOf t from
      MulEquiv.orderOf_eq (minusPhi hirr 0) t]
    exact hodd
  have hg1 := om6m_eq_one_of_mem_hinf_of_fixes hirr hgH hgQ0 hgx hoddg
  exact (minusPhi hirr 0).injective (by rw [hg1, map_one])

private theorem om8m_exists_conj_coroot_of_mem_hinf_of_fixes
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : OmegaMinusE K b c}
    (hgH : g ∈ Hinf (omegaMinusTailQAlpha K b c))
    (hgQ0 : g ∈ omegaMinusTailQZero K b c)
    (hgx : g.val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)))
    (hodd : Odd (orderOf g)) :
    ∃ e ∈ (tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))), ∃ u : Kˣ,
      (↑(e * g * e⁻¹) : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        prodHom (Fin 2 → K) (torusElt 3 K ![u, u⁻¹, 1]) ∧
      ((u : Kˣ) : K) • hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) =
        hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) := by
  obtain ⟨e, he, u, hτ, -⟩ := omegaMinus_exists_conj_coroot hirr ⟨hgH, hgQ0⟩ hodd
  have hτx : (↑(e * g * e⁻¹) : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)))
        (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) := by
    simpa using conj_apply_hypVec_inl_eq_self (K := K) (A := Fin 2 → K) (r := 3)
      (qA := minusTailForm K b c) (by norm_num) he hgx
  have hux : ((u : Kˣ) : K) • hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) := by
    have h := hτx
    rw [hτ] at h
    have hg : torusElt 3 K ![u, u⁻¹, 1] (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)) =
        ((u : Kˣ) : K) • Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
      funext i
      by_cases hi : i = Sum.inl (0 : Fin 3)
      · subst hi
        simp [torusElt_apply]
      · rw [torusElt_apply, Pi.smul_apply, Pi.single_eq_of_ne hi]
        simp
    rw [CFSG.RankThree.PartOne.KCOrthogonal.prodHom_apply_hypVec
      (torusElt 3 K ![u, u⁻¹, 1]) (Sum.inl (0 : Fin 3)) ((u : Kˣ) : K) hg] at h
    exact h
  exact ⟨e, he, u, hτ, hux⟩

private theorem om8m_eq_one_of_mem_hinf_of_fixes (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : OmegaMinusE K b c}
    (hgH : g ∈ Hinf (omegaMinusTailQAlpha K b c))
    (hgQ0 : g ∈ omegaMinusTailQZero K b c)
    (hgx : g.val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3))) =
      hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)))
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨e, he, u, hτ, hux⟩ :=
    om8m_exists_conj_coroot_of_mem_hinf_of_fixes hirr hgH hgQ0 hgx hodd
  have hu1 : u = 1 := by
    apply Units.ext
    exact eq_one_of_smul_hypVec_inl_eq_self (K := K) (A := Fin 2 → K) (r := 3)
      (by norm_num) (by simpa using hux)
  have hτ1 : e * g * e⁻¹ = 1 := by
    apply Subtype.ext
    rw [hτ, hu1]
    have h1 : (![1, (1 : Kˣ)⁻¹, 1] : Fin 3 → Kˣ) = 1 := by
      funext i
      fin_cases i <;> simp
    rw [h1, map_one, map_one]
    rfl
  exact eq_one_of_conj_eq_one hτ1

private theorem om8m_minusPhi_mem_of_mem_hinf_vecStab
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(StatedOmega (StatedQuadMinus 4 K b c))}
    (ht : t ∈ Hinf (omegaMinusQAlpha (minusPhi hirr 1)) ⊓
      vecStab (StatedOmega (StatedQuadMinus 4 K b c)).subtype
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K))) :
    minusPhi hirr 1 t ∈ Hinf (omegaMinusTailQAlpha K b c) ⊓ omegaMinusTailQZero K b c ∧
      (minusPhi hirr 1 t).val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3))) =
        hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) := by
  let φ := minusPhi hirr 1
  have hline : t ∈ KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c))
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)) := by
    rw [KTabD.mem_lineStab]
    exact ⟨1, by simpa using mem_vecStab.mp ht.2⟩
  have hQ0map : (orthParab 3 (minusTailForm K b c) ![0, 1]).map φ.symm.toMonoidHom =
      KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c))
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)) := by
    simpa [φ] using map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 1
  have hgQ0 : φ t ∈ omegaMinusTailQZero K b c := by
    have h : φ t ∈ (KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c))
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K))).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hline
    rw [← hQ0map, Subgroup.map_map,
      show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ from
        MulEquiv.toMonoidHom_comp_toMonoidHom_symm φ, Subgroup.map_id] at h
    exact h
  have hgH : φ t ∈ Hinf (omegaMinusTailQAlpha K b c) := by
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom ht.1
    rw [show omegaMinusQAlpha φ = (omegaMinusTailQAlpha K b c).comap φ.toMonoidHom from rfl,
      Hinf_map φ.toMonoidHom ((omegaMinusTailQAlpha K b c).comap φ.toMonoidHom),
      Subgroup.map_comap_eq_self_of_surjective φ.surjective
        (omegaMinusTailQAlpha K b c)] at h
    exact h
  exact ⟨⟨hgH, hgQ0⟩, by
    simpa [φ, hypVec] using minusPhi_apply_hypVec_inl_of_mem_vecStab (k := 1) hirr
      (t := t) (by simpa using ht.2)⟩

theorem om8m_eq_one_of_mem_hinf_vecStab (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(StatedOmega (StatedQuadMinus 4 K b c))}
    (ht : t ∈ Hinf (omegaMinusQAlpha (minusPhi hirr 1)) ⊓
      vecStab (StatedOmega (StatedQuadMinus 4 K b c)).subtype
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)))
    (hodd : Odd (orderOf t)) : t = 1 := by
  obtain ⟨⟨hgH, hgQ0⟩, hgx⟩ := om8m_minusPhi_mem_of_mem_hinf_vecStab hirr ht
  have hoddg : Odd (orderOf (minusPhi hirr 1 t)) := by
    rw [show orderOf (minusPhi hirr 1 t) = orderOf t from
      MulEquiv.orderOf_eq (minusPhi hirr 1) t]
    exact hodd
  have hg1 := om8m_eq_one_of_mem_hinf_of_fixes hirr hgH hgQ0 hgx hoddg
  exact (minusPhi hirr 1).injective (by rw [hg1, map_one])

private abbrev Om6mModel (K : Type) [Field K] (b c : K) : Type :=
  ↥(StatedOmega (StatedQuadMinus 3 K b c))

private abbrev Om8mModel (K : Type) [Field K] (b c : K) : Type :=
  ↥(StatedOmega (StatedQuadMinus 4 K b c))

private noncomputable def om6mE0 (K : Type) [Field K] :
    Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) (1 : K)

private noncomputable def om8mE0 (K : Type) [Field K] :
    Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (4 - 1))) (1 : K)

private noncomputable abbrev om6mQAlpha {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Subgroup (Om6mModel K b c) :=
  (orthParab 2 (minusTailForm K b c) ![0, 2]).map (minusPhi hirr 0).symm.toMonoidHom

private noncomputable abbrev om6mQZero (K : Type) [Field K] (b c : K) :
    Subgroup (Om6mModel K b c) :=
  KTabD.lineStab (StatedOmega (StatedQuadMinus 3 K b c)) (om6mE0 K)

private noncomputable abbrev om6mCZero (K : Type) [Field K] (b c : K) :
    Subgroup (Om6mModel K b c) :=
  vecStab (StatedOmega (StatedQuadMinus 3 K b c)).subtype (om6mE0 K)

private noncomputable def om6mSylow {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Sylow 2 (Om6mModel K b c) :=
  (t2Sylow K b c hirr).mapSurjective (f := (minusPhi hirr 0).symm.toMonoidHom)
    (minusPhi hirr 0).symm.surjective

private theorem om6mSylow_le_lineStab {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (om6mSylow hirr : Subgroup (Om6mModel K b c)) ≤ om6mQZero K b c := by
  have hQ0 : om6mQZero K b c =
      (orthParab 2 (minusTailForm K b c) ![0, 1]).map
        (minusPhi hirr 0).symm.toMonoidHom := by
    simpa [om6mQZero, om6mE0] using
      (map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 0).symm
  rw [show (om6mSylow hirr : Subgroup (Om6mModel K b c)) =
      (t2Sylow K b c hirr : Subgroup ↥(T2G K b c)).map
        (minusPhi hirr 0).symm.toMonoidHom from
    Sylow.coe_mapSurjective (f := (minusPhi hirr 0).symm.toMonoidHom)
      (minusPhi hirr 0).symm.surjective (t2Sylow K b c hirr), hQ0]
  refine Subgroup.map_mono ?_
  rw [t2Sylow_coe]
  exact (om6m_tailUnipotent_le_orthParab hirr).trans inf_le_left

private theorem om6m_leastParabolic {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo (Om6mModel K b c) (om6mQAlpha hirr) ∧
      (om6mSylow hirr : Subgroup (Om6mModel K b c)) ≤ om6mQAlpha hirr ∧
      ¬ om6mQAlpha hirr ≤ om6mQZero K b c ∧
      ∀ P : Subgroup (Om6mModel K b c), IsParabolicTwo (Om6mModel K b c) P →
        (om6mSylow hirr : Subgroup (Om6mModel K b c)) ≤ P →
        ¬ P ≤ om6mQZero K b c → om6mQAlpha hirr ≤ P := by
  have hU0 : (t2Sylow K b c hirr : Subgroup ↥(T2G K b c)) =
      (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := t2Sylow_coe K b c hirr
  have hUS : ((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c)))).map
      (minusPhi hirr 0).symm.toMonoidHom =
      (om6mSylow hirr : Subgroup (Om6mModel K b c)) := by
    rw [← hU0]
    exact (Sylow.coe_mapSurjective (f := (minusPhi hirr 0).symm.toMonoidHom)
      (minusPhi hirr 0).symm.surjective (t2Sylow K b c hirr)).symm
  have hQ0 : om6mQZero K b c =
      (orthParab 2 (minusTailForm K b c) ![0, 1]).map
        (minusPhi hirr 0).symm.toMonoidHom := by
    simpa [om6mQZero, om6mE0] using
      (map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 0).symm
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := leastParabolic_map (minusPhi hirr 0).symm hUS
    (om6m_isParabolicTwo_orthParab_two hirr)
    ((om6m_tailUnipotent_le_orthParab hirr).trans inf_le_right)
    (om6m_not_orthParab_two_le_one hirr)
    (fun P hP hU hnotP => om6m_orthParab_two_le_of_parabolic hirr hP hU hnotP)
  exact ⟨hpar, hUQ, by rwa [hQ0], fun P hP hU hnotP => hleast P hP hU (by rwa [hQ0] at hnotP)⟩

theorem kTab23cNineAt_of_realizes_om6m {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hreal : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))).Realizes H ⊤ ⊥) :
    KTab23cNineAt W H := by
  let e0 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := om6mE0 K
  let Qα : Subgroup (Om6mModel K b c) := om6mQAlpha hirr
  let Q₀ : Subgroup (Om6mModel K b c) := om6mQZero K b c
  let C₀ : Subgroup (Om6mModel K b c) := om6mCZero K b c
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := om6m_leastParabolic (K := K) (b := b) (c := c) hirr
  have he0 : e0 ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by
      have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1)))
      simpa [e0, om6mE0] using this
    exact one_ne_zero h1
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadMinus 3 K b c)) e0 := by
    simpa [e0, om6mE0] using
      KTabD.sylowFixedLine_omegaMinus (K := K) (m := 3) (b := b) (c := c)
        (by norm_num) hirr
  refine kTab23cNineAt_of_model H (om6mSylow hirr) Qα Q₀ C₀ ?_ hpar hUQ hnot hleast
    (fun t ht hodd => om6m_eq_one_of_mem_hinf_vecStab (K := K) (b := b) (c := c) hirr ht hodd)
  intro S
  exact exists_mulEquiv_pointStab_fixSub_eq_map_sylow (e₀ := e0) hreal he0 hline
    (om6mSylow hirr) (om6mSylow_le_lineStab hirr) S

theorem kTab23cNineAt_om6m {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 6 n) : KTab23cNineAt W H := by
  obtain ⟨-, K, hKf, hKfin, b, c, hK, hirr, hreal⟩ := h
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  rw [show 6 / 2 = 3 by norm_num] at hreal
  exact kTab23cNineAt_of_realizes_om6m H hirr hreal

private noncomputable abbrev om8mQAlpha {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Subgroup (Om8mModel K b c) :=
  omegaMinusQAlpha (minusPhi hirr 1)

private noncomputable def om8mSylow {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Sylow 2 (Om8mModel K b c) :=
  (t3Sylow (K := K) (b := b) (c := c) hirr).mapSurjective
    (f := (minusPhi hirr 1).symm.toMonoidHom) (minusPhi hirr 1).symm.surjective

private theorem om8mSylow_le_lineStab {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (om8mSylow hirr : Subgroup (Om8mModel K b c)) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c)) (om8mE0 K) := by
  have hQ0 : KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c)) (om8mE0 K) =
      (omegaMinusTailQZero K b c).map (minusPhi hirr 1).symm.toMonoidHom := by
    simpa [om8mE0, omegaMinusTailQZero] using
      (map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 1).symm
  rw [show (om8mSylow hirr : Subgroup (Om8mModel K b c)) =
      (t3Sylow (K := K) (b := b) (c := c) hirr : Subgroup (OmegaMinusE K b c)).map
        (minusPhi hirr 1).symm.toMonoidHom from
    Sylow.coe_mapSurjective (f := (minusPhi hirr 1).symm.toMonoidHom)
      (minusPhi hirr 1).symm.surjective (t3Sylow (K := K) (b := b) (c := c) hirr), hQ0]
  refine Subgroup.map_mono ?_
  rw [t3Sylow_coe]
  exact (omegaMinus_tailUnipotent_le_inf hirr).trans inf_le_left

private theorem om8m_leastParabolic {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo (Om8mModel K b c) (om8mQAlpha hirr) ∧
      (om8mSylow hirr : Subgroup (Om8mModel K b c)) ≤ om8mQAlpha hirr ∧
      ¬ om8mQAlpha hirr ≤ omegaMinusQZero K b c ∧
      ∀ P : Subgroup (Om8mModel K b c), IsParabolicTwo (Om8mModel K b c) P →
        (om8mSylow hirr : Subgroup (Om8mModel K b c)) ≤ P →
        ¬ P ≤ omegaMinusQZero K b c → om8mQAlpha hirr ≤ P := by
  have hU0 : (t3Sylow (K := K) (b := b) (c := c) hirr : Subgroup (OmegaMinusE K b c)) =
      t3U K b c := t3Sylow_coe hirr
  have hUS : (t3U K b c).map (minusPhi hirr 1).symm.toMonoidHom =
      (om8mSylow hirr : Subgroup (Om8mModel K b c)) := by
    rw [← hU0]
    exact (Sylow.coe_mapSurjective (f := (minusPhi hirr 1).symm.toMonoidHom)
      (minusPhi hirr 1).symm.surjective (t3Sylow (K := K) (b := b) (c := c) hirr)).symm
  have hφ : (omegaMinusQZero K b c).map (minusPhi hirr 1).toMonoidHom =
      omegaMinusTailQZero K b c := by
    have hQ0 : omegaMinusQZero K b c =
        (omegaMinusTailQZero K b c).map (minusPhi hirr 1).symm.toMonoidHom := by
      simpa [omegaMinusQZero, omegaMinusTailQZero] using
        (map_orthParab_minusPhi_symm (K := K) (b := b) (c := c) hirr 1).symm
    rw [hQ0, Subgroup.map_map,
      show (minusPhi hirr 1).toMonoidHom.comp (minusPhi hirr 1).symm.toMonoidHom =
        MonoidHom.id _ from MulEquiv.toMonoidHom_comp_toMonoidHom_symm (minusPhi hirr 1),
      Subgroup.map_id]
  have h := leastParabolic_omegaMinusQAlpha (K := K) (b := b) (c := c) hirr
    (minusPhi hirr 1) hφ
  refine ⟨h.1, ?_, h.2.2.1, ?_⟩
  · simpa only [hUS] using h.2.1
  · intro P hP hU hnotP
    exact h.2.2.2 P hP (by simpa only [← hUS] using hU) hnotP

theorem kTab23cNineAt_of_realizes_omegaMinusEight {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hreal : (FFModel.nat (StatedOmega (StatedQuadMinus 4 K b c))).Realizes H ⊤ ⊥) :
    KTab23cNineAt W H := by
  let e0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K := om8mE0 K
  let Qα : Subgroup (Om8mModel K b c) := om8mQAlpha hirr
  let Q₀ : Subgroup (Om8mModel K b c) :=
    KTabD.lineStab (StatedOmega (StatedQuadMinus 4 K b c)) e0
  let C₀ : Subgroup (Om8mModel K b c) :=
    vecStab (StatedOmega (StatedQuadMinus 4 K b c)).subtype e0
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := om8m_leastParabolic (K := K) (b := b) (c := c) hirr
  have he0 : e0 ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by
      have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin (4 - 1)))
      simpa [e0, om8mE0] using this
    exact one_ne_zero h1
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadMinus 4 K b c)) e0 := by
    simpa [e0, om8mE0] using
      KTabD.sylowFixedLine_omegaMinus (K := K) (m := 4) (b := b) (c := c)
        (by norm_num) hirr
  refine kTab23cNineAt_of_model H (om8mSylow hirr) Qα Q₀ C₀ ?_ hpar hUQ hnot hleast
    (fun t ht hodd => om8m_eq_one_of_mem_hinf_vecStab (K := K) (b := b) (c := c) hirr ht hodd)
  intro S
  exact exists_mulEquiv_pointStab_fixSub_eq_map_sylow (e₀ := e0) hreal he0 hline
    (om8mSylow hirr) (om8mSylow_le_lineStab hirr) S

theorem kTab23cNineAt_omegaMinusEight {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 8 n) :
    KTab23cNineAt W H := by
  obtain ⟨-, K, hKf, hKfin, b, c, hK, hirr, hreal⟩ := h
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  rw [show 8 / 2 = 4 by norm_num] at hreal
  exact kTab23cNineAt_of_realizes_omegaMinusEight H hirr hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
