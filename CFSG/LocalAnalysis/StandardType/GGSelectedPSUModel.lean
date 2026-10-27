module

public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
public import CFSG.LocalAnalysis.StandardType.GGSelPSUChart
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits Matrix CFSG.StandardType.SelectedRoot.SelPSU
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.StandardType.PsiDiagChar (sl2Diag)
open CFSG.StandardType.RankOneXfer (sl2UpperUniSub mem_sl2UpperUniSub_iff)

theorem weight_ne_two_smul_weight_aux {n : ℕ} {c i : Fin n} (hi : i ≠ Fin.rev i) :
    Unitary.weight n c ≠ 2 • Unitary.weight n i := by
  intro h
  obtain ⟨ci, hci⟩ := SUExtras.exists_weight_ne_zero hi
  have h1 := congrFun h ci
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, SUExtras.weight_apply'] at h1
  have := ci.isLt
  split_ifs at h1 <;> omega

theorem rootGroup_le_range_long {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
    {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) {γ : Fin (n / 2) → ℤ}
    (hw : 2 • Unitary.weight n i = Unitary.toStd n γ) :
    Unitary.rootGroup σ hσ n γ ≤ (Unitary.longRootHom σ hi).range := by
  unfold CFSG.LieType.Universal.Unitary.rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun ha =>
      iSup_le fun _ => iSup_le fun hba => iSup_le fun hw' => ?_
    exfalso
    rw [← hw] at hw'
    obtain ⟨rfl, hbi⟩ := SUExtras.eq_of_weight_sub_eq_two_smul hi hw'
    exact hba hbi
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hw' => ?_
    rw [← hw] at hw'
    have h2 : Unitary.weight n a - Unitary.weight n (Fin.rev a) = 2 • Unitary.weight n i := by
      rw [SUExtras.weight_rev', sub_neg_eq_add, ← two_nsmul]
      exact hw'
    obtain ⟨rfl, -⟩ := SUExtras.eq_of_weight_sub_eq_two_smul hi h2
    exact le_rfl
  · refine iSup_le fun a => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hk => iSup_le fun hw' => ?_
    exfalso
    rw [← hw] at hw'
    exact weight_ne_two_smul_weight_aux hi hw'

theorem exists_selectedModel_PSU_chart_twoWt_at {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (i : Fin n) (hne : i ≠ Fin.rev i) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n i),
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f),
        (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F) =
          embM (pairCoord i)
            ((fixedSubfield F 2 f).subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) _)) := by
  have hσ : ∀ c : F, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : ∀ x ∈ fixedSubfield F 2 f, unitaryInvolution F 2 f x = x :=
    fun x hx => mem_fixedSubfield.mp hx
  have hι : Function.Injective (pairCoord i) := pairCoord_injective hne
  have hrev : ∀ r, pairCoord i (Fin.rev r) =
      Fin.rev (pairCoord i r) := pairCoord_rev _
  have hup : ∀ τ : fixedSubfield F 2 f,
      chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk (sl2Upper τ) =
        longRootHom (unitaryInvolution F 2 f) hne (Multiplicative.ofAdd
          ⟨(τ : F), traceZero_of_mem (unitaryInvolution F 2 f) (fixedSubfield F 2 f) h2 hk τ⟩) :=
    fun τ => chart_upper (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hne h2 hk τ
  have hupper : (sl2UpperUniSub (fixedSubfield F 2 f)).map
      (chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk) =
      (Unitary.rootDatum hF n).rootGroup (InnerDiagSU.twoWtRoot n i) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨τ, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
      rw [hup]
      exact SUExtras.longRootHom_mem hσ hne (InnerDiagSU.toStd_twoWtRoot _).symm _
    · intro y hy
      obtain ⟨c, rfl⟩ := rootGroup_le_range_long hσ hne (InnerDiagSU.toStd_twoWtRoot _).symm hy
      exact Subgroup.mem_map.mpr ⟨sl2Upper (⟨((Multiplicative.toAdd c :
          Unitary.traceZero (unitaryInvolution F 2 f)) : F), mem_fixedSubfield.mpr
        (fixed_of_mem_traceZero (unitaryInvolution F 2 f) h2 (Multiplicative.toAdd c).2)⟩ :
          fixedSubfield F 2 f), mem_sl2UpperUniSub_iff.mpr ⟨_, rfl⟩, hup _⟩
  have hdiag : ∀ a : (fixedSubfield F 2 f)ˣ,
      chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk (sl2Diag a) ∈
        ggTorus (Unitary.rootDatum hF n) := by
    intro a
    exact MpStdSU.mem_ggTorus_of_mat_eq_diagonal hF
      (t := dgn (fixedSubfield F 2 f) a i)
      (chart_sl2Diag_mat (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hne h2 hk a)
      (dgn_unitary (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hne hk a)
  have hscal : ∀ h ∈ ggTorus (Unitary.rootDatum hF n),
      ∃ c : (fixedSubfield F 2 f)ˣ, ∀ τ : fixedSubfield F 2 f,
        h * chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk (sl2Upper τ) *
            h⁻¹ =
          chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk
            (sl2Upper ((c : fixedSubfield F 2 f) * τ)) := by
    intro h hh
    obtain ⟨t, hd, ht⟩ : ∃ t : Fin n → F, SUExtras.mat (unitaryInvolution F 2 f) n h = diagonal t ∧
        ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1 :=
      ⟨fun s => SUExtras.mat (unitaryInvolution F 2 f) n h s s,
        InnerDiagSU.eq_diagonal_of_mem_ggTorus hF hh⟩
    have hconj := InnerDiagSU.conj_eq_conjSU_diagJ hd ht
    have ht0 : t i ≠ 0 := Unitary.ne_zero_of_unitary ht _
    have hinv : unitaryInvolution F 2 f (t i) = (t (Fin.rev i))⁻¹ :=
      eq_inv_of_mul_eq_one_left (ht i)
    have hfix : unitaryInvolution F 2 f (t i * unitaryInvolution F 2 f (t i)) =
        t i * unitaryInvolution F 2 f (t i) := by
      rw [map_mul, hσ, mul_comm]
    have hmem : t i * unitaryInvolution F 2 f (t i) ∈ fixedSubfield F 2 f :=
      mem_fixedSubfield.mpr hfix
    have hne0 : t i * unitaryInvolution F 2 f (t i) ≠ 0 :=
      mul_ne_zero ht0 ((map_ne_zero (unitaryInvolution F 2 f)).mpr ht0)
    refine ⟨Units.mk0 ⟨t i * unitaryInvolution F 2 f (t i), hmem⟩
      (fun h0 => hne0 (congrArg Subtype.val h0)), fun τ => ?_⟩
    rw [hconj, hup τ, InnerDiagSU.conjSU_diagJ_longRootHom t ht hne, hup]
    refine congrArg (fun z => longRootHom (unitaryInvolution F 2 f) hne (Multiplicative.ofAdd z))
      (Subtype.ext ?_)
    show t i * (τ : F) * (t (Fin.rev i))⁻¹ =
      (t i * unitaryInvolution F 2 f (t i)) * (τ : F)
    rw [← hinv]
    ring
  exact ⟨⟨InnerDiagSU.twoWtRoot_mem_roots hne,
      chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk,
      chart_injective (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk,
      hupper, hdiag, hscal⟩,
    fun A => coe_chart (unitaryInvolution F 2 f) (fixedSubfield F 2 f) hι hrev h2 hk A⟩

theorem exists_selectedModel_PSU_chart_twoWt {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n ⟨0, by omega⟩),
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f),
        (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F) =
          embM (pairCoord (⟨0, by omega⟩ : Fin n))
            ((fixedSubfield F 2 f).subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) _)) := by
  refine exists_selectedModel_PSU_chart_twoWt_at hF ⟨0, by omega⟩ ?_
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_rev] at h'
  omega

theorem exists_selectedModel_PSU_chart {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ (γ : Fin (Unitary.rootDatum hF n).rank → ℤ)
      (model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f) γ),
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f),
        (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F) =
          embM (pairCoord (⟨0, by omega⟩ : Fin n))
            ((fixedSubfield F 2 f).subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) _)) :=
  let ⟨model, h⟩ := exists_selectedModel_PSU_chart_twoWt hF hn
  ⟨_, model, h⟩

theorem exists_selectedModel_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ (γ : Fin (Unitary.rootDatum hF n).rank → ℤ)
      (model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f) γ),
      ∀ (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f)) (i j : Fin n),
        ((i ≠ ⟨0, by omega⟩ ∧ i ≠ Fin.rev ⟨0, by omega⟩) ∨
            (j ≠ ⟨0, by omega⟩ ∧ j ≠ Fin.rev ⟨0, by omega⟩)) →
          (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
              Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  obtain ⟨γ, model, hm⟩ := exists_selectedModel_PSU_chart hF hn
  refine ⟨γ, model, fun A i j hij => ?_⟩
  rw [hm A]
  refine embM_apply_of_not_mem _ ?_
  rintro ⟨hi', hj'⟩
  rw [mem_range_pairCoord] at hi' hj'
  rcases hij with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · rcases hi' with h | h
    · exact h1 h
    · exact h2' h
  · rcases hj' with h | h
    · exact h1 h
    · exact h2' h

end CFSG.StandardType.SelectedRoot

end
