module

public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpDer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

private theorem ggK1CBc_commutator_equiv {G B : Type} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) : Nonempty (↥⁅A, A⁆ ≃* ↥(commutator B)) := by
  have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  exact ⟨e1.symm.trans (MulEquiv.commutatorCongr φ)⟩

private theorem ggK1CBc_isSolvable_of_mulEquiv {G B : Type} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) (hB : Group.IsSolvable B) : Group.IsSolvable ↥A := by
  haveI := hB
  exact Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective

private theorem ggK1CBc_not_quasisimple_of_isSolvable {G : Type} [Group G] {A : Subgroup G}
    (h : Group.IsSolvable ↥A) : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  haveI := h
  intro hq
  have hle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
  haveI : Group.IsSolvable ↥⁅A, A⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅A, A⁆ := hq.1
  haveI : Nontrivial ↥⁅A, A⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥⁅A, A⁆ inferInstance

private theorem ggK1CBc_statedSL_equiv (m : ℕ) (K : Type) [Field K] :
    Nonempty (↥(StatedSL m K) ≃* Matrix.SpecialLinearGroup (Fin m) K) :=
  ⟨((Subgroup.equivMapOfInjective (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m) K))
      Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [Subgroup.map_top]
      exact (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m K).symm))).symm.trans
      Subgroup.topEquiv⟩

private theorem ggK1CBc_sl_model {G : Type} [Group G] {A : Subgroup G} {m : ℕ} {K : Type} [Field K]
    (φ : ↥A ≃* Matrix.GeneralLinearGroup (Fin m) K)
    (hcomm : commutator (Matrix.GeneralLinearGroup (Fin m) K) = StatedSL m K) :
    Nonempty (↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin m) K) := by
  obtain ⟨e⟩ := ggK1CBc_commutator_equiv φ
  obtain ⟨eSL⟩ := ggK1CBc_statedSL_equiv m K
  exact ⟨e.trans ((MulEquiv.subgroupCongr hcomm).trans eSL)⟩

private theorem ggK1CBc_sp_model_of_isQuasisimple {G : Type} [Group G] {A : Subgroup G} {s : ℕ}
    {K : Type} [Field K] (φ : ↥A ≃* StatedSp s K)
    (hq : CFSG.IsQuasisimple (StatedSp s K)) :
    Nonempty (↥⁅A, A⁆ ≃* StatedSp s K) := by
  obtain ⟨e⟩ := ggK1CBc_commutator_equiv φ
  have htop : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp hq.1
  exact ⟨e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

private theorem ggK1CBc_kindOrbit_sl_one (nf : ℕ) :
    (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl 1)).qs = false := rfl

private theorem ggK1CBc_kindOrbit_sl_of_ne_one {nf m : ℕ} (hm : m ≠ 1) :
    (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl m)).qs =
      decide (¬ (m - 1 = 1 ∧ nf = 1)) := by
  match m with
  | 0 => rfl
  | 1 => exact absurd rfl hm
  | _ + 2 => rfl

private theorem ggK1CBc_kindOrbit_sp_one (nf : ℕ) :
    (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp 1)).qs = decide (nf ≠ 1) := rfl

private theorem ggK1CBc_kindOrbit_sp_two_one :
    (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sp 2)).qs = true := by
  simp [ggK1CCo_kindOrbit]

private theorem ggK1CBc_kindOrbit_sp_of_ne {nf s : ℕ} (h1 : s ≠ 1)
    (h2 : ¬ (s = 2 ∧ nf = 1)) :
    (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp s)).qs = true := by
  simp [ggK1CCo_kindOrbit, h1, h2]

theorem ggK1CBl_classical_sl {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {m : ℕ}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf) (hm : 1 ≤ m)
    (e : ↥A ≃* Matrix.GeneralLinearGroup (Fin m) K) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ ↔
        (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl m)).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ → ggK1CBl_Model nf K (ggK1CCo_Kind.sl m) ↥⁅A, A⁆) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rcases eq_or_ne m 1 with hm1 | hm1
  ·
    subst m
    have hsolv : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 1) K) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 K
        (Or.inl rfl)
    haveI : Group.IsSolvable ↥A := ggK1CBc_isSolvable_of_mulEquiv e hsolv
    have hnotq : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ :=
      ggK1CBc_not_quasisimple_of_isSolvable (A := A) inferInstance
    have hflag : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl 1)).qs = false :=
      ggK1CBc_kindOrbit_sl_one nf
    refine ⟨Or.inr inferInstance, ?_, ?_⟩
    · rw [hflag]
      exact ⟨fun h => absurd h hnotq, fun h => (Bool.false_eq_true.mp h).elim⟩
    · intro h
      exact absurd h hnotq
  · have hm2 : 2 ≤ m := by omega
    by_cases hcorner : m = 2 ∧ nf = 1
    ·
      obtain ⟨rfl, rfl⟩ := hcorner
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hsolv : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
          (Or.inl hK2)
      haveI : Group.IsSolvable ↥A := ggK1CBc_isSolvable_of_mulEquiv e hsolv
      have hnotq : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        ggK1CBc_not_quasisimple_of_isSolvable (A := A) inferInstance
      have hflag : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sl 2)).qs = false := by
        rw [ggK1CBc_kindOrbit_sl_of_ne_one (nf := 1) (by norm_num : (2 : ℕ) ≠ 1)]
        rfl
      refine ⟨Or.inr inferInstance, ?_, ?_⟩
      · rw [hflag]
        exact ⟨fun h => absurd h hnotq, fun h => (Bool.false_eq_true.mp h).elim⟩
      · intro h
        exact absurd h hnotq
    ·
      have hcond : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4 := by
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · obtain rfl : m = 2 := by omega
          right
          have hnf2 : 2 ≤ nf := by
            by_contra hcon
            exact hcorner ⟨rfl, by omega⟩
          have h4 : 4 ≤ Nat.card K := by
            rw [hK]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) hnf2
          have h4' : 4 ≤ (Finset.univ : Finset K).card := by
            simpa [Nat.card_eq_fintype_card] using h4
          obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
          exact ⟨s, hs⟩
        · exact Or.inl h3
      have hcomm : commutator (Matrix.GeneralLinearGroup (Fin m) K) = StatedSL m K :=
        GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm2 hcond
      have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) K) :=
        CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm2 hcond
      obtain ⟨eModel⟩ := ggK1CBc_sl_model e hcomm
      have hq : CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eModel.symm hqSL
      have hflag : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl m)).qs = true := by
        rw [ggK1CBc_kindOrbit_sl_of_ne_one (nf := nf) hm1]
        have hne : ¬ (m - 1 = 1 ∧ nf = 1) := by
          rintro ⟨h1, h2⟩
          exact hcorner ⟨by omega, h2⟩
        exact decide_eq_true_eq.mpr hne
      refine ⟨Or.inl hq, ⟨fun _ => hflag, fun _ => hq⟩, ?_⟩
      · intro _
        simpa only [ggK1CBl_Model] using
          (⟨eModel⟩ : Nonempty (↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin m) K))

theorem ggK1CBl_classical_sp {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {s : ℕ}
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf) (hs : 1 ≤ s)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {B : LinearMap.BilinForm K W} (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hdim : Module.finrank K W = 2 * s)
    (e : ↥A ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ ↔
        (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp s)).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ → ggK1CBl_Model nf K (ggK1CCo_Kind.sp s) ↥⁅A, A⁆) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨s', hs', ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
      (K := K) (W := W) hB hn
  have hs'eq : s' = s := by omega
  subst s'
  let φ : ↥A ≃* StatedSp s K := e.trans e₀
  rcases eq_or_ne s 1 with hs1 | hs1
  · subst s
    rcases eq_or_ne nf 1 with hnf1 | hnf1
    ·
      subst nf
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hsolvSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
        haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
          CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
            (Or.inl hK2)
        exact Group.isSolvable_of_isSolvable_injective
          (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective
      haveI : Group.IsSolvable (StatedSp 1 K) := by
        haveI := hsolvSL
        exact Group.isSolvable_of_surjective
          (f := (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).toMonoidHom)
          (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).surjective
      haveI : Group.IsSolvable ↥A := ggK1CBc_isSolvable_of_mulEquiv φ inferInstance
      have hnotq : ¬ CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        ggK1CBc_not_quasisimple_of_isSolvable (A := A) inferInstance
      have hflag : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sp 1)).qs = false := by
        rw [ggK1CBc_kindOrbit_sp_one]
        rfl
      refine ⟨Or.inr inferInstance, ?_, ?_⟩
      · rw [hflag]
        exact ⟨fun h => absurd h hnotq, fun h => (Bool.false_eq_true.mp h).elim⟩
      · intro h
        exact absurd h hnotq
    ·
      have hnf2 : 2 ≤ nf := by omega
      have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) hnf2
      have hqSp : CFSG.IsQuasisimple (StatedSp 1 K) :=
        CFSG.LieType.Universal.Symplectic.isQuasisimple 1 K le_rfl (Or.inl (Or.inr h4))
      obtain ⟨eModel⟩ := ggK1CBc_sp_model_of_isQuasisimple φ hqSp
      have hq : CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eModel.symm hqSp
      have hflag : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp 1)).qs = true := by
        rw [ggK1CBc_kindOrbit_sp_one]
        simp [hnf1]
      refine ⟨Or.inl hq, ⟨fun _ => hflag, fun _ => hq⟩, ?_⟩
      · intro _
        simpa [ggK1CBl_Model] using
          (⟨eModel⟩ : Nonempty (↥⁅A, A⁆ ≃* StatedSp 1 K))
  · by_cases hcorner : s = 2 ∧ nf = 1
    ·
      obtain ⟨rfl, rfl⟩ := hcorner
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hqB : CFSG.IsQuasisimple ↥(commutator (StatedSp 2 K)) :=
        TwoThreeOrth.isQuasisimple_commutator_statedSp (k := 2) hK2 le_rfl
      obtain ⟨eModel⟩ := ggK1CBc_commutator_equiv φ
      have hq : CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eModel.symm hqB
      have hflag : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sp 2)).qs = true :=
        ggK1CBc_kindOrbit_sp_two_one
      refine ⟨Or.inl hq, ⟨fun _ => hflag, fun _ => hq⟩, ?_⟩
      · intro _
        simpa [ggK1CBl_Model] using
          (⟨eModel⟩ : Nonempty (↥⁅A, A⁆ ≃* ↥(commutator (StatedSp 2 K))))
    ·
      have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
          (Nat.card K = 2 ∧ 3 ≤ s) := by
        rcases eq_or_lt_of_le hnf with hnf1 | hnf2
        · right
          right
          have hK2 : Nat.card K = 2 := by rw [hK, ← hnf1]; norm_num
          refine ⟨hK2, ?_⟩
          rcases lt_or_ge s 3 with h3 | h3
          · have hs2 : s = 2 := by omega
            exact absurd ⟨hs2, hnf1.symm⟩ hcorner
          · exact h3
        · left
          right
          rw [hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hqSp : CFSG.IsQuasisimple (StatedSp s K) :=
        CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hcond
      obtain ⟨eModel⟩ := ggK1CBc_sp_model_of_isQuasisimple φ hqSp
      have hq : CFSG.IsQuasisimple ↥⁅A, A⁆ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eModel.symm hqSp
      have hflag : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp s)).qs = true :=
        ggK1CBc_kindOrbit_sp_of_ne hs1 hcorner
      refine ⟨Or.inl hq, ⟨fun _ => hflag, fun _ => hq⟩, ?_⟩
      · intro _
        simpa only [ggK1CBl_Model, if_neg hs1, if_neg hcorner] using
          (⟨eModel⟩ : Nonempty (↥⁅A, A⁆ ≃* StatedSp s K))

end CFSG.StandardType

end
