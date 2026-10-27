module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.Quasithin.Background.H158TrioFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Matrix

private instance s16c11_fr_finiteO (m : ℕ) : Finite ↥(S16C11FrO m) :=
  Finite.of_injective
    (fun g : ↥(S16C11FrO m) =>
      ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)))
    (fun _ _ h => Subtype.ext (Units.ext h))

private abbrev s16c11_fr_vecSmul {m : ℕ} (g : ↥(S16C11FrO m)) (v : S16C11FrVec m) :
    S16C11FrVec m :=
  ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
    Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v

private instance s16c11_fr_natMulAction (m : ℕ) :
    MulAction ↥(S16C11FrO m) (S16C11FrVec m) where
  smul := s16c11_fr_vecSmul
  one_smul v := by
    change s16c11_fr_vecSmul 1 v = v
    simp only [s16c11_fr_vecSmul, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  mul_smul a b v := by
    change s16c11_fr_vecSmul (a * b) v = s16c11_fr_vecSmul a (s16c11_fr_vecSmul b v)
    simp only [s16c11_fr_vecSmul, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

private lemma s16c11_fr_smul_apply {m : ℕ} (g : ↥(S16C11FrO m)) (v : S16C11FrVec m) :
    g • v = ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v :=
  rfl

private lemma s16c11_fr_line_card {m : ℕ} (hm : m = 3 ∨ m = 4) :
    (s16c11FrLine m).card = 3 := by
  rcases hm with rfl | rfl <;> decide +kernel

theorem s16c11_modelRF3_orthMinus_zmod_struct {m : ℕ} (hm : m = 3 ∨ m = 4) :
    S16C11ModelRF3 (FFModel.nat
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus m (ZMod 2) 1 1))) := by
  classical
  change ∃ T X : Subgroup ↥(S16C11FrO m), T ≤ X ∧ IsPGroup 2 ↥T ∧ ¬ 2 ∣ T.index ∧
    T.relIndex X = 3 ∧
    ∃ y ∈ (⊤ : Subgroup (Multiplicative (S16C11FrIdx m → ZMod 2))),
      (∀ t ∈ T, natAct (S16C11FrO m) t y * y⁻¹ ∈
        (⊥ : Subgroup (Multiplicative (S16C11FrIdx m → ZMod 2)))) ∧
      ∃ g ∈ X, natAct (S16C11FrO m) g y * y⁻¹ ∉
        (⊥ : Subgroup (Multiplicative (S16C11FrIdx m → ZMod 2)))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀ : Sylow 2 ↥(s16c11FrP m)⟩ :=
    Sylow.nonempty (p := 2) (G := ↥(s16c11FrP m))
  let T : Subgroup ↥(S16C11FrO m) := (T₀ : Subgroup ↥(s16c11FrP m)).map (s16c11FrP m).subtype
  have hTP : T ≤ s16c11FrP m := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hT2 : IsPGroup 2 ↥T := (Sylow.isPGroup' T₀).map (s16c11FrP m).subtype
  have hsub : T.subgroupOf (s16c11FrP m) = (T₀ : Subgroup ↥(s16c11FrP m)) := by
    change Subgroup.comap (s16c11FrP m).subtype
      (Subgroup.map (s16c11FrP m).subtype (T₀ : Subgroup ↥(s16c11FrP m))) = _
    exact Subgroup.comap_map_eq_self_of_injective (fun _ _ h => Subtype.ext h) _
  have hTodd : ¬ 2 ∣ (T.subgroupOf (s16c11FrP m)).index := by
    rw [hsub]
    exact Sylow.not_dvd_index T₀
  have hTi : ¬ 2 ∣ T.index := by
    intro h
    have h' : 2 ∣ T.relIndex (s16c11FrP m) * (s16c11FrP m).index := by
      rw [Subgroup.relIndex_mul_index hTP]
      exact h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h' with h1 | h2
    · exact hTodd h1
    · exact s16c11_fr_P_index_odd hm h2
  obtain ⟨π, hπsurj, hπker⟩ := s16c11_fr_levi hm
  have hm2 : m - 2 = 1 ∨ m - 2 = 2 := by
    rcases hm with rfl | rfl <;> norm_num
  obtain ⟨X, hXP, hTX, hTX3, hPXK⟩ :=
    s16c11_fr_exists_index_three_of_levi (s16c11FrP m) (s16c11FrK m) T
      (s16c11_fr_K_le_P m) (s16c11_fr_K_normal m) (s16c11_fr_K_index hm)
      hTP hT2 hTodd π hπsurj hπker (s16c11_fr_sylow_normalizer (m := m - 2) hm2)
  obtain ⟨y, hyline, hyfix⟩ :=
    CFSG.Quasithin.H.Trio.exists_common_fixed (G := ↥(S16C11FrO m)) (α := S16C11FrVec m)
      (P := T) hT2 (s16c11FrLine m) (s16c11_fr_line_card hm)
      (fun g hg x hx => (hTP hg).1 x hx)
  obtain ⟨p, hpP, hpne⟩ := s16c11_fr_P_moves hm y hyline
  obtain ⟨x, hxX, k, hkK, hpk⟩ := hPXK p hpP
  have hkfix : ((k : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y = y := hkK y hyline
  have hxne : ((x : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y ≠ y := by
    intro hx
    apply hpne
    have hp_eq : ((p : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y =
        ((x : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
          Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y := by
      rw [hpk, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hkfix]
    rw [hp_eq, hx]
  refine ⟨T, X, hTX, hT2, hTi, hTX3, Multiplicative.ofAdd y, Subgroup.mem_top _,
    ?_, ?_⟩
  · rintro t ht
    refine Subgroup.mem_bot.2 (mul_inv_eq_one.2 ?_)
    have htfix : ((t : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y = y := by
      have h := hyfix t ht
      rwa [s16c11_fr_smul_apply] at h
    exact congrArg Multiplicative.ofAdd htfix
  · refine ⟨x, hxX, ?_⟩
    intro hcon
    exact hxne (congrArg Multiplicative.toAdd (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hcon)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
