module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U5Torus
public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Torus
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.EvenBN.U5.Setting
import CFSG.Adapters.LieModelUnitaryOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

@[expose] noncomputable def torusFixElemFive (h : UnitaryFieldData 2 2 K) (μ : Kˣ) :
    hypSU h 2 1 :=
  mkHypSU h (diagonal (torusEntries h ![μ, μ⁻¹] (1 : Fin 1 → Kˣ)))
    (diagonal_torusEntries_isometry h ![μ, μ⁻¹] (fun _ => by simp [UnitaryFieldData.norm]))
    (by
      rw [det_diagonal_torusEntries]
      simp [torusRatio, Fin.prod_univ_two, div_eq_mul_inv, mul_comm, mul_left_comm])

theorem coe_torusFixElemFive (h : UnitaryFieldData 2 2 K) (μ : Kˣ) :
    (((torusFixElemFive h μ : hypSU h 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      diagonal (torusEntries h ![μ, μ⁻¹] (1 : Fin 1 → Kˣ)) :=
  rfl

theorem orderOf_hypProj_torusFixElemFive (h : UnitaryFieldData 2 2 K) (μ : Kˣ) :
    orderOf (hypProj h 2 1 (torusFixElemFive h μ)) = orderOf μ := by
  have hmem : torusFixElemFive h μ ∈ Syl3.torusPow h 2 1 (orderOf μ) := by
    refine Syl3.mem_torusPow.mpr ⟨![μ, μ⁻¹], fun i => ?_, coe_torusFixElemFive h μ⟩
    fin_cases i <;> simp [pow_orderOf_eq_one]
  have hpow : (torusFixElemFive h μ) ^ orderOf μ = 1 :=
    Syl3.pow_eq_one_of_mem_torusPow hmem
  have hdvd : orderOf μ ∣ orderOf (torusFixElemFive h μ) := by
    apply orderOf_dvd_of_pow_eq_one
    have h := congrFun (congrFun (congrArg (fun g : hypSU h 2 1 =>
      (((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)))
      (pow_orderOf_eq_one (torusFixElemFive h μ))) (.inl 0)) (.inl 0)
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_torusFixElemFive,
      Matrix.diagonal_pow] at h
    refine Units.ext ?_
    simpa [torusEntries, Matrix.diagonal_apply_eq, Matrix.one_apply] using h
  have hxord : orderOf (torusFixElemFive h μ) = orderOf μ :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow) hdvd
  have hxpow : ∀ n : ℕ, (torusFixElemFive h μ) ^ n = 1 ↔ μ ^ n = 1 :=
    orderOf_eq_orderOf_iff.mp hxord
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro hπ
    have hker : (torusFixElemFive h μ) ^ n ∈ (hypProj h 2 1).ker := by
      rw [MonoidHom.mem_ker, map_pow, hπ]
    rw [ker_hypProj] at hker
    obtain ⟨c, -, -, hsc⟩ := mem_normOneScalars.mp hker
    have hmid : (c : K) = 1 := by
      have h := congrFun (congrFun (congrArg (fun g : GL (HypIndex 2 1) K =>
        ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K))) hsc) (.inr (.inl 0)))
        (.inr (.inl 0))
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_torusFixElemFive,
        Matrix.diagonal_pow] at h
      simpa [torusEntries, Matrix.diagonal_apply_eq, Matrix.one_apply] using h.symm
    have hc1 : c = 1 := Units.ext hmid
    have hxn : (torusFixElemFive h μ) ^ n = 1 :=
      Subtype.ext (hsc.trans (by rw [hc1]; simp))
    exact (hxpow n).mp hxn
  · intro hμ
    rw [← map_pow, (hxpow n).mpr hμ, map_one]

theorem hypProj_torusFixElemFive_mul_comm (h : UnitaryFieldData 2 2 K) (μ : Kˣ)
    {s : hypPSU h 2 1} (hs : s ∈ (Syl3.torusPow h 2 1 3).map (hypProj h 2 1)) :
    hypProj h 2 1 (torusFixElemFive h μ) * s = s * hypProj h 2 1 (torusFixElemFive h μ) := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  rw [← map_mul, ← map_mul]
  congr 1
  obtain ⟨a, -, htm⟩ := Syl3.mem_torusPow.mp ht
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, htm, coe_torusFixElemFive, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext y
  exact mul_comm _ _

theorem torusFixConcl_of_lieModel_PSU_five {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 5 2 2) : TorusFixConcl X 2 := by
  classical
  obtain ⟨K, _, h, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.U5.exists_hypPSU_equiv (X := X) (f := 2) (by norm_num) hX
  let S₀ : Subgroup X :=
    ((Syl3.torusPow h 2 1 3).map (hypProj h 2 1)).map e.symm.toMonoidHom
  have hS₀ : IsPGroup 3 S₀ := by
    dsimp only [S₀]
    exact IsPGroup.map (Syl3.sylow_three_hypPSU_two_one h).1 e.symm.toMonoidHom
  have hS₀i : ¬ 3 ∣ S₀.index := by
    dsimp only [S₀]
    rw [Subgroup.index_map_of_bijective e.symm.bijective]
    exact (Syl3.sylow_three_hypPSU_two_one h).2.1
  have hcard : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hfin : Finite Kˣ :=
    @Finite.of_injective (Kˣ) K h.finite (fun u => (u : K)) Units.val_injective
  obtain ⟨μ, hμ⟩ :=
    @exists_prime_orderOf_dvd_card' (Kˣ) _ hfin 5 ⟨by norm_num⟩ (by rw [hcard]; norm_num)
  let x₀ : X := e.symm.toMonoidHom (hypProj h 2 1 (torusFixElemFive h μ))
  have hx₀q : orderOf x₀ = 5 := by
    dsimp only [x₀]
    change orderOf (e.symm (hypProj h 2 1 (torusFixElemFive h μ))) = 5
    rw [MulEquiv.orderOf_eq, orderOf_hypProj_torusFixElemFive, hμ]
  have hx₀ : ∀ s ∈ S₀, x₀ * s = s * x₀ := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
    dsimp only [x₀]
    rw [← map_mul, ← map_mul, hypProj_torusFixElemFive_mul_comm h μ hs']
  have hφi : ¬ 3 ∣ ((MulAut.conj : X →* MulAut X).range ⊔
      Subgroup.zpowers (1 : MulAut X)).index := by
    rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq, Subgroup.index_eq_card]
    change ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)
    rw [CFSG.Blueprint.LieModel.card_outer_psu hX (by norm_num) (by norm_num)]
    norm_num
  exact torusFixConcl_of_torus hS₀ hS₀i ⟨0, by simp⟩ (by intro s hs; simpa using hs) hφi
    (by norm_num) (by norm_num) hx₀q hx₀ (by simp)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
