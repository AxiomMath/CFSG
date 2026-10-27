module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Core
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive

public section

namespace CFSG.Quasithin.Gap6R2.L3

open Subgroup

@[expose] def NormalizerTwoGroup (X : Type) [Group X] : Prop :=
  ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index →
    ∀ x ∈ normalizer (S : Set X), Odd (orderOf x) → x = 1

theorem normalizer_eq_of_conj {X : Type} [Group X] [Finite X] (P S : Sylow 2 X)
    (hP : normalizer ((P : Subgroup X) : Set X) = (P : Subgroup X)) :
    normalizer ((S : Subgroup X) : Set X) = (S : Subgroup X) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P S
  have hmem : ∀ y : X, y ∈ ((g • P : Sylow 2 X) : Subgroup X) ↔
      g⁻¹ * y * g ∈ (P : Subgroup X) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  ext x
  constructor
  · intro hx
    have h1 : g⁻¹ * x * g ∈ normalizer ((P : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have e1 := hmem (g * z * g⁻¹)
      have e2 := hmem (x * (g * z * g⁻¹) * x⁻¹)
      have h := (Subgroup.mem_normalizer_iff.mp hx) (g * z * g⁻¹)
      have c1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      have c2 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by
        group
      rw [c1] at e1
      rw [c2] at e2
      rw [← e2, ← h, e1]
    rw [hP] at h1
    exact (hmem x).mpr h1
  · exact fun hx => Subgroup.le_normalizer hx

theorem normalizerTwoGroup_of_exists {X : Type} [Group X] [Finite X]
    (h : ∃ P : Sylow 2 X, normalizer ((P : Subgroup X) : Set X) = (P : Subgroup X)) :
    NormalizerTwoGroup X := by
  obtain ⟨P, hP⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hidx x hx hodd
  set S' : Sylow 2 X := hS.toSylow hidx with hS'
  have hS'c : (S' : Subgroup X) = S := rfl
  have hn := normalizer_eq_of_conj P S' hP
  have hxS : x ∈ S := by
    rw [← hS'c, ← hn]
    simpa [hS'c] using hx
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact eq_one_of_odd_orderOf_of_pow hodd hk'

theorem NormalizerTwoGroup.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : NormalizerTwoGroup Y) : NormalizerTwoGroup X := by
  intro S hS hidx x hx hodd
  have hS' : IsPGroup 2 (S.map (e : X →* Y)) := hS.map _
  have hidx' : ¬ 2 ∣ (S.map (e : X →* Y)).index := by
    rwa [Subgroup.index_map_equiv]
  have hx' : e x ∈ normalizer ((S.map (e : X →* Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have hn := (Subgroup.mem_normalizer_iff.mp hx) y
    have h1 : ∀ z : X, e z ∈ S.map (e : X →* Y) ↔ z ∈ S := fun z => by
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z := e.injective hwz
        exact this ▸ hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [h1, ← map_mul, ← map_inv, ← map_mul, h1]
    exact hn
  have h1 := h _ hS' hidx' (e x) hx' (by rwa [MulEquiv.orderOf_eq])
  exact e.injective (by simpa using h1)

theorem normalizerTwoGroup_psl_three_two {X : Type} [Group X] [Finite X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1) : NormalizerTwoGroup X := by
  obtain ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.exists_projectiveSL_of_statedClassicalModel_PSL h
  have : Finite (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) :=
    Finite.of_equiv X e.toEquiv
  have hK2 : Nat.card K = 2 := by simpa using hK
  refine NormalizerTwoGroup.of_mulEquiv e (normalizerTwoGroup_of_exists ?_)
  exact (CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key (by norm_num) hK2).1

theorem normalizerTwoGroup_alt_six {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) : NormalizerTwoGroup X := by
  obtain ⟨e⟩ := h
  exact NormalizerTwoGroup.of_mulEquiv e
    (normalizerTwoGroup_of_exists CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_six)

end CFSG.Quasithin.Gap6R2.L3
