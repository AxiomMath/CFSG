module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagBase
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import CFSG.RankThree.PartOne.U5K.Hyp.Coord

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem finite_hypPSU_five : Finite (hypPSU hK 2 1) := by
  have := hK.finite
  have : Finite (hypSU hK 2 1) := inferInstance
  exact inferInstanceAs (Finite (↥(hypSU hK 2 1) ⧸ hypScalars hK 2 1))

theorem isSimpleGroup_hypPSU_five : IsSimpleGroup (hypPSU hK 2 1) := by
  have := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) hK
  have hKc : Nat.card K = (2 ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f hKc (2 * 2 + 1)
    (by norm_num) fun hq => absurd (Prod.mk.inj hq).1 (by norm_num)
  rw [(hypPSUEquivStatedProj hK hR (by norm_num)).isSimpleGroup_congr]
  exact hs

theorem u5_center_eq_bot : Subgroup.center (hypPSU hK 2 1) = ⊥ := by
  have hs := isSimpleGroup_hypPSU_five hK
  have := finite_hypPSU_five hK
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (hypPSU hK 2 1)) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ x y : hypPSU hK 2 1, x * y = y * x := fun x y =>
      (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top y) x)
    let _ : CommGroup (hypPSU hK 2 1) := { (inferInstance : Group (hypPSU hK 2 1)) with
      mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := hypPSU hK 2 1)
    obtain ⟨h1, -, -, ⟨e, -⟩, -⟩ := unitary_order_and_Sylow hK (r := 2) (ε := 1) (by norm_num)
      (by norm_num)
    have hdvd : Nat.card (hypProjUnitriangular hK 2 1) ∣ Nat.card (hypPSU hK 2 1) :=
      Subgroup.card_subgroup_dvd_card _
    have hcard : Nat.card (hypProjUnitriangular hK 2 1) = (2 ^ f) ^ 10 := by
      rw [← Nat.card_congr e.toEquiv, h1]
    rw [hcard] at hdvd
    have hf := hK.one_le
    have h2 : 2 ∣ Nat.card (hypPSU hK 2 1) := dvd_trans
      (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) hdvd
    have h3 : Nat.card (hypPSU hK 2 1) = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
    rw [h3] at hdvd
    have h4 : (2 ^ f) ^ 10 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h5 : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h6 : 2 ≤ (2 ^ f) ^ 10 := by
      calc 2 ≤ 2 ^ f := by simpa using h5
        _ ≤ (2 ^ f) ^ 10 := Nat.le_self_pow (by norm_num) _
    have h7 : (2 ^ f) ^ 10 = 2 := le_antisymm h4 h6
    have h8 : (2 ^ f) ^ 10 = 2 ^ (f * 10) := by rw [← pow_mul]
    rw [h8] at h7
    have := Nat.pow_right_injective (le_refl 2) (h7.trans (pow_one 2).symm)
    omega

theorem u5_sylow : IsSylowTwoOf (hypProjUnitriangular hK 2 1) ⊤ := by
  have := finite_hypPSU_five hK
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow hK (r := 2) (ε := 1) (by norm_num)
    (by norm_num)
  have h2 := isSylowTwoOf_top_of_sylow (show Sylow 2 (hypPSU hK 2 1) from P)
  rwa [show ((show Sylow 2 (hypPSU hK 2 1) from P) : Subgroup (hypPSU hK 2 1)) =
    hypProjUnitriangular hK 2 1 from hP] at h2

theorem proj_eq_one_of_eq {u t : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (ht : t ∈ hypTorus hK 2 1) (h : hypProj hK 2 1 u = hypProj hK 2 1 t) :
    hypProj hK 2 1 u = 1 := by
  have hz : u⁻¹ * t ∈ hypScalars hK 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := hz
  obtain ⟨a, d, -, -, hg⟩ := ht
  have hut := (mem_hypUnitriangular.1 hu)
  have hmat : ((t : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      (c : K) • ((u : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
    have h1 : (t : GL (HypIndex 2 1) K) = (u : GL (HypIndex 2 1) K) *
        GeneralLinearGroup.scalar (HypIndex 2 1) c := by
      have : (t : GL (HypIndex 2 1) K) = (u : GL (HypIndex 2 1) K) *
          ((u⁻¹ * t : hypSU hK 2 1) : GL (HypIndex 2 1) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this, hc]
    rw [h1, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hone : u = 1 := by
    apply hypSU_ext'
    ext i j
    change ((u : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j = (1 :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j
    by_cases hij : i = j
    · subst hij
      rw [hut.2 i, one_apply_eq]
    · have h1 := congrFun (congrFun hmat i) j
      rw [hg, diagonal_apply_ne _ hij, Matrix.smul_apply, smul_eq_mul] at h1
      rw [one_apply_ne hij]
      exact (mul_eq_zero.mp h1.symm).resolve_left hc0
  rw [hone, map_one]

theorem borelBase_u5 : BorelBase (hypProjUnitriangular hK 2 1)
    ((hypTorus hK 2 1).map (hypProj hK 2 1)) where
  center y hy := by
    have hc : y ∈ Subgroup.center (hypPSU hK 2 1) :=
      Subgroup.mem_center_iff.mpr fun g => (hy g).symm
    rw [u5_center_eq_bot hK, Subgroup.mem_bot] at hc
    exact hc
  sylow := u5_sylow hK
  H_comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hypTorus_comm hK ha hb]
  H_le := by
    rw [normalizer_hypProjUnitriangular hK (by norm_num) (by norm_num), hypProjBorel]
    exact Subgroup.map_mono (hypTorus_le_hypBorel hK)
  U_inf_H := by
    rintro _ ⟨u, hu, rfl⟩ ⟨t, ht, hut⟩
    exact proj_eq_one_of_eq hK hu ht hut.symm
  B_eq := by
    intro g hg
    rw [normalizer_hypProjUnitriangular hK (by norm_num) (by norm_num), hypProjBorel] at hg
    obtain ⟨b, hb, rfl⟩ := hg
    obtain ⟨u, hu, t, ht, rfl⟩ := normalizer_eq_mul hK (r := 2) (ε := 1) (by norm_num)
      (by norm_num) (g := b) (by
        rw [UnitaryHigher.normalizer_hypUnitriangular hK (by norm_num) (by norm_num)]
        exact hb)
    exact ⟨_, ⟨u, hu, rfl⟩, _, ⟨t, ht, rfl⟩, map_mul _ _ _⟩

end CFSG.Quasithin.H13.Sec53F.Unit
