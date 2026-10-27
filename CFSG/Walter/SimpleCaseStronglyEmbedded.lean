module

public import CFSG.Walter.Defs
public import CFSG.StronglyEmbedded
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Walter

open scoped MatrixGroups

theorem not_hasAbelianSylowTwo_of_fusionBenderBorel {G : Type*} [Group G] [Finite G]
    {q k : ℕ} (hB : CFSG.Open.fusionBenderBorel G q k) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    ¬ HasAbelianSylowTwo G := by
  intro hab
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨-, -, -, hZ, hQ⟩ := hB Q
  have hcomm := hab Q
  have hcenter : Subgroup.center (Q : Subgroup G) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hcomm.is_comm.comm y x
  rw [hcenter, Subgroup.card_top] at hZ
  have hlt : q < q ^ k :=
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem isTypeL2_of_stronglyEmbedded (L : Type) [Group L] [Finite L]
    [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hab : HasAbelianSylowTwo L) (M : Subgroup L)
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) : IsTypeL2 L := by
  have _ := hnonab
  rcases CFSG.BenderSuzuki.bender_suzuki M hM with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exfalso
    have hmodel : CFSG.Theory.Comparator.SzModel n = CFSG.Open.Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : L ≃* CFSG.Open.Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.Sz n) := Finite.of_surjective e' e'.surjective
    have hB := (CFSG.Open.bender_suzuki_borel_full n hn).map_mulEquiv e'.symm
    refine not_hasAbelianSylowTwo_of_fusionBenderBorel hB ?_ le_rfl hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : L ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_surjective e' e'.surjective
    have hB := (CFSG.Open.bender_psu3_borel_full n hn).map_mulEquiv e'.symm
    refine not_hasAbelianSylowTwo_of_fusionBenderBorel hB ?_ (by norm_num) hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Walter
