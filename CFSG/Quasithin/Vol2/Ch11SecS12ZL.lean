module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZE
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open

section Cover

variable {A : Type*} [Group A] [Finite A] (hA : commutator A = ⊤)
  {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
  (π : A →* Matrix.SpecialLinearGroup (Fin 3) F) (hπ : Function.Surjective π)
  (hker : IsPGroup 2 π.ker)
include hA hF hπ hker

omit hF in
theorem map_le_center_of_ne_top (N : Subgroup A) [N.Normal] (hN : N ≠ ⊤) :
    N.map π ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquasi : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))
  have : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi
    (N.map π) with h | htop
  · exact h
  exfalso
  apply hN
  have h1 : QuotientGroup.mk' N = 1 := by
    refine eq_one_of_isPGroup_range hA (QuotientGroup.mk' N) (p := 2) ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨n, hn, hna⟩ : π a ∈ N.map π := htop ▸ Subgroup.mem_top _
    have hmem : n⁻¹ * a ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hna, inv_mul_cancel]
    obtain ⟨m, hm⟩ := hker ⟨_, hmem⟩
    have hm' : (n⁻¹ * a) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have he : QuotientGroup.mk' N a = QuotientGroup.mk' N (n⁻¹ * a) := by
      rw [map_mul, map_inv, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
        inv_one, one_mul]
    refine ⟨m, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [he, ← map_pow, hm', map_one]
  rw [eq_top_iff]
  intro a _
  have := DFunLike.congr_fun h1 a
  rwa [MonoidHom.one_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

end Cover

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
