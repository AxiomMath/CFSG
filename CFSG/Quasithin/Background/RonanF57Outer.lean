module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CentralizerScalars

public section

namespace CFSG.Quasithin.RonanF57

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {E : Type} [Group E] {Gp : Subgroup E} {K : Type} [Field K]

theorem mem_sylow_of_central {G : Type*} [Group G] {x : G} (hx : x * x = 1)
    (hc : ∀ g : G, g * x = x * g) (Q : Sylow 2 G) : x ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show (x ^ k) ^ 2 ^ 1 = 1
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    calc (x ^ k) ^ 2 ^ 1 = x ^ (k * 2) := by
          rw [pow_one, ← _root_.zpow_natCast, ← _root_.zpow_mul]; rfl
      _ = x ^ (2 * k) := by rw [mul_comm]
      _ = (x ^ (2 : ℤ)) ^ k := by rw [_root_.zpow_mul]
      _ = 1 := by rw [h2, _root_.one_zpow]
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
    intro h
    have : x * h * x⁻¹ = h := by
      rw [← hc h]
      group
    rw [this]
  have h1 := hP.inf_normalizer_sylow Q
  rw [inf_eq_left.mpr hle] at h1
  have h2 : Subgroup.zpowers x ≤ (Q : Subgroup G) := inf_eq_left.mp h1.symm
  exact h2 (Subgroup.mem_zpowers x)

theorem central_mem_sylowOf {E : Type} [Group E] {C S : Subgroup E} (hSC : S ≤ C)
    (hSp : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.relIndex C) {x : E} (hxC : x ∈ C) (hx : x * x = 1)
    (hcent : ∀ c ∈ C, c * x = x * c) : x ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf C) := hSp.comap_subtype
  let Q : Sylow 2 ↥C := hP.toSylow hidx
  have := mem_sylow_of_central (G := ↥C) (x := ⟨x, hxC⟩)
    (Subtype.ext hx) (fun g => Subtype.ext (hcent g g.2)) Q
  have h3 : (⟨x, hxC⟩ : ↥C) ∈ S.subgroupOf C := this
  exact h3

section Transport

variable {K₁ : Type} [Field K₁]

theorem bar_fun_eq (h : UnitaryFieldData 2 1 K) : (fun x : K => x ^ 2 ^ 1) = (h.bar : K → K) :=
  funext fun x => (h.bar_apply x).symm

end Transport

end CFSG.Quasithin.RonanF57
