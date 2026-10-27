module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_mk_mem {Y A : Subgroup G} (hAY : A ≤ Y) {w : G} (hw : w ∈ A)
    (hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨w, hAY hw⟩ ∈ pCoreOf 2 (modO2Image Y A)) :
    w ∈ pCoreOf 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  set N : Subgroup G := A ⊓ ((pCoreOf 2 (modO2Image Y A)).comap π).map Y.subtype with hN
  have hmemN : ∀ {v : G} (hv : v ∈ A), π ⟨v, hAY hv⟩ ∈ pCoreOf 2 (modO2Image Y A) → v ∈ N :=
    fun {v} hv h => ⟨hv, ⟨⟨v, hAY hv⟩, h, rfl⟩⟩
  have key : ∀ a ∈ A, ∀ b ∈ N, a * b * a⁻¹ ∈ N := by
    rintro a ha b ⟨hb, ⟨y, hy, hyb⟩⟩
    have hab : a * b * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)
    refine hmemN hab ?_
    have hA : π ⟨a, hAY ha⟩ ∈ modO2Image Y A := ⟨⟨a, hAY ha⟩, ha, rfl⟩
    have hO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (modO2Image Y A) hA
    have hyb' : y = ⟨b, hAY hb⟩ := Subtype.ext hyb
    subst hyb'
    have := (Subgroup.mem_normalizer_iff.mp hO _).mp hy
    convert this using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hNn : A ≤ Subgroup.normalizer (N : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨key a ha b, fun h => ?_⟩
    have := key a⁻¹ (A.inv_mem ha) _ h
    simpa [mul_assoc] using this
  have hNp : IsPGroup 2 ↥N := by
    rintro ⟨v, hvA, ⟨y, hy, rfl⟩⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (modO2Image Y A)) ⟨_, hy⟩
    have h1 : π (y ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa [map_pow] using this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, h1⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg (fun z => ((z : ↥(CFSG.pCore 2 ↥Y)) : ↥Y)) hj
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    have h3 : (y : G) ^ 2 ^ (k + j) = 1 := by
      rw [pow_add, pow_mul]
      exact congrArg Subtype.val this
    simpa using h3
  have hle : N ≤ pCoreOf 2 A :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNn hNp
  exact hle (hmemN hw hmk)

theorem mem_sectionCentralizer_of_mk {Y A : Subgroup G} {x : G} (hAY : A ≤ Y) (hx : x ∈ Y)
    (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hx⟩ ∈
      sectionCentralizer (modO2Image Y A) (pCoreOf 2 (modO2Image Y A))) :
    x ∈ sectionCentralizer A (pCoreOf 2 A) := by
  refine ⟨hxA, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A hxA,
    fun a ha => ?_⟩
  have hw : x * a * x⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxA a).mp ha) (A.inv_mem ha)
  refine mem_pCoreOf_of_mk_mem hAY hw ?_
  have h1 := h.2.2 _ ⟨⟨a, hAY ha⟩, ha, rfl⟩
  convert h1 using 1
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  rfl

end CFSG.Quasithin.Vol2.Ch11.SecS
