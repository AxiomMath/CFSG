module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.HSzNPrime
public import CFSG.Quasithin.Background.HMathieuFacts
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace HRows

open CFSG.Assembly.LowTwoRank (StatedSU)

variable {W : Type} [CommGroup W] [Finite W] {G₀ K S : Subgroup (MulAut W)} {a : MulAut W}
  {z : W}

theorem conj_mem (h : Ctx1 W G₀ K a S z) {y : MulAut W} (hy : y ∈ G₀) {l : MulAut W}
    (hl : l ∈ K) : y * l * y⁻¹ ∈ K := by
  rcases h.mem_K_or_mul hy with hk | ⟨k, hk, rfl⟩
  · exact K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)
  · have e : k * a * l * (k * a)⁻¹ = k * (a * l * a⁻¹) * k⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hk (h.aN l hl)) (K.inv_mem hk)

theorem G₀_le_normalizer (h : Ctx1 W G₀ K a S z) :
    G₀ ≤ Subgroup.normalizer (K : Set (MulAut W)) := fun y hy => by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => conj_mem h hy hl, fun hl => ?_⟩
  have h1 := conj_mem h (G₀.inv_mem hy) hl
  have e : y⁻¹ * (y * l * y⁻¹) * (y⁻¹)⁻¹ = l := by group
  rw [e] at h1
  exact h1

theorem mParam_G₀_le_two (h : Ctx1 W G₀ K a S z) : E3.mParam G₀ ≤ 2 :=
  mParam_le_two h.a_mem h.a1 h.a2 h.rk

theorem false_of_su3_one {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ x y : Y, x * y ≠ y * x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) (π : ↥(StatedSU 3 (2 ^ 1) F) →* Y)
    (hπ : Function.Surjective π) : False := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, hF.trans (by norm_num)⟩
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite ↥(StatedSU 3 (2 ^ 1) F)
  have hsolv : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) F) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  have hsolvY : Group.IsSolvable Y := Group.isSolvable_of_surjective (f := π) hπ
  obtain ⟨x, y, hxy⟩ := hnab
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 hsolvY x y)

theorem false_of_su3_lt_two (h : Ctx1 W G₀ K a S z) {m : ℕ} (hm : BinaryNaturalSU3 K ⊤ ⊥ m)
    (hm2 : m < 2) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hm
  have := h.simple
  have hm1 : 1 ≤ m := by
    by_contra hlt
    have h0 : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, h0] at h1
    norm_num at h1
  have hm1' : m = 1 := by omega
  subst hm1'
  obtain ⟨x, y, hxy⟩ := h.nab
  exact false_of_su3_one (Y := ↥K) ⟨x, y, hxy⟩ hF π hπ.1

theorem oneSU3_holds : OneSU3 := by
  intro W _ _ G₀ K S a z h hm
  obtain ⟨m, hm⟩ := hm
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exact false_of_su3_lt_two h hm hm2
  · have hM := (CFSG.Quasithin.H.H2_SU3 hm2 hm h.K_le (G₀_le_normalizer h)).1
    have hle := mParam_G₀_le_two h
    omega

theorem oneSz_holds : OneSz := by
  intro W _ _ G₀ K S a z h hf
  obtain ⟨f, hf⟩ := hf
  obtain ⟨h2f, h3f⟩ := CFSG.Quasithin.H.H3_Sz_mParam hf h.K_le (G₀_le_normalizer h)
  have hle := mParam_G₀_le_two h
  omega

theorem oneM22Code_holds :
    OneM22Code := by
  intro W _ _ G₀ K S a z h hK
  have h3 := CFSG.Quasithin.H.Mathieu.code22_mParam ⟨h.K_le, G₀_le_normalizer h⟩ hK
  have hle := mParam_G₀_le_two h
  omega

end HRows

end S153G93D

end CFSG.Quasithin
