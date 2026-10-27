module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCommSound
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert

private theorem centralizer_smul_conj_eq {G : Type*} [Group G] (g : G) (s : Set G) :
    Subgroup.centralizer ((MulAut.conj g) • s) =
      (Subgroup.centralizer s).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨(MulAut.conj g).symm x, ?_,
      MulEquiv.apply_symm_apply (MulAut.conj g) x⟩
    intro y hy
    have h := hx ((MulAut.conj g) y) (Set.smul_mem_smul_set hy)
    apply (MulAut.conj g).injective
    change (MulAut.conj g) (y * (MulAut.conj g).symm x) =
      (MulAut.conj g) ((MulAut.conj g).symm x * y)
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ := (Set.mem_smul_set).1 hz
    change (MulAut.conj g) w * (MulAut.conj g) y =
      (MulAut.conj g) y * (MulAut.conj g) w
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) ((Subgroup.mem_centralizer_iff.mp hy) w hw)

private theorem card_centralizer_smul_conj {G : Type*} [Group G] (g : G) (s : Set G) :
    Nat.card ↥(Subgroup.centralizer ((MulAut.conj g) • s)) =
      Nat.card ↥(Subgroup.centralizer s) := by
  rw [centralizer_smul_conj_eq,
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

theorem gk7b_stdGroup_card_centralizer_eq :
    ∀ P : Subgroup Rgrp, Nat.card P = 49 →
      Nat.card ↥(Subgroup.centralizer (P : Set Rgrp)) = 49 := by
  intro P hP
  obtain ⟨z, hz, hScard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.exists_card_inf_centralizer_rep7B
  let S : Subgroup Rgrp := Subgroup.centralizer ({rep7B} : Set Rgrp) ⊓
    Subgroup.centralizer ({z} : Set Rgrp)
  have hScardS : Nat.card ↥S = 49 := hScard
  have hrep : rep7B ∈ S :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_singleton_iff.mpr (hz rep7B (by simp))⟩
  have hzS : z ∈ S :=
    Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hSsq : Nat.card ↥S = 7 ^ 2 := by rw [hScardS]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsMulCommutative ↥S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) hSsq
  have hle : S ≤ Subgroup.centralizer (S : Set Rgrp) := Subgroup.le_centralizer S
  have hge : Subgroup.centralizer (S : Set Rgrp) ≤ S := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) rep7B hrep).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) z hzS).symm
  have hcentS : Nat.card ↥(Subgroup.centralizer (S : Set Rgrp)) = 49 := by
    rw [le_antisymm hge hle, hScardS]
  haveI : Finite Rgrp := rgrp_finite
  have h343 : ¬ 343 ∣ Nat.card Rgrp := by
    rw [CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    norm_num
  have hS7 : IsPGroup 7 S := IsPGroup.of_card (n := 2) hSsq
  have hSnot : ¬ 7 ∣ S.index := by
    intro h7
    apply h343
    rw [← S.index_mul_card, hScardS]
    obtain ⟨k, hk⟩ := h7
    exact ⟨k, by rw [hk]; ring⟩
  have hP7 : IsPGroup 7 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hPnot : ¬ 7 ∣ P.index := by
    intro h7
    apply h343
    rw [← P.index_mul_card, hP]
    obtain ⟨k, hk⟩ := h7
    exact ⟨k, by rw [hk]; ring⟩
  haveI : Finite (Sylow 7 Rgrp) :=
    Finite.of_injective (fun T : Sylow 7 Rgrp => (T : Set Rgrp)) SetLike.coe_injective
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq Rgrp (hS7.toSylow hSnot) (hP7.toSylow hPnot)
  have hset : (P : Set Rgrp) = (MulAut.conj g) • (S : Set Rgrp) := by
    have h := congrArg (fun T : Sylow 7 Rgrp => (T : Subgroup Rgrp)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    have h' := congrArg (fun T : Subgroup Rgrp => (T : Set Rgrp)) h
    simp only [Subgroup.coe_pointwise_smul] at h'
    exact h'.symm
  rw [hset, card_centralizer_smul_conj]
  exact hcentS

end CFSG.StandardType.SporadicShape
