module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.Kit
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
open scoped Pointwise

private abbrev dA : Matrix (Fin 3) (Fin 3) (ZMod 7) := !![1, 0, 0; 0, 2, 0; 0, 0, 4]

private abbrev pM : Matrix (Fin 3) (Fin 3) (ZMod 7) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private abbrev uM : Matrix (Fin 3) (Fin 3) (ZMod 7) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private lemma det_dA : dA.det = 1 := by decide +kernel
private lemma det_pM : pM.det = 1 := by decide +kernel
private lemma det_uM : uM.det = 1 := by decide +kernel

private def sA : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨dA, det_dA⟩

private def sP : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨pM, det_pM⟩

private def sU : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨uM, det_uM⟩

private def zc : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7) :=
  ⟨Matrix.scalar (Fin 3) (4 : ZMod 7), by decide +kernel⟩

private lemma dA_pow_three : dA ^ 3 = 1 := by decide +kernel
private lemma pM_pow_three : pM ^ 3 = 1 := by decide +kernel

private lemma sA_pow_three : sA ^ 3 = 1 := by
  apply Subtype.ext
  exact dA_pow_three

private lemma sP_pow_three : sP ^ 3 = 1 := by
  apply Subtype.ext
  exact pM_pow_three

private lemma dA_pow_apply : ∀ n < 3, (dA ^ n) 1 0 = 0 := by decide +kernel

private lemma pM_mul_dA : pM * dA = dA * pM * Matrix.scalar (Fin 3) (4 : ZMod 7) := by
  decide +kernel

private lemma uM_mul_dA_ne : ∀ r : ZMod 7, uM * dA ≠ dA * uM * Matrix.scalar (Fin 3) r := by
  decide +kernel

private lemma scalar_ne_dA : ∀ r : ZMod 7, Matrix.scalar (Fin 3) r ≠ dA := by decide +kernel

private lemma mul_scalar_apply (M : Matrix (Fin 3) (Fin 3) (ZMod 7)) (r : ZMod 7) (i j : Fin 3) :
    (M * Matrix.scalar (Fin 3) r) i j = M i j * r := by
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]

private abbrev piPSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7) →*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7) :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)))

private lemma piPSL_eq_iff {c d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)} :
    piPSL c = piPSL d ↔
      c⁻¹ * d ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)) := by
  simp only [piPSL, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq

private lemma eq_mul_scalar_of_piPSL_eq {c d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)}
    (h : piPSL c = piPSL d) :
    ∃ r : ZMod 7, (d : Matrix (Fin 3) (Fin 3) (ZMod 7)) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 7)) * Matrix.scalar (Fin 3) r := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (piPSL_eq_iff.mp h)
  refine ⟨r, ?_⟩
  have hd : (d : Matrix (Fin 3) (Fin 3) (ZMod 7)) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 7)) *
        ((c⁻¹ * d : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)) :
          Matrix (Fin 3) (Fin 3) (ZMod 7)) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [hd, hr]

private lemma piPSL_sA_ne_one : piPSL sA ≠ 1 := by
  intro h
  simp only [piPSL, QuotientGroup.mk'_apply] at h
  obtain ⟨r, -, hr⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff sA).mp h)
  exact scalar_ne_dA r hr

private lemma piPSL_cube_sA : piPSL sA ^ 3 = 1 := by
  rw [← map_pow, sA_pow_three, map_one]

private lemma piPSL_cube_sP : piPSL sP ^ 3 = 1 := by
  rw [← map_pow, sP_pow_three, map_one]

private lemma piPSL_comm_sA_sP : piPSL sA * piPSL sP = piPSL sP * piPSL sA := by
  rw [← map_mul, ← map_mul, piPSL_eq_iff]
  have key : sP * sA = sA * sP * zc := Subtype.ext pM_mul_dA
  rw [inv_mul_eq_iff_eq_mul.mpr key]
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨4, by decide, rfl⟩

private lemma piPSL_not_comm : piPSL sA * piPSL sU ≠ piPSL sU * piPSL sA := by
  intro h
  rw [← map_mul, ← map_mul] at h
  obtain ⟨r, hr⟩ := eq_mul_scalar_of_piPSL_eq h
  exact uM_mul_dA_ne r hr

private lemma zpow_eq_zpow_mod3 {X : Type*} [Group X] (g : X) (hg : g ^ (3 : ℤ) = 1) (k : ℤ) :
    g ^ k = g ^ (k % 3) := by
  have hk : k = k % 3 + 3 * (k / 3) := by omega
  conv_lhs => rw [hk]
  rw [zpow_add, zpow_mul, hg, one_zpow, mul_one]

private lemma sA_zpow_apply (k : ℤ) :
    ((sA ^ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 7)) :
      Matrix (Fin 3) (Fin 3) (ZMod 7)) 1 0 = 0 := by
  have h3 : sA ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact sA_pow_three
  rw [zpow_eq_zpow_mod3 sA h3 k]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k % 3 = n := ⟨(k % 3).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [hn, zpow_natCast, Matrix.SpecialLinearGroup.coe_pow]
  exact dA_pow_apply n (by omega)

private lemma piPSL_sP_not_mem_zpowers : piPSL sP ∉ Subgroup.zpowers (piPSL sA) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow] at hk
  obtain ⟨r, hr⟩ := eq_mul_scalar_of_piPSL_eq hk
  have h10 := congrFun (congrFun hr 1) 0
  have h1 : (sP : Matrix (Fin 3) (Fin 3) (ZMod 7)) 1 0 = 1 := by decide +kernel
  rw [h1, mul_scalar_apply, sA_zpow_apply, zero_mul] at h10
  exact absurd h10 (by decide)

private lemma pow_three_zpow {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (k : ℤ) :
    (x ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private lemma exists_mul_of_mem_sup {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {s : X} (hs : s ∈ U ⊔ V) :
    ∃ u ∈ U, ∃ v ∈ V, u * v = s := by
  rw [Subgroup.sup_eq_closure] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, V.one_mem, mul_one x⟩
    · exact ⟨1, U.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, U.one_mem, 1, V.one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := hx
    obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := hy
    refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, v₁ * v₂, V.mul_mem hv₁ hv₂, ?_⟩
    have h := hUV u₂ hu₂ v₁ hv₁
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [h]
      _ = u₁ * v₁ * (u₂ * v₂) := by group
  | inv x _ ih =>
    obtain ⟨u, hu, v, hv, rfl⟩ := ih
    refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, ?_⟩
    rw [mul_inv_rev]
    exact (show Commute u v from hUV u hu v hv).inv_inv.eq

private lemma pow_three_of_mem_sup {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : ∀ u ∈ U, u ^ 3 = 1)
    (hV : ∀ v ∈ V, v ^ 3 = 1) {s : X} (hs : s ∈ U ⊔ V) : s ^ 3 = 1 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hUV hs
  rw [(show Commute u v from hUV u hu v hv).mul_pow, hU u hu, hV v hv, one_mul]

private lemma pow_three_of_pow_nine {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : Nat.card S = 9) (hind : ¬ 3 ∣ S.index) (hexp : ∀ s ∈ S, s ^ 3 = 1) {x : G}
    (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 S := IsPGroup.of_card (n := 2) (hS.trans (by norm_num))
  obtain ⟨Q0, hQ0⟩ : ∃ Q0 : Sylow 3 G, (Q0 : Subgroup G) = S := ⟨hP.toSylow hind, rfl⟩
  haveI : Finite (Sylow 3 G) := Sylow.finite_of_finiteIndex Q0
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 2)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨Q, hQ⟩ := hxP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q0 Q
  have hxQ : x ∈ g • Q0 := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers x)
  have hx' : x ∈ MulAut.conj g • (Q0 : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul]
    exact hxQ
  obtain ⟨y, hyQ0, hyx⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) (Q0 : Subgroup G)).mp hx'
  have hyS : y ∈ S := hQ0 ▸ hyQ0
  rw [← hyx]
  show (MulAut.conj g y) ^ 3 = 1
  rw [← map_pow, hexp y hyS, map_one]

private lemma pow_three_of_pow_nine_psl
    {S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7))}
    (hS : Nat.card S = 9) (hexp : ∀ s ∈ S, s ^ 3 = 1)
    {x : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)} (hx : x ^ 9 = 1) :
    x ^ 3 = 1 := by
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) :=
    Nat.finite_of_card_ne_zero (by rw [card_psl_three_seven]; norm_num)
  have hidx : S.index * Nat.card S =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) :=
    Subgroup.index_mul_card (H := S)
  rw [hS, card_psl_three_seven] at hidx
  have hind : ¬ 3 ∣ S.index := by
    have h : S.index = 208544 := by omega
    rw [h]
    norm_num
  exact pow_three_of_pow_nine hS hind hexp hx

private lemma sylow_S_card :
    Nat.card ↥(Subgroup.zpowers (piPSL sA) ⊔ Subgroup.zpowers (piPSL sP)) = 9 :=
  CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine piPSL_comm_sA_sP
    piPSL_cube_sA piPSL_sA_ne_one piPSL_cube_sP piPSL_sP_not_mem_zpowers

private lemma sylow_S_exp :
    ∀ s ∈ Subgroup.zpowers (piPSL sA) ⊔ Subgroup.zpowers (piPSL sP), s ^ 3 = 1 := by
  intro s hs
  refine pow_three_of_mem_sup ?_ ?_ ?_ hs
  · intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute (piPSL sA) (piPSL sP) from piPSL_comm_sA_sP).zpow_zpow k l).eq
  · intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact pow_three_zpow piPSL_cube_sA k
  · intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact pow_three_zpow piPSL_cube_sP k

theorem noNine_psl_three_seven :
    9 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) ∧
    ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7), x ^ 9 = 1 → x ^ 3 = 1 := by
  refine ⟨by rw [card_psl_three_seven]; norm_num, fun x hx => ?_⟩
  exact pow_three_of_pow_nine_psl sylow_S_card sylow_S_exp hx

theorem noNine_projSL_three_seven [Fact (Nat.Prime 7)] :
    9 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) ∧
    ∀ x : CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1), x ^ 9 = 1 → x ^ 3 = 1 := by
  obtain ⟨h9, hpow⟩ := noNine_psl_three_seven
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← Nat.card_congr pslEquivProjSL.toEquiv]
    exact h9
  · have hy : (pslEquivProjSL.symm x) ^ 9 = 1 := by
      rw [← map_pow, hx, map_one]
    have h3 := congrArg (⇑pslEquivProjSL) (hpow _ hy)
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h3

private lemma center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G] {a b : G}
    (hab : a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
  · exact hc
  · exfalso
    apply hab
    have hb : b ∈ Subgroup.center G := by
      rw [hc]
      exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

theorem center_projSL_three_seven_eq_bot [Fact (Nat.Prime 7)] :
    Subgroup.center (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = ⊥ := by
  have hs : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
    (MulEquiv.isSimpleGroup_congr pslEquivProjSL).mp isSimpleGroup_psl_three_seven
  refine center_eq_bot_of_simple (a := pslEquivProjSL (piPSL sA))
    (b := pslEquivProjSL (piPSL sU)) ?_
  intro h
  apply piPSL_not_comm
  apply pslEquivProjSL.injective
  rw [map_mul, map_mul]
  exact h

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
