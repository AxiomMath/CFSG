module

import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3
import CFSG.Timmesfeld.ARS.BasicTwoGroup
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Timmesfeld.Transvection.OddSU3Chord

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LocalAnalysis.UniquenessCase
  CFSG.LieType.BorelTits
open Pres

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {H : Type*} [Group H]

private theorem mat_two_zero_of_mem_su3Top {σ : F ≃+* F} {z : SU σ 3}
    (hz : z ∈ su3Top σ) : mat σ 3 z 2 0 = 0 := by
  obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := σ)).1 hz
  rw [UC22.uc22pwsu3_mat_Y]
  simp

private theorem mat_conj_apply_two_zero {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
    {u : SU σ 3} (hu : u ∈ UC22.uc22pwsu3X hσ) (y : SU σ 3) :
    mat σ 3 (u * y * u⁻¹) 2 0 = mat σ 3 y 2 0 := by
  obtain ⟨a, b, -, hu_mat⟩ := (mem_rootGroup_three hσ).1 hu
  obtain ⟨a', b', -, hu'_mat⟩ := (mem_rootGroup_three hσ).1 (Subgroup.inv_mem _ hu)
  have h1 : mat σ 3 u 2 0 = 0 := by rw [hu_mat]; simp
  have h2 : mat σ 3 u 2 1 = 0 := by rw [hu_mat]; simp
  have h3 : mat σ 3 u 2 2 = 1 := by rw [hu_mat]; simp
  have h4 : mat σ 3 u⁻¹ 0 0 = 1 := by rw [hu'_mat]; simp
  have h5 : mat σ 3 u⁻¹ 1 0 = 0 := by rw [hu'_mat]; simp
  have h6 : mat σ 3 u⁻¹ 2 0 = 0 := by rw [hu'_mat]; simp
  calc mat σ 3 (u * y * u⁻¹) 2 0
      = mat σ 3 (y * u⁻¹) 2 0 := by
        rw [map_mul]
        simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3]
    _ = mat σ 3 y 2 0 := by
        rw [map_mul]
        simp [Matrix.mul_apply, Fin.sum_univ_three, h4, h5, h6]

private theorem conjSub_su3Bot_ne_su3Top {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
    {u : SU σ 3} (hu : u ∈ UC22.uc22pwsu3X hσ) : conjSub (su3Bot σ) u ≠ su3Top σ := by
  intro heq
  have hpos : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set y : SU σ 3 := suLong σ (Sum.inr (0 : Fin (3 / 2))) 1 with hy_def
  have hy : y ∈ su3Bot σ := (mem_su3Bot_iff (σ := σ)).2 ⟨1, map_one σ, rfl⟩
  have hmem : u * y * u⁻¹ ∈ conjSub (su3Bot σ) u := conj_mem_conjSub u hy
  rw [heq] at hmem
  have hzero : mat σ 3 (u * y * u⁻¹) 2 0 = 0 := mat_two_zero_of_mem_su3Top hmem
  have hone : mat σ 3 (u * y * u⁻¹) 2 0 = 1 := by
    rw [mat_conj_apply_two_zero hσ hu]
    have hy20 : mat σ 3 y 2 0 = 1 := by
      rw [hy_def, mat_suLong (σ := σ) (Sum.inr (0 : Fin (3 / 2))) hpos,
        show crd (Sum.inr (0 : Fin (3 / 2))) = (2 : Fin 3) from rfl,
        show crd (Sum.swap (Sum.inr (0 : Fin (3 / 2)))) = (0 : Fin 3) from rfl]
      simp
    exact hy20
  rw [hone] at hzero
  exact one_ne_zero hzero

theorem exists_mem_torus_mem_heis_of_conjSub_su3Top_eq (hFn : Nat.card F = (2 ^ n) ^ 2)
    {x : SU (unitaryInvolution F 2 n) 3}
    (hx : conjSub (su3Top (unitaryInvolution F 2 n)) x = su3Top (unitaryInvolution F 2 n)) :
    ∃ h ∈ UC22.uc22pwsu3H (unitaryInvolution F 2 n),
      ∃ u ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn), x = h * u := by
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hFn
  rcases UC22.uc22pwsu3_bruhat hσ (UC22.uc22pwsu3_hnorm hFn) (rankOne_three_eq_top hFn) hζ
    x with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exact ⟨h, hh, u, hu, rfl⟩
  · exfalso
    have hconj : conjSub (su3Top (unitaryInvolution F 2 n))
        (u * UC22.uc22pwsu3W hσ ζ * h * v) =
        conjSub (su3Bot (unitaryInvolution F 2 n)) u := by
      rw [conjSub_mul, conjSub_su3Top_of_mem_X hσ hv, conjSub_mul,
        conjSub_su3Top_of_mem_H hσ hh, conjSub_mul, conjSub_su3Top_W hσ hζ]
    rw [hconj] at hx
    exact conjSub_su3Bot_ne_su3Top hσ hu hx

private theorem odd_card_levelTorus (hFn : Nat.card F = (2 ^ n) ^ 2) :
    Odd (Nat.card (UC22.uc22pwsu3H (unitaryInvolution F 2 n))) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have h1 : Nat.card Fˣ = 0 := by
        rw [CFSG.ClassicalGroups.Unitary.card_units_of_card hFn, h0]
        norm_num
      exact (Nat.card_pos (α := Fˣ)).ne' h1
    · exact hpos
  rw [show Nat.card (UC22.uc22pwsu3H (unitaryInvolution F 2 n)) = (2 ^ n) ^ 2 - 1 from
    card_levelTorus_three hFn, UC22.uc22pwsu3_sq_sub_one hn]
  exact (UC22.uc22pwsu3_odd_two_pow_sub_one hn).mul (UC22.uc22pwsu3_odd_two_pow_add_one hn)

private theorem inf_heis_levelTorus_eq_bot (hFn : Nat.card F = (2 ^ n) ^ 2) :
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn) ⊓
      UC22.uc22pwsu3H (unitaryInvolution F 2 n) = ⊥ := by
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxH⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x ∣ Nat.card (UC22.uc22pwsu3X hσ) := Subgroup.orderOf_dvd_natCard _ hxX
  have h2 : orderOf x ∣ Nat.card (UC22.uc22pwsu3H (unitaryInvolution F 2 n)) :=
    Subgroup.orderOf_dvd_natCard _ hxH
  have hodd : Odd (orderOf x) := (odd_card_levelTorus hFn).of_dvd_nat h2
  have hpow : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm 3 n, pow_mul]
  have hcop : Nat.Coprime (orderOf x) (Nat.card (UC22.uc22pwsu3X hσ)) := by
    rw [show Nat.card (UC22.uc22pwsu3X hσ) = (2 ^ n) ^ 3 from card_rootGroup_three hFn, ← hpow]
    exact (hodd.coprime_two_right).pow_right (3 * n)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h1)

theorem mem_heis_of_conjSub_su3Top_eq (hFn : Nat.card F = (2 ^ n) ^ 2)
    {x : SU (unitaryInvolution F 2 n) 3}
    (hx : conjSub (su3Top (unitaryInvolution F 2 n)) x = su3Top (unitaryInvolution F 2 n))
    {e : ℕ} (hxe : x ^ 2 ^ e = 1) : x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn) := by
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_mem_torus_mem_heis_of_conjSub_su3Top_eq hFn hx
  have hN : h ∈ Subgroup.normalizer (UC22.uc22pwsu3X hσ : Set (SU (unitaryInvolution F 2 n) 3)) :=
    UC22.uc22pwsu3_levelTorus_le_normalizer hσ hh
  obtain ⟨k', hk', hpow⟩ := CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow
    ((Subgroup.mem_normalizer_iff.mp hN u).mp hu) hN (2 ^ e)
  have hk : h ^ 2 ^ e = k'⁻¹ := by
    rw [show h * u * h⁻¹ * h = h * u by group, hxe] at hpow
    exact eq_inv_of_mul_eq_one_right hpow.symm
  have hX : h ^ 2 ^ e ∈ UC22.uc22pwsu3X hσ := by
    rw [hk]
    exact Subgroup.inv_mem _ hk'
  have hH : h ^ 2 ^ e ∈ UC22.uc22pwsu3H (unitaryInvolution F 2 n) := pow_mem hh _
  have hbot : h ^ 2 ^ e = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨hX, hH⟩
    rwa [inf_heis_levelTorus_eq_bot hFn, Subgroup.mem_bot] at hmem
  have hone : h = 1 := by
    have hdvd1 : orderOf h ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hbot
    have hdvd2 : orderOf h ∣ Nat.card (UC22.uc22pwsu3H (unitaryInvolution F 2 n)) :=
      Subgroup.orderOf_dvd_natCard _ hh
    have hcop : Nat.Coprime (2 ^ e) (Nat.card (UC22.uc22pwsu3H (unitaryInvolution F 2 n))) :=
      (odd_card_levelTorus hFn).coprime_two_left.pow_left e
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  rw [hone, one_mul]
  exact hu

private theorem card_su3Top (hFn : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (su3Top (unitaryInvolution F 2 n)) = 2 ^ n := by
  let σ := unitaryInvolution F 2 n
  let f : Multiplicative (traceZero σ) →* SU σ 3 :=
    longRootHom σ (i := (0 : Fin 3)) (by decide)
  have hmat : ∀ c : Multiplicative (traceZero σ), mat σ 3 (f c) 0 2 = (c.toAdd : F) := by
    intro c
    rw [show f c = longRootHom σ (i := (0 : Fin 3)) (by decide) c from rfl, mat_apply,
      coe_longRootHom]
    simp [longRootMatrix, Matrix.add_apply, Matrix.single_apply]
  have hf : Function.Injective f := by
    intro c d hcd
    have h := congrArg (fun z => mat σ 3 z 0 2) hcd
    rw [hmat c, hmat d] at h
    exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hbij : Function.Bijective (fun c : Multiplicative (traceZero σ) =>
      (⟨f c, MonoidHom.mem_range.2 ⟨c, rfl⟩⟩ : su3Top σ)) := by
    refine ⟨fun c d hcd => hf (Subtype.ext_iff.1 hcd), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hy
    exact ⟨c, Subtype.ext hc⟩
  calc Nat.card (su3Top σ) = Nat.card (Multiplicative (traceZero σ)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card (traceZero σ) := Nat.card_congr Multiplicative.toAdd
    _ = 2 ^ n := card_traceZero hFn

private theorem isPGroup_su3Top (hFn : Nat.card F = (2 ^ n) ^ 2) :
    IsPGroup 2 (su3Top (unitaryInvolution F 2 n)) :=
  IsPGroup.of_card (n := n) (card_su3Top hFn)

private theorem inf_su3Top_ker_eq_bot (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) :
    su3Top (unitaryInvolution F 2 n) ⊓ θ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxZ, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x ∣ Nat.card (su3Top (unitaryInvolution F 2 n)) :=
    Subgroup.orderOf_dvd_natCard _ hxZ
  have h2 : orderOf x ∣ Nat.card θ.ker := Subgroup.orderOf_dvd_natCard _ hxN
  have hodd : Odd (orderOf x) := hθk.of_dvd_nat h2
  have hcop : Nat.Coprime (orderOf x) (Nat.card (su3Top (unitaryInvolution F 2 n))) := by
    rw [card_su3Top hFn]
    exact (hodd.coprime_two_right).pow_right n
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h1)

private theorem exists_conjSub_eq_of_le_sup_ker (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker))
    {x : SU (unitaryInvolution F 2 n) 3}
    (hx : conjSub (su3Top (unitaryInvolution F 2 n)) x ≤
      su3Top (unitaryInvolution F 2 n) ⊔ θ.ker) :
    ∃ u ∈ su3Top (unitaryInvolution F 2 n) ⊔ θ.ker,
      conjSub (conjSub (su3Top (unitaryInvolution F 2 n)) x) u =
        su3Top (unitaryInvolution F 2 n) := by
  let Z : Subgroup (SU (unitaryInvolution F 2 n) 3) := su3Top (unitaryInvolution F 2 n)
  let K : Subgroup (SU (unitaryInvolution F 2 n) 3) := θ.ker
  let P : Subgroup (SU (unitaryInvolution F 2 n) 3) := Z ⊔ K
  let C : Subgroup (SU (unitaryInvolution F 2 n) 3) := conjSub Z x
  have hZle : Z ≤ P := le_sup_left
  have hCP : C ≤ P := hx
  have hZ2 : IsPGroup 2 Z := isPGroup_su3Top hFn
  have hC2 : IsPGroup 2 C := hZ2.map (MulAut.conj x).toMonoidHom
  have hCcard : Nat.card C = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hrelP : Z.relIndex P = Z.relIndex K := by
    have h := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal K Z
    rwa [sup_comm] at h
  have hrelK : Z.relIndex K = Nat.card K := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := K)
    rw [inf_su3Top_ker_eq_bot hFn hθk, Subgroup.card_bot, mul_one] at h
    exact h
  have hrelC : C.relIndex P = Z.relIndex P := by
    have h1 : C.relIndex P * Nat.card C = Nat.card P := by
      have h := Subgroup.relIndex_mul_card (H := C) (K := P)
      rwa [inf_eq_left.mpr hCP] at h
    have h2 : Z.relIndex P * Nat.card Z = Nat.card P := by
      have h := Subgroup.relIndex_mul_card (H := Z) (K := P)
      rwa [inf_eq_left.mpr hZle] at h
    have h3 : C.relIndex P * Nat.card C = Z.relIndex P * Nat.card C := by
      rw [h1, hCcard]
      exact h2.symm
    exact (Nat.mul_right_cancel_iff (Nat.card_pos (α := C))).1 h3
  have hoddrel : ¬ 2 ∣ Z.relIndex P := by
    rw [hrelP, hrelK]
    intro h
    exact (Nat.not_even_iff_odd.2 hθk) (even_iff_two_dvd.2 h)
  have hZP : CFSG.ABGLocalTools.IsSylowOf 2 Z P := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hZle, hZ2, hoddrel⟩
  have hCP' : CFSG.ABGLocalTools.IsSylowOf 2 C P := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hCP, hC2, by rwa [hrelC]⟩
  obtain ⟨u, huP, hu⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hCP' hZP
  refine ⟨u, huP, ?_⟩
  change conjSub C u = Z
  ext y
  rw [mem_conjSub]
  exact (hu y).symm

theorem mem_map_heis_of_conjSub_eq (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) {A : Subgroup H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = A) {g : H} (hg : g ∈ θ.range)
    (hgA : conjSub A g = A) {e : ℕ} (hge : g ^ 2 ^ e = 1) :
    g ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  rcases Nat.eq_zero_or_pos e with he | he
  · rw [he] at hge
    have hg1 : g = 1 := by simpa using hge
    rw [hg1]
    exact Subgroup.one_mem _
  obtain ⟨x, hx⟩ := hg
  have hCZ : conjSub (su3Top (unitaryInvolution F 2 n)) x ≤
      su3Top (unitaryInvolution F 2 n) ⊔ θ.ker := by
    rintro y ⟨z, hz, rfl⟩
    have hzconj : (MulAut.conj x).toMonoidHom z = x * z * x⁻¹ := rfl
    rw [hzconj]
    have hθy : θ (x * z * x⁻¹) = g * θ z * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hx]
    have hzA : θ z ∈ A := hθt ▸ Subgroup.mem_map_of_mem θ hz
    have hyA : θ (x * z * x⁻¹) ∈ A := by
      rw [hθy]
      exact hgA ▸ conj_mem_conjSub g hzA
    rw [← hθt] at hyA
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.1 hyA
    have hyN : x * z * x⁻¹ * z'⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz'eq, mul_inv_cancel]
    have hy : x * z * x⁻¹ = (x * z * x⁻¹ * z'⁻¹) * z' := by group
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyN) (Subgroup.mem_sup_left hz')
  obtain ⟨u, huP, hu⟩ := exists_conjSub_eq_of_le_sup_ker hFn hθk hCZ
  have hsupA : su3Top (unitaryInvolution F 2 n) ⊔ θ.ker ≤ A.comap θ := by
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_comap, ← hθt]
      exact Subgroup.mem_map_of_mem θ hz
    · intro n hn
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hn]
      exact A.one_mem
  have huA : θ u ∈ A := Subgroup.mem_comap.1 (hsupA huP)
  rw [← hθt] at huA
  obtain ⟨z, hzZ, hzθ⟩ := Subgroup.mem_map.1 huA
  have hx'θ : θ (z⁻¹ * u * x) = g := by
    rw [map_mul, map_mul, map_inv, hzθ, hx]
    group
  have hx'norm : conjSub (su3Top (unitaryInvolution F 2 n)) (z⁻¹ * u * x) =
      su3Top (unitaryInvolution F 2 n) := by
    rw [conjSub_mul, conjSub_mul, hu, conjSub_of_mem (Subgroup.inv_mem _ hzZ)]
  have hcop : Nat.Coprime (2 ^ e) (Nat.card θ.ker) :=
    hθk.coprime_two_left.pow_left e
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hgk : g ^ k = g := by
    have h := pow_eq_pow_of_modEq hk1 hge
    simpa using h
  have hx'e : (z⁻¹ * u * x) ^ 2 ^ e ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx'θ, hge]
  have hNpow : ((z⁻¹ * u * x) ^ 2 ^ e) ^ Nat.card θ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard θ.ker hx'e)
  obtain ⟨t, ht⟩ := Nat.modEq_zero_iff_dvd.1 hk0
  have hpow2 : ((z⁻¹ * u * x) ^ k) ^ 2 ^ e = 1 := by
    rw [← pow_mul, mul_comm k (2 ^ e), pow_mul, ht, pow_mul, hNpow]
    simp
  have hnorm : conjSub (su3Top (unitaryInvolution F 2 n)) ((z⁻¹ * u * x) ^ k) =
      su3Top (unitaryInvolution F 2 n) :=
    conjSub_eq_self_iff.mpr (pow_mem (conjSub_eq_self_iff.mp hx'norm) k)
  have hmem : (z⁻¹ * u * x) ^ k ∈ UC22.uc22pwsu3X hσ :=
    mem_heis_of_conjSub_su3Top_eq hFn hnorm hpow2
  have hfin : θ ((z⁻¹ * u * x) ^ k) = g := by
    rw [map_pow, hx'θ, hgk]
  rw [← hfin]
  exact Subgroup.mem_map_of_mem θ hmem

end CFSG.Timmesfeld.Transvection
