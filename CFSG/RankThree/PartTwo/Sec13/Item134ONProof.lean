module

public import CFSG.RankThree.PartTwo.Sec13.Item134
public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.Native.ONTripleUnique
public import CFSG.RankThree.Native.ONTripleAut
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec13.ON134

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.Native.ONTriple
open Subgroup
open scoped commutatorElement

section Model

theorem model_pow_three
    {y : GM} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hyP : y ∈ (P : Subgroup GM) := hP (mem_zpowers y)
  rw [hg] at hyP
  exact (relG_conj g).pow_three_of_mem hyP

theorem model_zpowers_normal :
    (zpowers zG).Normal := by
  rw [← center_GM]
  infer_instance

theorem model_exists_centralizer
    {y : GM} (hy3 : y ^ 3 = 1) (hyz : y ∉ zpowers zG) :
    ∃ x : GM, x ^ 3 = 1 ∧ x * y = y * x ∧ x ∉ zpowers y ⊔ zpowers zG := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := fun h => hyz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hy3 hy1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hyP : (MulAut.conj g).toMonoidHom y ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers y))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hyP (conj_not_mem_zpowers hyz g)
  set n := g⁻¹ * wordN w with hn
  have hyn : y = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← hyn] at h1 h2
  set K := K0G.map (MulAut.conj n).toMonoidHom with hK
  have hxK : n * xG 1 * n⁻¹ ∈ K := ⟨xG 1, by rw [← yG_zero]; exact yG_mem_K0 (by norm_num), rfl⟩
  have hzK : zG ∈ K := ⟨zG, zG_mem_K0', by rw [conj_zG]⟩
  refine ⟨n * xG 1 * n⁻¹, ?_, ?_, ?_⟩
  · rw [conj_pow, relG.vcube 1, mul_one, mul_inv_cancel]
  · have hxC : n * xG 1 * n⁻¹ ∈ centralizer {y} := h1 ▸ mem_sup_right hxK
    exact mem_centralizer_singleton_iff.mp hxC
  · intro hmem
    have : (zpowers zG).Normal := model_zpowers_normal
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hmem
    obtain ⟨u, hu, t, ht, hut⟩ := Set.mem_mul.mp hmem
    have huK : u ∈ K := by
      have e : u = n * xG 1 * n⁻¹ * t⁻¹ := by rw [← hut]; group
      rw [e]
      exact mul_mem hxK (inv_mem (zpowers_le.mpr hzK ht))
    have hu1 : u = 1 := by
      have : u ∈ zpowers y ⊓ K := mem_inf.mpr ⟨hu, huK⟩
      rw [h2, mem_bot] at this
      exact this
    rw [hu1, one_mul] at hut
    have hx1 : xG 1 ∈ zpowers zG := by
      have e : xG 1 = n⁻¹ * t * n := by rw [hut]; group
      rw [e]
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
      have hc : Commute (zG ^ k) n := Commute.zpow_left (zG_central n) k
      rw [mul_assoc, hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact zpow_mem_zpowers zG k
    have h0 := (relG.coord_eq_zero_iff ⟨xG 1, ThreeQRel.v_mem 1⟩).2 hx1
    rw [coord_xG] at h0
    exact absurd (congrFun h0 1) (by decide)

theorem P0_le_normalizer_AG
    (j : ℕ) : P0G ≤ normalizer (AG j : Set GM) := by
  intro p hp
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have hc : ⁅p, a⁆ ∈ zpowers zG := relG.comm_mem hp (AG_le_P0 j ha)
  have e : p * a * p⁻¹ = ⁅p, a⁆ * a := by rw [commutatorElement_def]; group
  rw [SetLike.mem_coe, e]
  exact mul_mem (zpowers_le.mpr (zG_mem_AG j) hc) ha

theorem inL_decomp : ∀ j < 2, ∀ v : Fin 4 → ZMod 3, inL j v →
    v = (v 0).val • (Pi.single 0 1 : Fin 4 → ZMod 3) + (v 1).val • yv j := by
  decide +kernel

theorem zpowers_pow_of_cube {X : Type*} [Group X] {y : X} (hy : y ^ 3 = 1) {s : ℕ}
    (hs : s % 3 ≠ 0) : zpowers (y ^ s) = zpowers y := by
  apply le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) s))
  rw [Subgroup.zpowers_le]
  have e : y = (y ^ s) ^ s := by
    rw [← pow_mul, ← pow_mod_three hy (s * s)]
    have : s * s % 3 = 1 := by
      have : s % 3 = 1 ∨ s % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [this, pow_one]
  have h := Subgroup.pow_mem _ (Subgroup.mem_zpowers (y ^ s)) s
  rwa [← e] at h

theorem conj_x3_x0
    (e : ℕ) :
    (xG 3)⁻¹ ^ e * xG 0 * ((xG 3)⁻¹ ^ e)⁻¹ = xG 0 * zG ^ e := by
  have h03 : ⁅xG 0, xG 3⁆ = zG := by
    have h1 : omegaN ((0 : Fin 4) : ℕ) ((3 : Fin 4) : ℕ) = 1 := rfl
    rw [relG.comm 0 3, omegaZ_val, h1, pow_one]
  have h1 : (xG 3)⁻¹ * xG 0 * ((xG 3)⁻¹)⁻¹ = xG 0 * zG := by
    have h2 : xG 0 * xG 3 = zG * (xG 3 * xG 0) := by
      rw [← h03, commutatorElement_def]
      group
    calc (xG 3)⁻¹ * xG 0 * ((xG 3)⁻¹)⁻¹ = (xG 3)⁻¹ * (xG 0 * xG 3) := by group
      _ = (xG 3)⁻¹ * (zG * (xG 3 * xG 0)) := by rw [h2]
      _ = (xG 3)⁻¹ * (xG 3 * xG 0 * zG) := by rw [zG_central (xG 3 * xG 0)]
      _ = xG 0 * zG := by group
  induction e with
  | zero => simp
  | succ e ih =>
    calc (xG 3)⁻¹ ^ (e + 1) * xG 0 * ((xG 3)⁻¹ ^ (e + 1))⁻¹
        = (xG 3)⁻¹ * ((xG 3)⁻¹ ^ e * xG 0 * ((xG 3)⁻¹ ^ e)⁻¹) * ((xG 3)⁻¹)⁻¹ := by group
      _ = (xG 3)⁻¹ * (xG 0 * zG ^ e) * ((xG 3)⁻¹)⁻¹ := by rw [ih]
      _ = ((xG 3)⁻¹ * xG 0 * ((xG 3)⁻¹)⁻¹) * zG ^ e := by
          have hc : Commute (zG ^ e) (xG 3) := Commute.pow_left (zG_central _) e
          rw [inv_inv, mul_assoc, mul_assoc, hc.eq]
          group
      _ = xG 0 * zG ^ (e + 1) := by rw [h1, pow_succ']; group

theorem model_line_transitive
    {j : ℕ} (hj : j < 2) {m : GM}
    (hm : m ∈ AG j) (hmz : m ∉ zpowers zG) :
    ∃ g ∈ normalizer (AG j : Set GM),
      (zpowers (xG 0)).map (MulAut.conj g).toMonoidHom = zpowers m := by
  obtain ⟨hmP, hmL⟩ := mem_AG.1 hm
  set v := relG.coord ⟨m, hmP⟩ with hv
  have hv0 : v ≠ 0 := fun h0 => hmz ((relG.coord_eq_zero_iff _).1 h0)
  have hdec := inL_decomp j hj v hmL
  obtain ⟨l, hl, s, hs, hs0, hvs⟩ := line_of_vec j hj (v 0) (v 1) (by
    intro h
    apply hv0
    rw [hdec, (Prod.mk.inj h).1, (Prod.mk.inj h).2]
    simp)
  have hcoord : relG.coord ⟨m, hmP⟩ =
      relG.coord ⟨mL j l ^ s, pow_mem (mL_mem_P0 hj hl) s⟩ := by
    rw [coord_pow' (mL_mem_P0 hj hl), coord_mL hj hl, ← hvs, ← hdec]
  obtain ⟨c, hc⟩ := eq_mul_zpow_of_coord hmP (pow_mem (mL_mem_P0 hj hl) s) hcoord
  set e := (c * s) % 3 with he
  have hs3 : s % 3 ≠ 0 := by omega
  have hzm : Commute (mL j l) (zG ^ e) := (Commute.pow_left (zG_central _) e).symm
  have hcube : (mL j l * zG ^ e) ^ 3 = 1 := cube_of_mem_P0
    (mul_mem (mL_mem_P0 hj hl) (pow_mem ThreeQRel.x_mem e))
  have hpow : (mL j l * zG ^ e) ^ s = m := by
    rw [hzm.mul_pow, ← pow_mul, hc, ← pow_mod_three relG.xcube (e * s),
      ← pow_mod_three relG.xcube c]
    congr 2
    have : s = 1 ∨ s = 2 := by omega
    rcases this with rfl | rfl
    · simp [he]
    · rw [he]
      omega
  refine ⟨(nL j l)⁻¹ * (xG 3)⁻¹ ^ e, ?_, ?_⟩
  · refine mul_mem ?_ (pow_mem (inv_mem (P0_le_normalizer_AG j (ThreeQRel.v_mem 3))) e)
    rw [mem_normalizer_iff_map_conj_eq]
    exact map_conj_AG hj hl
  · rw [MonoidHom.map_zpowers, ← hpow, zpowers_pow_of_cube hcube hs3]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    calc (nL j l)⁻¹ * (xG 3)⁻¹ ^ e * xG 0 * (((xG 3)⁻¹ ^ e)⁻¹ * nL j l)
        = (nL j l)⁻¹ * ((xG 3)⁻¹ ^ e * xG 0 * ((xG 3)⁻¹ ^ e)⁻¹) * nL j l := by group
      _ = (nL j l)⁻¹ * (xG 0 * zG ^ e) * nL j l := by rw [conj_x3_x0]
      _ = (nL j l)⁻¹ * xG 0 * (zG ^ e * nL j l) := by group
      _ = (nL j l)⁻¹ * xG 0 * (nL j l * zG ^ e) := by
          rw [(Commute.pow_left (zG_central (nL j l)) e).eq]
      _ = mL j l * zG ^ e := by rw [mL]; group

theorem map_conj_mul {Y : Type*} [Group Y] (H : Subgroup Y) (g k : Y) :
    H.map (MulAut.conj (g * k)).toMonoidHom =
      (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem model_transitive
    {A : Subgroup GM} (hA : Late.IsE27 A) {a a' : GM} (ha : a ∈ A) (ha' : a' ∈ A)
    (haz : a ∉ zpowers zG) (haz' : a' ∉ zpowers zG) :
    ∃ g ∈ normalizer (A : Set GM),
      (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers a' := by
  obtain ⟨h, j, hj, hAh⟩ := exists_conj_AG hA
  have hm : (MulAut.conj h).toMonoidHom a ∈ AG j := hAh ▸ mem_map_of_mem _ ha
  have hm' : (MulAut.conj h).toMonoidHom a' ∈ AG j := hAh ▸ mem_map_of_mem _ ha'
  obtain ⟨g₁, hg₁, e₁⟩ := model_line_transitive hj hm (conj_not_mem_zpowers haz h)
  obtain ⟨g₂, hg₂, e₂⟩ := model_line_transitive hj hm' (conj_not_mem_zpowers haz' h)
  have hback : ∀ F : Subgroup GM,
      (F.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = F := by
    intro F
    rw [← map_conj_mul, inv_mul_cancel, map_conj_one]
  have key : ∀ F : Subgroup GM, F.map (MulAut.conj (h⁻¹ * (g₂ * g₁⁻¹) * h)).toMonoidHom =
      (((F.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g₁⁻¹).toMonoidHom).map
        (MulAut.conj g₂).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom := by
    intro F
    rw [show h⁻¹ * (g₂ * g₁⁻¹) * h = h⁻¹ * (g₂ * (g₁⁻¹ * h)) by group, map_conj_mul,
      map_conj_mul, map_conj_mul]
  have s1 : ((zpowers a).map (MulAut.conj h).toMonoidHom).map (MulAut.conj g₁⁻¹).toMonoidHom =
      zpowers (xG 0) := by
    rw [MonoidHom.map_zpowers, ← e₁, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  refine ⟨h⁻¹ * (g₂ * g₁⁻¹) * h, ?_, ?_⟩
  · refine mem_normalizer_iff_map_conj_eq.mpr ?_
    show A.map (MulAut.conj _).toMonoidHom = A
    rw [key, hAh, Sec13.map_conj_eq_of_mem_normalizer (inv_mem hg₁),
      Sec13.map_conj_eq_of_mem_normalizer hg₂, ← hAh, hback]
  · rw [key, s1, e₂, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Model

section Abstract

variable {X : Type} [Group X]

theorem nonempty_equiv_model
    [Finite X]
    (hperf : Group.IsPerfect X) (hT : Sec4.IsTripleCover X Blueprint.NativeSporadic.ON) :
    Nonempty (X ≃* GM) := by
  obtain ⟨K₀, hK₀n, ⟨eK⟩, ⟨eQ⟩⟩ := hT.isExtOf
  have := hperf
  have := hK₀n
  obtain ⟨e⟩ := nonempty_equiv_FHat K₀ eK eQ
  exact ⟨e.trans modelEquiv⟩

theorem mem_center_iff_model
    (ψ : X ≃* GM) {x : X} :
    x ∈ center X ↔ ψ x ∈ zpowers zG := by
  rw [← center_GM, mem_center_iff, mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨y, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, hx y]
  · intro hx g
    apply ψ.injective
    rw [map_mul, map_mul, hx (ψ g)]

theorem symm_zG_mem_center
    (ψ : X ≃* GM) :
    ψ.symm zG ∈ center X := by
  rw [mem_center_iff_model ψ, MulEquiv.apply_symm_apply]
  exact mem_zpowers zG

theorem aut_inner
    (ψ : X ≃* GM) (β : MulAut X)
    (hβ : ∀ z ∈ center X, β z = z) : ∃ g : X, ∀ x, β x = g * x * g⁻¹ := by
  set β' : GM ≃* GM := (ψ.symm.trans β).trans ψ with hβ'
  have hz : β' zG = zG := by
    show ψ (β (ψ.symm zG)) = zG
    rw [hβ _ (symm_zG_mem_center ψ), MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := aut_fix_z_inner β' hz
  refine ⟨ψ.symm g, fun x => ?_⟩
  apply ψ.injective
  have h1 := hg (ψ x)
  have h2 : β' (ψ x) = ψ (β x) := by
    show ψ (β (ψ.symm (ψ x))) = ψ (β x)
    rw [MulEquiv.symm_apply_apply]
  rw [h2] at h1
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem pow_three_eq_one
    (ψ : X ≃* GM) {x : X} {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    x ^ 3 = 1 := by
  apply ψ.injective
  rw [map_pow, map_one]
  exact model_pow_three (k := k) (by rw [← map_pow, hx, map_one])

theorem exists_centralizer
    (ψ : X ≃* GM) {b : X} (hb3 : b ^ 3 = 1) (hbz : b ∉ center X) :
    ∃ x : X, x ^ 3 = 1 ∧ x * b = b * x ∧ x ∉ zpowers b ⊔ center X := by
  obtain ⟨y, hy3, hyb, hyn⟩ := model_exists_centralizer (y := ψ b)
    (by rw [← map_pow, hb3, map_one]) (fun h => hbz ((mem_center_iff_model ψ).2 h))
  refine ⟨ψ.symm y, ?_, ?_, ?_⟩
  · rw [← map_pow, hy3, map_one]
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hyb]
  · intro hmem
    apply hyn
    have h1 : ψ (ψ.symm y) ∈ (zpowers b ⊔ center X).map ψ.toMonoidHom :=
      mem_map_of_mem _ hmem
    rw [MulEquiv.apply_symm_apply, Subgroup.map_sup, MonoidHom.map_zpowers] at h1
    have hle : (center X).map ψ.toMonoidHom ≤ zpowers zG := by
      rintro _ ⟨z, hz, rfl⟩
      exact (mem_center_iff_model ψ).1 hz
    exact sup_le_sup_left hle _ h1

theorem map_map_conj {Y : Type*} [Group Y] (φ : X ≃* Y) (H : Subgroup X) (g : X) :
    (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
      (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem isE27_map {Y : Type*} [Group Y] {A : Subgroup X} (hA : Late.IsE27 A) (f : X →* Y)
    (hf : Function.Injective f) : Late.IsE27 (A.map f) := by
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩, by rw [Subgroup.card_map_of_injective hf, hA.2]⟩
  · obtain ⟨_, x, hx, rfl⟩ := u
    obtain ⟨_, y, hy, rfl⟩ := v
    apply Subtype.ext
    change f x * f y = f y * f x
    have hc : x * y = y * x := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hc]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.1.2 x hx, map_one]

theorem transitive
    (ψ : X ≃* GM) {A : Subgroup X} (hA : Late.IsE27 A) {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A)
    (haz : a ∉ center X) (haz' : a' ∉ center X) :
    ∃ g ∈ normalizer (A : Set X),
      (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers a' := by
  obtain ⟨g', hg', hgg⟩ := model_transitive (isE27_map hA ψ.toMonoidHom ψ.injective)
    (mem_map_of_mem _ ha) (mem_map_of_mem _ ha')
    (fun h => haz ((mem_center_iff_model ψ).2 h)) (fun h => haz' ((mem_center_iff_model ψ).2 h))
  have hinj := Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  refine ⟨ψ.symm g', ?_, hinj ?_⟩
  · refine mem_normalizer_iff_map_conj_eq.mpr ?_
    show A.map (MulAut.conj _).toMonoidHom = A
    apply hinj
    rw [map_map_conj, MulEquiv.apply_symm_apply]
    exact Sec13.map_conj_eq_of_mem_normalizer hg'
  · rw [map_map_conj, MulEquiv.apply_symm_apply]
    simpa only [MonoidHom.map_zpowers] using hgg

end Abstract

section Setup

variable {G : Type} [Group G] [Finite G]

theorem setup
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) :
    d ∈ L ∧ d ∈ K ∧ c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A ⊓ L ≤ K ∧
      A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∈ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hspor : SporadicModels131 := sporadicModels131
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  obtain ⟨hdL, hc⟩ := exists_sylow_of_center_eq hS
  obtain ⟨-, -, hdJ, -⟩ := residual_facts h415 hJ hdL hd1 hc
  replace hdJ : d ∈ J := hdJ
  have hdK : d ∈ K := hLK hdJ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hspor' := hspor
  obtain ⟨-, -, -, hJ2z⟩ := hspor'
  obtain ⟨φ⟩ := hJ
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ hJ2z
  have hcL : c ∉ L := not_mem_of_center_eq_bot h hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    obtain ⟨-, -, h9 | hPGL⟩ := facts_of_not_mem h131 hspor slTwoCenter h hcL
    · exact h9
    · exfalso
      obtain ⟨p, e, hp, -, hiso⟩ := (facts_of_isZ3PGLThreePi h hPGL).1
      apply KFacts.KS14.ks17J2NotList.1 p e
      rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
      · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
      · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  have hAL : A ⊓ L ≤ J := fun a ha =>
    mem_residual_of_pow_three h415 ⟨φ⟩ hdL hd1 hc ha.2
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.commute ha.1 hdA))
      (k := 1) (by rw [pow_one]; exact h.isElemAbelian.2 a ha.1)
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  have hcd : c ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute h.mem_A hdA)
  have hcJ : ∀ j ∈ J, c * j = j * c := fun j hj =>
    (hLc j ((Subgroup.map_subtype_le _ hj : j ∈ L ⊓ _).1)).symm
  have hJperf : Group.IsPerfect J := by
    have h := (perfect_residual_characterization
      (G := ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G))).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  have hJne : J ≠ ⊥ := fun hb => hd1 (by rw [hb] at hdJ; exact Subgroup.mem_bot.mp hdJ)
  have hJc : J.map (MulAut.conj c).toMonoidHom = J := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      change c * j * c⁻¹ ∈ J
      rw [hcJ j hj, mul_inv_cancel_right]
      exact hj
    · intro hx
      refine ⟨x, hx, ?_⟩
      change c * x * c⁻¹ = x
      rw [hcJ x hx, mul_inv_cancel_right]
  have hKc : K.map (MulAut.conj c).toMonoidHom = K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt
      Nat.prime_three
      (conj_mem_thetaComponentsAt_of_mem_centralizer hcd hK) hK hJne hJperf
      (hJc ▸ Subgroup.map_mono hLK) hLK
  exact ⟨hdL, hdK, hcL, h9, hAL.trans hLK, hAB, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKc⟩

end Setup

section Action

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_of_mem {K : Subgroup G} (k : K) :
    Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer k.2⟩) =
      MulAut.conj (k : K ⧸ aschbacherSolvableCore 3 K) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem center_eq_zpowers {K : Subgroup G} {d : G} (hdK : d ∈ K) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hON : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K)
      CFSG.Blueprint.NativeSporadic.ON) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) =
        Subgroup.zpowers ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∧
      ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ^ 3 = 1 ∧
      ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ≠ 1 := by
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hdK3 : (⟨d, hdK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have h3 : ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hdK3, QuotientGroup.mk_one]
  have h1 : ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    have := eq_one_of_pow_three_pow_of_not_dvd hN3 h (k := 1) (by rw [pow_one, hdK3])
    exact hd1 (congrArg Subtype.val this)
  have hZ : ((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKd x.2))
  refine ⟨?_, h3, h1⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hZ)
  rw [hON.1, card_zpowers_of_pow_three h3 h1]

theorem pow_apply_of_conj {Y : Type*} [Group Y] {σ : MulAut Y} {k : Y}
    (hσ : ∀ x, σ x = k * x * k⁻¹) (i : ℕ) (x : Y) : (σ ^ i) x = k ^ i * x * (k ^ i)⁻¹ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hσ, pow_succ']
    group

theorem mem_of_maximal
    {A B K : Subgroup G} {c d : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → A ≤ E → E = A)
    (hcA : c ∈ A) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hBK : B ≤ K)
    (hAB : A = Subgroup.zpowers c ⊔ B) (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hdB : d ∈ B) (hd1 : d ≠ 1) (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hON : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K)
      CFSG.Blueprint.NativeSporadic.ON) :
    c ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcK
  set N := aschbacherSolvableCore 3 K with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨ψ⟩ := nonempty_equiv_model hq.1 hON
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [hAB]
    exact sup_le (Subgroup.zpowers_le.mpr hcN) (hBK.trans Subgroup.le_normalizer)
  have hAK : ∀ a ∈ A, a ∈ K → a ∈ B := by
    intro a ha haK
    obtain ⟨i, hi, b, hb, rfl⟩ := exists_pow_mul_of_mem hAe hcA hAB ha
    have hci : c ^ i ∈ K := by
      have := K.mul_mem haK (K.inv_mem (hBK hb))
      rwa [mul_inv_cancel_right] at this
    interval_cases i
    · rwa [pow_zero, one_mul]
    · exact absurd (by rwa [pow_one] at hci) hcK
    · exfalso
      apply hcK
      have h4 : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul]
      rw [h4]
      exact K.pow_mem hci 2
  set B' : Subgroup K := B.subgroupOf K with hB'
  have hB'3 : IsPGroup 3 B' := IsPGroup.of_card (n := 2) (by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hB9]
    norm_num)
  have hinj : Set.InjOn π (B' : Set K) := injOn_mk_of_isPGroup Nat.prime_three hB'3
  set dK : K := ⟨d, hBK hdB⟩ with hdK
  have hd3 : d ^ 3 = 1 := hAe.2 d (hBA hdB)
  have hdB' : dK ∈ B' := Subgroup.mem_subgroupOf.mpr hdB
  obtain ⟨hZ, hπd3, -⟩ := center_eq_zpowers (hBK hdB) hd3 hd1 hKd hON
  replace hZ : Subgroup.center (K ⧸ N) = Subgroup.zpowers (π dK) := hZ
  replace hπd3 : π dK ^ 3 = 1 := hπd3
  set τ : Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ N) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hτ
  have hτc : ∀ (x : K) (hx : c * x * c⁻¹ ∈ K), τ ⟨c, hcN⟩ (π x) = π ⟨c * x * c⁻¹, hx⟩ :=
    fun x hx => rfl
  have hτfix : ∀ b ∈ A, ∀ hb : b ∈ K, τ ⟨c, hcN⟩ (π ⟨b, hb⟩) = π ⟨b, hb⟩ := by
    intro b hb hbK
    rw [hτc ⟨b, hbK⟩ (by rw [hcomm c hcA b hb, mul_inv_cancel_right]; exact hbK)]
    congr 1
    apply Subtype.ext
    show c * b * c⁻¹ = b
    rw [hcomm c hcA b hb, mul_inv_cancel_right]
  have hfix : ∀ z ∈ Subgroup.center (K ⧸ N), τ ⟨c, hcN⟩ z = z := by
    intro z hz
    rw [hZ] at hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hτfix d (hBA hdB) (hBK hdB)]
  obtain ⟨k, hk⟩ := aut_inner ψ (τ ⟨c, hcN⟩) hfix
  have hk3 : k ^ 3 = 1 := by
    have hτ3 : τ ⟨c, hcN⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hc3
      rw [this, map_one]
    have hkZ : k ^ 3 ∈ Subgroup.center (K ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h1 := pow_apply_of_conj hk 3 q
      rw [hτ3, MulAut.one_apply] at h1
      calc q * k ^ 3 = k ^ 3 * q * (k ^ 3)⁻¹ * k ^ 3 := by rw [← h1]
        _ = k ^ 3 * q := by group
    rw [hZ] at hkZ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkZ
    refine pow_three_eq_one ψ (k := 2) ?_
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ← hn, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hπd3, one_zpow]
  have hkB : ∀ b ∈ B', k * π b = π b * k := by
    intro b hb
    have h1 := hτfix b (hBA hb) b.2
    rw [hk] at h1
    calc k * π b = k * π b * k⁻¹ * k := by group
      _ = π b * k := by rw [h1]
  obtain ⟨x, hx3, hxB, hxBc, hxk⟩ : ∃ x : K ⧸ N, x ^ 3 = 1 ∧ x ∉ B'.map π ∧
      (∀ b ∈ B', x * π b = π b * x) ∧ x * k = k * x := by
    by_cases hkB' : k ∈ B'.map π
    · obtain ⟨b₁, hb₁B, hb₁d⟩ : ∃ b₁ ∈ B, b₁ ∉ Subgroup.zpowers d := by
        by_contra hne
        push Not at hne
        have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers d from hne)
        rw [hB9, card_zpowers_of_pow_three hd3 hd1] at this
        omega
      set b₁K : K := ⟨b₁, hBK hb₁B⟩ with hb₁K
      have hb₁3 : b₁ ^ 3 = 1 := hAe.2 b₁ (hBA hb₁B)
      have hb₁1 : b₁ ≠ 1 := fun h => hb₁d (h ▸ one_mem _)
      have hπb₁3 : π b₁K ^ 3 = 1 := by
        rw [← map_pow]
        have : b₁K ^ 3 = 1 := Subtype.ext (by simpa [hb₁K] using hb₁3)
        rw [this, map_one]
      have hb₁B' : b₁K ∈ B' := Subgroup.mem_subgroupOf.mpr hb₁B
      have hπb₁Z : π b₁K ∉ Subgroup.center (K ⧸ N) := by
        rw [hZ]
        intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        apply hb₁d
        have h1 : π (dK ^ n) = π b₁K := by rw [map_zpow, hn]
        have h2 := hinj (Subgroup.zpow_mem _ hdB' n) hb₁B' h1
        have h3 : ((dK ^ n : K) : G) = b₁ := congrArg Subtype.val h2
        rw [← h3, Subgroup.coe_zpow]
        exact Subgroup.zpow_mem_zpowers d n
      obtain ⟨x, hx3, hxb, hxn⟩ := exists_centralizer ψ hπb₁3 hπb₁Z
      have hBeq : B = Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d := by
        have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d ≤ B :=
          sup_le (Subgroup.zpowers_le.mpr hb₁B) (Subgroup.zpowers_le.mpr hdB)
        have hcomm' : ∀ u ∈ Subgroup.zpowers b₁, ∀ v ∈ Subgroup.zpowers d, u * v = v * u :=
          fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr (hBA hb₁B) hu) v
            (Subgroup.zpowers_le.mpr (hBA hdB) hv)
        obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm'
        rw [zpowers_inf_eq_bot hb₁3 hb₁d, Subgroup.card_bot, mul_one,
          card_zpowers_of_pow_three hb₁3 hb₁1, card_zpowers_of_pow_three hd3 hd1] at hcard
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hcard])).symm
      have hBle : B'.map π ≤ Subgroup.zpowers (π b₁K) ⊔ Subgroup.center (K ⧸ N) := by
        rintro _ ⟨b, hb, rfl⟩
        have hbB : (b : G) ∈ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d := by
          rw [← hBeq]
          exact Subgroup.mem_subgroupOf.mp hb
        obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup
          (hcomm b₁ (hBA hb₁B) d (hBA hdB)) hbB
        have hbe : b = b₁K ^ i * dK ^ j := Subtype.ext (by simpa [hb₁K, hdK] using hij)
        rw [hbe, map_mul, map_zpow, map_zpow]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ i))
          (Subgroup.mem_sup_right (hZ ▸ Subgroup.zpow_mem_zpowers _ j))
      have hcent : Subgroup.zpowers (π b₁K) ⊔ Subgroup.center (K ⧸ N) ≤
          Subgroup.centralizer ({x} : Set (K ⧸ N)) :=
        sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxb.symm))
          (Subgroup.center_le_centralizer _)
      refine ⟨x, hx3, fun h => hxn (hBle h), fun b hb => ?_, ?_⟩
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent (hBle ⟨b, hb, rfl⟩))).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent (hBle hkB'))).symm
    · exact ⟨k, hk3, hkB', hkB, rfl⟩
  have hτB : ∀ b (hb : b ∈ B), τ ⟨b, hAN (hBA hb)⟩ = MulAut.conj (π ⟨b, hBK hb⟩) :=
    fun b hb => thetaQuotMulAut_of_mem ⟨b, hBK hb⟩
  have hAfix : ∀ a (ha : a ∈ A), τ ⟨a, hAN ha⟩ x = x := by
    intro a ha
    obtain ⟨i, -, b, hb, rfl⟩ := exists_pow_mul_of_mem hAe hcA hAB ha
    have he : (⟨c ^ i * b, hAN ha⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨c, hcN⟩ ^ i * ⟨b, hAN (hBA hb)⟩ := Subtype.ext (by simp)
    rw [he, map_mul, map_pow, MulAut.mul_apply, hτB b hb, MulAut.conj_apply,
      ← hxBc ⟨b, hBK hb⟩ (Subgroup.mem_subgroupOf.mpr hb), mul_inv_cancel_right,
      pow_apply_of_conj hk i, ← ((Commute.pow_right hxk i).eq), mul_inv_cancel_right]
  let α : A →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hαN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    show (α a) n ∈ aschbacherSolvableCore 3 K
    rw [← Sec4.map_aschbacherSolvableCore (α a)]
    exact Subgroup.mem_map_of_mem _ hn
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hαN hN3
  have hxmem : x ∈ {q : K ⧸ N | ∀ a : A,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
    intro a
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact hAfix a a.2
  rw [hlift] at hxmem
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxmem
  obtain ⟨e, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₁).ne' 3 (by norm_num)
  set y : K := x₁ ^ m with hy
  have hx₁A : ∀ a ∈ A, a * (x₁ : G) = x₁ * a := by
    intro a ha
    have h1 : (a : G) * x₁ * a⁻¹ = x₁ := congrArg Subtype.val (hx₁ ⟨a, ha⟩)
    calc a * (x₁ : G) = a * x₁ * a⁻¹ * a := by group
      _ = x₁ * a := by rw [h1]
  have hyA : ∀ a ∈ A, a * (y : G) = (y : G) * a := by
    intro a ha
    rw [hy, Subgroup.coe_pow]
    exact ((Commute.pow_right (hx₁A a ha) m)).eq
  have hy3e : y ^ 3 ^ e = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hπy : π y = x ^ m := by
    rw [hy, map_pow]
    exact congrArg (· ^ m) hx₁x
  have hy3 : y ^ 3 = 1 := by
    have hmemN : y ^ 3 ∈ N := by
      have h1 : π (y ^ 3) = 1 := by
        rw [map_pow, hπy, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact eq_one_of_pow_three_pow_of_not_dvd hN3 hmemN (k := e)
      (by rw [← pow_mul, mul_comm, pow_mul, hy3e, one_pow])
  have hyA' : (y : G) ∉ A := by
    intro hyA'
    have hπyB : π y ∈ B'.map π := ⟨y, Subgroup.mem_subgroupOf.mpr (hAK _ hyA' y.2), rfl⟩
    apply hxB
    have e1 : x = (x ^ m) ^ m := by
      rw [← pow_mul, ← pow_mod_three hx3 (m * m)]
      have : m * m % 3 = 1 := by
        have : m % 3 = 1 ∨ m % 3 = 2 := by omega
        rcases this with h | h <;> simp [Nat.mul_mod, h]
      rw [this, pow_one]
    rw [e1, ← hπy]
    exact Subgroup.pow_mem _ hπyB m
  have hy3' : (y : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  have hE := Sec13.isElemAbelian_sup hAe (Sec13.isElemAbelian_zpowers hy3')
    (fun a ha z hz => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_right (hyA a ha) n).eq)
  apply hyA'
  rw [← hmax _ hE le_sup_left]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem zpowers_eq_of_mk {K : Subgroup G} {P : Subgroup K} (hP : IsPGroup 3 P) {u v : K}
    (hu : u ∈ P) (hv : v ∈ P)
    (h : Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) u) =
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) v)) :
    Subgroup.zpowers u = Subgroup.zpowers v := by
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hP
  have key : ∀ {u v : K}, u ∈ P → v ∈ P →
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) u ∈
        Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) v) →
      u ∈ Subgroup.zpowers v := by
    intro u v hu hv hm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
    have := hinj (Subgroup.zpow_mem _ hv n) hu (by rw [map_zpow, hn])
    rw [← this]
    exact Subgroup.zpow_mem_zpowers v n
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact key hu hv (h ▸ Subgroup.mem_zpowers _)
  · rw [Subgroup.zpowers_le]
    exact key hv hu (h.symm ▸ Subgroup.mem_zpowers _)

theorem exists_conj_of_le
    {A K : Subgroup G} {d : G}
    (hA : Late.IsE27 A) (hAK : A ≤ K) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K))
    (hON : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K)
      CFSG.Blueprint.NativeSporadic.ON)
    {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A) (had : a ∉ Subgroup.zpowers d)
    (had' : a' ∉ Subgroup.zpowers d) :
    ∃ g ∈ Subgroup.normalizer (A : Set G),
      (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 K with hNdef
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨ψ⟩ := nonempty_equiv_model hq.1 hON
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set A' : Subgroup K := A.subgroupOf K with hA'
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA.2]
  have hA'3 : IsPGroup 3 A' := IsPGroup.of_card (n := 3) (by rw [hA'27]; norm_num)
  have hinj : Set.InjOn π (A' : Set K) := injOn_mk_of_isPGroup Nat.prime_three hA'3
  have hAbar : Late.IsE27 (A'.map π) := by
    refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := u
      obtain ⟨_, y, hy, rfl⟩ := v
      apply Subtype.ext
      change π x * π y = π y * π x
      have hc : x * y = y * x := Subtype.ext (by
        simpa using congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      rw [← map_mul, ← map_mul, hc]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 x hx)
      rw [this, map_one]
    · rw [card_map_eq_of_injOn π hinj, hA'27]
  obtain ⟨hZ, -, -⟩ := center_eq_zpowers (hAK hdA) (hA.1.2 d hdA) hd1 hKd hON
  have hnz : ∀ b (hb : b ∈ A), b ∉ Subgroup.zpowers d →
      π ⟨b, hAK hb⟩ ∉ Subgroup.center (K ⧸ N) := by
    intro b hb hbd hmem
    rw [hZ] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hbd
    have h2 := hinj (Subgroup.zpow_mem _ (show (⟨d, hAK hdA⟩ : K) ∈ A' from hdA) n)
      (show (⟨b, hAK hb⟩ : K) ∈ A' from hb) ((map_zpow π _ n).trans hn)
    have h3 : (((⟨d, hAK hdA⟩ : K) ^ n : K) : G) = b := congrArg Subtype.val h2
    rw [← h3, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers d n
  obtain ⟨gb, hgb, hgbe⟩ := transitive ψ hAbar (⟨⟨a, hAK ha⟩, ha, rfl⟩ : π ⟨a, hAK ha⟩ ∈ A'.map π)
    (⟨⟨a', hAK ha'⟩, ha', rfl⟩ : π ⟨a', hAK ha'⟩ ∈ A'.map π) (hnz a ha had) (hnz a' ha' had')
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective N gb
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 A' (N ⊔ A') :=
    CFSG.ABGLocalTools.isSylowOf_sup_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3) hA'3
  have hcomap : (A'.map π).comap π = N ⊔ A' := by
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_comm]
  have hA''le : A'.map (MulAut.conj g₀).toMonoidHom ≤ N ⊔ A' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hcomap, Subgroup.mem_comap]
    have h1 : π ((MulAut.conj g₀).toMonoidHom x) = π g₀ * π x * (π g₀)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hgb (π x)).mp ⟨x, hx, rfl⟩
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf 3 (A'.map (MulAut.conj g₀).toMonoidHom) (N ⊔ A') :=
    CFSG.ABGLocalTools.isSylowOf_of_card hA''le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective, ← hSyl.card_eq])
  obtain ⟨t, ht, htA⟩ := hSyl.exists_mem_conj hSyl'
  set g : K := t⁻¹ * g₀ with hg
  have hgN : ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro x hx
    have h1 : g₀ * x * g₀⁻¹ ∈ A'.map (MulAut.conj g₀).toMonoidHom := ⟨x, hx, rfl⟩
    have h2 := (htA _).mp h1
    have e : g * x * g⁻¹ = t⁻¹ * (g₀ * x * g₀⁻¹) * t := by rw [hg]; group
    rw [e]
    exact h2
  have htb : π t ∈ A'.map π := by
    have : t ∈ (A'.map π).comap π := hcomap ▸ ht
    exact this
  have hga : g * ⟨a, hAK ha⟩ * g⁻¹ ∈ A' := hgN _ ha
  have hπga : π (g * ⟨a, hAK ha⟩ * g⁻¹) =
      π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ := by
    have hw : π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ ∈ A'.map π :=
      (Subgroup.mem_normalizer_iff.mp hgb _).mp ⟨_, ha, rfl⟩
    have hct : π t * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) =
        (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t :=
      congrArg Subtype.val (hAbar.1.1.is_comm.comm ⟨_, htb⟩ ⟨_, hw⟩)
    have e1 : π (g * ⟨a, hAK ha⟩ * g⁻¹) =
        (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t := by
      rw [hg]
      simp only [map_mul, map_inv]
      group
    rw [e1]
    calc (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹) * π t
        = (π t)⁻¹ * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ * π t) := by group
      _ = (π t)⁻¹ * (π t * (π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹)) := by rw [hct]
      _ = π g₀ * π ⟨a, hAK ha⟩ * (π g₀)⁻¹ := by group
  have hzk : Subgroup.zpowers (g * ⟨a, hAK ha⟩ * g⁻¹) = Subgroup.zpowers ⟨a', hAK ha'⟩ := by
    apply zpowers_eq_of_mk hA'3 hga ha'
    rw [show QuotientGroup.mk' (aschbacherSolvableCore 3 K) (g * ⟨a, hAK ha⟩ * g⁻¹) =
      π (g * ⟨a, hAK ha⟩ * g⁻¹) from rfl, hπga]
    rw [MonoidHom.map_zpowers] at hgbe
    exact hgbe
  refine ⟨(g : G), ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have := hgN ⟨x, hAK hx⟩ hx
    exact this
  · rw [MonoidHom.map_zpowers]
    have := congrArg (Subgroup.map K.subtype) hzk
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    simpa [MulAut.conj_apply] using this

end Action

section NotOmega

theorem not_isPerfect_of_isHeisCentral {X Y : Type} [Group X] [Group Y] [Finite X]
    (h : Sec4.IsHeisCentral X Y) : ¬ Group.IsPerfect X := by
  intro hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, V, hUV, hcomm, hU, -, hcard⟩ := h
  have hVn : V.Normal := by
    refine ⟨fun v hv g => ?_⟩
    have hg : g ∈ U ⊔ V := hUV ▸ Subgroup.mem_top g
    have hN : U ⊔ V ≤ Subgroup.normalizer (V : Set X) := sup_le
      (fun u hu => Subgroup.mem_normalizer_iff.mpr fun w => by
        constructor
        · intro hw
          rw [hcomm u hu w hw, mul_inv_cancel_right]
          exact hw
        · intro hw
          have e : w = u * w * u⁻¹ := by
            have h1 := hcomm u hu (u * w * u⁻¹) hw
            calc w = u⁻¹ * (u * w * u⁻¹) * u := by group
              _ = u⁻¹ * ((u * w * u⁻¹) * u) := by group
              _ = u⁻¹ * (u * (u * w * u⁻¹)) := by rw [h1]
              _ = u * w * u⁻¹ := by group
          rw [e]
          exact hw)
      Subgroup.le_normalizer
    exact (Subgroup.mem_normalizer_iff.mp (hN hg) v).mp hv
  have hU3 : IsPGroup 3 U := IsPGroup.of_card (n := 3) (by rw [hU.2.1]; norm_num)
  have hQ3 : IsPGroup 3 (X ⧸ V) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ U ⊔ V := hUV ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have huk : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc : Commute u v := hcomm u hu v hv
    rw [hc.mul_pow, huk, one_mul]
    exact pow_mem hv _
  have hsub : Subsingleton (X ⧸ V) := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ V) hQ3.isNilpotent
  have hUleV : U ≤ V := fun u _ => (QuotientGroup.eq_one_iff u).mp (Subsingleton.elim _ _)
  rw [inf_eq_left.mpr hUleV, hU.2.1] at hcard
  norm_num at hcard

theorem not_isPerfect_of_isSLThreePiTwo {X : Type} [Group X] (h : Sec4.IsSLThreePiTwo X) :
    ¬ Group.IsPerfect X := by
  intro hX
  obtain ⟨L₀, hL, u, a, -, -, huL, -, -, hgen, -, hua, -⟩ := h
  set φ := QuotientGroup.mk' L₀ with hφ
  have hcua : Commute (φ u) (φ a) := by
    have h1 : φ (u * a * u⁻¹ * a⁻¹) = 1 := by
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hua.1
    simp only [map_mul, map_inv] at h1
    calc φ u * φ a = φ u * φ a * (φ u)⁻¹ * (φ a)⁻¹ * (φ a * φ u) := by group
      _ = φ a * φ u := by rw [h1, one_mul]
  have htop : Subgroup.closure ({φ u, φ a} : Set (X ⧸ L₀)) = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) hgen
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective L₀),
      MonoidHom.map_closure, Set.image_pair] at h1
    rwa [(Subgroup.map_eq_bot_iff _).mpr (by rw [hφ, QuotientGroup.ker_mk']), bot_sup_eq] at h1
  have hpair : ({φ u, φ a} : Set (X ⧸ L₀)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcua
    · exact hcua.symm
    · exact Commute.refl _
  have hcl := Subgroup.isMulCommutative_closure hpair
  have hcomm : IsMulCommutative (X ⧸ L₀) := by
    refine ⟨⟨fun p q => ?_⟩⟩
    have hp : p ∈ Subgroup.closure ({φ u, φ a} : Set (X ⧸ L₀)) := htop ▸ Subgroup.mem_top p
    have hq : q ∈ Subgroup.closure ({φ u, φ a} : Set (X ⧸ L₀)) := htop ▸ Subgroup.mem_top q
    exact congrArg Subtype.val (hcl.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)
  have hsub := Group.IsPerfect.subsingleton_of_isMulCommutative (G := X ⧸ L₀)
  exact huL ((QuotientGroup.eq_one_iff u).mp (Subsingleton.elim _ _))

variable {G : Type} [Group G] [Finite G]

theorem not_mem_omegaA
    (h131 : Item131) (h45 : Sec4.Item4_5) (h422 : Sec4.Item4_22)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) (hdK : d ∈ K) (hAK : A ≤ K) :
    Subgroup.zpowers d ∉ omegaA A := by
  intro hdΩ
  have hd3 : d ^ 3 = 1 := h.isElemAbelian.2 d hdA
  obtain ⟨L', hL'⟩ := item13SetupAt_of h422 h45 G h.toPartTwoStanding h.partTwoS_eq A
    h.mem_partTwoF h.not_mem_partTwoT d hdΩ
  obtain ⟨hL'c, hAN', hsc', hα'⟩ := hL'
  have hL'K : L' = K := by
    by_contra hne
    have hA_le : A ≤ Subgroup.zpowers d := by
      intro a ha
      have hmem : a ∈ Late.sectionCentralizer A L'
          ((aschbacherSolvableCore 3 L').map L'.subtype) := by
        refine ⟨ha, fun x hx => ?_⟩
        have h1 := Sec10.commutator_mem_theta_of_ne hK hL'c (Ne.symm hne) (hAK ha) hx
        have h2 : a * x * a⁻¹ * x⁻¹ ∈ L' :=
          L'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN' ha) x).mp hx) (L'.inv_mem hx)
        have h3 : a * x * a⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L' := by
          rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL'c]
          exact ⟨h2, h1⟩
        exact h3
      rw [hsc'] at hmem
      exact hmem
    have := Subgroup.card_le_of_le hA_le
    rw [h.card_eq, card_zpowers_of_pow_three hd3 hd1] at this
    omega
  subst hL'K
  have hK13 : Sec13Data G A d L' :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := h.mem_partTwoF
      not_mem_partTwoT := h.not_mem_partTwoT
      zpowers_mem_omegaA := hdΩ
      mem_lA := ⟨hL'c, hAN', hsc', hα'⟩ }
  have hperf : Group.IsPerfect (lBarA d L' A) := by
    have hsup : L' ⊔ A = L' := sup_eq_left.mpr hAK
    have hLN : L' ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      intro x hx
      have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp
        (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'c hx)
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [SetLike.mem_coe, ← conj_zpow, show x * d * x⁻¹ = d by rw [hxd, mul_inv_cancel_right]]
      exact Subgroup.zpow_mem_zpowers d k
    have hKp : Group.IsPerfect L' := Sec6.isPerfect_of_mem_thetaComponentsAt hL'c
    have : Group.IsPerfect (L'.subgroupOf (Subgroup.normalizer (Subgroup.zpowers d : Set G))) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
        (MulEquiv.surjective _)
    unfold lBarA
    rw [hsup]
    exact Group.IsPerfect.map _
  rcases cases131 h131 sporadicModels131 slTwoCenter hK13 with ⟨hdK', -⟩ | ⟨hdK', -⟩ |
      ⟨hdK', -⟩ | ⟨-, h7⟩
  · exact hdK' hdK
  · exact hdK' hdK
  · exact hdK' hdK
  · rcases h7 with hSL | ⟨hHeis, -⟩
    · exact not_isPerfect_of_isSLThreePiTwo hSL hperf
    · exact not_isPerfect_of_isHeisCentral hHeis hperf

end NotOmega

section Count

variable {G : Type} [Group G] [Finite G]

theorem ncard_pointsOff_eq_card {A B : Subgroup G} {a : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) (hAa : A = Subgroup.zpowers a ⊔ B)
    (haB : a ∉ B) : (pointsOff A B).ncard = Nat.card B := by
  have heq : pointsOff A B = (fun b : B => Subgroup.zpowers (a * b)) '' Set.univ := by
    ext F
    rw [mem_pointsOff_iff hA haA hAa haB]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
  rw [heq, Set.ncard_image_of_injective _ (fun b b' h => Subtype.ext
    (zpowers_mul_injOn hA haA hAa haB b.2 b'.2 h)), Set.ncard_univ]

theorem ncard_lines_ne {A B : Subgroup G} {c d : G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hAB : A = Subgroup.zpowers c ⊔ B) (hcB : c ∉ B) (hB9 : Nat.card B = 9)
    (hdB : d ∈ B) (hd1 : d ≠ 1) :
    {F : Subgroup G | F ≤ A ∧ Nat.card F = 3 ∧ F ≠ Subgroup.zpowers d}.ncard = 12 := by
  have hBA : B ≤ A := hAB ▸ le_sup_right
  have hd3 : d ^ 3 = 1 := hA.2 d (hBA hdB)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
    have h1 := congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hBA x.2⟩ ⟨y, hBA y.2⟩)
    simpa using h1
  obtain ⟨b, hbB, hbd⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers d := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers d from hne)
    rw [hB9, card_zpowers_of_pow_three hd3 hd1] at this
    omega
  have hb3 : b ^ 3 = 1 := hA.2 b (hBA hbB)
  have hb1 : b ≠ 1 := fun h => hbd (h ▸ one_mem _)
  have hBbd : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers d ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr hbB) (Subgroup.zpowers_le.mpr hdB)
    have hcomm : ∀ u ∈ Subgroup.zpowers b, ∀ v ∈ Subgroup.zpowers d, u * v = v * u :=
      fun u hu v hv => congrArg Subtype.val (hBe.1.is_comm.comm
        ⟨u, Subgroup.zpowers_le.mpr hbB hu⟩ ⟨v, Subgroup.zpowers_le.mpr hdB hv⟩)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [zpowers_inf_eq_bot hb3 hbd, Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hb3 hb1, card_zpowers_of_pow_three hd3 hd1] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hcard])).symm
  have heq : {F : Subgroup G | F ≤ A ∧ Nat.card F = 3 ∧ F ≠ Subgroup.zpowers d} =
      pointsOff A B ∪ pointsOff B (Subgroup.zpowers d) := by
    ext F
    constructor
    · rintro ⟨hFA, hF3, hFd⟩
      by_cases hFB : F ≤ B
      · refine Or.inr ⟨hFB, hF3, fun hle => hFd ?_⟩
        exact Subgroup.eq_of_le_of_card_ge hle
          (by rw [hF3, card_zpowers_of_pow_three hd3 hd1])
      · exact Or.inl ⟨hFA, hF3, hFB⟩
    · rintro (⟨hFA, hF3, hFB⟩ | ⟨hFB, hF3, hFd⟩)
      · exact ⟨hFA, hF3, fun h => hFB (h ▸ Subgroup.zpowers_le.mpr hdB)⟩
      · exact ⟨hFB.trans hBA, hF3, fun h => hFd h.le⟩
  have hdisj : Disjoint (pointsOff A B) (pointsOff B (Subgroup.zpowers d)) :=
    Set.disjoint_left.mpr fun F hF hF' => hF.2.2 hF'.1
  rw [heq, Set.ncard_union_eq hdisj, ncard_pointsOff_eq_card hA hcA hAB hcB,
    ncard_pointsOff_eq_card hBe hbB hBbd (fun h => hbd h), hB9,
    card_zpowers_of_pow_three hd3 hd1]

end Count

end CFSG.RankThree.PartTwo.Sec13.ON134

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item134ON_of
    (h131 : Item131) (h45 : Sec4.Item4_5)
    (h422 : Sec4.Item4_22) : Item134ON := by
  intro G _ _ A c L h hJ d hdA hd1 hS K hK hLK hON
  obtain ⟨hdL, hdK, hcL, h9, hBK, hAB, hcN⟩ := ON134.setup h131 h hJ hdA hd1 hS hK hLK
  have hd3 : d ^ 3 = 1 := h.isElemAbelian.2 d hdA
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have hcK : c ∈ K := ON134.mem_of_maximal h.isElemAbelian (fun E hE hAE => h.eq_of_le hE hAE)
    h.mem_A inf_le_left h9 hBK hAB hcN ⟨hdA, hdL⟩ hd1 hKd hq hON
  have hAK : A ≤ K := by
    rw [hAB]
    exact sup_le (Subgroup.zpowers_le.mpr hcK) hBK
  have hnot : Subgroup.zpowers d ∉ omegaA A :=
    ON134.not_mem_omegaA h131 h45 h422 h hdA hd1 hK hdK hAK
  have hA27 : Late.IsE27 A := ⟨h.isElemAbelian, h.card_eq⟩
  have hcd : c ∉ Subgroup.zpowers d := fun hc => hcL (Subgroup.zpowers_le.mpr hdL hc)
  have htrans : ∀ F : Subgroup G, F ≤ A → Nat.card F = 3 → F ≠ Subgroup.zpowers d →
      ∃ g ∈ Subgroup.normalizer (A : Set G),
        F = (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom := by
    intro F hFA hF3 hFd
    obtain ⟨a, haF, ha1⟩ : ∃ a ∈ F, a ≠ 1 := by
      by_contra hne
      push Not at hne
      have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hne
      rw [hbot, Subgroup.card_bot] at hF3
      omega
    have ha3 : a ^ 3 = 1 := h.isElemAbelian.2 a (hFA haF)
    have hFa : F = Subgroup.zpowers a :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haF)
        (by rw [hF3, card_zpowers_of_pow_three ha3 ha1])).symm
    have had : a ∉ Subgroup.zpowers d := by
      intro had
      apply hFd
      rw [hFa]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr had)
        (by rw [card_zpowers_of_pow_three ha3 ha1, card_zpowers_of_pow_three hd3 hd1])
    obtain ⟨g, hg, hge⟩ := ON134.exists_conj_of_le hA27 hAK hdA hd1 hKd hq hON h.mem_A
      (hFA haF) hcd had
    exact ⟨g, hg, by rw [hFa, hge]⟩
  have hΩ : omegaA A = {F | F ≤ A ∧ Nat.card F = 3 ∧ F ≠ Subgroup.zpowers d} := by
    ext F
    constructor
    · intro hF
      exact ⟨hF.1, hF.2.1, fun hFd => hnot (hFd ▸ hF)⟩
    · rintro ⟨hFA, hF3, hFd⟩
      obtain ⟨g, hg, rfl⟩ := htrans F hFA hF3 hFd
      exact (map_conj_mem_omegaA_iff hg).mpr h.zpowers_mem_omegaA
  refine ⟨?_, ?_, ?_⟩
  ·
    intro g hg
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers d
    by_contra hne
    have hF : (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom ∈ omegaA A := by
      rw [hΩ]
      refine ⟨?_, ?_, hne⟩
      · rw [MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.mpr ((Subgroup.mem_normalizer_iff.mp hg d).mp hdA)
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          card_zpowers_of_pow_three hd3 hd1]
    exact hnot ((map_conj_mem_omegaA_iff hg).mp hF)
  ·
    ext F
    constructor
    · intro hF
      rw [hΩ] at hF
      exact htrans F hF.1 hF.2.1 hF.2.2
    · rintro ⟨g, hg, rfl⟩
      exact (map_conj_mem_omegaA_iff hg).mpr h.zpowers_mem_omegaA
  ·
    rw [hΩ]
    exact ON134.ncard_lines_ne h.isElemAbelian h.mem_A hAB
      (fun hc => hcL (Subgroup.mem_inf.mp hc).2) h9 ⟨hdA, hdL⟩ hd1

end CFSG.RankThree.PartTwo.Sec13
