module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs
import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

private theorem borel86_rootsmall_mk_comp_eq_one_iff {K N : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K N φ) (k : ↥K) :
    (QuotientGroup.mk' (Subgroup.center X)) (φ k) = 1 ↔ (k : G) ∈ centerPre K N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  change (∀ g : X, g * φ k = φ k * g) ↔
    (k : G) ∈ K ∧ ∀ x ∈ K, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ N
  constructor
  · intro hk
    refine ⟨k.2, fun x hx => ?_⟩
    have h1 : φ (k * (⟨x, hx⟩ : ↥K) * k⁻¹ * (⟨x, hx⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
      group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (hφ.ker_iff _).mp h1
  · rintro ⟨-, hx⟩ g
    obtain ⟨y, rfl⟩ := hφ.surjective g
    have h1 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
      refine (hφ.ker_iff _).mpr ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx (y : G) y.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

private theorem borel86_rootsmall_mk_ne_one_of_sq {A : Type} [Group A] {s : A}
    (hp : CFSG.pCore 2 A = ⊥) (hsq : s * s = 1) (hs1 : s ≠ 1) :
    (QuotientGroup.mk s : A ⧸ Subgroup.center A) ≠ 1 := by
  intro h
  have hcent : s ∈ Subgroup.center A :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center A) s).mp h
  have hP2 : IsPGroup 2 (Subgroup.zpowers s) := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  have hN : (Subgroup.zpowers s).Normal := by
    refine ⟨fun m hm g => ?_⟩
    have hm' := (Subgroup.zpowers_le.mpr hcent) hm
    rw [Subgroup.mem_center_iff] at hm'
    rw [show g * m * g⁻¹ = m by rw [hm' g, mul_inv_cancel_right]]
    exact hm
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hN hP2
  have hsbot : s ∈ CFSG.pCore 2 A := hle (Subgroup.mem_zpowers s)
  rw [hp, Subgroup.mem_bot] at hsbot
  exact hs1 hsbot

private theorem borel86_rootsmall_three_le_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ}
    (h : IsPSUGp Y m n) : 3 ≤ m ∧ 1 ≤ n := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  exact ⟨h1.2.2.1, h1.2.1⟩

private theorem borel86_rootsmall_sub_one_mul_self {F : Type} [Field F] [CharP F 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] {t : Matrix ι ι F} (ht : t * t = 1) :
    (t - 1) * (t - 1) = 0 := by
  have hadd : ∀ M : Matrix ι ι F, M + M = 0 := by
    intro M
    ext a b
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h : (t - 1) * (t - 1) = t * t + 1 - (t + t) := by
    rw [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [h, ht, hadd t, sub_zero, hadd 1]

private theorem borel86_rootsmall_rank_eq_zero_imp {F : Type} [Field F] {ι : Type}
    [Fintype ι] [DecidableEq ι] {N : Matrix ι ι F} (h : N.rank = 0) : N = 0 := by
  have h1 : LinearMap.range N.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
  ext i j
  have h2 : N.mulVec (Pi.single j 1) ∈ LinearMap.range N.mulVecLin := ⟨Pi.single j 1, rfl⟩
  rw [h1, Submodule.mem_bot] at h2
  have := congrFun h2 i
  simpa [Matrix.mulVec_single_one] using this

private theorem borel86_rootsmall_rank_sub_one_eq_one {F : Type} [Field F] [CharP F 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι ≤ 3)
    {t : Matrix ι ι F} (ht : t * t = 1) (ht1 : t ≠ 1) : (t - 1).rank = 1 := by
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero
    (A := t - 1) (B := t - 1) (borel86_rootsmall_sub_one_mul_self ht)
  have hpos : 0 < (t - 1).rank := by
    by_contra h0
    have h0' : (t - 1).rank = 0 := Nat.eq_zero_of_not_pos h0
    exact ht1 (sub_eq_zero.mp (borel86_rootsmall_rank_eq_zero_imp h0'))
  omega

theorem nonempty_mulEquiv_of_kBarCenterShape (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {P : ∀ (X : Type) [Group X], Prop} (hP : KBarCenterShape V H T P) {X : Type} [Group X]
    {φ : ↥(kGenIn V H) →* X} (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ (Y : Type) (_ : Group Y), P Y ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* Y) := by
  rw [Hyp83.kBarCenterShape_iff h hKT] at hP
  obtain ⟨Y, hYgrp, ψ, hψsurj, hψker, hPY⟩ := hP
  refine ⟨Y, hYgrp, hPY, ⟨?_⟩⟩
  let ψ₀ : ↥(kGenIn V H) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp φ
  have hψ₀surj : Function.Surjective ψ₀ :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).comp hφ.surjective
  have hker : ψ₀.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show ((QuotientGroup.mk' (Subgroup.center X)) (φ k) = 1) ↔ ψ k = 1
    rw [borel86_rootsmall_mk_comp_eq_one_iff hφ k, hψker k]
  exact ((QuotientGroup.quotientKerEquivOfSurjective (φ := ψ₀) hψ₀surj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψsurj)

theorem shape86DeltaT'_of_small (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {m n : ℕ}
    (hn : 1 < n) (hr : rankBarV V H T = 1) (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hsh : KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
      KBarCenterShape V H T (fun X _ => IsPSUGp X m n)) :
    Shape86DeltaT' V H T := by
  let X : Type := ↥(kGenIn V H) ⧸ CFSG.pCore 2 ↥(kGenIn V H)
  let φ : ↥(kGenIn V H) →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥(kGenIn V H))
  have hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ :=
    isBarMap_mk_pCore (kGenIn V H)
  have hpbot : CFSG.pCore 2 X = ⊥ := pCore_eq_bot_of_isBarMap hφ
  refine ⟨m, n, hn, hr, X, inferInstance, φ, hφ, ?_⟩
  rcases hsh with hSp | hPU
  · left
    refine ⟨hm2, fun s hs hs1 => ?_⟩
    obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp hs
    have hv2 : (v : G) * (v : G) = 1 := by
      simpa [pow_two] using h.elemAbelian.2 (v : G) hvV
    have hvprod : v * v = 1 := by
      apply Subtype.ext
      simpa using hv2
    have hs2 : s * s = 1 := by
      rw [← hvφ, ← map_mul, hvprod, map_one]
    have hnotmk : (QuotientGroup.mk s : X ⧸ Subgroup.center X) ≠ 1 :=
      borel86_rootsmall_mk_ne_one_of_sq hpbot hs2 hs1
    obtain ⟨Y, hYgrp, hPY, ⟨e₁⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape h hKT hSp hφ
    obtain ⟨k, hmk, F, hFld, hFin, hFcard, ⟨e₂⟩⟩ := hPY
    have hk : k = 1 := by omega
    subst k
    haveI := hFin
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    have hcharF : Fintype.card F = 2 ^ n := by
      rw [Fintype.card_eq_nat_card, hFcard]
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) hcharF
    refine ⟨1, hmk, F, inferInstance, inferInstance, hFcard, e₁.trans e₂, ?_⟩
    let g : ↥(StatedSp 1 F) := e₂ (e₁ (QuotientGroup.mk s))
    have hmk2 : (QuotientGroup.mk s : X ⧸ Subgroup.center X) *
        QuotientGroup.mk s = 1 := by
      rw [← QuotientGroup.mk_mul, hs2, QuotientGroup.mk_one]
    have hg2 : g * g = 1 := by
      simp only [g]
      rw [← map_mul, ← map_mul, hmk2, map_one, map_one]
    have hg1 : g ≠ 1 := by
      intro hg
      have h1 : e₁ (QuotientGroup.mk s) = 1 := by
        apply e₂.injective
        rw [map_one]
        simpa [g] using hg
      exact hnotmk (e₁.injective (by rw [h1, map_one]))
    have hGL2 : (g : GL (Fin 1 ⊕ Fin 1) F) * (g : GL (Fin 1 ⊕ Fin 1) F) = 1 := by
      have := congrArg (fun u : ↥(StatedSp 1 F) => (u : GL (Fin 1 ⊕ Fin 1) F)) hg2
      simpa using this
    have hmat2 : ((g : GL (Fin 1 ⊕ Fin 1) F) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) *
        ((g : GL (Fin 1 ⊕ Fin 1) F) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) = 1 := by
      have := congrArg (fun u : GL (Fin 1 ⊕ Fin 1) F =>
        (u : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)) hGL2
      simpa using this
    have hmat1 : ((g : GL (Fin 1 ⊕ Fin 1) F) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) ≠ 1 := by
      intro hgt
      exact hg1 (Subtype.ext (Units.ext hgt))
    exact borel86_rootsmall_rank_sub_one_eq_one (ι := Fin 1 ⊕ Fin 1) (by simp) hmat2 hmat1
  · obtain ⟨Y, hYgrp, hPY, ⟨e₁⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape h hKT hPU hφ
    have hm3' : m = 3 := le_antisymm hm3 (borel86_rootsmall_three_le_of_isPSUGp hPY).1
    refine Or.inr ⟨hm3'.ge, fun s hs hs1 => ?_⟩
    rw [hm3']
    obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp hs
    have hv2 : (v : G) * (v : G) = 1 := by
      simpa [pow_two] using h.elemAbelian.2 (v : G) hvV
    have hvprod : v * v = 1 := by
      apply Subtype.ext
      simpa using hv2
    have hs2 : s * s = 1 := by
      rw [← hvφ, ← map_mul, hvprod, map_one]
    have hnotmk : (QuotientGroup.mk s : X ⧸ Subgroup.center X) ≠ 1 :=
      borel86_rootsmall_mk_ne_one_of_sq hpbot hs2 hs1
    have hPY3 : IsPSUGp Y 3 n := hm3' ▸ hPY
    have hSCM : StatedClassicalModel Y .PSU 3 2 n :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hPY3
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨e₂⟩⟩ := hSCM
    haveI := hFin
    refine ⟨F, inferInstance, inferInstance, hFcard, e₁.trans e₂, ?_⟩
    let t : StatedProj (StatedSU 3 (2 ^ n) F) := e₂ (e₁ (QuotientGroup.mk s))
    change IsUnitaryTransvectionIn 3 n t
    have hmk2 : (QuotientGroup.mk s : X ⧸ Subgroup.center X) *
        QuotientGroup.mk s = 1 := by
      rw [← QuotientGroup.mk_mul, hs2, QuotientGroup.mk_one]
    have ht2 : t * t = 1 := by
      simp only [t]
      rw [← map_mul, ← map_mul, hmk2, map_one, map_one]
    have ht1 : t ≠ 1 := by
      intro ht
      have h1 : e₁ (QuotientGroup.mk s) = 1 := by
        apply e₂.injective
        rw [map_one]
        simpa [t] using ht
      exact hnotmk (e₁.injective (by rw [h1, map_one]))
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective t
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    have hcharF : Fintype.card F = 2 ^ (2 * n) := by
      rw [Fintype.card_eq_nat_card, hFcard, ← pow_mul, Nat.mul_comm n 2]
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n) hcharF
    have hmem : (g₀ * g₀ : ↥(StatedSU 3 (2 ^ n) F)) ∈
        (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) := by
      have hq : (QuotientGroup.mk (g₀ * g₀) :
          StatedProj (StatedSU 3 (2 ^ n) F)) = 1 := by
        rw [QuotientGroup.mk_mul, hg₀, ht2]
      exact (QuotientGroup.eq_one_iff (g₀ * g₀)).mp hq
    have hGLmem : (g₀ : GL (Fin 3) F) * (g₀ : GL (Fin 3) F) ∈
        StatedScalars (Fin 3) F := by
      simpa using Subgroup.mem_subgroupOf.mp hmem
    rw [StatedScalars] at hGLmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hGLmem
    have hdet : Matrix.GeneralLinearGroup.det (g₀ : GL (Fin 3) F) = 1 := by
      apply Units.ext
      simpa using CFSG.Open.StatedAPI.det_of_mem_statedSU (n := 3) (q := 2 ^ n) g₀.2
    have hlambda : c ^ 3 = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
        rw [hc, map_mul, hdet, mul_one]
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
      exact h1
    have hgsq : (g₀ : GL (Fin 3) F) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [pow_two, ← hc]
    have hg6 : (g₀ : GL (Fin 3) F) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hgsq, ← map_pow, hlambda, map_one]
    let g : ↥(StatedSU 3 (2 ^ n) F) := g₀ ^ 3
    have hmg : (QuotientGroup.mk g : StatedProj (StatedSU 3 (2 ^ n) F)) = t := by
      show (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf
        (StatedSU 3 (2 ^ n) F))) g = t
      rw [show g = g₀ ^ 3 from rfl, map_pow]
      change (QuotientGroup.mk g₀ : StatedProj (StatedSU 3 (2 ^ n) F)) ^ 3 = t
      rw [hg₀]
      show t ^ (2 + 1) = t
      rw [pow_succ, pow_two, ht2, one_mul]
    have hg2 : g * g = 1 := by
      apply Subtype.ext
      show ((g * g : ↥(StatedSU 3 (2 ^ n) F)) : GL (Fin 3) F) = 1
      rw [Subgroup.coe_mul]
      have hgcoe : (g : GL (Fin 3) F) = (g₀ : GL (Fin 3) F) ^ 3 := by
        rw [show g = g₀ ^ 3 from rfl, Subgroup.coe_pow]
      rw [hgcoe, ← pow_two, ← pow_mul, show 3 * 2 = 6 from rfl, hg6]
    have hg1 : (g : GL (Fin 3) F) ≠ 1 := by
      intro hgg
      have hgsub : g = 1 := Subtype.ext hgg
      apply ht1
      rw [← hmg, hgsub, QuotientGroup.mk_one]
    have hGL2 : (g : GL (Fin 3) F) * (g : GL (Fin 3) F) = 1 := by
      have := congrArg (fun u : ↥(StatedSU 3 (2 ^ n) F) => (u : GL (Fin 3) F)) hg2
      simpa using this
    have hmat2 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hGL2
      simpa using this
    have hmat1 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
      fun hgt => hg1 (Units.ext hgt)
    exact ⟨g, hmg, borel86_rootsmall_rank_sub_one_eq_one (ι := Fin 3) (by simp) hmat2 hmat1⟩

end CFSG.LocalAnalysis.WeakClosure81

end
