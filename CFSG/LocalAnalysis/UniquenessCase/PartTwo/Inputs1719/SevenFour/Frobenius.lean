module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge

import CFSG.GroupTheory.BinaryFixedFreeRank
import CFSG.Quasithin.Background.SzG11NCSchur
import CFSG.RankThree.S4Free.Stellmacher25

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Quasithin.G11 CFSG.Quasithin.SzG11NC

variable {W : Type} [CommGroup W] [Finite W]


private theorem inv_mem_of_map_mem {G : Type*} [Group G] {M : Subgroup G} [Finite M]
    {y : MulAut G} (hy : ∀ m ∈ M, y m ∈ M) : ∀ m ∈ M, y⁻¹ m ∈ M := by
  classical
  have hinj : Function.Injective (fun m : M => (⟨y m, hy m m.2⟩ : M)) := by
    intro a b hab
    exact Subtype.ext (y.injective (congrArg Subtype.val hab))
  have hsurj : Function.Surjective (fun m : M => (⟨y m, hy m m.2⟩ : M)) :=
    Finite.injective_iff_surjective.1 hinj
  intro m hm
  obtain ⟨m', hm'⟩ := hsurj ⟨m, hm⟩
  have hm'' : y m' = m := congrArg Subtype.val hm'
  subst hm''
  simp

private noncomputable def mulAutToGL (G : Type*) [CommGroup G]
    [Module (ZMod 2) (Additive G)] : MulAut G →* (Additive G ≃ₗ[ZMod 2] Additive G) where
  toFun y := (MulEquiv.toAdditive y).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive y))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change Additive.ofMul ((1 : MulAut G) (Additive.toMul x)) = x
    rw [MulAut.one_apply]
    rfl
  map_mul' y z := by
    apply LinearEquiv.ext
    intro x
    change Additive.ofMul ((y * z) (Additive.toMul x)) =
      Additive.ofMul (y (Additive.toMul (Additive.ofMul (z (Additive.toMul x)))))
    rw [MulAut.mul_apply]
    rfl

@[simp] private theorem mulAutToGL_apply (G : Type*) [CommGroup G]
    [Module (ZMod 2) (Additive G)] (y : MulAut G) (m : G) :
    mulAutToGL G y (Additive.ofMul m) = Additive.ofMul (y m) := rfl

private theorem mulAutToGL_injective (G : Type*) [CommGroup G]
    [Module (ZMod 2) (Additive G)] : Function.Injective (mulAutToGL G) := by
  intro y z h
  ext m
  have := congrArg (fun f => (f (Additive.ofMul m)).toMul) h
  simpa using this

theorem dParam_dvd_rk (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    {x : MulAut W} (hx : orderOf x = p) {M : Subgroup W} (hMx : ∀ m ∈ M, x m ∈ M)
    (hfix : M ⊓ fixV (zpowers x) = ⊥) : dParam p ∣ rk ↥M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hxinv : ∀ m ∈ M, x⁻¹ m ∈ M := inv_mem_of_map_mem hMx
  have hx_stab : x ∈ stabSub M := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h := hxinv (x u) hu
      simpa using h, hMx u⟩
  have hY : ∀ y ∈ Subgroup.zpowers x, ∀ m ∈ M, y m ∈ M := by
    intro y hy m hm
    have hy_stab : y ∈ stabSub M := by
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, rfl⟩ := hy
      exact Subgroup.zpow_mem (K := stabSub M) hx_stab k
    exact (mem_stabSub.mp hy_stab m).2 hm
  have hYp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hdvd := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hW hYp hY hfix
  simpa [dParam] using hdvd

private theorem isIrr_zpowers_of_apply {E : Type} [CommGroup E] [Finite E] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {y : MulAut E} {U : Subgroup E}
    [Module (ZMod 2) (Additive U)] {yU : MulAut U}
    (hyU_apply : ∀ u : U, ((yU u : U) : E) = y u) (hyU_order : orderOf yU = p)
    (hfix : U ⊓ fixV (Subgroup.zpowers y) = ⊥) (hU : rk ↥U = dParam p)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    IsIrr (Subgroup.zpowers (mulAutToGL U yU)) ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hU2 : ∀ u : U, u ^ 2 = 1 := fun u => Subtype.ext (hE2 u.1)
  have : FiniteDimensional (ZMod 2) (Additive U) := Module.Finite.of_finite
  have hU_ne : U ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥U = 0 := by rw [hbot]; simp [rk]
    rw [hU] at h0
    exact (dParam_pos hp hp2).ne' h0
  have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU_ne
  have : Nontrivial (Additive U) := inferInstance
  let T := CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (W := U)
  have htopdim : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Additive U)) = dParam p := by
    have h := CFSG.LocalAnalysis.WeakClosure81.w16g_rk_eq_finrank hU2 (⊤ : Subgroup U)
    rw [CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_top] at h
    rw [← h, CFSG.Quasithin.rk_top, hU]
  refine ⟨fun _ _ _ hv => Submodule.mem_top, bot_lt_top, ?_⟩
  intro J hJ _ _
  by_cases hJbot : J = ⊥
  · exact Or.inl hJbot
  right
  by_contra hJtop
  let UJ : Subgroup U := T.symm J
  have hmem : ∀ v : Additive U, v ∈ J ↔ v.toMul ∈ UJ := by
    intro v
    have h := CFSG.LocalAnalysis.WeakClosure81.w16g_mem_toSub UJ v
    rwa [OrderIso.apply_symm_apply] at h
  have hyUJ : ∀ u ∈ UJ, yU u ∈ UJ := by
    intro u hu
    have huJ : Additive.ofMul u ∈ J := (hmem (Additive.ofMul u)).mpr (by simpa using hu)
    have h := hJ (mulAutToGL U yU) (Subgroup.mem_zpowers _) (Additive.ofMul u) huJ
    rw [mulAutToGL_apply] at h
    exact (hmem (Additive.ofMul (yU u))).mp h
  have hfixUJ : UJ ⊓ fixV (Subgroup.zpowers yU) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    have hfixu : yU u = u :=
      CFSG.RankThree.S4Free.Stell.mem_fixV_zpowers_iff_apply.mp hu.2
    have hyu : y u.1 = u.1 := by
      have := congrArg (fun v : U => (v : E)) hfixu
      simpa [hyU_apply u] using this
    have hmem' : (u.1 : E) ∈ U ⊓ fixV (Subgroup.zpowers y) :=
      ⟨u.2, CFSG.RankThree.S4Free.Stell.mem_fixV_zpowers_iff_apply.mpr hyu⟩
    rw [hfix] at hmem'
    exact Subtype.ext (by simpa using hmem')
  have hdvd := dParam_dvd_rk (W := U) hU2 hp hp2 hyU_order hyUJ hfixUJ
  have hdvdJ : dParam p ∣ Module.finrank (ZMod 2) J := by
    have h := hdvd
    rwa [CFSG.LocalAnalysis.WeakClosure81.w16g_rk_eq_finrank hU2 UJ,
      OrderIso.apply_symm_apply] at h
  have hJdim_lt : Module.finrank (ZMod 2) J < dParam p := by
    rw [← htopdim]
    simpa using Submodule.finrank_lt (K := ZMod 2) (V := Additive U) hJtop
  have hpos : 0 < Module.finrank (ZMod 2) J := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) J) with h0 | hpos
    · exact absurd ((Submodule.finrank_eq_zero).mp h0) hJbot
    · exact hpos
  have hle := Nat.le_of_dvd hpos hdvdJ
  omega


private theorem coe_pow_linearEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[K] V) : Module.End K V) = (e : Module.End K V) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

theorem exists_two_pow_of_conj_eq_pow (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x n : MulAut W} (hx : orderOf x = p) {M : Subgroup W}
    (hMx : ∀ m ∈ M, x m ∈ M) (hMn : ∀ m ∈ M, n m ∈ M) (hfix : M ⊓ fixV (zpowers x) = ⊥)
    (hM : rk ↥M = dParam p) {k : ℕ} (hn : n * x * n⁻¹ = x ^ k) :
    ∃ j : ℕ, (k : ZMod p) = 2 ^ j := by
  classical
  have : Module (ZMod 2) (Additive ↥M) :=
    CFSG.RankThree.FFModules.moduleOfSq (fun m : ↥M => Subtype.ext (hW m.1))
  have hxinv : ∀ m ∈ M, x⁻¹ m ∈ M := inv_mem_of_map_mem hMx
  have hx_stab : x ∈ stabSub M := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h := hxinv (x u) hu
      simpa using h, hMx u⟩
  let xM : MulAut ↥M := resHom M ⟨x, hx_stab⟩
  have hxM_apply : ∀ m : ↥M, ((xM m : ↥M) : W) = x m := fun m => resHom_apply M _ m
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxMp : xM ^ p = 1 := by
    change resHom M ⟨x, hx_stab⟩ ^ p = 1
    rw [← map_pow, show (⟨x, hx_stab⟩ : stabSub M) ^ p = 1 by
      apply Subtype.ext
      simpa using hxp, map_one]
  have hMne : M ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥M = 0 := by rw [hbot]; simp [rk]
    rw [hM] at h0
    exact (dParam_pos hp hp2).ne' h0
  have hxMne : xM ≠ 1 := by
    intro h1
    obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
    have hxm : x m = m := by
      have := congrArg (fun f : MulAut ↥M => ((f ⟨m, hm⟩ : ↥M) : W)) h1
      simpa [xM, resHom_apply] using this
    have hmem : m ∈ M ⊓ fixV (Subgroup.zpowers x) :=
      ⟨hm, CFSG.RankThree.S4Free.Stell.mem_fixV_zpowers_iff_apply.mpr hxm⟩
    rw [hfix] at hmem
    have hm_eq : m = 1 := by simpa using hmem
    exact hm1 (Subtype.ext hm_eq)
  have hxM_order : orderOf xM = p := by
    have hdvd : orderOf xM ∣ p := orderOf_dvd_of_pow_eq_one hxMp
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hxMne
    · exact hp'
  let X : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M := mulAutToGL ↥M xM
  let H : Subgroup (Additive ↥M ≃ₗ[ZMod 2] Additive ↥M) := Subgroup.zpowers X
  have hirr : IsIrr H ⊤ :=
    isIrr_zpowers_of_apply (E := W) (y := x) (U := M) (yU := xM) hp hp2
      hxM_apply hxM_order hfix hM hW
  have hXmem : (X : Module.End (ZMod 2) (Additive ↥M)) ∈ commutantOf H := by
    rw [mem_commutantOf]
    intro h hh v
    rw [Subgroup.mem_zpowers_iff] at hh
    obtain ⟨m, rfl⟩ := hh
    have hc : Commute X (X ^ m) := Commute.self_zpow X m
    simpa [LinearEquiv.mul_apply] using
      congrArg (fun f : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M => f v) hc.eq
  have hninv : ∀ m ∈ M, n⁻¹ m ∈ M := inv_mem_of_map_mem hMn
  have hn_stab : n ∈ stabSub M := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h := hninv (n u) hu
      simpa using h, hMn u⟩
  let nM : MulAut ↥M := resHom M ⟨n, hn_stab⟩
  let N : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M := mulAutToGL ↥M nM
  have hNX_mulAut : nM * xM * nM⁻¹ = xM ^ k := by
    have hrel : (⟨n, hn_stab⟩ : stabSub M) * ⟨x, hx_stab⟩ * ⟨n, hn_stab⟩⁻¹
        = (⟨x, hx_stab⟩ : stabSub M) ^ k := by
      apply Subtype.ext
      simpa using hn
    calc
      nM * xM * nM⁻¹
          = resHom M ((⟨n, hn_stab⟩ : stabSub M) * ⟨x, hx_stab⟩) *
              resHom M (⟨n, hn_stab⟩⁻¹) := by rw [map_mul, map_inv]
      _ = resHom M (((⟨n, hn_stab⟩ : stabSub M) * ⟨x, hx_stab⟩) *
              ⟨n, hn_stab⟩⁻¹) := by rw [← map_mul]
      _ = resHom M ((⟨x, hx_stab⟩ : stabSub M) ^ k) := by rw [hrel]
      _ = xM ^ k := by rw [map_pow]
  have hNX : N * X * N⁻¹ = X ^ k := by
    calc
      N * X * N⁻¹ = mulAutToGL ↥M (nM * xM * nM⁻¹) := by simp [N, X]
      _ = mulAutToGL ↥M (xM ^ k) := by rw [hNX_mulAut]
      _ = mulAutToGL ↥M xM ^ k := by rw [map_pow]
      _ = X ^ k := by rfl
  have hγ : ∀ h ∈ H, N * h * N⁻¹ ∈ H := by
    intro h hh
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨m, rfl⟩ := hh
    refine ⟨(k : ℤ) * m, ?_⟩
    symm
    calc
      N * X ^ m * N⁻¹ = MulAut.conj N (X ^ m) := (MulAut.conj_apply N (X ^ m)).symm
      _ = (MulAut.conj N X) ^ m := map_zpow (MulAut.conj N) X m
      _ = (N * X * N⁻¹) ^ m := by rw [MulAut.conj_apply]
      _ = (X ^ k) ^ m := by rw [hNX]
      _ = X ^ ((k : ℤ) * m) := by rw [← zpow_natCast, ← zpow_mul]
  have : Finite (Additive ↥M ≃ₗ[ZMod 2] Additive ↥M) :=
    Finite.of_injective (fun e : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M =>
      (e : Additive ↥M → Additive ↥M)) DFunLike.coe_injective
  have : Finite ↥H := Subtype.finite
  have hmapH_le : H.map (MulAut.conj N).toMonoidHom ≤ H := by
    rintro - ⟨h, hh, rfl⟩
    exact hγ h hh
  have hmapH_card : Nat.card (H.map (MulAut.conj N).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj N).injective
  have hmapH : H.map (MulAut.conj N).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hmapH_le (by rw [hmapH_card])
  have hγ' : ∀ h ∈ H, N⁻¹ * h * N ∈ H := by
    intro h hh
    have hmem : h ∈ H.map (MulAut.conj N).toMonoidHom := by rw [hmapH]; exact hh
    obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.mp hmem
    have hh'val : N⁻¹ * h * N = h' := by
      have hconj : MulAut.conj N h' = h := by simpa using hh'eq
      rw [← hconj, MulAut.conj_apply]
      group
    rw [hh'val]
    exact hh'
  let : Algebra (ZMod 2) (CommF H hirr) :=
    inferInstanceAs (Algebra (ZMod 2) ↥(commutantOf H))
  let σRing : CommF H hirr ≃+* CommF H hirr := CommF.conj N hγ hγ'
  have hσRing_alg : ∀ c : ZMod 2, σRing (algebraMap (ZMod 2) (CommF H hirr) c) =
      algebraMap (ZMod 2) (CommF H hirr) c := by
    intro c
    have hc : c = 0 ∨ c = 1 := by
      have hlt : c.val < 2 := ZMod.val_lt c
      interval_cases h : c.val
      · left; rw [← ZMod.natCast_zmod_val c, h]; norm_num
      · right; rw [← ZMod.natCast_zmod_val c, h]; norm_num
    rcases hc with rfl | rfl
    · simp
    · rw [show algebraMap (ZMod 2) (CommF H hirr) (1 : ZMod 2) = 1 from map_one _]
      simp
  let σ : CommF H hirr ≃ₐ[ZMod 2] CommF H hirr :=
    AlgEquiv.ofRingEquiv (f := σRing) hσRing_alg
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 (CommF H hirr) σ
  rw [Nat.card_zmod] at hj
  let XK : CommF H hirr := CommF.mk (X : Module.End (ZMod 2) (Additive ↥M)) hXmem
  have hσXK : σ XK = XK ^ 2 ^ j := hj XK
  have hσXK_val : (σ XK).val = X ^ k := by
    change conjEnd N X = X ^ k
    have h1 : ((N * X * N⁻¹ : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M) :
        Module.End (ZMod 2) (Additive ↥M)) =
        (X : Module.End (ZMod 2) (Additive ↥M)) ^ k := by
      rw [← coe_pow_linearEquiv X k]
      exact congrArg (fun e : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M =>
        (e : Module.End (ZMod 2) (Additive ↥M))) hNX
    simpa [conjEnd] using h1
  have hXKpow_val : ∀ n : ℕ, (XK ^ n).val = X ^ n := by
    intro n
    induction n with
    | zero => simp [XK, CommF.val_one]
    | succ n ih =>
        rw [pow_succ, CommF.val_mul, ih, pow_succ]
        simp [XK]
  have hσXK_eq : σ XK = XK ^ k := by
    apply CommF.val_injective
    rw [hσXK_val, hXKpow_val]
  have hXpow_K : ((X ^ k : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M) :
      Module.End (ZMod 2) (Additive ↥M)) =
      ((X ^ (2 ^ j) : Additive ↥M ≃ₗ[ZMod 2] Additive ↥M) :
        Module.End (ZMod 2) (Additive ↥M)) := by
    have h1 : XK ^ k = XK ^ (2 ^ j) := by rw [← hσXK_eq, hσXK]
    have h2 := congrArg (fun e : CommF H hirr => e.val) h1
    simpa [hXKpow_val, coe_pow_linearEquiv] using h2
  have hXpow : X ^ k = X ^ (2 ^ j) := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) (Additive ↥M) => f v) hXpow_K
  have hXorder : orderOf X = p := by
    rw [orderOf_injective (mulAutToGL ↥M) (mulAutToGL_injective ↥M) xM, hxM_order]
  have hmod : k ≡ 2 ^ j [MOD p] := by
    rw [← hXorder]
    exact (pow_eq_pow_iff_modEq).mp hXpow
  exact ⟨j, by simpa using (ZMod.natCast_eq_natCast_iff k (2 ^ j) p).mpr hmod⟩

theorem false_of_conj_eq_pow (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x n : MulAut W} (hx : orderOf x = p) {M : Subgroup W} (hM1 : M ≠ ⊥)
    (hMx : ∀ m ∈ M, x m ∈ M) (hMn : ∀ m ∈ M, n m ∈ M) (hfix : M ⊓ fixV (zpowers x) = ⊥)
    (hM : rk ↥M < 2 * dParam p) {k : ℕ} (hn : n * x * n⁻¹ = x ^ k)
    (hk : ∀ j : ℕ, (2 : ZMod p) ^ j ≠ k) : False := by
  classical
  have hrk_pos : 0 < rk ↥M := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hM1 ((rk_eq_zero_iff hW).mp h0)
  have hdvd : dParam p ∣ rk ↥M := dParam_dvd_rk hW hp hp2 hx hMx hfix
  have hrk : rk ↥M = dParam p := Nat.eq_of_dvd_of_lt_two_mul hrk_pos.ne' hdvd hM
  obtain ⟨j, hj⟩ := exists_two_pow_of_conj_eq_pow hW hp hp2 hx hMx hMn hfix hrk hn
  exact hk j hj.symm

private theorem false_of_pow_two_eq_neg_one {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hodd : Odd (dParam p)) (hj : (2 : ZMod p) ^ j = -1) : False := by
  have hsq : (2 : ZMod p) ^ (2 * j) = 1 := by
    have h := congrArg (fun x : ZMod p => x ^ 2) hj
    rw [neg_one_sq, ← pow_mul, mul_comm j 2] at h
    exact h
  have hdvd2j : dParam p ∣ 2 * j := by
    exact orderOf_dvd_of_pow_eq_one hsq
  have hcop : Nat.Coprime (dParam p) 2 := Nat.coprime_two_right.mpr hodd
  have hdvdj : dParam p ∣ j := by
    exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd2j)
  have hone : (2 : ZMod p) ^ j = 1 := by
    obtain ⟨q, rfl⟩ := hdvdj
    rw [pow_mul, pow_dParam, one_pow]
  have hneg : (1 : ZMod p) = -1 := hone.symm.trans hj
  have htwo : (2 : ZMod p) = 0 := by
    have h := congrArg (fun x : ZMod p => x + 1) hneg
    norm_num at h
    exact h
  have hpdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd)

theorem dihedralDeg_le_rk (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x g : MulAut W} (hx : orderOf x = p) {M : Subgroup W} (hM1 : M ≠ ⊥)
    (hMx : ∀ m ∈ M, x m ∈ M) (hMg : ∀ m ∈ M, g m ∈ M) (hfix : M ⊓ fixV (zpowers x) = ⊥)
    (hinv : g * x * g⁻¹ = x⁻¹) : WeakClosure81.dihedralDeg p ≤ rk ↥M := by
  classical
  have hdvd : dParam p ∣ rk ↥M := dParam_dvd_rk hW hp hp2 hx hMx hfix
  have hrk_pos : 0 < rk ↥M := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hM1 ((rk_eq_zero_iff hW).mp h0)
  unfold WeakClosure81.dihedralDeg
  split_ifs with hd
  · exact Nat.le_of_dvd hrk_pos hdvd
  · have hodd : Odd (dParam p) := Nat.not_even_iff_odd.mp hd
    have hrk_ne : rk ↥M ≠ dParam p := by
      intro hrk
      have hxpow : x ^ (p - 1) = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, ← hx, pow_orderOf_eq_one]
      have hg : g * x * g⁻¹ = x ^ (p - 1) := by rw [hinv, ← hxpow]
      obtain ⟨j, hj⟩ := exists_two_pow_of_conj_eq_pow hW hp hp2 hx hMx hMg hfix hrk hg
      have hjneg : (2 : ZMod p) ^ j = -1 := by
        rw [← hj, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
      exact false_of_pow_two_eq_neg_one hp hp2 hodd hjneg
    obtain ⟨q, hq⟩ := hdvd
    have hqpos : 0 < q := by
      apply Nat.pos_of_mul_pos_left
      rwa [← hq]
    have hqne : q ≠ 1 := by
      intro hq1
      exact hrk_ne (by rw [hq, hq1, mul_one])
    have h2q : 2 ≤ q := by omega
    calc
      2 * dParam p = dParam p * 2 := by ring
      _ ≤ dParam p * q := Nat.mul_le_mul_left _ h2q
      _ = rk ↥M := hq.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
