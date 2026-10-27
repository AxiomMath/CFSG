module

public import CFSG.Quasithin.Background.SmithB45ExcSylow
public import CFSG.Quasithin.Background.SmithB45ExcOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary

public section

namespace CFSG.Quasithin.B45Exc

open Module CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

variable {V : Type} [CommGroup V]

section Stable

variable {p : ℕ} {x y z : MulAut V}

theorem apply_mem_eigE_zero (h : ExtraCfg p x y z) {e : V} (he : e ∈ eigE x z 0) :
    z e ∈ eigE x z 0 := by
  obtain ⟨heT, hex⟩ := mem_eigE.1 he
  refine mem_eigE.2 ⟨apply_mem_imgT rfl heT, ?_⟩
  have hex' : x e = e := by simpa using hex
  have hxz : x (z e) = z (x e) := by
    have := congrArg (fun g : MulAut V => g e) h.zx
    simpa only [MulAut.mul_apply] using this
  simp [hxz, hex']

theorem conj_apply_mem_eigE_zero {t : MulAut V} {n : ℕ} (htx : t * x * t⁻¹ = x)
    (htz : t * z * t⁻¹ = z ^ n) {e : V} (he : e ∈ eigE x z 0) : t e ∈ eigE x z 0 := by
  obtain ⟨heT, hex⟩ := mem_eigE.1 he
  have hex' : x e = e := by simpa using hex
  refine mem_eigE.2 ⟨?_, ?_⟩
  · obtain ⟨v, rfl⟩ := mem_imgT.1 heT
    have h1 : t (z v * v⁻¹) = (z ^ n) (t v) * (t v)⁻¹ := by
      rw [map_mul, map_inv, ← htz, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [h1, pow_apply_div]
    exact mem_imgT.2 ⟨_, rfl⟩
  · have hxt : x (t e) = t (x e) := by
      conv_lhs => rw [← htx]
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    simp [hxt, hex']

end Stable

variable [Finite V]

theorem two_pow_le_card_of_extraspecial_inv {S : Type*} [Group S] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hf : Odd (orderOf (2 : ZMod p))) {x y t : S} (hx : x ^ p = 1)
    (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (htx : t * x * t⁻¹ = x) (htz : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆ ^ (p - 1))
    (hV : ∀ v : V, v * v = 1) (σ : S →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ (2 * p * orderOf (2 : ZMod p)) ≤ Nat.card V := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have : Fact (∀ v : V, v * v = 1) := ⟨hV⟩
  have hzp : ⁅x, y⁆ ^ p = 1 := heis_comm_pow hzx hzy hx
  have hcfg : ExtraCfg p (σ x) (σ y) (σ ⁅x, y⁆) :=
    extraCfg_map σ hσ hx hzp hzx.eq.symm hzy.eq.symm (heis_yinv_x_y hzx hzy) hz1
  set X := σ x with hX
  set Z := σ ⁅x, y⁆ with hZ
  set T := σ t with hT
  have hTX : T * X * T⁻¹ = X := by rw [hT, hX, ← map_inv, ← map_mul, ← map_mul, htx]
  have hTZ : T * Z = Z ^ (p - 1) * T := by
    have h1 : T * Z * T⁻¹ = Z ^ (p - 1) := by
      rw [hT, hZ, ← map_inv, ← map_mul, ← map_mul, htz, map_pow]
    rw [← h1, inv_mul_cancel_right]
  have hTZ' : T * Z * T⁻¹ = Z ^ (p - 1) := by rw [hTZ, mul_inv_cancel_right]
  set E0 := eigE X Z 0 with hE0
  let M : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup E0)
  have hmemM : ∀ v : Additive V, v ∈ M ↔ Additive.toMul v ∈ E0 := fun v => Iff.rfl
  have hcardM : Nat.card M = Nat.card E0 :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.toMul hmemM)
  have hcardM2 : Nat.card M = 2 ^ finrank (ZMod 2) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hZM : ∀ v ∈ M, binaryLin Z v ∈ M := fun v hv => apply_mem_eigE_zero hcfg hv
  have hTM : ∀ v ∈ M, binaryLin T v ∈ M := fun v hv => conj_apply_mem_eigE_zero hTX hTZ' hv
  set zM := restrictEquiv (binaryLin Z) M hZM with hzM
  set tM := restrictEquiv (binaryLin T) M hTM with htM
  have hzMp : zM ^ p = 1 := by
    ext v
    rw [restrictEquiv_pow_apply, ← map_pow, hcfg.zp, map_one]
    rfl
  have hTZl : binaryLin T * binaryLin Z = binaryLin Z ^ (p - 1) * binaryLin T := by
    have := congrArg binaryLin hTZ
    rwa [map_mul, map_mul, map_pow] at this
  have hrel : tM * zM * tM⁻¹ = zM ^ (p - 1) := by
    have h1 : tM * zM = zM ^ (p - 1) * tM := by
      ext v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, restrictEquiv_apply, restrictEquiv_apply,
        restrictEquiv_pow_apply, restrictEquiv_apply, ← LinearEquiv.mul_apply,
        ← LinearEquiv.mul_apply, hTZl]
    rw [h1, mul_inv_cancel_right]
  have hdvd2 := orderOf_dvd_finrank_range_sub1 hp2 hzMp hrel
  have hord : orderOf (((p - 1 : ℕ) : ZMod p)) = 2 := by
    rw [Nat.cast_sub hp.out.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, orderOf_neg_one,
      ZMod.ringChar_zmod_n]
    simp [hp2]
  have hrange : LinearMap.range (sub1 zM) = ⊤ := by
    have hinj : Function.Injective (sub1 zM) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker, sub1_apply, sub_eq_zero] at hv
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have h1 : Z (Additive.toMul (v : Additive V)) = Additive.toMul (v : Additive V) :=
        congrArg (fun w : M => Additive.toMul (w : Additive V)) hv
      have h2 := eq_one_of_mem_imgT_fixed hV hodd hcfg.zp (mem_eigE.1 ((hmemM _).1 v.2)).1 h1
      exact congrArg Additive.ofMul h2
    exact LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective.1 hinj)
  rw [hrange, finrank_top, hord] at hdvd2
  have hfM : orderOf (2 : ZMod p) ∣ finrank (ZMod 2) M := by
    have hmod := hcfg.card_eigE_zero_modEq hV hodd
    rw [← hE0, ← hcardM, hcardM2] at hmod
    have h2 : ((2 ^ finrank (ZMod 2) M : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
    push_cast at h2
    exact orderOf_dvd_of_pow_eq_one h2
  have hMpos : finrank (ZMod 2) M ≠ 0 := by
    intro h0
    obtain ⟨j, hj, hjne⟩ := hcfg.exists_eigE_ne_bot hV hodd
    have h1 : Nat.card (eigE X Z j) = 1 := by
      rw [hcfg.card_eigE_eq hj.le, ← hE0, ← hcardM, hcardM2, h0, pow_zero]
    exact hjne (Subgroup.card_eq_one.1 h1)
  have hcop : Nat.Coprime 2 (orderOf (2 : ZMod p)) := Nat.coprime_two_left.2 hf
  have h2f : 2 * orderOf (2 : ZMod p) ∣ finrank (ZMod 2) M :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd2 hfM
  have hle : 2 * orderOf (2 : ZMod p) ≤ finrank (ZMod 2) M :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hMpos) h2f
  have hE : 2 ^ (2 * orderOf (2 : ZMod p)) ≤ Nat.card E0 := by
    rw [← hcardM, hcardM2]
    exact Nat.pow_le_pow_right (by norm_num) hle
  calc 2 ^ (2 * p * orderOf (2 : ZMod p)) = (2 ^ (2 * orderOf (2 : ZMod p))) ^ p := by
        rw [← pow_mul, mul_right_comm]
    _ ≤ Nat.card E0 ^ p := Nat.pow_le_pow_left hE p
    _ = Nat.card (prodE X Z p).range := (card_range_prodE_of_cfg hcfg hV hodd).symm
    _ ≤ Nat.card V := Subgroup.card_le_card_group _

end CFSG.Quasithin.B45Exc
