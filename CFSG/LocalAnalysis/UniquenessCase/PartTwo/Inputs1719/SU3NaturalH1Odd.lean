module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3Modules
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.Asc81cPfTen8
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module
public import CFSG.Fischer.Classification.Recognition.SymOBasic
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3Key
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise Matrix

@[expose] def K_SU3NaturalH1Even : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut W)) (n : ℕ), IsSU3 ↥K n → 2 ≤ n → Even n →
      ∀ (Z W' : Subgroup W), StableUnder K Z → Z ≤ fixV K →
        W' ⊔ Z = ⊤ → W' ⊓ Z = ⊥ →
        NatSUn (autQuot K Z) ⊤ ⊥ 3 n →
          ∃ W'' : Subgroup W, StableUnder K W'' ∧ W'' ⊓ Z = ⊥ ∧ W'' ⊔ Z = ⊤ ∧
            W'' = CFSG.Quasithin.commSub (⊤ : Subgroup W) K ∧
            CNatModSU3Sub W W'' K n

theorem k_SU3NaturalH1_odd (W : Type) [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (K : Subgroup (MulAut W)) (n : ℕ)
    (hK : IsSU3 ↥K n) (hn : 2 ≤ n) (hodd : Odd n)
    (Z W' : Subgroup W) (hZK : StableUnder K Z) (hZ : Z ≤ fixV K)
    (hsup : W' ⊔ Z = ⊤) (hinf : W' ⊓ Z = ⊥)
    (hNat : NatSUn (autQuot K Z) ⊤ ⊥ 3 n) :
    ∃ W'' : Subgroup W, StableUnder K W'' ∧ W'' ⊓ Z = ⊥ ∧ W'' ⊔ Z = ⊤ ∧
      W'' = CFSG.Quasithin.commSub (⊤ : Subgroup W) K ∧
      CNatModSU3Sub W W'' K n := by
  classical
  obtain ⟨Kf, hKfield, hKfin, hKcard, hReal⟩ := hNat
  letI : Field Kf := hKfield
  have : Finite Kf := hKfin
  obtain ⟨π, hπ⟩ := hReal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful (FFModel.nat_faithful (StatedSU 3 (2 ^ n) Kf)) hπ
  have hπsurj : Function.Surjective π := hπ.1
  let e : ↥(StatedSU 3 (2 ^ n) Kf) ≃* ↥(autQuot K Z) :=
    MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  obtain ⟨β, hβsurj, hβker, hβeq⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSU 3 (2 ^ n) Kf)) rfl rfl hπ
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : (u * v⁻¹ : ↥(⊤ : Subgroup (W ⧸ Z))) = 1 := by
      apply Subtype.ext
      have h3 := (hβker (u * v⁻¹)).1 h1
      simpa using h3
    rwa [mul_inv_eq_one] at h2
  have hq : 2 ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3q : 3 ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.three_dvd_two_pow_add_one_of_odd n hodd
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 3 ∣ Nat.card Kfˣ := by
    rw [Nat.card_units, hKcard]
    refine h3q.trans ⟨2 ^ n - 1, ?_⟩
    rw [StatedCenterThree.sq_sub_one_eq hq1, mul_comm]
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kfˣ) 3 hdvd
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  have hcmem : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 (2 ^ n) Kf :=
    StatedCenterThree.scalar_mem hq h3q hc3
  let γ : ↥(StatedSU 3 (2 ^ n) Kf) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, hcmem⟩
  have hγval : (γ : Matrix.GeneralLinearGroup (Fin 3) Kf) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := rfl
  have hγ3 : γ ^ 3 = 1 := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ^ 3 = 1
    rw [← map_pow, hc3, map_one]
  have hγ1 : γ ≠ 1 := by
    intro h
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 3) c = 1 := by
      rw [← hγval, h]
      rfl
    have h2 : c = 1 := by
      have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) Kf =>
        (g : Matrix (Fin 3) (Fin 3) Kf) 0 0) h1
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
    exact hc1 h2
  have hγord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hγcenter : γ ∈ Subgroup.center ↥(StatedSU 3 (2 ^ n) Kf) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    change (x : Matrix.GeneralLinearGroup (Fin 3) Kf) *
        Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c *
        (x : Matrix.GeneralLinearGroup (Fin 3) Kf)
    exact (Matrix.GeneralLinearGroup.scalar_commute c
      (x : Matrix.GeneralLinearGroup (Fin 3) Kf)).symm
  let h : ↥(autQuot K Z) := e γ
  have hh_ord : orderOf h = 3 := by
    have h1 := orderOf_injective e.toMonoidHom e.injective γ
    rw [show h = e.toMonoidHom γ from rfl, h1, hγord]
  have hh1 : h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hh_ord
    exact absurd hh_ord (by norm_num)
  have hh_center : h ∈ Subgroup.center ↥(autQuot K Z) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [show h = e γ from rfl, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp hγcenter x]
  have hKstab : K ≤ stabSub Z := by
    intro x hx u
    constructor
    · intro hxu
      have hx' : x⁻¹ ∈ K := K.inv_mem hx
      have h1 := hZK x⁻¹ hx' (x u) hxu
      simpa using h1
    · intro hu
      exact hZK x hx u hu
  let φ₀ : ↥K →* MulAut (W ⧸ Z) :=
    (quotHom Z).comp (Subgroup.inclusion hKstab)
  let φ : ↥K →* ↥(autQuot K Z) :=
    φ₀.codRestrict (autQuot K Z) (by
      intro x
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKstab x, x.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : MulAut (W ⧸ Z)) ∈ (K.subgroupOf (stabSub Z)).map (quotHom Z) := y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨(x : MulAut W), hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hker_sq : ∀ x ∈ φ.ker, x * x = 1 := by
    intro x hx
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have hxq : quotHom Z (Subgroup.inclusion hKstab x) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    have hmem : (x : MulAut W) w * w⁻¹ ∈ Z := by
      have h1 := congrArg (fun f : MulAut (W ⧸ Z) => f (QuotientGroup.mk w)) hxq
      simp only [MulAut.one_apply, quotHom_mk] at h1
      exact (mk_eq_mk_iff ((x : MulAut W) w) w).mp h1
    have hfixZ : ∀ z ∈ Z, (x : MulAut W) z = z := fun z hz =>
      (mem_fixV.mp (hZ hz)) (x : MulAut W) x.2
    calc ((x * x : ↥K) : MulAut W) w = (x : MulAut W) ((x : MulAut W) w) := rfl
      _ = (x : MulAut W) (((x : MulAut W) w * w⁻¹) * w) := by
          rw [show ((x : MulAut W) w * w⁻¹) * w = (x : MulAut W) w by group]
      _ = (x : MulAut W) ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w := by rw [map_mul]
      _ = ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w := by rw [hfixZ _ hmem]
      _ = w := by
        rw [show ((x : MulAut W) w * w⁻¹) * (x : MulAut W) w =
          ((x : MulAut W) w * (x : MulAut W) w) * w⁻¹ by ac_rfl]
        rw [show (x : MulAut W) w * (x : MulAut W) w = 1 by
          simpa [pow_two] using hW ((x : MulAut W) w), one_mul,
          inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hW w)]
  have hker_comm : ∀ a ∈ φ.ker, ∀ b ∈ φ.ker, a * b = b * a := by
    intro a ha b hb
    have ha2 := hker_sq a ha
    have hb2 := hker_sq b hb
    have hab2 := hker_sq (a * b) (φ.ker.mul_mem ha hb)
    have h1 : a * b = (a * b)⁻¹ := mul_eq_one_iff_eq_inv.mp hab2
    rw [h1, mul_inv_rev, (mul_eq_one_iff_inv_eq.mp hb2), (mul_eq_one_iff_inv_eq.mp ha2)]
  have hker_le_center : φ.ker ≤ Subgroup.center ↥K :=
    CFSG.Fischer.Classification.Recognition.SymO.le_center_of_normal hK.1 φ.normal_ker hker_comm
  obtain ⟨g, hg⟩ := hφsurj h
  have hg_center : g ∈ Subgroup.center ↥K := by
    have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect
      (Group.isPerfect_def.2 hK.1.1) φ hφsurj hker_le_center
    rw [← hcomap, Subgroup.mem_comap, hg]
    exact hh_center
  have hg3ker : g ^ 3 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hg]
    have h1 := pow_orderOf_eq_one h
    rwa [hh_ord] at h1
  have hg6 : g ^ 6 = 1 := by
    have h1 := hker_sq (g ^ 3) hg3ker
    rwa [← pow_add, show 3 + 3 = 6 by norm_num] at h1
  have hgdvd6 : orderOf g ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hg6
  have hg3dvd : 3 ∣ orderOf g := by
    have h1 := orderOf_map_dvd φ g
    rwa [hg, hh_ord] at h1
  have hgord : orderOf g = 3 ∨ orderOf g = 6 := by
    have h1 : 3 ≤ orderOf g := Nat.le_of_dvd (orderOf_pos g) hg3dvd
    have h2 : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hgdvd6
    interval_cases orderOf g <;> simp_all
  let m := orderOf g / 3
  have hm : orderOf g = 3 * m := by
    rcases hgord with h | h <;> simp [m, h]
  let zK : ↥K := g ^ m
  have hzK_center : zK ∈ Subgroup.center ↥K := Subgroup.pow_mem _ hg_center m
  have hzK_ord : orderOf zK = 3 := by
    have hx : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hdvd3 : 3 ∣ orderOf g := ⟨m, hm⟩
    have h1 := orderOf_pow_orderOf_div (x := g) hx hdvd3
    simpa [zK, m] using h1
  have hm_cases : m = 1 ∨ m = 2 := by
    rcases hgord with h | h <;> simp [m, h]
  have hφzK : φ zK = π (γ ^ m) := by
    have h1 : φ zK = h ^ m := by rw [show zK = g ^ m from rfl, map_pow, hg]
    rw [h1, show h = π γ from rfl]
    exact (map_pow π γ m).symm
  have hγmval : ((γ ^ m : ↥(StatedSU 3 (2 ^ n) Kf)) :
      Matrix.GeneralLinearGroup (Fin 3) Kf) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ m) := by
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ^ m =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ m)
    rw [← map_pow]
  have hcm1 : c ^ m ≠ 1 := by
    rcases hm_cases with h1 | h2
    · rw [h1]; simpa using hc1
    · rw [h2]
      intro h3
      have h4 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h3
      rw [hc] at h4
      norm_num at h4
  have hfp : ∀ u : W ⧸ Z, ((φ zK : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u = u → u = 1 := by
    intro u hu
    let v : Fin 3 → Kf := Multiplicative.toAdd (β ⟨u, Subgroup.mem_top u⟩)
    let cm : Kf := ((c ^ m : Kfˣ) : Kf)
    have h1 : β ⟨u, Subgroup.mem_top u⟩ =
        β ⟨((φ zK : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) u, Subgroup.mem_top _⟩ := by rw [hu]
    have h4 := hβeq (γ ^ m) ⟨u, Subgroup.mem_top u⟩ (Subgroup.mem_top _)
    rw [← hφzK] at h4
    rw [h4] at h1
    have hsmul : ∀ w : Fin 3 → Kf,
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ m) :
            Matrix (Fin 3) (Fin 3) Kf) *ᵥ w = cm • w := by
      intro w
      ext i
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rfl
    have h3 : v = ((Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ m) :
        Matrix (Fin 3) (Fin 3) Kf) *ᵥ v) := by
      have h5 := congrArg Multiplicative.toAdd h1
      change v = Multiplicative.toAdd ((FFModel.nat (StatedSU 3 (2 ^ n) Kf)).act
        (γ ^ m) (β ⟨u, Subgroup.mem_top u⟩)) at h5
      rw [show Multiplicative.toAdd ((FFModel.nat (StatedSU 3 (2 ^ n) Kf)).act
          (γ ^ m) (β ⟨u, Subgroup.mem_top u⟩)) =
        (((γ ^ m : ↥(StatedSU 3 (2 ^ n) Kf)) :
            Matrix.GeneralLinearGroup (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *ᵥ v
          from rfl] at h5
      rw [hγmval] at h5
      exact h5
    have h2 : v = cm • v := h3.trans (hsmul v)
    have hzero : v = 0 := by
      funext i
      have hi : v i = cm * v i := congrFun h2 i
      have hz : (cm - 1) * v i = 0 := by
        rw [sub_mul, one_mul, ← hi, sub_self]
      have hcne : cm - 1 ≠ 0 := by
        apply sub_ne_zero.mpr
        intro h1
        exact hcm1 (Units.ext h1)
      exact (mul_eq_zero.mp hz).resolve_left hcne
    have hβu : β ⟨u, Subgroup.mem_top u⟩ = 1 := by
      rw [← ofAdd_toAdd (β ⟨u, Subgroup.mem_top u⟩)]
      change Multiplicative.ofAdd v = 1
      rw [hzero, ofAdd_zero]
    have hmem : u ∈ (⊥ : Subgroup (W ⧸ Z)) := (hβker _).mp hβu
    simpa using hmem
  let Y : Subgroup (MulAut W) := Subgroup.zpowers (zK : MulAut W)
  have hfixY : fixV Y = Z := by
    apply le_antisymm
    · intro w hw
      have hzw : ((φ zK : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
          QuotientGroup.mk w := by
        have h1 : ((φ zK : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
            QuotientGroup.mk ((zK : MulAut W) w) := by
          change quotHom Z (Subgroup.inclusion hKstab zK) (QuotientGroup.mk w) = _
          rw [quotHom_mk]
          rfl
        rw [h1, hw (zK : MulAut W) (Subgroup.mem_zpowers _)]
      exact (QuotientGroup.eq_one_iff w).mp (hfp _ hzw)
    · intro z hz
      rw [mem_fixV]
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact CFSG.Quasithin.Asc81c.Pf.zpow_apply_eq
        ((mem_fixV.mp (hZ hz)) (zK : MulAut W) zK.2) i
  have hoddY : Odd (Nat.card Y) := by
    rw [show Nat.card Y = 3 by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzK_ord]]
    decide
  have hPinf : Z ⊓ commSub (⊤ : Subgroup W) Y = ⊥ := by
    rw [← hfixY]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_inf_commSub_eq_bot hW hoddY
  have hPsup : Z ⊔ commSub (⊤ : Subgroup W) Y = ⊤ := by
    rw [← hfixY]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_sup_commSub_eq_top hW hoddY
  let P : Subgroup W := commSub (⊤ : Subgroup W) Y
  have hPstable : StableUnder K P := by
    intro x hx u hu
    have hxz : (x : MulAut W) * (zK : MulAut W) = (zK : MulAut W) * (x : MulAut W) := by
      have h1 := Subgroup.mem_center_iff.mp hzK_center ⟨x, hx⟩
      exact congrArg Subtype.val h1
    have hconj : MulAut.conj (x : MulAut W) (zK : MulAut W) = (zK : MulAut W) := by
      rw [MulAut.conj_apply, hxz]
      group
    have hYmap : Y.map (MulAut.conj (x : MulAut W)).toMonoidHom = Y := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj (x : MulAut W)) (zK : MulAut W)) =
        Subgroup.zpowers (zK : MulAut W)
      rw [hconj]
    have hmap := CFSG.Quasithin.Asc81c.commSub_map_conj Y (x : MulAut W)
    rw [hYmap] at hmap
    rw [show P = commSub (⊤ : Subgroup W) Y from rfl, hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hcommK : commSub (⊤ : Subgroup W) K = P := by
    apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro q ⟨x, hx, w, -, rfl⟩
      have hwtop : w ∈ P ⊔ Z := by
        rw [show P ⊔ Z = ⊤ from by rw [sup_comm]; exact hPsup]
        exact Subgroup.mem_top w
      obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hwtop
      have hxp : (x : MulAut W) p ∈ P := hPstable x hx p hp
      have hxs : (x : MulAut W) s = s := (mem_fixV.mp (hZ hs)) x hx
      have heq : (x : MulAut W) (p * s) * (p * s)⁻¹ = (x : MulAut W) p * p⁻¹ := by
        rw [map_mul, hxs]
        group
      rw [heq]
      exact P.mul_mem hxp (P.inv_mem hp)
    · exact commSub_mono le_rfl (Subgroup.zpowers_le.mpr zK.2)
  let f : ↥P →* (W ⧸ Z) := (QuotientGroup.mk' Z).comp (Subgroup.subtype P)
  let f' : ↥P →* ↥(⊤ : Subgroup (W ⧸ Z)) := f.codRestrict ⊤ (fun _ => Subgroup.mem_top _)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h1 : (a : W) * (b : W)⁻¹ ∈ Z := (mk_eq_mk_iff (a : W) (b : W)).mp hab
    have h2 : (a : W) * (b : W)⁻¹ ∈ P := P.mul_mem a.2 (P.inv_mem b.2)
    have h3 : (a : W) * (b : W)⁻¹ ∈ P ⊓ Z := ⟨h2, h1⟩
    have h4 : (a : W) * (b : W)⁻¹ = 1 := by
      have h5 : P ⊓ Z = ⊥ := by rw [inf_comm]; exact hPinf
      rw [h5] at h3
      simpa using h3
    rwa [mul_inv_eq_one] at h4
  have hf_surj : Function.Surjective f := by
    intro u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Z u
    have hwtop : w ∈ P ⊔ Z := by
      rw [show P ⊔ Z = ⊤ from by rw [sup_comm]; exact hPsup]
      exact Subgroup.mem_top w
    obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hwtop
    refine ⟨⟨p, hp⟩, ?_⟩
    change QuotientGroup.mk p = QuotientGroup.mk (p * s : W)
    rw [QuotientGroup.mk_mul]
    have h2 : (QuotientGroup.mk s : W ⧸ Z) = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    rw [h2, mul_one]
  have hcomp_inj : Function.Injective (β.comp f') := by
    intro a b h
    exact hf_inj (congrArg Subtype.val (hβinj h))
  have hcomp_surj : Function.Surjective (β.comp f') := by
    intro y
    obtain ⟨u, hu⟩ := hβsurj y
    obtain ⟨p, hp⟩ := hf_surj u
    refine ⟨p, ?_⟩
    change β (f' p) = y
    have hfp' : f' p = ⟨u, Subgroup.mem_top u⟩ := Subtype.ext hp
    rw [hfp', hu]
  let eP : ↥P ≃* Multiplicative (Fin 3 → Kf) :=
    MulEquiv.ofBijective (β.comp f') ⟨hcomp_inj, hcomp_surj⟩
  have heP : ∀ (w : W) (hw : w ∈ P),
      eP ⟨w, hw⟩ = β ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ := by
    intro w hw
    rfl
  refine ⟨P, hPstable, ?_, ?_, hcommK.symm, ?_⟩
  · rw [inf_comm]
    exact hPinf
  · rw [sup_comm]
    exact hPsup
  · refine ⟨⟨Kf, hKcard, eP, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx w hw
      exact hPstable x hx w hw
    · intro x hx
      obtain ⟨γx, hγx⟩ := hπsurj (φ ⟨x, hx⟩)
      let γx' : ↥(StatedSU 3 (2 ^ n) Kf) := γx
      refine ⟨(γx' : Matrix.GeneralLinearGroup (Fin 3) Kf), γx'.2, ?_⟩
      intro w hw hxw
      have hxw' : ((π γx : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
          QuotientGroup.mk ((x : MulAut W) w) := by
        rw [hγx]
        change quotHom Z (Subgroup.inclusion hKstab ⟨x, hx⟩) (QuotientGroup.mk w) =
          QuotientGroup.mk ((x : MulAut W) w)
        rw [quotHom_mk]
        rfl
      rw [heP (x w) hxw, ← hxw']
      rw [hβeq γx' ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ (Subgroup.mem_top _)]
      rw [heP w hw]
      rfl
    · intro A hA
      let γA : ↥(StatedSU 3 (2 ^ n) Kf) := ⟨A, hA⟩
      obtain ⟨x, hx⟩ := hφsurj (π γA)
      refine ⟨x, x.2, ?_⟩
      intro w hw hxw
      have hxw' : ((π γA : ↥(autQuot K Z)) : MulAut (W ⧸ Z)) (QuotientGroup.mk w) =
          QuotientGroup.mk ((x : MulAut W) w) := by
        rw [← hx]
        change quotHom Z (Subgroup.inclusion hKstab x) (QuotientGroup.mk w) =
          QuotientGroup.mk ((x : MulAut W) w)
        rw [quotHom_mk]
        rfl
      rw [heP ((x : MulAut W) w) hxw, ← hxw']
      rw [hβeq γA ⟨QuotientGroup.mk w, Subgroup.mem_top _⟩ (Subgroup.mem_top _)]
      rw [heP w hw]
      rfl
    · intro x hx hfix
      apply MulEquiv.ext
      intro u
      have hutop : u ∈ P ⊔ Z := by
        rw [show P ⊔ Z = ⊤ from by rw [sup_comm]; exact hPsup]
        exact Subgroup.mem_top u
      obtain ⟨p, hp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hutop
      have hxp : (x : MulAut W) p = p := hfix p hp
      have hxs : (x : MulAut W) s = s := (mem_fixV.mp (hZ hs)) x hx
      rw [map_mul, hxp, hxs]
      rfl

theorem k_SU3NaturalH1_of_even (h : K_SU3NaturalH1Even) : K_SU3NaturalH1 := by
  intro W _ _ hW K n hK hn Z W' hZK hZ hsup hinf hNat
  rcases Nat.even_or_odd n with hEven | hOdd
  · exact h W hW K n hK hn hEven Z W' hZK hZ hsup hinf hNat
  · exact k_SU3NaturalH1_odd W hW K n hK hn hOdd Z W' hZK hZ hsup hinf hNat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
