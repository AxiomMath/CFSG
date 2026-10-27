module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin
import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

private theorem IsLinRefl.exists_eq_sub_smul_of_apply_eq_neg {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) (hp2 : p ≠ 2) {v : V}
    (hv : v ≠ 0) (hTv : T v = -v) :
    ∃ f : Module.Dual (ZMod p) V, f v = 2 ∧ ∀ w, T w = w - f w • v := by
  have hrefl : IsLinRefl T := h
  obtain ⟨x, f, hfx, hT⟩ := h
  have hxneg : T x = -x := by
    rw [hT x, hfx, two_smul]
    abel
  obtain ⟨c, hc⟩ := hrefl.anti_eq_smul hp2 hv hTv hxneg
  refine ⟨c • f, ?_, fun w => ?_⟩
  · rw [hc, map_smul, smul_eq_mul] at hfx
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact hfx
  · rw [hT w, hc, LinearMap.smul_apply, smul_eq_mul]
    module

private theorem mem_zpowers_of_pow_eq_of_ne_one {H : Type*} [Group H] [Finite H] {u b : H}
    (hexp : ∀ x : H, x ^ p = 1) (hu1 : u ≠ 1) (hb1 : b ≠ 1) {k : ℤ} (hk : u ^ k = b) :
    u ∈ Subgroup.zpowers b := by
  have hordU : orderOf u = p := orderOf_eq_prime (hexp u) hu1
  have hordb : orderOf b = p := orderOf_eq_prime (hexp b) hb1
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers u :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩)
  have hcard : Nat.card (Subgroup.zpowers u) ≤ Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hordU, hordb]
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]
  exact Subgroup.mem_zpowers u

private theorem pow_eq_one_of_sq_eq_one {H : Type*} [Group H] {p : ℕ} (hodd : Odd p) {u : H}
    (h2 : u * u = 1) (hp : u ^ p = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hup : u ^ p = u := by
    rw [hk, pow_add, pow_mul, pow_two, h2, one_pow, one_mul, pow_one]
  rwa [hup] at hp

theorem GGIsReflection.exists_apply_eq_inv (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) : ∃ b : ↥Bs, b ≠ 1 ∧ t b = b⁻¹ := by
  obtain ⟨V, iAV, iMV, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  let := iAV
  let := iMV
  have hB : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  have : Finite (Additive ↥Bs) := hB
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  obtain ⟨w, hw0, hTw⟩ := (isLinRefl_ggLin (p := p) ι ht).exists_anti hp2
  refine ⟨Additive.toMul (ι.symm w), ?_, ?_⟩
  · intro h
    refine hw0 ?_
    rw [← AddEquiv.apply_symm_apply ι w, ← ofMul_toMul (ι.symm w), h]
    simp
  · rw [ggLin_inv_iff (p := p) ι t, ofMul_toMul, AddEquiv.apply_symm_apply]
    exact hTw

theorem GGIsReflection.mem_zpowers_of_apply_eq_inv (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) {u v : ↥Bs} (hu : u ≠ 1) (htu : t u = u⁻¹)
    (htv : t v = v⁻¹) : v ∈ Subgroup.zpowers u := by
  rcases eq_or_ne v 1 with hv1 | hv1
  · rw [hv1]
    exact Subgroup.one_mem _
  obtain ⟨V, iAV, iMV, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  let := iAV
  let := iMV
  have hB : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  have : Finite (Additive ↥Bs) := hB
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hT := isLinRefl_ggLin (p := p) ι ht
  have hu0 : ι (Additive.ofMul u) ≠ 0 := by
    intro h
    rw [← map_zero ι] at h
    exact hu (ofMul_eq_zero.mp (ι.injective h))
  have hv0 : ι (Additive.ofMul v) ≠ 0 := by
    intro h
    rw [← map_zero ι] at h
    exact hv1 (ofMul_eq_zero.mp (ι.injective h))
  have hTu : ggLin (p := p) ι t (ι (Additive.ofMul u)) = -ι (Additive.ofMul u) :=
    (ggLin_inv_iff (p := p) ι t u).mp htu
  have hTv : ggLin (p := p) ι t (ι (Additive.ofMul v)) = -ι (Additive.ofMul v) :=
    (ggLin_inv_iff (p := p) ι t v).mp htv
  obtain ⟨c, hc⟩ := hT.anti_eq_smul hp2 hu0 hTu hTv
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Additive.ofMul.injective
  apply ι.injective
  rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) c.val (ι (Additive.ofMul u)),
    ZMod.natCast_zmod_val]
  exact hc.symm

theorem GGIsReflection.apply_eq_of_commute (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {s t : MulAut ↥Bs} (hs : GGIsReflection p s) (ht : GGIsReflection p t) (hc : s * t = t * s)
    (hne : s ≠ t) {b : ↥Bs} (hb : t b = b⁻¹) : s b = b := by
  obtain ⟨V, iAV, iMV, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  let := iAV
  let := iMV
  have hB : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  have : Finite (Additive ↥Bs) := hB
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hS := isLinRefl_ggLin (p := p) ι hs
  have hT := isLinRefl_ggLin (p := p) ι ht
  have hc' : ggLin (p := p) ι s * ggLin (p := p) ι t =
      ggLin (p := p) ι t * ggLin (p := p) ι s := by
    rw [← map_mul, ← map_mul, hc]
  have hne' : ggLin (p := p) ι s ≠ ggLin (p := p) ι t :=
    fun h => hne (ggLin_injective ι h)
  have hb' : ggLin (p := p) ι t (ι (Additive.ofMul b)) = -ι (Additive.ofMul b) :=
    (ggLin_inv_iff (p := p) ι t b).mp hb
  exact (ggLin_fix_iff (p := p) ι s b).mpr
    (IsLinRefl.comm_fix hp2 hT hS hc'.symm hne'.symm hb')

theorem GGIsReflection.apply_eq_inv_of_fix (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {t : MulAut ↥Bs} (ht : GGIsReflection p t) {S : Set (MulAut ↥Bs)}
    (hS : ∀ φ ∈ S, GGIsReflection p φ ∧ φ * t = t * φ ∧ φ ≠ t) {u : G} (hu : u ∈ Bs)
    (hu1 : u ≠ 1)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ Subgroup.closure S, φ b = b) → (b : G) ∈ Subgroup.zpowers u) :
    t ⟨u, hu⟩ = ⟨u, hu⟩⁻¹ := by
  obtain ⟨b, hb1, htb⟩ := ht.exists_apply_eq_inv hp2 hBs
  have hfixb : ∀ φ ∈ Subgroup.closure S, φ b = b := by
    intro φ hφ
    refine Subgroup.closure_induction (p := fun ψ _ => ψ b = b) ?_ ?_ ?_ ?_ hφ
    · intro ψ hψ
      exact GGIsReflection.apply_eq_of_commute hp2 hBs (hS ψ hψ).1 ht (hS ψ hψ).2.1
        (hS ψ hψ).2.2 htb
    · rfl
    · intro ψ χ _ _ hψ hχ
      rw [MulAut.mul_apply, hχ, hψ]
    · intro ψ _ hψ
      simpa only [hψ] using MulAut.inv_apply_self ↥Bs ψ b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hfix b hfixb)
  have hbk : (⟨u, hu⟩ : ↥Bs) ^ k = b := Subtype.ext (by simpa using hk)
  have hexp : ∀ x : ↥Bs, x ^ p = 1 := fun x => by
    apply Subtype.ext
    simpa using hBs.2 x x.2
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_pow_eq_of_ne_one (p := p) hexp (by simpa using hu1) hb1 hbk)
  rw [← hl, map_zpow, htb, inv_zpow]

theorem GGIsReflection.eq_of_apply_eq_inv (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {s t : MulAut ↥Bs} (hsN : s ∈ ggInduced ⊤ Bs)
    (htN : t ∈ ggInduced ⊤ Bs) (hs : GGIsReflection p s) (ht : GGIsReflection p t) {b : ↥Bs}
    (hb : b ≠ 1) (hsb : s b = b⁻¹) (htb : t b = b⁻¹) : s = t := by
  obtain ⟨V, iAV, iMV, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  let := iAV
  let := iMV
  have hB : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  have : Finite (Additive ↥Bs) := hB
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  set bv : V := ι (Additive.ofMul b) with hbvdef
  have hbv : bv ≠ 0 := by
    rw [hbvdef]
    intro h
    rw [← map_zero ι] at h
    exact hb (ofMul_eq_zero.mp (ι.injective h))
  have hSb : ggLin (p := p) ι s bv = -bv := (ggLin_inv_iff (p := p) ι s b).mp hsb
  have hTb : ggLin (p := p) ι t bv = -bv := (ggLin_inv_iff (p := p) ι t b).mp htb
  obtain ⟨fs, hfsv, hfs⟩ :=
    (isLinRefl_ggLin (p := p) ι hs).exists_eq_sub_smul_of_apply_eq_neg hp2 hbv hSb
  obtain ⟨gs, hgsv, hgs⟩ :=
    (isLinRefl_ggLin (p := p) ι ht).exists_eq_sub_smul_of_apply_eq_neg hp2 hbv hTb
  let h : Module.Dual (ZMod p) V :=
    IsLinearMap.mk' (fun v => gs v - fs v)
      { map_add := by intro x y; simp only [map_add]; abel
        map_smul := by intro c x; simp only [map_smul, smul_sub] }
  by_contra hst
  have hSTne : ggLin (p := p) ι s ≠ ggLin (p := p) ι t :=
    fun h => hst (ggLin_injective ι h)
  have htrans : GGIsTransvection p (s * t) := by
    refine ggIsTransvection_of_apply (p := p) ι (w := bv) (f := h) hbv ?_ ?_ ?_
    · intro hzero
      apply hSTne
      ext w
      have hw : gs w = fs w := by
        refine sub_eq_zero.mp ?_
        simpa [h] using congrArg (fun l : Module.Dual (ZMod p) V => l w) hzero
      rw [hfs w, hgs w, hw]
    · change gs bv - fs bv = 0
      rw [hgsv, hfsv, sub_self]
    · intro w
      rw [map_mul, LinearEquiv.mul_apply, hgs w]
      have h1 : ggLin (p := p) ι s (w - gs w • bv) = w - fs w • bv - gs w • (-bv) := by
        rw [map_sub, map_smul, hfs w, hSb]
      rw [h1]
      change w - fs w • bv - gs w • (-bv) = w + (gs w - fs w) • bv
      module
  exact (hNT (s * t) (mul_mem_ggInduced hsN htN)) htrans

theorem GGIsReflection.commute_of_apply_eq (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {s t : MulAut ↥Bs} (hsN : s ∈ ggInduced ⊤ Bs)
    (htN : t ∈ ggInduced ⊤ Bs) (ht : GGIsReflection p t) {b : ↥Bs} (hb : b ≠ 1)
    (htb : t b = b⁻¹) (hsb : s b = b) : s * t = t * s := by
  have hs'inv : s⁻¹ b = b := by
    simpa only [hsb] using MulAut.inv_apply_self ↥Bs s b
  have hconjb : (s * t * s⁻¹) b = b⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, hs'inv, htb, map_inv, hsb]
  have hconjN : s * t * s⁻¹ ∈ ggInduced ⊤ Bs :=
    mul_mem_ggInduced (mul_mem_ggInduced hsN htN) (inv_mem_ggInduced hsN)
  have hconj : s * t * s⁻¹ = t :=
    GGIsReflection.eq_of_apply_eq_inv hp2 hBs hNT hconjN htN (ht.conj s) ht hb hconjb htb
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [hconj]

omit [Finite G] in
theorem mem_zpowers_of_apply_eq_of_mem_closure (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {t : MulAut ↥Bs} {x y z : ↥Bs} (htx : t x = x⁻¹) (hty : t y = y) (htz : t z = z)
    (hz : (z : G) ∈ Subgroup.closure ({(x : G), (y : G)} : Set G)) :
    (z : G) ∈ Subgroup.zpowers (y : G) := by
  let : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with
      mul_comm := fun a b => hBs.1.is_comm.comm a b }
  have hz' : z ∈ Subgroup.closure ({(x : ↥Bs), (y : ↥Bs)} : Set ↥Bs) := by
    have hmem : (z : G) ∈ (Subgroup.closure ({(x : ↥Bs), (y : ↥Bs)} : Set ↥Bs)).map
        (Subgroup.subtype Bs) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      exact hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmem
    rw [← Subtype.ext hwz]
    exact hw
  obtain ⟨m, n, hmn⟩ := Subgroup.mem_closure_pair.mp hz'
  have hxm : x ^ m = 1 := by
    have hxp : x ^ p = 1 := by
      apply Subtype.ext
      simpa using hBs.2 x x.2
    have hxm_p : (x ^ m) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    have hEq : x ^ (-m) * y ^ n = x ^ m * y ^ n := by
      calc x ^ (-m) * y ^ n = t (x ^ m) * t (y ^ n) := by
            simp only [map_zpow, htx, hty, inv_zpow']
        _ = t (x ^ m * y ^ n) := by rw [map_mul]
        _ = t z := by rw [hmn]
        _ = x ^ m * y ^ n := by rw [htz, hmn]
    have h2 : x ^ (-m) = x ^ m := mul_right_cancel hEq
    have hsq : x ^ m * x ^ m = 1 := by
      nth_rw 1 [← h2]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    exact pow_eq_one_of_sq_eq_one ((Fact.out : p.Prime).odd_of_ne_two hp2) hsq hxm_p
  have hzmem : z ∈ Subgroup.zpowers y := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨n, by rw [← hmn, hxm, one_mul]⟩
  have hmap : (z : G) ∈ (Subgroup.zpowers y).map (Subgroup.subtype Bs) := ⟨z, hzmem, rfl⟩
  rwa [MonoidHom.map_zpowers] at hmap

omit [Finite G] [Fact p.Prime] in
theorem apply_eq_of_mem_closure_pair {s : MulAut ↥Bs} {x y z : ↥Bs} (hsx : s x = x)
    (hsy : s y = y) (hz : (z : G) ∈ Subgroup.closure ({(x : G), (y : G)} : Set G)) :
    s z = z := by
  let F : Subgroup ↥Bs :=
    { carrier := {b : ↥Bs | s b = b}
      one_mem' := by
        show s 1 = 1
        exact map_one s
      mul_mem' := by
        intro a b ha hb
        show s (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        show s a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hz' : z ∈ Subgroup.closure ({(x : ↥Bs), (y : ↥Bs)} : Set ↥Bs) := by
    have hmem : (z : G) ∈ (Subgroup.closure ({(x : ↥Bs), (y : ↥Bs)} : Set ↥Bs)).map
        (Subgroup.subtype Bs) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      exact hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmem
    rw [← Subtype.ext hwz]
    exact hw
  have hle : Subgroup.closure ({(x : ↥Bs), (y : ↥Bs)} : Set ↥Bs) ≤ F := by
    rw [Subgroup.closure_le]
    rintro b (rfl | rfl)
    · exact hsx
    · exact hsy
  exact hle hz'

end CFSG.StandardType

end
