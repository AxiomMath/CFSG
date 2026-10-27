module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.GF2Type.Smith1979.W4AsSurvNine
public import CFSG.GroupTheory.InvertingInvolutionRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

private theorem w16g_isElemAbelianOfRank_of_card {p : ℕ} [Fact p.Prime] {V : Type*} [Group V]
    [Finite V] (hc : ∀ x y : V, x * y = y * x) (hp : ∀ x : V, x ^ p = 1) {n : ℕ}
    (hcard : Nat.card V = p ^ n) : IsElemAbelianOfRank p n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hzero : ∀ x : Additive V, p • x = 0 := by
    intro x
    have h1 : p • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ p) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at h1
    rw [h1, hp (Additive.toMul x), ofMul_one]
  let _ : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule (n := p) hzero
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) (Additive V)
  have hd : Module.finrank (ZMod p) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    have hcard' : Nat.card (Additive V) = p ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let e : Additive V ≃ₗ[ZMod p] (Fin n → ZMod p) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

private theorem w16g_conj_self_of_sq {G : Type*} [Group G] {t : G} (htt : t * t = 1) (y : G) :
    t * (t * y * t⁻¹) * t⁻¹ = y := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  calc t * (t * y * t⁻¹) * t⁻¹
      = (t * t) * y * (t⁻¹ * t⁻¹) := by group
    _ = y := by rw [htt, one_mul, show t⁻¹ * t⁻¹ = 1 by rw [htinv, htt], mul_one]

theorem w16h_inverts_of_abelian (h : Cfg132 t P) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at hpow
    exact hpow
  let Q : Subgroup (MulAut W) :=
    { carrier := {y | y ∈ P ∧ t * y * t⁻¹ = y⁻¹}
      one_mem' := by
        refine ⟨P.one_mem, ?_⟩
        simp
      mul_mem' := by
        rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
        refine ⟨P.mul_mem haP hbP, ?_⟩
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha, hb]
          _ = (a * b)⁻¹ := by
              rw [mul_inv_rev]
              exact hab a⁻¹ (P.inv_mem haP) b⁻¹ (P.inv_mem hbP)
      inv_mem' := by
        rintro a ⟨haP, ha⟩
        refine ⟨P.inv_mem haP, ?_⟩
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [ha] }
  have hle : P ≤ Q := by
    rw [← h.hc]
    rw [Subgroup.commutator_le]
    intro a haP b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have ht_norm : t ∈ Subgroup.normalizer P := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => h.hn y hy, fun hy => ?_⟩
      have hmem := h.hn (t * y * t⁻¹) hy
      rwa [w16g_conj_self_of_sq htt y] at hmem
    have hb_norm : b ∈ Subgroup.normalizer P := Subgroup.zpowers_le.mpr ht_norm hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hb_norm a⁻¹).mp (P.inv_mem haP)
    have hmemP : ⁅a, b⁆ ∈ P := by
      have heq : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact P.mul_mem haP hconj
    refine ⟨hmemP, ?_⟩
    rw [← hk]
    have h2pow : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, htt]
    have hpow_even : ∀ m : ℤ, t ^ (2 * m) = 1 := by
      intro m
      rw [zpow_mul, h2pow, one_zpow]
    have hpow_odd : ∀ m : ℤ, t ^ (2 * m + 1) = t := by
      intro m
      rw [zpow_add, hpow_even m, one_mul, zpow_one]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · rw [hm, hpow_even m, commutatorElement_def]
      simp
    · rw [hm, hpow_odd m, commutatorElement_def]
      calc t * (a * t * a⁻¹ * t⁻¹) * t⁻¹
          = t * a * t * a⁻¹ * (t⁻¹ * t⁻¹) := by group
        _ = t * a * t * a⁻¹ := by
            rw [show t⁻¹ * t⁻¹ = 1 by
              rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt, htt], mul_one]
        _ = (a * t * a⁻¹ * t⁻¹)⁻¹ := by
            rw [show (a * t * a⁻¹ * t⁻¹)⁻¹ = t * a * t⁻¹ * a⁻¹ by group]
            rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt]
  intro x hx
  exact (hle hx).2

theorem w16h_elemAbelian_of_exp_three (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ k : ℕ, k ≤ 3 ∧ IsElemAbelianOfRank 3 k ↥P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).mp h.hP
  have hE : IsElemAbelianOfRank 3 m ↥P :=
    w16g_isElemAbelianOfRank_of_card (p := 3)
      (fun x y : ↥P => Subtype.ext (hab x x.2 y y.2))
      (fun x : ↥P => Subtype.ext (hexp x x.2)) hm
  refine ⟨m, ?_, hE⟩
  have hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := w16h_inverts_of_abelian h hab
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · exfalso
      apply h.hne
      have hcard : Nat.card ↥P = 1 := by rw [hm, hm0, pow_zero]
      exact Subgroup.card_eq_one.mp hcard
    · exact hm0
  have hbound := n_mul_dihedralDeg_le_two_mul_rk h.hW h.ht (p := 3) (n := m)
    (by norm_num) (by norm_num) hm0 hE hinv
  have hd3 : dParam 3 = 2 := by
    rw [dParam]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hdd : dihedralDeg 3 = 2 := by
    rw [dihedralDeg, hd3]
    rw [if_pos (show Even 2 from ⟨1, by norm_num⟩)]
  rw [hdd] at hbound
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := h.hrk
  omega

private theorem w16g_inf_fixV_commSub_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W}
    (hx : Odd (orderOf x)) :
    commSub ⊤ (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
  have hx' : Odd (Nat.card (Subgroup.zpowers x)) := by rwa [Nat.card_zpowers]
  have h := (coprime_decomp (P := Subgroup.zpowers x) hx' hW
    (W := (⊤ : Subgroup W)) (fun g _ w _ => Subgroup.mem_top w)).2
  simpa using h

private theorem w16g_eq_one_of_fixed_commSub (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W}
    (hx : Odd (orderOf x)) {y : MulAut W}
    (hy1 : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), y u = u)
    (hy2 : ∀ u ∈ fixV (Subgroup.zpowers x), y u = u) : y = 1 := by
  have hx' : Odd (Nat.card (Subgroup.zpowers x)) := by rwa [Nat.card_zpowers]
  have hsup := (coprime_decomp (P := Subgroup.zpowers x) hx' hW
    (W := (⊤ : Subgroup W)) (fun g _ w _ => Subgroup.mem_top w)).1
  ext w
  have hw : w ∈ commSub ⊤ (Subgroup.zpowers x) ⊔ (⊤ ⊓ fixV (Subgroup.zpowers x)) := by
    rw [hsup]; trivial
  rw [Subgroup.mem_sup] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  calc y (a * b) = y a * y b := map_mul y a b
    _ = a * b := by rw [hy1 a ha, hy2 b hb.2]

private theorem w16g_zpow_apply_eq_self {G : Type*} [Group G] {σ : MulAut G} {y : G}
    (h : σ y = y) (k : ℤ) : (σ ^ k) y = y :=
  MulAction.mem_stabilizer_iff.mp
    (Subgroup.zpow_mem (MulAction.stabilizer (MulAut G) y)
      (MulAction.mem_stabilizer_iff.mpr h) k)

private theorem w16g_faithful_commSub (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W}
    (hx : Odd (orderOf x)) {k : ℤ}
    (hk : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), (x ^ k) u = u) : x ^ k = 1 := by
  refine w16g_eq_one_of_fixed_commSub hW hx hk ?_
  intro u hu
  exact w16g_zpow_apply_eq_self (mem_fixV.mp hu x (Subgroup.mem_zpowers x)) k

private theorem w16g_fixSub_eq_fixV {G : Type*} [CommGroup G] (c : MulAut G) :
    SimsE2.Dih.fixSub c = fixV (Subgroup.zpowers c) := by
  ext u
  rw [SimsE2.Dih.mem_fixSub, mem_fixV]
  exact ⟨fun h g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact w16g_zpow_apply_eq_self h k,
    fun h => h c (Subgroup.mem_zpowers c)⟩

private theorem w16g_stableUnder_commSub {H X : Subgroup (MulAut W)}
    (hn : ∀ h ∈ H, ∀ a ∈ X, h * a * h⁻¹ ∈ X) {M : Subgroup W} (hM : StableUnder H M) :
    StableUnder H (commSub M X) := by
  intro h hh u hu
  refine Subgroup.closure_induction (p := fun z _ => h z ∈ commSub M X) ?_ ?_ ?_ ?_ hu
  · rintro z ⟨a, ha, w, hw, rfl⟩
    refine Subgroup.subset_closure ⟨h * a * h⁻¹, hn h hh a ha, h w, hM h hh w hw, ?_⟩
    calc (h * a * h⁻¹) (h w) * (h w)⁻¹
        = h (a (h⁻¹ (h w))) * (h w)⁻¹ := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = h (a w) * (h w)⁻¹ := by rw [MulAut.inv_apply_self]
      _ = h (a w) * h (w⁻¹) := by rw [← map_inv]
      _ = h (a w * w⁻¹) := by rw [map_mul]
  · rw [map_one]; exact Subgroup.one_mem _
  · intro z z' _ _ hz hz'
    rw [map_mul]; exact Subgroup.mul_mem _ hz hz'
  · intro z _ hz
    rw [map_inv]; exact Subgroup.inv_mem _ hz

private theorem w16g_rk_commSub_le_six (h : Cfg132 t P) {x : MulAut W}
    (hinv : ∀ y ∈ Subgroup.zpowers x, t * y * t⁻¹ = y⁻¹) (hodd : Odd (orderOf x))
    (hfix : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u = u → u = 1) :
    rk ↥(commSub ⊤ (Subgroup.zpowers x)) ≤ 6 := by
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at hpow
    exact hpow
  have hxt : t * x * t⁻¹ = x⁻¹ := hinv x (Subgroup.mem_zpowers x)
  have hnorm : ∀ a ∈ Subgroup.zpowers x, t * a * t⁻¹ ∈ Subgroup.zpowers x :=
    CFSG.GroupTheory.normalizes_zpowers_of_conj_mem (by
      rw [hxt]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hnorm a ha, fun ha => by
      have h1 := hnorm (t * a * t⁻¹) ha
      rwa [w16g_conj_self_of_sq htt a] at h1⟩
  have hn : ∀ h' ∈ Subgroup.zpowers t, ∀ a ∈ Subgroup.zpowers x,
      h' * a * h'⁻¹ ∈ Subgroup.zpowers x := by
    intro h' hh' a ha
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr ht_norm hh') a).mp ha
  have hXnorm : ∀ h' ∈ Subgroup.zpowers x, ∀ a ∈ Subgroup.zpowers x,
      h' * a * h'⁻¹ ∈ Subgroup.zpowers x := by
    intro h' hh' a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have heq : x ^ m * x ^ n * (x ^ m)⁻¹ = x ^ n := by group
    rw [heq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
  have hUx : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u ∈ commSub ⊤ (Subgroup.zpowers x) :=
    w16g_stableUnder_commSub hXnorm (fun _ _ _ _ => Subgroup.mem_top _)
      x (Subgroup.mem_zpowers x)
  have hUt : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), t u ∈ commSub ⊤ (Subgroup.zpowers x) :=
    w16g_stableUnder_commSub hn (fun _ _ _ _ => Subgroup.mem_top _)
      t (Subgroup.mem_zpowers t)
  have hUt_stab : t ∈ stabSub (commSub ⊤ (Subgroup.zpowers x)) := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h1 : t (t u) ∈ commSub ⊤ (Subgroup.zpowers x) := hUt (t u) hu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h1,
      fun hu => hUt u hu⟩
  have hmain := CFSG.GroupTheory.rk_eq_two_mul_rk_fix_of_inverting h.hW htt hxt hodd hUx hUt hfix
  rw [w16g_fixSub_eq_fixV t] at hmain
  have hnull := rk_commSub_add_rk_inf_fixV (V := W) (g := t)
    (W := commSub ⊤ (Subgroup.zpowers x))
    (fun a ha u hu => (mem_stabSub.1 (Subgroup.zpowers_le.mpr hUt_stab ha) u).2 hu)
  have hle : rk ↥(commSub (commSub ⊤ (Subgroup.zpowers x)) (Subgroup.zpowers t)) ≤ 3 :=
    (rk_mono (commSub_mono le_top le_rfl)).trans h.hrk
  omega

private theorem w16g_six_le_rk_commSub (h : Cfg132 t P) {x : MulAut W} (hx9 : orderOf x = 9)
    (hfix : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u = u → u = 1) :
    6 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq h.hW
  let W₁ : Subgroup W := commSub ⊤ (Subgroup.zpowers x)
  have hUx : ∀ u ∈ W₁, x u ∈ W₁ :=
    w16g_stableUnder_commSub (H := Subgroup.zpowers x) (X := Subgroup.zpowers x)
      (fun h' hh' a ha => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have heq : x ^ m * x ^ n * (x ^ m)⁻¹ = x ^ n := by group
        rw [heq]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n)
      (fun _ _ _ _ => Subgroup.mem_top _) x (Subgroup.mem_zpowers x)
  have hUx_inv : ∀ u ∈ W₁, x⁻¹ u ∈ W₁ := by
    have hle : W₁.map x.toMonoidHom ≤ W₁ := by
      rintro _ ⟨u, hu, rfl⟩; exact hUx u hu
    have heq : W₁.map x.toMonoidHom = W₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective x.injective])
    intro u hu
    have hmem : u ∈ W₁.map x.toMonoidHom := by rw [heq]; exact hu
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hmem
    have hxw : x⁻¹ u = w := by
      rw [← hw']
      exact MulEquiv.symm_apply_apply x w
    rw [hxw]; exact hw
  let hX : Additive W ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective (CFSG.RankThree.FFModules.autRep W x) (by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have h1 : x a.toMul = x b.toMul := Additive.ofMul.injective hab
        exact Additive.toMul.injective (x.injective h1)
      · intro b
        exact ⟨Additive.ofMul (x.symm b.toMul), by
          rw [CFSG.RankThree.FFModules.autRep_apply]; simp⟩)
  have hmap : (w16g_toSub W₁).map (hX : Additive W →ₗ[ZMod 2] Additive W) = w16g_toSub W₁ := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u.toMul ∈ W₁ := by simpa using hu
      have hxu : (hX u).toMul ∈ W₁ := by
        change (CFSG.RankThree.FFModules.autRep W x u).toMul ∈ W₁
        rw [CFSG.RankThree.FFModules.autRep_apply]
        exact hUx u.toMul hu'
      simpa using hxu
    · intro v hv
      have hv' : v.toMul ∈ W₁ := by simpa using hv
      refine ⟨CFSG.RankThree.FFModules.autRep W x⁻¹ v, ?_, ?_⟩
      · have hxv : (CFSG.RankThree.FFModules.autRep W x⁻¹ v).toMul ∈ W₁ := by
          rw [CFSG.RankThree.FFModules.autRep_apply]
          exact hUx_inv v.toMul hv'
        simpa using hxv
      · change CFSG.RankThree.FFModules.autRep W x
          (CFSG.RankThree.FFModules.autRep W x⁻¹ v) = v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  let V : Submodule (ZMod 2) (Additive W) := w16g_toSub W₁
  let X : V ≃ₗ[ZMod 2] V := hX.ofSubmodules V V hmap
  have hXapply : ∀ v : V, ((X v : V) : Additive W) =
      (CFSG.RankThree.FFModules.autRep W x) v := by
    intro v
    rw [LinearEquiv.ofSubmodules_apply]
    change CFSG.RankThree.FFModules.autRep W x v =
      CFSG.RankThree.FFModules.autRep W x v
    rfl
  have hXpow : ∀ n : ℕ, ∀ v : V,
      ((X ^ n) v : Additive W) = ((CFSG.RankThree.FFModules.autRep W x) ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, Module.End.mul_apply, ih, hXapply]
  have harep : (CFSG.RankThree.FFModules.autRep W x) ^ 9 = 1 := by
    rw [← map_pow, show x ^ 9 = 1 by rw [← hx9]; exact pow_orderOf_eq_one x, map_one]
  have hX9 : X ^ 9 = 1 := by
    ext v
    rw [hXpow 9 v, harep, Module.End.one_apply]
    rfl
  have hX3 : X ^ 3 ≠ 1 := by
    intro h1
    have hx3one : x ^ 3 = 1 := by
      refine w16g_faithful_commSub h.hW (by rw [hx9]; norm_num) (k := 3) ?_
      intro u hu
      let v : V := ⟨Additive.ofMul u, by rw [w16g_mem_toSub]; exact hu⟩
      have h3 : (X ^ 3) v = v := by rw [h1]; rfl
      have h4 := hXpow 3 v
      rw [h3] at h4
      rw [show (CFSG.RankThree.FFModules.autRep W x) ^ 3 =
          CFSG.RankThree.FFModules.autRep W (x ^ 3) by rw [← map_pow]] at h4
      rw [CFSG.RankThree.FFModules.autRep_apply] at h4
      exact Additive.ofMul.injective h4.symm
    have hdvd : 9 ∣ 3 := by rw [← hx9]; exact orderOf_dvd_of_pow_eq_one hx3one
    exact absurd hdvd (by norm_num)
  have hord : orderOf X = 9 := orderOf_eq_prime_pow (p := 3) (n := 1) hX3 hX9
  have hsix := CFSG.GF2Type.Smith1979.W4As.Surv.six_le_finrank_of_orderOf_eq_nine (σ := X) hord
  change 6 ≤ Module.finrank (ZMod 2) (w16g_toSub W₁) at hsix
  rwa [← w16g_rk_eq_finrank h.hW W₁] at hsix

private theorem w16g_rk_commSub_eq_six (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) : rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6 := by
  have hodd : Odd (orderOf x) := by rw [hx9]; norm_num
  have hinv : ∀ y ∈ Subgroup.zpowers x, t * y * t⁻¹ = y⁻¹ := fun y hy =>
    w16h_inverts_of_abelian h hab y (Subgroup.zpowers_le.mpr hxP hy)
  have hfix : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u = u → u = 1 := by
    intro u hu hxu
    have hmem : u ∈ (commSub ⊤ (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) :
        Subgroup W) := Subgroup.mem_inf.mpr ⟨hu, (CFSG.Quasithin.mem_fixV).mpr (by
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact w16g_zpow_apply_eq_self hxu k)⟩
    rw [w16g_inf_fixV_commSub_eq_bot h.hW hodd] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hle := w16g_rk_commSub_le_six h hinv hodd hfix
  have hge := w16g_six_le_rk_commSub h hx9 hfix
  omega

private theorem w16g_commSub_commSub_zpowers_t_eq (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) :
    commSub (commSub ⊤ (Subgroup.zpowers x)) (Subgroup.zpowers t) =
      commSub ⊤ (Subgroup.zpowers t) := by
  have h6 := w16g_rk_commSub_eq_six h hab hxP hx9
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at hpow
    exact hpow
  have hxt : t * x * t⁻¹ = x⁻¹ :=
    w16h_inverts_of_abelian h hab x (Subgroup.zpowers_le.mpr hxP (Subgroup.mem_zpowers x))
  have hodd : Odd (orderOf x) := by rw [hx9]; norm_num
  have hinv : ∀ y ∈ Subgroup.zpowers x, t * y * t⁻¹ = y⁻¹ := fun y hy =>
    w16h_inverts_of_abelian h hab y (Subgroup.zpowers_le.mpr hxP hy)
  have hfix : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u = u → u = 1 := by
    intro u hu hxu
    have hmem : u ∈ (commSub ⊤ (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) :
        Subgroup W) := Subgroup.mem_inf.mpr ⟨hu, (CFSG.Quasithin.mem_fixV).mpr (by
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact w16g_zpow_apply_eq_self hxu k)⟩
    rw [w16g_inf_fixV_commSub_eq_bot h.hW hodd] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hnorm : ∀ a ∈ Subgroup.zpowers x, t * a * t⁻¹ ∈ Subgroup.zpowers x :=
    CFSG.GroupTheory.normalizes_zpowers_of_conj_mem (by
      rw [hxt]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hnorm a ha, fun ha => by
      have h1 := hnorm (t * a * t⁻¹) ha
      rwa [w16g_conj_self_of_sq htt a] at h1⟩
  have hn : ∀ h' ∈ Subgroup.zpowers t, ∀ a ∈ Subgroup.zpowers x,
      h' * a * h'⁻¹ ∈ Subgroup.zpowers x := by
    intro h' hh' a ha
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr ht_norm hh') a).mp ha
  have hUx : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), x u ∈ commSub ⊤ (Subgroup.zpowers x) :=
    w16g_stableUnder_commSub
      (H := Subgroup.zpowers x) (X := Subgroup.zpowers x)
      (fun h' hh' a ha => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have heq : x ^ m * x ^ n * (x ^ m)⁻¹ = x ^ n := by group
        rw [heq]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n)
      (fun _ _ _ _ => Subgroup.mem_top _) x (Subgroup.mem_zpowers x)
  have hUt : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), t u ∈ commSub ⊤ (Subgroup.zpowers x) :=
    w16g_stableUnder_commSub hn (fun _ _ _ _ => Subgroup.mem_top _) t (Subgroup.mem_zpowers t)
  have hUt_stab : t ∈ stabSub (commSub ⊤ (Subgroup.zpowers x)) := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h1 : t (t u) ∈ commSub ⊤ (Subgroup.zpowers x) := hUt (t u) hu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h1,
      fun hu => hUt u hu⟩
  have hmain := CFSG.GroupTheory.rk_eq_two_mul_rk_fix_of_inverting h.hW htt hxt hodd hUx hUt hfix
  rw [w16g_fixSub_eq_fixV t] at hmain
  have hnull := rk_commSub_add_rk_inf_fixV (V := W) (g := t)
    (W := commSub ⊤ (Subgroup.zpowers x))
    (fun a ha u hu => (mem_stabSub.1 (Subgroup.zpowers_le.mpr hUt_stab ha) u).2 hu)
  have hrk : rk ↥(commSub (commSub ⊤ (Subgroup.zpowers x)) (Subgroup.zpowers t)) = 3 := by
    omega
  have hrk_t : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := h.hrk
  refine Subgroup.eq_of_le_of_card_ge (commSub_mono le_top le_rfl) ?_
  rw [card_eq_two_pow h.hW, card_eq_two_pow h.hW]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem w16g_six_le_rk_of_x_stable (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W}
    (hx9 : orderOf x = 9) {U : Subgroup W} (hUx : ∀ u ∈ U, x u ∈ U) (hne : U ≠ ⊥)
    (hfix3 : ∀ u ∈ U, (x ^ 3) u = u → u = 1) : 6 ≤ rk U := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have hUx_inv : ∀ u ∈ U, x⁻¹ u ∈ U := by
    have hle : U.map x.toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩; exact hUx u hu
    have heq : U.map x.toMonoidHom = U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective x.injective])
    intro u hu
    have hmem : u ∈ U.map x.toMonoidHom := by rw [heq]; exact hu
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hmem
    have hxw : x⁻¹ u = w := by
      rw [← hw']
      exact MulEquiv.symm_apply_apply x w
    rw [hxw]; exact hw
  let hX : Additive W ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective (CFSG.RankThree.FFModules.autRep W x) (by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have h1 : x a.toMul = x b.toMul := Additive.ofMul.injective hab
        exact Additive.toMul.injective (x.injective h1)
      · intro b
        exact ⟨Additive.ofMul (x.symm b.toMul), by
          rw [CFSG.RankThree.FFModules.autRep_apply]; simp⟩)
  have hmap : (w16g_toSub U).map (hX : Additive W →ₗ[ZMod 2] Additive W) = w16g_toSub U := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u.toMul ∈ U := by simpa using hu
      have hxu : (hX u).toMul ∈ U := by
        change (CFSG.RankThree.FFModules.autRep W x u).toMul ∈ U
        rw [CFSG.RankThree.FFModules.autRep_apply]
        exact hUx u.toMul hu'
      simpa using hxu
    · intro v hv
      have hv' : v.toMul ∈ U := by simpa using hv
      refine ⟨CFSG.RankThree.FFModules.autRep W x⁻¹ v, ?_, ?_⟩
      · have hxv : (CFSG.RankThree.FFModules.autRep W x⁻¹ v).toMul ∈ U := by
          rw [CFSG.RankThree.FFModules.autRep_apply]
          exact hUx_inv v.toMul hv'
        simpa using hxv
      · change CFSG.RankThree.FFModules.autRep W x
          (CFSG.RankThree.FFModules.autRep W x⁻¹ v) = v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  let V : Submodule (ZMod 2) (Additive W) := w16g_toSub U
  let X : V ≃ₗ[ZMod 2] V := hX.ofSubmodules V V hmap
  have hXapply : ∀ v : V, ((X v : V) : Additive W) =
      (CFSG.RankThree.FFModules.autRep W x) v := by
    intro v
    rw [LinearEquiv.ofSubmodules_apply]
    change CFSG.RankThree.FFModules.autRep W x v =
      CFSG.RankThree.FFModules.autRep W x v
    rfl
  have hXpow : ∀ n : ℕ, ∀ v : V,
      ((X ^ n) v : Additive W) = ((CFSG.RankThree.FFModules.autRep W x) ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, Module.End.mul_apply, ih, hXapply]
  have harep : (CFSG.RankThree.FFModules.autRep W x) ^ 9 = 1 := by
    rw [← map_pow, show x ^ 9 = 1 by rw [← hx9]; exact pow_orderOf_eq_one x, map_one]
  have hX9 : X ^ 9 = 1 := by
    ext v
    rw [hXpow 9 v, harep, Module.End.one_apply]
    rfl
  have hX3 : X ^ 3 ≠ 1 := by
    intro h1
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    let v : V := ⟨Additive.ofMul u.1, by rw [w16g_mem_toSub]; exact u.2⟩
    have h3 : (X ^ 3) v = v := by rw [h1]; rfl
    have h4 := hXpow 3 v
    rw [h3] at h4
    rw [show (CFSG.RankThree.FFModules.autRep W x) ^ 3 =
        CFSG.RankThree.FFModules.autRep W (x ^ 3) by rw [← map_pow]] at h4
    rw [CFSG.RankThree.FFModules.autRep_apply] at h4
    exact hu1 (Subtype.ext (hfix3 u.1 u.2 (Additive.ofMul.injective h4.symm)))
  have hord : orderOf X = 9 := orderOf_eq_prime_pow (p := 3) (n := 1) hX3 hX9
  have hsix := CFSG.GF2Type.Smith1979.W4As.Surv.six_le_finrank_of_orderOf_eq_nine (σ := X) hord
  change 6 ≤ Module.finrank (ZMod 2) (w16g_toSub U) at hsix
  rwa [← w16g_rk_eq_finrank hW U] at hsix

private theorem w16g_irreducible_nine (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) :
    ∀ S : Subgroup W, (∀ u ∈ S, x u ∈ S) → S ≤ commSub ⊤ (Subgroup.zpowers x) → S ≠ ⊥ →
      S = commSub ⊤ (Subgroup.zpowers x) := by
  intro S hSx hSle hSne
  let W₁ : Subgroup W := commSub ⊤ (Subgroup.zpowers x)
  have h6 : rk W₁ = 6 := w16g_rk_commSub_eq_six h hab hxP hx9
  have hodd : Odd (orderOf x) := by rw [hx9]; norm_num
  have hfaithW : ∀ k : ℤ, (∀ u ∈ W₁, (x ^ k) u = u) → x ^ k = 1 :=
    fun k hk => w16g_faithful_commSub h.hW hodd hk
  have hW₁x : ∀ u ∈ W₁, x u ∈ W₁ :=
    w16g_stableUnder_commSub (H := Subgroup.zpowers x) (X := Subgroup.zpowers x)
      (fun h' hh' a ha => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have heq : x ^ m * x ^ n * (x ^ m)⁻¹ = x ^ n := by group
        rw [heq]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n)
      (fun _ _ _ _ => Subgroup.mem_top _) x (Subgroup.mem_zpowers x)
  have hW₁x3 : ∀ u ∈ W₁, (x ^ 3) u ∈ W₁ := fun u hu => by
    have h1 := hW₁x u hu
    have h2 := hW₁x (x u) h1
    have h3 := hW₁x (x (x u)) h2
    simpa [pow_succ, MulAut.mul_apply] using h3
  have hx3_stab : (x ^ 3) ∈ stabSub W₁ := by
    rw [mem_stabSub]
    intro u
    refine ⟨fun hu => ?_, fun hu => hW₁x3 u hu⟩
    have hx3cube : (x ^ 3) ^ 3 = 1 := by
      rw [← pow_mul, show 3 * 3 = 9 by norm_num, ← hx9]
      exact pow_orderOf_eq_one x
    have h1 : (x ^ 3) ((x ^ 3) u) ∈ W₁ := hW₁x3 ((x ^ 3) u) hu
    have h2 : (x ^ 3) ((x ^ 3) ((x ^ 3) u)) ∈ W₁ := hW₁x3 _ h1
    have heq : (x ^ 3) ((x ^ 3) ((x ^ 3) u)) = u := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_two, ← pow_succ, hx3cube,
        MulAut.one_apply]
    rwa [heq] at h2
  have hW₁x3' : ∀ g ∈ Subgroup.zpowers (x ^ 3), ∀ w ∈ W₁, g w ∈ W₁ :=
    fun g hg w hw => (mem_stabSub.1 (Subgroup.zpowers_le.mpr hx3_stab hg) w).2 hw
  have hx3ord : orderOf (x ^ 3) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : (x ^ 3) ^ 3 = 1 := by
      rw [← pow_mul, show 3 * 3 = 9 by norm_num, ← hx9]
      exact pow_orderOf_eq_one x
    refine orderOf_eq_prime h3 ?_
    intro h1
    have hdvd : 9 ∣ 3 := by rw [← hx9]; exact orderOf_dvd_of_pow_eq_one h1
    exact absurd hdvd (by norm_num)
  have hP3 : Odd (Nat.card (Subgroup.zpowers (x ^ 3))) := by
    rw [Nat.card_zpowers, hx3ord]; norm_num
  have hUx : ∀ u ∈ commSub W₁ (Subgroup.zpowers (x ^ 3)),
      x u ∈ commSub W₁ (Subgroup.zpowers (x ^ 3)) := by
    intro u hu
    refine Subgroup.closure_induction (p := fun z _ =>
        x z ∈ commSub W₁ (Subgroup.zpowers (x ^ 3))) ?_ ?_ ?_ ?_ hu
    · rintro z ⟨a, ha, w, hw, rfl⟩
      have hxa : x * a * x⁻¹ ∈ Subgroup.zpowers (x ^ 3) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [← hn, ← MulAut.conj_apply, map_zpow,
          show MulAut.conj x (x ^ 3) = x ^ 3 by rw [MulAut.conj_apply]; group]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ 3)) n
      refine Subgroup.subset_closure ⟨x * a * x⁻¹, hxa, x w, hW₁x w hw, ?_⟩
      calc (x * a * x⁻¹) (x w) * (x w)⁻¹
          = x (a (x⁻¹ (x w))) * (x w)⁻¹ := by rw [MulAut.mul_apply, MulAut.mul_apply]
        _ = x (a w) * (x w)⁻¹ := by rw [MulAut.inv_apply_self]
        _ = x (a w) * x (w⁻¹) := by rw [← map_inv]
        _ = x (a w * w⁻¹) := by rw [map_mul]
    · rw [map_one]; exact Subgroup.one_mem _
    · intro z z' _ _ hz hz'
      rw [map_mul]; exact Subgroup.mul_mem _ hz hz'
    · intro z _ hz
      rw [map_inv]; exact Subgroup.inv_mem _ hz
  have hcompl := (coprime_decomp (P := Subgroup.zpowers (x ^ 3)) hP3 h.hW (W := W₁) hW₁x3')
  have hfixU : ∀ u ∈ commSub W₁ (Subgroup.zpowers (x ^ 3)), (x ^ 3) u = u → u = 1 := by
    intro u hu hu3
    have hmem : u ∈ commSub W₁ (Subgroup.zpowers (x ^ 3)) ⊓
        (W₁ ⊓ fixV (Subgroup.zpowers (x ^ 3))) :=
      Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_inf.mpr ⟨commSub_le_of_invariant hW₁x3' hu,
        (CFSG.Quasithin.mem_fixV).mpr (by
          intro g hg
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
          exact w16g_zpow_apply_eq_self hu3 k)⟩⟩
    rw [hcompl.2] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hUne : commSub W₁ (Subgroup.zpowers (x ^ 3)) ≠ ⊥ := by
    intro hbot
    have hle : W₁ ≤ fixV (Subgroup.zpowers (x ^ 3)) := by
      rw [← hcompl.1, hbot, bot_sup_eq]
      exact inf_le_right
    have hx3one : x ^ 3 = 1 := by
      refine hfaithW 3 ?_
      intro u hu
      exact (CFSG.Quasithin.mem_fixV.mp (hle hu)) (x ^ 3) (Subgroup.mem_zpowers (x ^ 3))
    have hdvd : 9 ∣ 3 := by
      rw [← hx9]; exact orderOf_dvd_of_pow_eq_one hx3one
    exact absurd hdvd (by norm_num)
  have hU6 : 6 ≤ rk ↥(commSub W₁ (Subgroup.zpowers (x ^ 3))) :=
    w16g_six_le_rk_of_x_stable h.hW hx9 hUx hUne hfixU
  have hUeq : commSub W₁ (Subgroup.zpowers (x ^ 3)) = W₁ :=
    Subgroup.eq_of_le_of_card_ge (commSub_le_of_invariant hW₁x3') (by
      rw [card_eq_two_pow h.hW, card_eq_two_pow h.hW, h6]
      exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfix3W : ∀ u ∈ W₁, (x ^ 3) u = u → u = 1 := by
    intro u hu hu3
    have hmem : u ∈ W₁ ⊓ fixV (Subgroup.zpowers (x ^ 3)) :=
      Subgroup.mem_inf.mpr ⟨hu, (CFSG.Quasithin.mem_fixV).mpr (by
        intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact w16g_zpow_apply_eq_self hu3 k)⟩
    have hmem' : u ∈ (commSub W₁ (Subgroup.zpowers (x ^ 3)) ⊓
        (W₁ ⊓ fixV (Subgroup.zpowers (x ^ 3))) : Subgroup W) :=
      ⟨hUeq.symm ▸ hu, hmem⟩
    rw [hcompl.2] at hmem'
    exact Subgroup.mem_bot.mp hmem'
  have hfix3S : ∀ u ∈ S, (x ^ 3) u = u → u = 1 := fun u hu hu3 =>
    hfix3W u (hSle hu) hu3
  have hge : 6 ≤ rk S := w16g_six_le_rk_of_x_stable h.hW hx9 hSx hSne hfix3S
  exact Subgroup.eq_of_le_of_card_ge hSle (by
    rw [card_eq_two_pow h.hW, card_eq_two_pow h.hW, h6]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))

private theorem w16g_acts_as_power (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) :
    ∀ y ∈ P, ∃ i : ℕ, ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), y u = (x ^ i) u := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let W₁ : Subgroup W := commSub ⊤ (Subgroup.zpowers x)
  have hodd : Odd (orderOf x) := by rw [hx9]; norm_num
  have hW₁x : ∀ u ∈ W₁, x u ∈ W₁ :=
    w16g_stableUnder_commSub (H := Subgroup.zpowers x) (X := Subgroup.zpowers x)
      (fun h' hh' a ha => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have heq : x ^ m * x ^ n * (x ^ m)⁻¹ = x ^ n := by group
        rw [heq]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n)
      (fun _ _ _ _ => Subgroup.mem_top _) x (Subgroup.mem_zpowers x)
  have hW₁x_inv : ∀ u ∈ W₁, x⁻¹ u ∈ W₁ := by
    have hle : W₁.map x.toMonoidHom ≤ W₁ := by
      rintro _ ⟨u, hu, rfl⟩; exact hW₁x u hu
    have heq : W₁.map x.toMonoidHom = W₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective x.injective])
    intro u hu
    have hmem : u ∈ W₁.map x.toMonoidHom := by rw [heq]; exact hu
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hmem
    have hxw : x⁻¹ u = w := by rw [← hw']; exact MulEquiv.symm_apply_apply x w
    rw [hxw]; exact hw
  have hPstab : P ≤ stabSub W₁ := by
    have hstable : StableUnder P W₁ :=
      w16g_stableUnder_commSub (H := P) (X := Subgroup.zpowers x)
        (fun h' hh' a ha => by
          have haP : a ∈ P := Subgroup.zpowers_le.mpr hxP ha
          have hcomm : h' * a = a * h' := hab h' hh' a haP
          have heq : h' * a * h'⁻¹ = a := by rw [hcomm]; group
          rw [heq]; exact ha)
        (fun _ _ _ _ => Subgroup.mem_top _)
    intro g hg
    rw [mem_stabSub]
    intro u
    refine ⟨fun hu => ?_, fun hu => hstable g hg u hu⟩
    have h2 := hstable g⁻¹ (P.inv_mem hg) (g u) hu
    rwa [show g⁻¹ (g u) = u from MulEquiv.symm_apply_apply g u] at h2
  have hx_stab : x ∈ stabSub W₁ := hPstab hxP
  let xbar : MulAut W₁ := resHom W₁ ⟨x, hx_stab⟩
  have hxbar_mem : xbar ∈ autSub P W₁ :=
    mem_autSub.mpr ⟨⟨x, hx_stab⟩, hxP, rfl⟩
  have hxbar9 : xbar ^ 9 = 1 := by
    change (resHom W₁ ⟨x, hx_stab⟩) ^ 9 = 1
    rw [← map_pow]
    have h1 : (⟨x, hx_stab⟩ : stabSub W₁) ^ 9 = 1 := by
      apply Subtype.ext
      simp [show x ^ 9 = 1 by rw [← hx9]; exact pow_orderOf_eq_one x]
    rw [h1, map_one]
  have hxbar3 : xbar ^ 3 ≠ 1 := by
    intro h3
    have hx3one : x ^ 3 = 1 := by
      refine w16g_faithful_commSub h.hW hodd (k := 3) ?_
      intro u hu
      have h2 : ((xbar ^ 3) ⟨u, hu⟩ : W) = (x ^ 3) u := by
        change (((resHom W₁ ⟨x, hx_stab⟩) ^ 3) ⟨u, hu⟩ : W) = (x ^ 3) u
        rw [← map_pow, resHom_apply]
        rfl
      have h1 : ((xbar ^ 3) ⟨u, hu⟩ : W) = ((⟨u, hu⟩ : W₁) : W) := by rw [h3]; rfl
      rw [h2] at h1; exact h1
    have hdvd : 9 ∣ 3 := by rw [← hx9]; exact orderOf_dvd_of_pow_eq_one hx3one
    exact absurd hdvd (by norm_num)
  have hxbar_ord : orderOf xbar = 9 :=
    orderOf_eq_prime_pow (p := 3) (n := 1) hxbar3 hxbar9
  have hfree : ∀ g ∈ autSub P W₁, g ≠ 1 → ∀ v : W₁, g v = v → v = 1 := by
    intro g hg hgne v hv
    obtain ⟨h₀, hhP, hgh⟩ := mem_autSub.mp hg
    have hxS : ∀ u ∈ W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)),
        x u ∈ W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) := by
      intro u hu
      obtain ⟨huW₁, hufix⟩ := Subgroup.mem_inf.mp hu
      refine Subgroup.mem_inf.mpr ⟨hW₁x u huW₁, ?_⟩
      rw [mem_fixV] at hufix ⊢
      intro g' hg'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
      have hhu : (h₀ : MulAut W) u = u :=
        hufix (h₀ : MulAut W) (Subgroup.mem_zpowers (h₀ : MulAut W))
      have hcomm : (h₀ : MulAut W) * x = x * (h₀ : MulAut W) :=
        hab (h₀ : MulAut W) hhP x hxP
      have hxh : (h₀ : MulAut W) (x u) = x u := by
        rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hhu]
      exact w16g_zpow_apply_eq_self hxh k
    have hS : W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) = ⊥ := by
      by_contra hSne
      have heq : W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) = W₁ :=
        w16g_irreducible_nine h hab hxP hx9 _ hxS inf_le_left hSne
      have hg1 : g = 1 := by
        ext u
        rw [← hgh, resHom_apply, MulAut.one_apply]
        have hfix : (u : W) ∈ fixV (Subgroup.zpowers (h₀ : MulAut W)) := by
          have hmem : (u : W) ∈ W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) := by
            rw [heq]; exact u.2
          exact (Subgroup.mem_inf.mp hmem).2
        exact (mem_fixV.mp hfix) (h₀ : MulAut W) (Subgroup.mem_zpowers (h₀ : MulAut W))
      exact hgne hg1
    have hvW : (h₀ : MulAut W) (v : W) = (v : W) := by
      have h1 := congrArg (fun w : W₁ => (w : W)) hv
      rw [← hgh, resHom_apply] at h1
      exact h1
    have hvfix : (v : W) ∈ W₁ ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) := by
      refine Subgroup.mem_inf.mpr ⟨v.2, ?_⟩
      rw [mem_fixV]
      intro g' hg'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
      exact w16g_zpow_apply_eq_self hvW k
    rw [hS] at hvfix
    exact Subtype.ext (Subgroup.mem_bot.mp hvfix)
  have hW₁card : Nat.card W₁ = 2 ^ 6 := by
    rw [card_eq_two_pow h.hW W₁, w16g_rk_commSub_eq_six h hab hxP hx9]
  have hsncard : Nat.card ({v : W₁ | v ≠ 1} : Set W₁) = 63 := by
    rw [Nat.card_coe_set_eq]
    have h1 := Set.ncard_add_ncard_compl ({1} : Set W₁)
    rw [Set.ncard_singleton] at h1
    have h2 : ({1} : Set W₁)ᶜ = {v : W₁ | v ≠ 1} := by ext v; simp
    rw [h2] at h1
    rw [show Nat.card W₁ = 64 by rw [hW₁card]; norm_num] at h1
    omega
  have hcard63 : Nat.card (autSub P W₁) ∣ 63 := by
    have hdvd := card_dvd_card_of_free (V := W₁) (G := autSub P W₁)
      (Ω := {v : W₁ | v ≠ 1})
      (fun g hg a ha => by
        have h1 : g a ≠ 1 := by
          intro h0
          exact ha ((g : MulAut W₁).injective (by rw [h0, map_one]))
        exact h1)
      (fun g hg a ha hga => by
        by_contra hgne
        exact ha (hfree g hg hgne a hga))
    rwa [hsncard] at hdvd
  have hcardP : Nat.card (autSub P W₁) ∣ Nat.card P := by
    have h := card_autSub_mul (A := P) (U := W₁) hPstab
    exact ⟨_, h.symm⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).mp h.hP
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hm ▸ hcardP)
  have h9dvd : 9 ∣ Nat.card (autSub P W₁) := by
    have h := Subgroup.orderOf_dvd_natCard (autSub P W₁) hxbar_mem
    rwa [hxbar_ord] at h
  have hk2 : k = 2 := by
    have hk_ge : 2 ≤ k := by
      by_contra hc
      have h1 : k ≤ 1 := by omega
      have hle : Nat.card (autSub P W₁) ≤ 3 := by
        rw [hk]; exact Nat.pow_le_pow_right (by norm_num) h1
      have h9le : 9 ≤ Nat.card (autSub P W₁) :=
        Nat.le_of_dvd (by rw [hk]; positivity) h9dvd
      omega
    have hk_le2 : k ≤ 2 := by
      by_contra hc
      have h3 : 3 ≤ k := by omega
      have h27 : 27 ∣ Nat.card (autSub P W₁) := by rw [hk]; exact pow_dvd_pow 3 h3
      exact absurd (h27.trans hcard63) (by norm_num)
    omega
  have hRcard : Nat.card (autSub P W₁) = 9 := by rw [hk, hk2]; norm_num
  have hReq : Subgroup.zpowers xbar = autSub P W₁ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxbar_mem) (by
      rw [Nat.card_zpowers, hxbar_ord, hRcard])
  intro y hyP
  have hy_stab : y ∈ stabSub W₁ := hPstab hyP
  let ybar : MulAut W₁ := resHom W₁ ⟨y, hy_stab⟩
  have hybar_mem : ybar ∈ autSub P W₁ :=
    mem_autSub.mpr ⟨⟨y, hy_stab⟩, hyP, rfl⟩
  have hybar_zp : ybar ∈ Subgroup.zpowers xbar := hReq ▸ hybar_mem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hybar_zp
  have hmod : xbar ^ ((n % 9).toNat) = ybar := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num : (9 : ℤ) ≠ 0)),
      show (9 : ℤ) = (orderOf xbar : ℤ) by exact_mod_cast hxbar_ord.symm,
      zpow_mod_orderOf, hn]
  refine ⟨(n % 9).toNat, ?_⟩
  intro u hu
  have h := congrArg (fun f : MulAut W₁ => ((f ⟨u, hu⟩ : W₁) : W)) hmod
  have hx : ((xbar ^ ((n % 9).toNat)) ⟨u, hu⟩ : W) = (x ^ ((n % 9).toNat)) u := by
    change (((resHom W₁ ⟨x, hx_stab⟩) ^ ((n % 9).toNat)) ⟨u, hu⟩ : W) =
      (x ^ ((n % 9).toNat)) u
    rw [← map_pow, resHom_apply]
    rfl
  have hy : ((ybar ⟨u, hu⟩ : W₁) : W) = y u := by
    change (((resHom W₁ ⟨y, hy_stab⟩) ⟨u, hu⟩ : W₁) : W) = y u
    rw [resHom_apply]
  rw [hx, hy] at h
  exact h.symm

private theorem w16g_kernel_trivial (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) :
    ∀ c ∈ P, (∀ u ∈ commSub ⊤ (Subgroup.zpowers x), c u = u) → c = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).mp h.hP
  intro c hcP hctriv
  let W₁ : Subgroup W := commSub ⊤ (Subgroup.zpowers x)
  have hodd : Odd (orderOf x) := by rw [hx9]; norm_num
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at hpow
    exact hpow
  have hxt : t * x * t⁻¹ = x⁻¹ := w16h_inverts_of_abelian h hab x hxP
  have hnorm : ∀ a ∈ Subgroup.zpowers x, t * a * t⁻¹ ∈ Subgroup.zpowers x :=
    CFSG.GroupTheory.normalizes_zpowers_of_conj_mem (by
      rw [hxt]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hnorm a ha, fun ha => by
      have h1 := hnorm (t * a * t⁻¹) ha
      rwa [w16g_conj_self_of_sq htt a] at h1⟩
  have hn : ∀ h' ∈ Subgroup.zpowers t, ∀ a ∈ Subgroup.zpowers x,
      h' * a * h'⁻¹ ∈ Subgroup.zpowers x := by
    intro h' hh' a ha
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr ht_norm hh') a).mp ha
  have hW₁t_stable : StableUnder (Subgroup.zpowers t) W₁ :=
    w16g_stableUnder_commSub (H := Subgroup.zpowers t) (X := Subgroup.zpowers x) hn
      (fun _ _ _ _ => Subgroup.mem_top _)
  have hcomm_le : commSub ⊤ (Subgroup.zpowers t) ≤ W₁ := by
    rw [← w16g_commSub_commSub_zpowers_t_eq h hab hxP hx9]
    exact commSub_le_of_invariant hW₁t_stable
  have htW₁ : ∀ w : W, t w * w⁻¹ ∈ W₁ := fun w =>
    hcomm_le (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, Subgroup.mem_top w, rfl⟩)
  have hdec : commSub ⊤ (Subgroup.zpowers x) ⊔ (⊤ ⊓ fixV (Subgroup.zpowers x)) = ⊤ :=
    (coprime_decomp (P := Subgroup.zpowers x) (by rwa [Nat.card_zpowers]) h.hW
      (W := (⊤ : Subgroup W)) (fun g _ w _ => Subgroup.mem_top w)).1
  have hbot : W₁ ⊓ fixV (Subgroup.zpowers x) = ⊥ :=
    w16g_inf_fixV_commSub_eq_bot h.hW hodd
  have htfix : ∀ u ∈ fixV (Subgroup.zpowers x), t u = u := by
    intro u hu
    have h1 : t u * u⁻¹ ∈ W₁ := htW₁ u
    have h2 : t u * u⁻¹ ∈ fixV (Subgroup.zpowers x) := by
      rw [mem_fixV]
      intro g' hg'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
      have hxt' : x * t = t * x⁻¹ := by
        have h1 : x * t⁻¹ = t⁻¹ * x⁻¹ := by
          calc x * t⁻¹ = t⁻¹ * (t * x * t⁻¹) := by group
            _ = t⁻¹ * x⁻¹ := by rw [hxt]
        rwa [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt] at h1
      have htu : x (t u) = t u := by
        rw [← MulAut.mul_apply, hxt', MulAut.mul_apply]
        rw [(mem_fixV.mp hu) x⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))]
      have htu' : x (u⁻¹) = u⁻¹ := by
        rw [map_inv, (mem_fixV.mp hu) x (Subgroup.mem_zpowers x)]
      have hbase : x (t u * u⁻¹) = t u * u⁻¹ := by rw [map_mul, htu, htu']
      exact w16g_zpow_apply_eq_self hbase k
    have h3 : t u * u⁻¹ ∈ W₁ ⊓ fixV (Subgroup.zpowers x) := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hbot] at h3
    exact (mul_inv_eq_one).mp (Subgroup.mem_bot.mp h3)
  have hc_fix : ∀ u ∈ fixV (Subgroup.zpowers x), c u ∈ fixV (Subgroup.zpowers x) := by
    intro u hu
    rw [mem_fixV]
    intro g' hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    have hxcu : x (c u) = c u := by
      have hxc : x * c = c * x := hab x hxP c hcP
      rw [← MulAut.mul_apply, hxc, MulAut.mul_apply,
        (mem_fixV.mp hu) x (Subgroup.mem_zpowers x)]
    exact w16g_zpow_apply_eq_self hxcu k
  have hcinv : t * c * t⁻¹ = c⁻¹ := w16h_inverts_of_abelian h hab c hcP
  have hc2fix : ∀ u ∈ fixV (Subgroup.zpowers x), (c ^ 2) u = u := by
    intro u hu
    have hu_inv : t⁻¹ u = u := by
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right htt, htfix u hu]
    have h1 : c⁻¹ u = c u := by
      calc c⁻¹ u = (t * c * t⁻¹) u := by rw [hcinv]
        _ = t (c (t⁻¹ u)) := rfl
        _ = t (c u) := by rw [hu_inv]
        _ = c u := htfix (c u) (hc_fix u hu)
    have h2 : c (c u) = u := by
      rw [h1.symm]
      exact MulEquiv.apply_symm_apply c u
    rwa [pow_two, MulAut.mul_apply]
  have hc2W₁ : ∀ u ∈ W₁, (c ^ 2) u = u := by
    intro u hu
    rw [pow_two, MulAut.mul_apply, hctriv u hu, hctriv u hu]
  have hc2 : c ^ 2 = 1 := by
    ext w
    have hw : w ∈ commSub ⊤ (Subgroup.zpowers x) ⊔ (⊤ ⊓ fixV (Subgroup.zpowers x)) := by
      rw [hdec]; trivial
    rw [Subgroup.mem_sup] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁w₂⟩ := hw
    rw [← hw₁w₂, map_mul, hc2W₁ w₁ hw₁, hc2fix w₂ hw₂.2, MulAut.one_apply]
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
  have hord3 : orderOf c ∣ 3 ^ m := by
    rw [← hm]
    exact Subgroup.orderOf_dvd_natCard P hcP
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord3
  have hk0 : k = 0 := by
    by_contra hk0
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have h3dvd : 3 ∣ orderOf c := by rw [hk]; exact pow_dvd_pow 3 hk1
    exact absurd (h3dvd.trans hord2) (by norm_num)
  have hc1 : orderOf c = 1 := by rw [hk, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp hc1

theorem w16h_eq_zpowers_of_order_nine (h : Cfg132 t P)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x : MulAut W} (hxP : x ∈ P)
    (hx9 : orderOf x = 9) : P = Subgroup.zpowers x := by
  refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hxP)
  obtain ⟨i, hi⟩ := w16g_acts_as_power h hab hxP hx9 y hy
  have hcP : x ^ (-(i : ℤ)) * y ∈ P := P.mul_mem (P.zpow_mem hxP _) hy
  have hctriv : ∀ u ∈ commSub ⊤ (Subgroup.zpowers x), (x ^ (-(i : ℤ)) * y) u = u := by
    intro u hu
    rw [MulAut.mul_apply, hi u hu, ← zpow_natCast x i]
    rw [← MulAut.mul_apply, ← zpow_add, show -(i : ℤ) + (i : ℤ) = 0 by ring,
      zpow_zero, MulAut.one_apply]
  have hc1 : x ^ (-(i : ℤ)) * y = 1 :=
    w16g_kernel_trivial h hab hxP hx9 _ hcP hctriv
  have hy_eq : y = x ^ i := by
    have h1 := congrArg (fun z => x ^ i * z) hc1
    simp only [mul_one] at h1
    have h2 : x ^ i * (x ^ (-(i : ℤ)) * y) = (x ^ (i : ℤ) * x ^ (-(i : ℤ))) * y := by
      rw [← zpow_natCast x i]; group
    rw [h2] at h1
    rw [← zpow_add, show (i : ℤ) + (-(i : ℤ)) = 0 by ring, zpow_zero, one_mul] at h1
    exact h1
  rw [hy_eq, ← zpow_natCast x i]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) (i : ℤ)

theorem w16h_abelian (h : Cfg132 t P) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨ ∃ k : ℕ, k ≤ 3 ∧ IsElemAbelianOfRank 3 k ↥P := by
  by_cases h9 : ∃ x ∈ P, orderOf x = 9
  · obtain ⟨x, hxP, hx9⟩ := h9
    left
    have hPx : P = Subgroup.zpowers x := w16h_eq_zpowers_of_order_nine h hab hxP hx9
    refine ⟨?_, ?_⟩
    · rw [hPx]; infer_instance
    · rw [hPx, Nat.card_zpowers, hx9]
  · right
    have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
      intro x hx
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := h.hP.exists_orderOf_eq_pow ⟨x, hx⟩
      have hxord : orderOf x = 3 ^ k := by
        rw [← Subgroup.orderOf_mk x hx]; exact hk
      have hk1 : k ≤ 1 := by
        by_contra hk1
        push Not at hk1
        have hdvd : 9 ∣ orderOf x := by
          rw [hxord]
          exact pow_dvd_pow 3 hk1
        have hxne : orderOf x ≠ 0 := by rw [hxord]; exact pow_ne_zero k (by norm_num)
        have h9' : orderOf (x ^ (orderOf x / 9)) = 9 := orderOf_pow_orderOf_div hxne hdvd
        exact h9 ⟨x ^ (orderOf x / 9), P.pow_mem hx _, h9'⟩
      have hdvd : orderOf x ∣ 3 := by
        rw [hxord]
        exact pow_dvd_pow 3 hk1
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact w16h_elemAbelian_of_exp_three h hab hexp

end CFSG.LocalAnalysis.WeakClosure81
