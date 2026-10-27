module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore

public section

namespace CFSG.StandardType

theorem fixed_or_inverted_of_injective_framed_action
    {A M : Type*} [Group A] [Group M]
    (f : A →* M) (hf : Function.Injective f) (φ : MulAut A)
    (a : A) (m R : M) (hfa : f a = m)
    (hact : f (φ a) = R * m * R⁻¹)
    (hsign : R * m * R⁻¹ = m ∨ R * m * R⁻¹ = m⁻¹) :
    φ a = a ∨ φ a = a⁻¹ := by
  rcases hsign with h | h
  · exact Or.inl (hf (hact.trans (h.trans hfa.symm)))
  · have hinv : f a⁻¹ = m⁻¹ := (map_inv f a).trans (congrArg Inv.inv hfa)
    exact Or.inr (hf (hact.trans (h.trans hinv.symm)))

theorem fixed_iff_of_injective_common_fixed
    {X Y : Type*} [Finite X] (v : Y → X) (hv : Function.Injective v)
    (φ ψ : X → X) (hφv : ∀ y, φ (v y) = v y) (hψv : ∀ y, ψ (v y) = v y)
    (hφcard : Nat.card {x : X // φ x = x} ≤ Nat.card Y)
    (hψcard : Nat.card {x : X // ψ x = x} ≤ Nat.card Y) :
    ∀ x : X, φ x = x ↔ ψ x = x := by
  let vφ : Y → {x : X // φ x = x} := fun y => ⟨v y, hφv y⟩
  let vψ : Y → {x : X // ψ x = x} := fun y => ⟨v y, hψv y⟩
  have hiφ : Function.Injective vφ := fun y z h => hv (congrArg Subtype.val h)
  have hiψ : Function.Injective vψ := fun y z h => hv (congrArg Subtype.val h)
  have hsφ := (hiφ.bijective_of_nat_card_le hφcard).2
  have hsψ := (hiψ.bijective_of_nat_card_le hψcard).2
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hsφ ⟨x, hx⟩
    have hvx : v y = x := congrArg Subtype.val hy
    exact hvx ▸ hψv y
  · intro hx
    obtain ⟨y, hy⟩ := hsψ ⟨x, hx⟩
    have hvx : v y = x := congrArg Subtype.val hy
    exact hvx ▸ hφv y

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggGamma_conjAut_eq_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {g : G} (hgX : g ∈ X) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (ht2 : ggConjAut Bs hgN ^ 2 = 1) (b : ↥Bs) :
    ggGamma X hN (ggConjAut Bs hgN b) = ggGamma X hN b ↔ ggConjAut Bs hgN b = b := by
  classical
  set t := ggConjAut Bs hgN with ht
  have htt : ∀ b : ↥Bs, t (t b) = b := by
    intro b
    have := congrArg (fun φ : MulAut ↥Bs => φ b) ht2
    simpa [ht, pow_two, MulAut.mul_apply] using this
  constructor
  · intro hγ
    set u : ↥Bs := t b * b⁻¹ with hu
    have hu1 : ggGamma X hN u = 1 := by
      rw [hu, map_mul, map_inv, hγ, mul_inv_cancel]
    have huc : (u : G) ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hN u).mp hu1
    have hufix : t u = u := by
      apply Subtype.ext
      rw [ht, ggConjAut_apply, Subgroup.mem_centralizer_iff.mp huc g hgX, mul_inv_cancel_right]
    have htu : t u = u⁻¹ := by
      rw [hu, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
    have huu : u = u⁻¹ := hufix.symm.trans htu
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [huu]
      exact mul_inv_cancel u
    have hup : u ^ p = 1 := Subtype.ext (by simpa using hBs.2 (u : G) u.2)
    have hcop : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have hord : orderOf u = 1 := by
      have h2 := orderOf_dvd_of_pow_eq_one hu2
      have hp' := orderOf_dvd_of_pow_eq_one hup
      have h := Nat.dvd_gcd h2 hp'
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      exact Nat.dvd_one.mp h
    have hu1' : u = 1 := orderOf_eq_one_iff.mp hord
    exact mul_inv_eq_one.mp (by rw [← hu]; exact hu1')
  · intro h
    rw [h]

theorem not_forall_ggAutomizerGammaHom_fixed_iff_of_A2
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hNoTr : GGNoTransvection 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 2 → MulAut ↥Bs) (h : Fin 2 → V)
    (α : Fin 2 → Module.Dual (ZMod 3) V)
    (hform : ∀ i v, ggLin (p := 3) ι (r i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hrefl : ∀ i, GGIsReflection 3 (r i))
    (hmem : ∀ i, r i ∈ ggAutomizer J Bs) :
    ¬ (∀ a : ↥(ggGamma J hN).range,
        ((ggAutomizerGammaHom hN ⟨r 0, hmem 0⟩ :
            MulAut ↥(ggGamma J hN).range) a = a ↔
          (ggAutomizerGammaHom hN ⟨r 1, hmem 1⟩ :
            MulAut ↥(ggGamma J hN).range) a = a)) := by
  classical
  intro hsame
  have hex : ∀ i : Fin 2, ∃ (g : G) (hgJ : g ∈ J)
      (hgN : g ∈ Subgroup.normalizer (Bs : Set G)), r i = ggConjAut Bs hgN := by
    intro i
    obtain ⟨g, hgJ, hgN, hg⟩ := mem_ggAutomizer_iff.mp (hmem i)
    exact ⟨g, hgJ, hgN, MulEquiv.ext fun b => Subtype.ext (hg b)⟩
  choose g hgJ hgN hr using hex
  have hkey : ∀ (i : Fin 2) (b : ↥Bs),
      ggGamma J hN (r i b) = ggGamma J hN b ↔ r i b = b := by
    intro i b
    have ht2 : ggConjAut Bs (hgN i) ^ 2 = 1 := by
      rw [← hr i]
      exact (hrefl i).1
    rw [hr i]
    exact ggGamma_conjAut_eq_iff (p := 3) Nat.prime_three (by decide) hBs hN
      (hgJ i) (hgN i) ht2 b
  have hiff : ∀ (i : Fin 2) (b : ↥Bs),
      (ggAutomizerGammaHom hN ⟨r i, hmem i⟩ :
          MulAut ↥(ggGamma J hN).range) ((ggGamma J hN).rangeRestrict b) =
        (ggGamma J hN).rangeRestrict b ↔ r i b = b := by
    intro i b
    have hov := ggAutomizerGammaHom_overGamma hN ⟨r i, hmem i⟩ b
    constructor
    · intro hfix
      have hγ : ggGamma J hN (r i b) = ggGamma J hN b := by
        have h := congrArg Subtype.val (hov.trans hfix)
        simpa only [MonoidHom.coe_rangeRestrict] using h
      exact (hkey i b).mp hγ
    · intro hfix
      have hγ : ggGamma J hN (r i b) = ggGamma J hN b := (hkey i b).mpr hfix
      apply Subtype.ext
      rw [← hov]
      simpa only [MonoidHom.coe_rangeRestrict] using hγ
  have hsub : ∀ b : ↥Bs, r 0 b = b ↔ r 1 b = b := by
    intro b
    exact (hiff 0 b).symm.trans
      ((hsame ((ggGamma J hN).rangeRestrict b)).trans (hiff 1 b))
  have hα0h0 : α 0 (h 0) = 2 := by
    have hA : CartanMatrix.A 2 0 0 = 2 := by decide
    rw [hpair 0 0, hA]
    norm_num
  have hα1h0 : α 1 (h 0) = 2 := by
    have hA : CartanMatrix.A 2 1 0 = -1 := by decide
    rw [hpair 1 0, hA]
    show ((-1 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  have hα1h1 : α 1 (h 1) = 2 := by
    have hA : CartanMatrix.A 2 1 1 = 2 := by decide
    rw [hpair 1 1, hA]
    norm_num
  have h1ne : h 1 ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hα1h1
    exact (by decide : (2 : ZMod 3) ≠ 0) hα1h1.symm
  have hαeq : α 0 = α 1 := by
    ext v
    let w : V := v + (α 0 v) • h 0
    have hα0w : α 0 w = 0 := by
      have hexp : α 0 w = α 0 v + α 0 v * α 0 (h 0) := by
        simp [w, map_add, map_smul, smul_eq_mul]
      rw [hexp, hα0h0]
      calc α 0 v + α 0 v * 2 = α 0 v * 3 := by ring
        _ = 0 := by
          rw [show (3 : ZMod 3) = 0 by decide, mul_zero]
    have hfix0 : ggLin (p := 3) ι (r 0) w = w := by
      rw [hform 0 w, hα0w, zero_smul, sub_zero]
    have hgrp0 : r 0 (Additive.toMul (ι.symm w)) = Additive.toMul (ι.symm w) := by
      rw [ggLin_fix_iff (p := 3) ι (r 0)]
      simpa using hfix0
    have hgrp1 : r 1 (Additive.toMul (ι.symm w)) = Additive.toMul (ι.symm w) :=
      (hsub (Additive.toMul (ι.symm w))).mp hgrp0
    have hfix1 : ggLin (p := 3) ι (r 1) w = w := by
      simpa using
        (ggLin_fix_iff (p := 3) ι (r 1) (Additive.toMul (ι.symm w))).mp hgrp1
    have hα1w : α 1 w = 0 := by
      have hh := hform 1 w
      rw [hfix1] at hh
      have hz : α 1 w • h 1 = 0 := sub_eq_self.mp hh.symm
      exact (smul_eq_zero.mp hz).resolve_right h1ne
    have hexp1 : α 1 w = α 1 v + α 0 v * α 1 (h 0) := by
      simp [w, map_add, map_smul, smul_eq_mul]
    have hsub0 : α 1 v - α 0 v = 0 := by
      have h := hα1w
      rw [hexp1, hα1h0] at h
      calc α 1 v - α 0 v = α 1 v + α 0 v * 2 := by
            rw [show (2 : ZMod 3) = -1 by decide]
            ring
        _ = 0 := h
    exact (sub_eq_zero.mp hsub0).symm
  have hroots : LinearIndependent (ZMod 3) α :=
    linearIndependent_roots_of_lineJDatum_A2 ι hform hpair hind hmem hNoTr
  rw [linearIndependent_fin2] at hroots
  exact hroots.2 1 (by rw [one_smul, ← hαeq])

theorem A2_mul_pow_three_eq_one
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 2 → MulAut ↥Bs) (h : Fin 2 → V)
    (α : Fin 2 → Module.Dual (ZMod 3) V)
    (hform : ∀ i v, ggLin (p := 3) ι (r i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3)) :
    (r 0 * r 1) ^ 3 = 1 := by
  have hα0h0 : α 0 (h 0) = 2 := by
    have hA : CartanMatrix.A 2 0 0 = 2 := by decide
    rw [hpair 0 0, hA]
    norm_num
  have hα1h1 : α 1 (h 1) = 2 := by
    have hA : CartanMatrix.A 2 1 1 = 2 := by decide
    rw [hpair 1 1, hA]
    norm_num
  have hα0h1 : α 0 (h 1) = -1 := by
    have hA : CartanMatrix.A 2 0 1 = -1 := by decide
    rw [hpair 0 1, hA]
    norm_num
  have hα1h0 : α 1 (h 0) = -1 := by
    have hA : CartanMatrix.A 2 1 0 = -1 := by decide
    rw [hpair 1 0, hA]
    norm_num
  have hcross : α 0 (h 1) * α 1 (h 0) = 1 := by
    rw [hα0h1, hα1h0]
    norm_num
  have h0 : ggLin (p := 3) ι (r 0) = Module.reflection hα0h0 := by
    ext v
    rw [show ggLin (p := 3) ι (r 0) v = v - α 0 v • h 0 from hform 0 v,
      Module.reflection_apply (y := v) (h := hα0h0)]
  have h1 : ggLin (p := 3) ι (r 1) = Module.reflection hα1h1 := by
    ext v
    rw [show ggLin (p := 3) ι (r 1) v = v - α 1 v • h 1 from hform 1 v,
      Module.reflection_apply (y := v) (h := hα1h1)]
  have hlin : (ggLin (p := 3) ι (r 0) * ggLin (p := 3) ι (r 1)) ^ 3 = 1 := by
    rw [h0, h1]
    exact reflection_mul_reflection_pow_three hα0h0 hα1h1 hcross
  refine ggLin_injective (p := 3) ι ?_
  simpa [map_pow, map_mul] using hlin

theorem A2_image_mul_pow_three_eq_one
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 2 → MulAut ↥Bs) (h : Fin 2 → V)
    (α : Fin 2 → Module.Dual (ZMod 3) V)
    (hform : ∀ i v, ggLin (p := 3) ι (r i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3))
    (hmem : ∀ i, r i ∈ ggAutomizer J Bs) :
    ((ggAutomizerGammaHom hN ⟨r 0, hmem 0⟩ : MulAut ↥(ggGamma J hN).range) *
      (ggAutomizerGammaHom hN ⟨r 1, hmem 1⟩ : MulAut ↥(ggGamma J hN).range)) ^ 3 = 1 := by
  have hcube : (r 0 * r 1) ^ 3 = 1 := A2_mul_pow_three_eq_one ι r h α hform hpair
  have hsub : (⟨r 0, hmem 0⟩ * ⟨r 1, hmem 1⟩ : ggAutomizer J Bs) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hcube
  have hmap : ggAutomizerGammaHom hN
      ((⟨r 0, hmem 0⟩ * ⟨r 1, hmem 1⟩ : ggAutomizer J Bs) ^ 3) = 1 := by
    rw [hsub, map_one]
  have hφ : ((ggAutomizerGammaHom hN ⟨r 0, hmem 0⟩ *
      ggAutomizerGammaHom hN ⟨r 1, hmem 1⟩) ^ 3) = 1 := by
    rw [← map_mul, ← map_pow]
    exact hmap
  simpa using congrArg Subtype.val hφ

theorem no_mem_inverted_by_both_of_A2
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 2 → MulAut ↥Bs) (h : Fin 2 → V)
    (α : Fin 2 → Module.Dual (ZMod 3) V)
    (hform : ∀ i v, ggLin (p := 3) ι (r i) v = v - α i v • h i)
    (hind : LinearIndependent (ZMod 3) h) :
    ¬ ∃ b : ↥Bs, b ≠ 1 ∧ r 0 b = b⁻¹ ∧ r 1 b = b⁻¹ := by
  rintro ⟨b, hb1, hb0, hb1inv⟩
  let v : V := ι (Additive.ofMul b)
  have hvne : v ≠ 0 := by
    intro hv
    apply hb1
    have h0 : Additive.ofMul b = 0 := by
      have hsymm : ι.symm v = ι.symm (0 : V) := by rw [hv]
      simpa [v] using hsymm
    simpa using Additive.ofMul.injective h0
  have hscaled : ∀ (i : Fin 2), r i b = b⁻¹ → α i v • h i = (2 : ZMod 3) • v := by
    intro i hi
    have hlin : ggLin (p := 3) ι (r i) v = -v := by
      simpa [v] using (ggLin_inv_iff (p := 3) ι (r i) b).mp hi
    have hsub : v - α i v • h i = -v := by
      rw [← hform i v]
      exact hlin
    have hh : v = -v + α i v • h i := sub_eq_iff_eq_add.mp hsub
    calc α i v • h i = (-v + α i v • h i) + v := by abel
      _ = v + v := by rw [← hh]
      _ = (2 : ZMod 3) • v := by
          rw [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul]
  have hα0eq : α 0 v • h 0 = (2 : ZMod 3) • v := hscaled 0 hb0
  have hα1eq : α 1 v • h 1 = (2 : ZMod 3) • v := hscaled 1 hb1inv
  have hrel : α 0 v • h 0 = α 1 v • h 1 := by rw [hα0eq, hα1eq]
  have h2v : (2 : ZMod 3) • v ≠ 0 := by
    intro h2
    rcases (smul_eq_zero.mp h2) with h20 | hv0
    · exact (by decide : (2 : ZMod 3) ≠ 0) h20
    · exact hvne hv0
  have ha : α 0 v ≠ 0 := by
    intro ha0
    apply h2v
    calc (2 : ZMod 3) • v = α 0 v • h 0 := hα0eq.symm
      _ = 0 := by rw [ha0, zero_smul]
  have hbv : α 1 v ≠ 0 := by
    intro hb0
    apply h2v
    calc (2 : ZMod 3) • v = α 1 v • h 1 := hα1eq.symm
      _ = 0 := by rw [hb0, zero_smul]
  rw [linearIndependent_fin2] at hind
  have hprop : h 0 = ((α 0 v)⁻¹ * (α 1 v)) • h 1 := by
    calc h 0 = (α 0 v)⁻¹ • (α 0 v • h 0) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = (α 0 v)⁻¹ • (α 1 v • h 1) := by rw [hrel]
      _ = ((α 0 v)⁻¹ * (α 1 v)) • h 1 := by rw [smul_smul]
  exact hind.2 ((α 0 v)⁻¹ * (α 1 v)) hprop.symm

theorem same_sign_of_mulAut_cube
    {B : Type} [Group B] (ρ0 ρ1 : MulAut B) {a : B}
    (hρ : (ρ0 * ρ1) ^ 3 = 1) (ha3 : a ^ 3 = 1) (hane : a ≠ 1)
    (h0 : ρ0 a = a ∨ ρ0 a = a⁻¹) (h1 : ρ1 a = a ∨ ρ1 a = a⁻¹) :
    (ρ0 a = a ∧ ρ1 a = a) ∨ (ρ0 a = a⁻¹ ∧ ρ1 a = a⁻¹) := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact Or.inl ⟨h0, h1⟩
  · exfalso
    let c : MulAut B := ρ0 * ρ1
    have hc : c a = a⁻¹ := by
      dsimp [c]
      rw [h1, map_inv, h0]
    have hc2 : c (c a) = a := by rw [hc, map_inv, hc, inv_inv]
    have hc3' : c (c (c a)) = a⁻¹ := by rw [hc2, hc]
    have hc3 : c (c (c a)) = a := by
      have := congrArg (fun φ : MulAut B => φ a) hρ
      simpa [c, pow_succ, pow_two, MulAut.mul_apply] using this
    have haeq : a = a⁻¹ := hc3.symm.trans hc3'
    have ha2 : a * a = 1 := by
      nth_rewrite 2 [haeq]
      exact mul_inv_cancel a
    have ha3' : a ^ 3 = a := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, ha2, one_mul]
    exact hane (ha3'.symm.trans ha3)
  · exfalso
    let c : MulAut B := ρ0 * ρ1
    have hc : c a = a⁻¹ := by
      dsimp [c]
      rw [h1, h0]
    have hc2 : c (c a) = a := by rw [hc, map_inv, hc, inv_inv]
    have hc3' : c (c (c a)) = a⁻¹ := by rw [hc2, hc]
    have hc3 : c (c (c a)) = a := by
      have := congrArg (fun φ : MulAut B => φ a) hρ
      simpa [c, pow_succ, pow_two, MulAut.mul_apply] using this
    have haeq : a = a⁻¹ := hc3.symm.trans hc3'
    have ha2 : a * a = 1 := by
      nth_rewrite 2 [haeq]
      exact mul_inv_cancel a
    have ha3' : a ^ 3 = a := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, ha2, one_mul]
    exact hane (ha3'.symm.trans ha3)
  · exact Or.inr ⟨h0, h1⟩

namespace GGResLineJDatum

theorem A2_exists_image_fixed_ne
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hNoTr : GGNoTransvection 3 Bs)
    (hD : GGResLineJDatum 3 Bs J .A2) :
    ∃ (r : Fin 2 → MulAut ↥Bs) (hmem : ∀ i, r i ∈ ggAutomizer J Bs),
      (∀ i, GGIsReflection 3 (r i)) ∧
      ¬ (∀ a : ↥(ggGamma J hN).range,
          ((ggAutomizerGammaHom hN ⟨r 0, hmem 0⟩ :
              MulAut ↥(ggGamma J hN).range) a = a ↔
            (ggAutomizerGammaHom hN ⟨r 1, hmem 1⟩ :
              MulAut ↥(ggGamma J hN).range) a = a)) := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hmem : ∀ i : Fin 2, r i ∈ ggAutomizer J Bs := by
    intro i
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hpairA : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3) := by
    intro i j
    simpa [GGResLineJType.cartan] using hpair i j
  exact ⟨r, hmem, hrefl,
    not_forall_ggAutomizerGammaHom_fixed_iff_of_A2 hBs hN hNoTr ι r h α
      hform hpairA hind hrefl hmem⟩

theorem A2_exists_cube_and_no_both_inverted
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hD : GGResLineJDatum 3 Bs J .A2) :
    ∃ r : Fin 2 → MulAut ↥Bs,
      (r 0 * r 1) ^ 3 = 1 ∧
      ¬ ∃ b : ↥Bs, b ≠ 1 ∧ r 0 b = b⁻¹ ∧ r 1 b = b⁻¹ := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, _hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hpairA : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3) := by
    intro i j
    simpa [GGResLineJType.cartan] using hpair i j
  exact ⟨r, A2_mul_pow_three_eq_one ι r h α hform hpairA,
    no_mem_inverted_by_both_of_A2 ι r h α hform hind⟩

theorem A2_exists_pair_obstructions
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hNoTr : GGNoTransvection 3 Bs) (hD : GGResLineJDatum 3 Bs J .A2) :
    ∃ (r : Fin 2 → MulAut ↥Bs) (hmem : ∀ i, r i ∈ ggAutomizer J Bs),
      (∀ i, GGIsReflection 3 (r i)) ∧ (r 0 * r 1) ^ 3 = 1 ∧
      (¬ ∃ b : ↥Bs, b ≠ 1 ∧ r 0 b = b⁻¹ ∧ r 1 b = b⁻¹) ∧
      ¬ (∀ a : ↥(ggGamma J hN).range,
        (ggAutomizerGammaHom hN ⟨r 0, hmem 0⟩ : MulAut ↥(ggGamma J hN).range) a = a ↔
        (ggAutomizerGammaHom hN ⟨r 1, hmem 1⟩ : MulAut ↥(ggGamma J hN).range) a = a) := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hmem : ∀ i : Fin 2, r i ∈ ggAutomizer J Bs := by
    intro i
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hpairA : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3) := by
    intro i j
    simpa [GGResLineJType.cartan] using hpair i j
  exact ⟨r, hmem, hrefl, A2_mul_pow_three_eq_one ι r h α hform hpairA,
    no_mem_inverted_by_both_of_A2 ι r h α hform hind,
    not_forall_ggAutomizerGammaHom_fixed_iff_of_A2 hBs hN hNoTr ι r h α
      hform hpairA hind hrefl hmem⟩

end GGResLineJDatum

end CFSG.StandardType

end
