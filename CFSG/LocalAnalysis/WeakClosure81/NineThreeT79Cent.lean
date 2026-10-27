module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreOdd
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private lemma nine3_cent_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

private lemma nine3_cent_zmodRefl_mul_refl (c c' : ZMod p) :
    zmodRefl p c * zmodRefl p c' = Equiv.addRight (2 * (c - c')) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.coe_addRight]
  ring

private lemma nine3_cent_addRight_pow (d : ZMod p) : ∀ (n : ℕ) (i : ZMod p),
    ((Equiv.addRight d) ^ n) i = i + (n : ZMod p) * d := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [pow_succ, Equiv.Perm.mul_apply, ih ((Equiv.addRight d) i),
        Equiv.coe_addRight, Nat.cast_succ]
      ring

private theorem nine3_cent_sylow_conj [Fact p.Prime] {P Q R : Subgroup G}
    (hP : IsSylowIn p P R) (hQ : IsSylowIn p Q R) :
    ∃ r ∈ R, A1b.conjSub r P = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R hP.toSylow hQ.toSylow
  refine ⟨g, g.2, ?_⟩
  have h1 : (P.subgroupOf R).map (MulAut.conj g).toMonoidHom = Q.subgroupOf R := by
    have h2 : MulAut.conj g • (hP.toSylow : Subgroup R) = (hQ.toSylow : Subgroup R) := by
      rw [← Sylow.coe_subgroup_smul, hg]
    rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow] at h2
    exact h2
  have hmain : A1b.conjSub (g : G) P = Q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyR : y ∈ R := hP.1 hy
      have hmem : (MulAut.conj g) (⟨y, hyR⟩ : R) ∈ Q.subgroupOf R :=
        h1 ▸ Subgroup.mem_map_of_mem _ (show (⟨y, hyR⟩ : R) ∈ P.subgroupOf R from hy)
      exact hmem
    · intro hx
      have hxR : x ∈ R := hQ.1 hx
      have hmem : (⟨x, hxR⟩ : R) ∈ (P.subgroupOf R).map (MulAut.conj g).toMonoidHom := by
        rw [h1]
        exact hx
      obtain ⟨y, hy, hyx⟩ := hmem
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  simpa only [CFSG.Quasithin.conjSubgroup, A1b.conjSub, inv_inv] using hmain

theorem nine3_thm77_core (hc : Nine3Choice V T A K S X p g x) {ρ : ↥K →* Equiv.Perm (ZMod p)}
    (hρ : Nine3FibreAct K S p x ρ) {U : Subgroup G} {c : ZMod p} (hUc : Nine3Fib K p ρ U c)
    (hc0 : c ≠ 0) {a u : ↥K} (haA : (a : G) ∈ A) (haR : (a : G) ∉ pCoreOf 2 K)
    (huU : (u : G) ∈ U) (huR : (u : G) ∉ pCoreOf 2 K) {h : G}
    (hh : h ∉ normalizer (V : Set G))
    (hDa : ∀ z ∈ conjSubgroup V h, z * (a : G) = (a : G) * z)
    (hDu : ∀ z ∈ conjSubgroup V h, z * (u : G) = (u : G) * z) : False := by
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.toTwoPTwo.prime⟩
  have hp : p.Prime := hc.core.hyp.base.toTwoPTwo.prime
  have hp2 : p ≠ 2 := hc.core.hyp.base.toTwoPTwo.odd
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.nineOmegaIn_le_K hc.core.A_mem_nineOmegaIn⟩
  have hAfib : Nine3Fib K p ρ A 0 :=
    (nine3_fib_zero_iff hc hρ hAΩ).mpr hc.core.A_mem_nineOmegaIn.2
  have hρa : ρ a = zmodRefl p 0 := hAfib a haA haR
  have hρu : ρ u = zmodRefl p c := hUc u huU huR
  have hρau : ρ (a * u) = Equiv.addRight (2 * (0 - c)) := by
    rw [map_mul, hρa, hρu, nine3_cent_zmodRefl_mul_refl]
  have hd : 2 * (0 - c) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := nine3_cent_two_ne_zero hp hp2
    have h0c : (0 - c : ZMod p) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hc0)
    exact mul_ne_zero h2 h0c
  have hpow1 : (Equiv.addRight (2 * (0 - c))) ^ p = 1 := by
    ext i
    rw [nine3_cent_addRight_pow, ZMod.natCast_self, zero_mul, add_zero]
    rfl
  have hne1 : Equiv.addRight (2 * (0 - c)) ≠ 1 := by
    intro h1
    have h0 : (Equiv.addRight (2 * (0 - c))) 0 = (0 : ZMod p) := by
      rw [h1]
      simp
    have h0' : 2 * (0 - c) = 0 := by
      simpa only [Equiv.coe_addRight, zero_add] using h0
    exact hd h0'
  have horder : orderOf (ρ (a * u)) = p := by
    rw [hρau]
    exact orderOf_eq_prime hpow1 hne1
  have hdvd : p ∣ orderOf (a * u) := by
    have h1 : orderOf (ρ (a * u)) ∣ orderOf (a * u) := orderOf_map_dvd ρ _
    rwa [horder] at h1
  let x0 : ↥K := a * u
  let y : ↥K := x0 ^ (orderOf x0 / p)
  have hx0ne : orderOf x0 ≠ 0 := (orderOf_pos x0).ne'
  have hdvd' : p ∣ orderOf x0 := by simpa [x0] using hdvd
  have hyord_sub : orderOf y = p := by
    simpa [y] using orderOf_pow_orderOf_div (x := x0) (n := p) hx0ne hdvd'
  have hyord : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hyord_sub
  let Y : Subgroup G := Subgroup.zpowers (y : G)
  have hYcard : Nat.card Y = p := by rw [Nat.card_zpowers, hyord]
  have hYleK : Y ≤ K := Subgroup.zpowers_le.mpr y.2
  have hXsyl : IsSylowIn p X K := hc.core.hyp.base.toTwoPTwo.sylowP
  have hYcard' : Nat.card Y = p ^ (Nat.card K).factorization p := by
    have hpoweq : p ^ (Nat.card K).factorization p = p := hXsyl.card_eq.symm.trans hc.core.card
    rw [hYcard, hpoweq]
  have hYsyl : IsSylowIn p Y K := isSylowIn_of_card_eq hYleK hYcard'
  obtain ⟨r, hrK, hr⟩ := nine3_cent_sylow_conj hYsyl hXsyl
  have hr' : conjSubgroup Y r⁻¹ = X := by
    simpa only [CFSG.Quasithin.conjSubgroup, A1b.conjSub, inv_inv] using hr
  have hcommY : conjSubgroup V h ≤ Subgroup.centralizer (Y : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    have hzau : Commute z ((a : G) * (u : G)) := by
      show z * ((a : G) * (u : G)) = ((a : G) * (u : G)) * z
      calc z * ((a : G) * (u : G))
          = (z * (a : G)) * (u : G) := by rw [mul_assoc]
        _ = ((a : G) * z) * (u : G) := by rw [hDa z hz]
        _ = (a : G) * (z * (u : G)) := by rw [mul_assoc]
        _ = (a : G) * ((u : G) * z) := by rw [hDu z hz]
        _ = ((a : G) * (u : G)) * z := by rw [mul_assoc]
    have hyG_eq : (y : G) = ((a : G) * (u : G)) ^ (orderOf x0 / p) := by
      simp only [y, x0, Subgroup.coe_pow, Subgroup.coe_mul]
    have hzy : Commute z (y : G) := by
      show z * (y : G) = (y : G) * z
      rw [hyG_eq]
      exact (hzau.pow_right _).eq
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn]
    exact (hzy.zpow_right n).eq.symm
  have hVrX : conjSubgroup V (h * r⁻¹) ≤ Subgroup.centralizer (X : Set G) := by
    have hconj := E3.conjSubgroup_mono_left r⁻¹ hcommY
    rw [E3.conjSubgroup_centralizer, hr'] at hconj
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup] at hconj
    exact hconj
  have hcomm' : ⁅X, conjSubgroup V (h * r⁻¹)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVrX
  have hrM : r ∈ normalizer (V : Set G) := hc.core.hyp.base.le hrK
  have hh' : h * r⁻¹ ∉ normalizer (V : Set G) := by
    intro hmem
    apply hh
    have heq : h = (h * r⁻¹) * r := by group
    rw [heq]
    exact (normalizer (V : Set G)).mul_mem hmem hrM
  exact hc.nine_not_exists ⟨h * r⁻¹, hh', hcomm'⟩

end CFSG.LocalAnalysis.WeakClosure81
