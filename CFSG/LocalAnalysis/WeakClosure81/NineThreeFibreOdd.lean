module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreAct
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeS4FrameBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
  {ρ : ↥K →* Equiv.Perm (ZMod p)}

private lemma nine3_two_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

private lemma nine3_zmodRefl_mul_refl (c c' : ZMod p) :
    zmodRefl p c * zmodRefl p c' = Equiv.addRight (2 * (c - c')) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply, Equiv.coe_addRight]
  ring

private lemma nine3_addRight_pow (d : ZMod p) : ∀ (n : ℕ) (i : ZMod p),
    ((Equiv.addRight d) ^ n) i = i + (n : ZMod p) * d := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [pow_succ, Equiv.Perm.mul_apply, ih ((Equiv.addRight d) i),
        Equiv.coe_addRight, Nat.cast_succ]
      ring

@[expose] def Nine3Fib (K : Subgroup G) (p : ℕ) (ρ : ↥K →* Equiv.Perm (ZMod p))
    (U : Subgroup G) (c : ZMod p) : Prop :=
  ∀ u : ↥K, (u : G) ∈ U → (u : G) ∉ pCoreOf 2 K → ρ u = zmodRefl p c

private lemma nine3_exists_translation_priv (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) (t : ZMod p) :
    ∃ k : ↥K, ∀ i : ZMod p, ρ k i = i + t := by
  haveI : NeZero p := ⟨hc.core.hyp.base.toTwoPTwo.prime.ne_zero⟩
  have hxK : x ∈ K := hc.core.hyp.base.toTwoPTwo.sylowP.le hc.x_mem
  let x₀ : ↥K := ⟨x, hxK⟩
  have hshift : ∀ i : ZMod p, ρ x₀ i = i + 1 := hρ.shift x₀ rfl
  have hpow : ∀ n : ℕ, ∀ i : ZMod p, (ρ x₀ ^ n) i = i + n := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
        intro i
        rw [pow_succ, Equiv.Perm.mul_apply, hshift i, ih (i + 1), Nat.cast_succ]
        ring
  refine ⟨x₀ ^ t.val, fun i => ?_⟩
  rw [map_pow, hpow t.val i, ZMod.natCast_zmod_val]

private theorem nine3_fib_conj_aux {U : Subgroup G} {c t : ZMod p}
    (h : Nine3Fib K p ρ U c) {k : ↥K}
    (hk : ∀ i : ZMod p, ρ k i = i + t) : Nine3Fib K p ρ (conjSubgroup U (k : G)) (c - t) := by
  intro w hw hwR
  have hwU : ((k * w * k⁻¹ : ↥K) : G) ∈ U := by
    have h1 : (k : G) * (w : G) * (k : G)⁻¹ ∈ U := mem_conjSubgroup_iff.mp hw
    simpa using h1
  have hw'R : ((k * w * k⁻¹ : ↥K) : G) ∉ pCoreOf 2 K := by
    intro hh
    exact hwR ((Nine3Core.mem_pCoreOf_conj_iff K k.2).mpr (by simpa using hh))
  have hconj : ρ k * ρ w * (ρ k)⁻¹ = zmodRefl p c := by
    have h2 := h (k * w * k⁻¹) hwU hw'R
    rwa [map_mul, map_mul, map_inv] at h2
  have hw_eq : ρ w = (ρ k)⁻¹ * zmodRefl p c * ρ k := by
    rw [← hconj]
    group
  have hk_inv : ∀ j : ZMod p, (ρ k)⁻¹ j = j - t := by
    intro j
    rw [Equiv.Perm.inv_eq_iff_eq, hk, sub_add_cancel]
  rw [hw_eq]
  ext i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk_inv]
  rw [zmodRefl, zmodRefl, Equiv.subLeft_apply, Equiv.subLeft_apply, hk i]
  ring

theorem nine3_exists_fib (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ∃ c : ZMod p, Nine3Fib K p ρ U c := by
  obtain ⟨y, hUy, -, hnle⟩ := mem_omegaSet.mp hU.1
  obtain ⟨u, huU, huR⟩ := SetLike.not_le_iff_exists.mp hnle
  have huK : u ∈ K := hU.2 huU
  have hu2 : u * u = 1 := by
    have hel : IsElemAbelian 2 U := by
      rw [hUy]
      exact E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 y
    have h := hel.2 u huU
    rwa [pow_two] at h
  let k : ↥K := ⟨u, huK⟩
  have hkk : k * k = 1 := by
    apply Subtype.ext
    simpa [k] using hu2
  obtain ⟨c, hkc⟩ := hρ.refl k huR hkk
  refine ⟨c, fun u' hu'U hu'R => ?_⟩
  have hrel : (U ⊓ pCoreOf 2 K).relIndex U = 2 := nine3_relIndex_of_mem_omegaIn hc hU
  have hinv : u⁻¹ * (u' : G) ∈ pCoreOf 2 K := by
    have hiff : (⟨u⁻¹, U.inv_mem huU⟩ : ↥U) ∈ (U ⊓ pCoreOf 2 K).subgroupOf U ↔
        (⟨(u' : G), hu'U⟩ : ↥U) ∈ (U ⊓ pCoreOf 2 K).subgroupOf U := by
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact iff_of_false
        (fun h => huR (by simpa using (pCoreOf 2 K).inv_mem h.2)) (fun h => hu'R h.2)
    have hmem := (Subgroup.mul_mem_iff_of_index_two
        (H := (U ⊓ pCoreOf 2 K).subgroupOf U) hrel
        (a := (⟨u⁻¹, U.inv_mem huU⟩ : ↥U)) (b := ⟨(u' : G), hu'U⟩)).2 hiff
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  have hdecomp : ρ u' = ρ k * ρ (k⁻¹ * u') := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
    group
  have hw : ρ (k⁻¹ * u') = 1 := hρ.le_ker (k⁻¹ * u') (by simpa [k] using hinv)
  rw [hdecomp, hw, mul_one]
  exact hkc

theorem nine3_fib_zero_iff (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    Nine3Fib K p ρ U 0 ↔ U ≤ S := by
  constructor
  · intro hfib a haU
    by_cases haR : a ∈ pCoreOf 2 K
    · exact hc.core.hyp.base.toTwoPTwo.pCoreOf_le_sylowTwo haR
    · have haK : a ∈ K := hU.2 haU
      have h0 : ρ ⟨a, haK⟩ 0 = 0 := by
        rw [hfib ⟨a, haK⟩ haU haR]
        simp [zmodRefl, Equiv.subLeft_apply]
      exact (hρ.stab ⟨a, haK⟩).mp h0
  · intro hUS u huU huR
    haveI : Fact p.Prime := ⟨hc.core.hyp.base.toTwoPTwo.prime⟩
    have huzero : ρ u 0 = 0 := (hρ.stab u).mpr (hUS huU)
    obtain ⟨c, hcfib⟩ := nine3_exists_fib hc hρ hU
    have hcu := hcfib u huU huR
    have h2c : (2 : ZMod p) * c = 0 := by
      have h0 := congrFun (congrArg DFunLike.coe hcu) 0
      simp only [zmodRefl, Equiv.subLeft_apply] at h0
      rw [huzero] at h0
      exact sub_eq_zero.mp h0.symm
    have hc0 : c = 0 :=
      (mul_eq_zero.mp h2c).resolve_left
        (nine3_two_ne_zero hc.core.hyp.base.toTwoPTwo.prime hc.core.hyp.base.toTwoPTwo.odd)
    rw [hcu, hc0]

theorem nine3_fib_comm (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) (hU' : U' ∈ omegaIn V K (nineE V K))
    {c : ZMod p} (h : Nine3Fib K p ρ U c) (h' : Nine3Fib K p ρ U' c) :
    ∀ a ∈ U, ∀ b ∈ U', a * b = b * a := by
  intro a haU b hbU'
  obtain ⟨k, hk⟩ := nine3_exists_translation_priv hc hρ c
  have hU0 : Nine3Fib K p ρ (conjSubgroup U (k : G)) 0 := by
    simpa using nine3_fib_conj_aux h hk
  have hU'0 : Nine3Fib K p ρ (conjSubgroup U' (k : G)) 0 := by
    simpa using nine3_fib_conj_aux h' hk
  have hUΩ : conjSubgroup U (k : G) ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn hU k.2
  have hU'Ω : conjSubgroup U' (k : G) ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn hU' k.2
  have hUS : conjSubgroup U (k : G) ≤ S := (nine3_fib_zero_iff hc hρ hUΩ).mp hU0
  have hU'S : conjSubgroup U' (k : G) ≤ S := (nine3_fib_zero_iff hc hρ hU'Ω).mp hU'0
  have hleW : conjSubgroup U (k : G) ≤ nineW V S :=
    le_iSup₂_of_le _ ((hc.core.mem_nineDelta_iff).mpr (Or.inr ⟨hUΩ.1, hUS⟩)) le_rfl
  have hleW' : conjSubgroup U' (k : G) ≤ nineW V S :=
    le_iSup₂_of_le _ ((hc.core.mem_nineDelta_iff).mpr (Or.inr ⟨hU'Ω.1, hU'S⟩)) le_rfl
  have ha0 : (k : G)⁻¹ * a * (k : G) ∈ conjSubgroup U (k : G) := by
    rw [mem_conjSubgroup_iff]
    have h1 : (k : G) * ((k : G)⁻¹ * a * (k : G)) * (k : G)⁻¹ = a := by group
    rw [h1]
    exact haU
  have hb0 : (k : G)⁻¹ * b * (k : G) ∈ conjSubgroup U' (k : G) := by
    rw [mem_conjSubgroup_iff]
    have h1 : (k : G) * ((k : G)⁻¹ * b * (k : G)) * (k : G)⁻¹ = b := by group
    rw [h1]
    exact hbU'
  have hcomm : ((k : G)⁻¹ * a * (k : G)) * ((k : G)⁻¹ * b * (k : G)) =
      ((k : G)⁻¹ * b * (k : G)) * ((k : G)⁻¹ * a * (k : G)) :=
    hc.core.nineW_mul_comm (hleW ha0) (hleW' hb0)
  have hcomm' : (k : G)⁻¹ * (a * b) * (k : G) = (k : G)⁻¹ * (b * a) * (k : G) := by
    calc (k : G)⁻¹ * (a * b) * (k : G)
        = ((k : G)⁻¹ * a * (k : G)) * ((k : G)⁻¹ * b * (k : G)) := by group
      _ = ((k : G)⁻¹ * b * (k : G)) * ((k : G)⁻¹ * a * (k : G)) := hcomm
      _ = (k : G)⁻¹ * (b * a) * (k : G) := by group
  calc a * b = (k : G) * ((k : G)⁻¹ * (a * b) * (k : G)) * (k : G)⁻¹ := by group
    _ = (k : G) * ((k : G)⁻¹ * (b * a) * (k : G)) * (k : G)⁻¹ := by rw [hcomm']
    _ = b * a := by group

theorem nine3_fib_pow (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) (hU' : U' ∈ omegaIn V K (nineE V K))
    {c c' : ZMod p} (h : Nine3Fib K p ρ U c) (h' : Nine3Fib K p ρ U' c') (hne : c ≠ c') :
    ∀ u ∈ U, u ∉ pCoreOf 2 K → ∀ u' ∈ U', u' ∉ pCoreOf 2 K → (u * u') ^ p = 1 := by
  intro u huU huR u' hu'U' hu'R
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.toTwoPTwo.prime⟩
  have hp : p.Prime := hc.core.hyp.base.toTwoPTwo.prime
  let ku : ↥K := ⟨u, hU.2 huU⟩
  let ku' : ↥K := ⟨u', hU'.2 hu'U'⟩
  have hku : ρ ku = zmodRefl p c := h ku huU huR
  have hku' : ρ ku' = zmodRefl p c' := h' ku' hu'U' hu'R
  have hprod : ρ (ku * ku') = Equiv.addRight (2 * (c - c')) := by
    rw [map_mul, hku, hku', nine3_zmodRefl_mul_refl]
  have hpow_one : ρ ((ku * ku') ^ p) = 1 := by
    rw [map_pow, hprod]
    ext i
    rw [nine3_addRight_pow]
    simp [ZMod.natCast_self]
  have hd_ne : 2 * (c - c') ≠ 0 := by
    intro h0
    have h2 : (2 : ZMod p) ≠ 0 := nine3_two_ne_zero hp hc.core.hyp.base.toTwoPTwo.odd
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h2))
  have horder : orderOf (ρ (ku * ku')) = p := by
    rw [hprod]
    have hdvd : orderOf (Equiv.addRight (2 * (c - c'))) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr (by
        ext i
        rw [nine3_addRight_pow]
        simp [ZMod.natCast_self])
    have hne1 : orderOf (Equiv.addRight (2 * (c - c'))) ≠ 1 := by
      intro h1
      have h_eq : Equiv.addRight (2 * (c - c')) = 1 := orderOf_eq_one_iff.mp h1
      have h0 : 2 * (c - c') = 0 := by
        have := congrArg (fun f : Equiv.Perm (ZMod p) => f 0) h_eq
        simpa [Equiv.coe_addRight] using this
      exact hd_ne h0
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd h1 hne1
    · exact hp'
  have hp_dvd : p ∣ orderOf (u * u') := by
    have hmap : orderOf (ρ (ku * ku')) ∣ orderOf (ku * ku') := orderOf_map_dvd ρ _
    have hK : p ∣ orderOf (ku * ku') := horder ▸ hmap
    have hcoe : ((ku * ku' : ↥K) : G) = u * u' := by
      simp [ku, ku', Subgroup.coe_mul]
    rw [← Subgroup.orderOf_coe (ku * ku')] at hK
    rwa [hcoe] at hK
  have hnot : ¬ IsPGroup 2 (Subgroup.closure ({u, u'} : Set G)) := by
    intro hP
    have hu_mem : u ∈ Subgroup.closure ({u, u'} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hu'_mem : u' ∈ Subgroup.closure ({u, u'} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hprod_mem : u * u' ∈ Subgroup.closure ({u, u'} : Set G) :=
      mul_mem hu_mem hu'_mem
    obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow
      (⟨u * u', hprod_mem⟩ : Subgroup.closure ({u, u'} : Set G))
    have hk' : orderOf (u * u') ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe
        (⟨u * u', hprod_mem⟩ : Subgroup.closure ({u, u'} : Set G))] at hk
      exact hk
    have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow (hp_dvd.trans hk')
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2dvd with h | h
    · exact hp.ne_one h
    · exact hc.core.hyp.base.toTwoPTwo.odd h
  have hodd : Odd (orderOf (u * u')) :=
    seven_three_A hc.core.hyp7.1 hc.core.hyp7.2.2 (isElemAbelian_nineE V K).1
      hU.1 hU'.1 huU hu'U' hnot
  have hmemR : (u * u') ^ p ∈ pCoreOf 2 K := by
    have h1 := hρ.ker_le ((ku * ku') ^ p) hpow_one
    simpa [ku, ku', Subgroup.coe_pow, Subgroup.coe_mul] using h1
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_orderOf_dvd_pow
    (⟨(u * u') ^ p, hmemR⟩ : ↥(pCoreOf 2 K))
  have h2dvd : orderOf ((u * u') ^ p) ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_coe (⟨(u * u') ^ p, hmemR⟩ : ↥(pCoreOf 2 K))] at hn
    exact hn
  have hodd_p : Odd (orderOf ((u * u') ^ p)) := hodd.of_dvd_nat (orderOf_pow_dvd p)
  have hcop : Nat.Coprime (orderOf ((u * u') ^ p)) (2 ^ n) :=
    hodd_p.coprime_two_right.pow_right n
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h2dvd)

theorem nine3_fib_inf_centralizer (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K))
    (hU' : U' ∈ omegaIn V K (nineE V K)) {c c' : ZMod p} (h : Nine3Fib K p ρ U c)
    (h' : Nine3Fib K p ρ U' c') (hne : c ≠ c') : U' ⊓ centralizer (U : Set G) = ⊥ := by
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.toTwoPTwo.prime⟩
  have hp : p.Prime := hc.core.hyp.base.toTwoPTwo.prime
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  by_contra hb1
  have hbcent : b ∈ centralizer (U : Set G) := hb.2
  have hbU' : b ∈ U' := hb.1
  obtain ⟨y', hU'y', -, -⟩ := mem_omegaSet.mp hU'.1
  have hbV' : b ∈ conjSubgroup V y' := by rwa [← hU'y']
  have hnorm : Subgroup.centralizer ({b} : Set G) ≤
      normalizer (conjSubgroup V y' : Set G) :=
    centralizer_le_normalizer_conj hc.core.hyp7.2.2 y' hbV' hb1
  have hUleN : U ≤ normalizer (conjSubgroup V y' : Set G) := by
    intro z hzU
    apply hnorm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ((Subgroup.mem_centralizer_iff.mp hbcent) z hzU).symm
  obtain ⟨-, -, -, hnleU⟩ := mem_omegaSet.mp hU.1
  obtain ⟨-, -, -, hnleU'⟩ := mem_omegaSet.mp hU'.1
  obtain ⟨u, huU, huR⟩ := SetLike.not_le_iff_exists.mp hnleU
  obtain ⟨u', hu'U', hu'R⟩ := SetLike.not_le_iff_exists.mp hnleU'
  obtain ⟨a, hUa, -, -⟩ := mem_omegaSet.mp hU.1
  have huConj : u ∈ conjSubgroup V a := by rw [← hUa]; exact huU
  have hu'Conj : u' ∈ conjSubgroup V y' := by rw [← hU'y']; exact hu'U'
  have huN : u ∈ normalizer (conjSubgroup V y' : Set G) := hUleN huU
  have hP : IsPGroup 2 (Subgroup.closure ({u, u'} : Set G)) :=
    isPGroup_closure_pair_of_mem_normalizer hc.core.hyp7.1 huConj hu'Conj huN
  have hpow : (u * u') ^ p = 1 := nine3_fib_pow hc hρ hU hU' h h' hne u huU huR u' hu'U' hu'R
  have hu2 : u * u = 1 := by
    obtain ⟨y, hUy, -, -⟩ := mem_omegaSet.mp hU.1
    have hel : IsElemAbelian 2 U := by
      rw [hUy]
      exact E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 y
    have hh := hel.2 u huU
    rwa [pow_two] at hh
  have hu'mem : u * u' ∈ Subgroup.closure ({u, u'} : Set G) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨k, hk⟩ := hP.exists_orderOf_dvd_pow
    (⟨u * u', hu'mem⟩ : Subgroup.closure ({u, u'} : Set G))
  have hk' : orderOf (u * u') ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_coe
      (⟨u * u', hu'mem⟩ : Subgroup.closure ({u, u'} : Set G))] at hk
    exact hk
  have hord_dvd_p : orderOf (u * u') ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hp2 : Nat.Coprime p 2 :=
    hp.coprime_iff_not_dvd.mpr (by
      intro h2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · exact hp.ne_one h1
      · exact hc.core.hyp.base.toTwoPTwo.odd h1)
  have hcop : Nat.Coprime p (2 ^ k) := hp2.pow_right k
  have hu_eq : u * u' = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord_dvd_p hk')
  have hu'u : u' = u := by
    rw [← inv_eq_of_mul_eq_one_right hu_eq, inv_eq_of_mul_eq_one_right hu2]
  have hku : (⟨u, hU.2 huU⟩ : ↥K) = ⟨u', hU'.2 hu'U'⟩ := Subtype.ext hu'u.symm
  have hρeq : zmodRefl p c = zmodRefl p c' := by
    rw [← h ⟨u, hU.2 huU⟩ huU huR, ← h' ⟨u', hU'.2 hu'U'⟩ hu'U' hu'R, hku]
  have h2 : (2 : ZMod p) * c = (2 : ZMod p) * c' := by
    have := congrArg (fun f : Equiv.Perm (ZMod p) => f 0) hρeq
    simpa [zmodRefl, Equiv.subLeft_apply] using this
  exact hne (mul_left_cancel₀ (nine3_two_ne_zero hp hc.core.hyp.base.toTwoPTwo.odd) h2)

end CFSG.LocalAnalysis.WeakClosure81
