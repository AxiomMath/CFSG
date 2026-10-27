module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Adapters.LieModelUnitaryOuter
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4Out
import CFSG.GroupTheory.CyclicPowRoot
import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K]

theorem uFieldAut_pow_eq_one_of_mem_range (h : UnitaryFieldData 2 f K)
    (hX : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ f) K)) f) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {k : ℕ}
    (hk : uFieldAut h (n := 4) (by norm_num) σ ^ k ∈
      (MulAut.conj : StatedProj (StatedSU 4 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 4 (2 ^ f) K))).range) :
    uFieldAut h (n := 4) (by norm_num) σ ^ k = 1 := by
  let Φ : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) := uFieldAut h (n := 4) (by norm_num) σ
  let N : Subgroup (MulAut (StatedProj (StatedSU 4 (2 ^ f) K))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU 4 (2 ^ f) K))
  have hΦ : ∀ α : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)),
      ∃ y : StatedProj (StatedSU 4 (2 ^ f) K), ∃ j : ℕ,
        α = MulAut.conj y * Φ ^ j := by
    intro α
    obtain ⟨y, j, hα⟩ := exists_conj_mul_uFieldAut_pow h hσ α
    exact ⟨y, j, hα⟩
  have hgen : ∀ x : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N,
      x ∈ Subgroup.zpowers (QuotientGroup.mk' N Φ) := by
    intro x
    obtain ⟨j, hj⟩ := CFSG.exists_eq_quotient_mk'_pow (H := N) hΦ le_rfl x
    rw [hj]
    exact Subgroup.npow_mem_zpowers _ j
  have hord : orderOf (QuotientGroup.mk' N Φ) =
      Nat.card (MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N) :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hgcd : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have h2dvd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := h.one_le; omega)
    have h2 : Nat.Coprime 2 (2 ^ f + 1) :=
      Nat.coprime_two_left.mpr (even_iff_two_dvd.mpr h2dvd).add_one
    have h4 : Nat.Coprime 4 (2 ^ f + 1) := by simpa using h2.pow_left 2
    exact h4
  have hcard : Nat.card (MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N) = 2 * f := by
    have hout := CFSG.Blueprint.LieModel.card_outer_psu hX (by norm_num) (by norm_num)
    rw [hgcd, mul_one] at hout
    simpa [N, CFSG.ComponentClassification.OuterAutomorphisms.inner,
      CFSG.ComponentClassification.OuterAutomorphisms.Outer] using hout
  have hqk : (QuotientGroup.mk' N Φ) ^ k = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simpa [N, CFSG.ComponentClassification.OuterAutomorphisms.inner] using hk
  have hdiv : 2 * f ∣ k := by
    have h := orderOf_dvd_of_pow_eq_one hqk
    rwa [hord, hcard] at h
  obtain ⟨t, ht⟩ := hdiv
  rw [ht, pow_mul, uFieldAut_pow_two_mul_eq_one h hσ, one_pow]

private lemma card_pow_ker_le {p : ℕ} (hp : p.Prime) :
    Nat.card ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker) ≤
      p ^ 3 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let H := (powMonoidHom p :
    (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker
  let F : H → (Fin 3 → rootsOfUnity p K) := fun d i =>
    ⟨((d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) i : Kˣ), by
      have h2 : ((d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) i) ^ p = 1 := by
        have h1 := congrFun d.2 i
        simpa using h1
      exact congrArg (fun x : rootsOfUnity (2 ^ f + 1) K => (x : Kˣ)) h2⟩
  have hinj : Function.Injective F := by
    intro d e hde
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have h1 := congrArg (fun x : Fin 3 → rootsOfUnity p K => (x i : Kˣ)) hde
    simpa [F] using h1
  calc Nat.card H ≤ Nat.card (Fin 3 → rootsOfUnity p K) :=
        Nat.card_le_card_of_injective F hinj
    _ = Nat.card (rootsOfUnity p K) ^ 3 := by
        rw [Nat.card_fun]; norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left (card_rootsOfUnity K p) 3

private lemma mem_map_pow_ker_of_mem_u4TorusSylow (h : UnitaryFieldData 2 f K) {p : ℕ}
    {x : StatedProj (StatedSU 4 (2 ^ f) K)}
    (hx : x ∈ u4TorusSylow (f := f) (K := K) p) (hxp : x ^ p = 1) :
    x ∈ ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom := by
  rw [u4TorusSylow] at hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map_of_mem _ ?_
  have hd' : d ^ p = 1 := by
    apply u4TorusHom_injective h.one_le
    rw [map_pow, map_one]
    exact hxp
  simpa [MonoidHom.mem_ker, powMonoidHom_apply] using hd'

theorem card_le_of_le_u4TorusSylow (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K))}
    (hE : E ≤ u4TorusSylow (f := f) (K := K) p) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  have := h.finite
  have h1 : E ≤ ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom := fun x hx =>
    mem_map_pow_ker_of_mem_u4TorusSylow h (hE hx) (hEel.2 x hx)
  calc Nat.card E ≤ Nat.card (((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom) := Subgroup.card_le_of_le h1
    _ = Nat.card ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker) :=
        Subgroup.card_map_of_injective (u4TorusHom_injective h.one_le)
    _ ≤ p ^ 3 := card_pow_ker_le hp

theorem mem_of_le_u4TorusSylow_of_card (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K))}
    (hE : E ≤ u4TorusSylow (f := f) (K := K) p) (hEel : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {x : StatedProj (StatedSU 4 (2 ^ f) K)}
    (hx : x ∈ u4TorusSylow (f := f) (K := K) p) (hxp : x ^ p = 1) : x ∈ E := by
  have := h.finite
  have h1 : E ≤ ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom := fun y hy =>
    mem_map_pow_ker_of_mem_u4TorusSylow h (hE hy) (hEel.2 y hy)
  have hx' : x ∈ ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom := mem_map_pow_ker_of_mem_u4TorusSylow h hx hxp
  have hcardΩ : Nat.card (((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom) ≤ p ^ 3 := by
    rw [Subgroup.card_map_of_injective (u4TorusHom_injective h.one_le)]
    exact card_pow_ker_le hp
  have hEq : E = ((powMonoidHom p :
      (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 3 → rootsOfUnity (2 ^ f + 1) K)).ker).map
        u4TorusHom := Subgroup.eq_of_le_of_card_ge h1 (by omega)
  rw [hEq]
  exact hx'

private lemma mulAut_conj_comp {G : Type*} [Group G] (F : MulAut G) (z : G) :
    F * MulAut.conj z * F⁻¹ = MulAut.conj (F z) := by
  ext w
  simp [MulAut.conj_apply, MulAut.mul_apply]

private def nprod {G : Type*} [Group G] (g : G) (F : MulAut G) : ℕ → G
  | 0 => 1
  | n + 1 => g * F (nprod g F n)

private lemma conj_mul_pow {G : Type*} [Group G] (g : G) (F : MulAut G) (n : ℕ) :
    (MulAut.conj g * F) ^ n = MulAut.conj (nprod g F n) * F ^ n := by
  induction n with
  | zero => simp [nprod]
  | succ n ih =>
    have hF : F * MulAut.conj (nprod g F n) = MulAut.conj (F (nprod g F n)) * F := by
      rw [← mulAut_conj_comp F (nprod g F n), inv_mul_cancel_right]
    calc (MulAut.conj g * F) ^ (n + 1)
          = MulAut.conj g * F * (MulAut.conj (nprod g F n) * F ^ n) := by rw [pow_succ', ih]
      _ = MulAut.conj g * (F * MulAut.conj (nprod g F n)) * F ^ n := by simp only [mul_assoc]
      _ = MulAut.conj g * MulAut.conj (F (nprod g F n)) * (F * F ^ n) := by
          rw [hF]; simp only [mul_assoc]
      _ = MulAut.conj (nprod g F (n + 1)) * F ^ (n + 1) := by
          rw [nprod, map_mul, ← pow_succ']

private lemma conj_mul_conj_conj {G : Type*} [Group G] (y z : G) (F : MulAut G) :
    MulAut.conj y * (MulAut.conj z * F) * (MulAut.conj y)⁻¹ =
      MulAut.conj (y * z * (F y)⁻¹) * F := by
  ext w
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
    mul_inv_rev]

private def geomN (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ e * geomN e n

private lemma geomN_mul (e n : ℕ) :
    geomN e n * (2 ^ e - 1) = 2 ^ (e * n) - 1 := by
  induction n with
  | zero => simp [geomN]
  | succ n ih =>
    have hA : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
    have hAB : 2 ^ e ≤ 2 ^ e * 2 ^ (e * n) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    rw [geomN, Nat.add_mul, one_mul, mul_assoc, ih, Nat.mul_sub, mul_one,
      show e * (n + 1) = e + e * n by ring, pow_add]
    omega

private lemma factorization_two_pow_sub_one (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f + 1) {e : ℕ}
    (h2f : 2 * f ∣ e * p) (he : ¬ 2 * f ∣ e) :
    p ∣ 2 ^ e - 1 ∧ (2 ^ e - 1).factorization p = (2 ^ f + 1).factorization p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := h.one_le
  have hpdvd : p ∣ 2 * f := by
    by_contra hcon
    have hcop : Nat.Coprime (2 * f) p := ((hp.coprime_iff_not_dvd).mpr hcon).symm
    exact he (hcop.dvd_of_dvd_mul_right h2f)
  obtain ⟨g, hg⟩ := hpdvd
  have hge : g ∣ e := by
    have h1 : p * g ∣ p * e := by rw [← hg, ← Nat.mul_comm e p]; exact h2f
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
  obtain ⟨m, hm⟩ := hge
  have hpm : ¬ p ∣ m := by
    intro hd
    apply he
    obtain ⟨c, hc⟩ := hd
    exact ⟨c, by rw [hg, hm, hc]; ring⟩
  have he0 : e ≠ 0 := fun h => he (h ▸ dvd_zero (2 * f))
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact he0 (by rw [hm, Nat.mul_zero])
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · rw [h0, Nat.mul_zero] at hg
      omega
    · exact hpos
  have h2g1 : 1 < 2 ^ g := Nat.one_lt_pow (by omega) (by norm_num)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    rcases (Nat.dvd_prime Nat.prime_two).mp h2d with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  have hord2f : orderOf (2 : ZMod p) ∣ 2 * f := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hneg : (2 : ZMod p) ^ f = -1 := by
      have h : (((2 ^ f + 1 : ℕ)) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (2 ^ f + 1) p).mpr hpf
      rw [eq_neg_iff_add_eq_zero]
      simpa using h
    rw [show 2 * f = f * 2 by ring, pow_mul, hneg]
    exact neg_one_sq
  have hppos : 0 < p := hp.pos
  have hcop_ord : Nat.Coprime (orderOf (2 : ZMod p)) p := by
    have hnot : ¬ p ∣ orderOf (2 : ZMod p) := by
      intro hd
      have h2 : p ∣ p - 1 := dvd_trans hd (ZMod.orderOf_dvd_card_sub_one h2ne)
      have h3 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) h2
      rw [show p - (p - 1) = 1 by omega] at h3
      exact hp.not_dvd_one h3
    exact ((hp.coprime_iff_not_dvd).mpr hnot).symm
  have hordg : orderOf (2 : ZMod p) ∣ g := by
    have h := hord2f
    rw [hg] at h
    exact hcop_ord.dvd_of_dvd_mul_left h
  have hpdiv : p ∣ 2 ^ g - 1 := by
    have h2g : (2 : ZMod p) ^ g = 1 := orderOf_dvd_iff_pow_eq_one.mp hordg
    have h : (((2 ^ g - 1 : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow g 2 (by norm_num)), Nat.cast_one, Nat.cast_pow,
        Nat.cast_ofNat, h2g]
      ring
    exact (ZMod.natCast_eq_zero_iff (2 ^ g - 1) p).mp h
  have hp2g : ¬ p ∣ 2 ^ g := by
    intro hd
    have h2d : p ∣ 2 := hp.dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2d with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  set b := (2 ^ f + 1).factorization p with hb
  have hfac22 : (2 ^ (2 * f) - 1).factorization p = b := by
    have hsq : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have hpow : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by
        rw [show 2 * f = f * 2 by ring, pow_mul]
      rw [hpow]
      have h := Nat.sq_sub_sq (2 ^ f) 1
      rw [one_pow] at h
      rw [h]
      ring
    have hne1 : 2 ^ f - 1 ≠ 0 := by
      have h1 : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have hne2 : 2 ^ f + 1 ≠ 0 := by positivity
    have hnot : ¬ p ∣ 2 ^ f - 1 := by
      intro hd
      have h2d : p ∣ 2 := by
        have h := Nat.dvd_sub hpf hd
        rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h
      rcases (Nat.dvd_prime Nat.prime_two).mp h2d with h' | h'
      · exact hp.ne_one h'
      · exact hp2 h'
    rw [hsq, Nat.factorization_mul hne1 hne2, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  have hfacg : (2 ^ g - 1).factorization p = b - 1 := by
    have hL := CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hp hp2
      (q := 2 ^ g) (j := p) h2g1 hpdiv hp.ne_zero
    have hgp : (2 ^ g) ^ p = 2 ^ (2 * f) := by rw [← pow_mul, hg, Nat.mul_comm g p]
    rw [hgp, hp.factorization_self, hfac22] at hL
    omega
  have hL := CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hp hp2
    (q := 2 ^ g) (j := m) h2g1 hpdiv hm0
  have hgm : (2 ^ g) ^ m = 2 ^ e := by rw [← pow_mul, ← hm]
  rw [hgm, hfacg, Nat.factorization_eq_zero_of_not_dvd hpm, add_zero] at hL
  refine ⟨?_, hL⟩
  rw [← hgm]
  exact dvd_trans hpdiv (Nat.sub_one_dvd_pow_sub_one (2 ^ g) m)

private lemma geomN_pos (e n : ℕ) : 0 < geomN e (n + 1) := by
  simp only [geomN]
  positivity

private lemma factorization_geomN {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e)
    (hface : (2 ^ e - 1).factorization p = (2 ^ f + 1).factorization p - 1)
    (hpdiv : p ∣ 2 ^ e - 1) :
    (geomN e p).factorization p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hlam2 : 1 < 2 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
  have hlamne : 2 ^ e - 1 ≠ 0 := by omega
  have hplam : ¬ p ∣ 2 ^ e := by
    intro hd
    have h2d : p ∣ 2 := hp.dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2d with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  have hL := CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hp hp2
    (q := 2 ^ e) (j := p) hlam2 hpdiv hp.ne_zero
  have hgeom : geomN e p * (2 ^ e - 1) = (2 ^ e) ^ p - 1 := by
    rw [geomN_mul, ← pow_mul]
  have hNne : geomN e p ≠ 0 := by
    rcases p with _ | k
    · exact absurd rfl hp.ne_zero
    · exact (geomN_pos e k).ne'
  have hmul : ((2 ^ e) ^ p - 1).factorization p =
      (geomN e p).factorization p + (2 ^ e - 1).factorization p := by
    rw [← hgeom, Nat.factorization_mul hNne hlamne, Finsupp.add_apply]
  rw [hface, hp.factorization_self] at hL
  rw [hface] at hmul
  omega

private lemma exists_root_of_unity_pow (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    {e : ℕ} (he : 1 ≤ e)
    (hface : (2 ^ e - 1).factorization p = (2 ^ f + 1).factorization p - 1)
    (hpdiv : p ∣ 2 ^ e - 1) {z : Kˣ} (hzp : z ^ p = 1) :
    ∃ w : Kˣ, w ^ p ^ (2 ^ f + 1).factorization p = 1 ∧ w ^ (2 ^ e - 1) = z := by
  classical
  have := h.finite
  have hne : 2 ^ e - 1 ≠ 0 := by
    have h2 : 1 < 2 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  set b := (2 ^ f + 1).factorization p with hb
  have hb2 : 2 ≤ b := by
    have h1 : 0 < (2 ^ e - 1).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp hne hpdiv
    omega
  have hcardT : Nat.card (rootsOfUnity (p ^ b) K) = p ^ b := by
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have h := Nat.sq_sub_sq (2 ^ f) 1
      rw [one_pow] at h
      rw [h]; ring
    have hdvd : p ^ b ∣ (2 ^ f) ^ 2 - 1 := by
      rw [hsq]
      exact dvd_mul_of_dvd_right (Nat.ordProj_dvd (2 ^ f + 1) p) _
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, h.card,
      show 2 * f = f * 2 by ring, pow_mul]
    exact Nat.gcd_eq_right hdvd
  have hzT : z ∈ rootsOfUnity (p ^ b) K := by
    rw [mem_rootsOfUnity]
    rw [show p ^ b = p * p ^ (b - 1) by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ b)]]
    rw [pow_mul, hzp, one_pow]
  have hpdvd : p ∣ Nat.card (rootsOfUnity (p ^ b) K) := by
    rw [hcardT]
    exact dvd_pow_self p (by omega)
  have hzTp : (⟨z, hzT⟩ : rootsOfUnity (p ^ b) K) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hzp
  obtain ⟨y, hy⟩ := CFSG.GroupTheory.exists_pow_eq_of_pow_eq_one_of_isCyclic
    (G := rootsOfUnity (p ^ b) K) (k := p) (x := ⟨z, hzT⟩) hpdvd hzTp
  have hy' : (y : Kˣ) ^ p ^ (b - 1) = z := by
    have h1 : Nat.card (rootsOfUnity (p ^ b) K) / p = p ^ (b - 1) := by
      rw [hcardT]
      simpa using Nat.pow_div (x := p) (m := b) (n := 1) (by omega) hp.pos
    rw [← h1]
    exact congrArg Subtype.val hy
  have hpb_dvd : p ^ (b - 1) ∣ 2 ^ e - 1 := by
    have h := Nat.ordProj_dvd (2 ^ e - 1) p
    rwa [hface] at h
  set u := (2 ^ e - 1) / p ^ (b - 1) with hu
  have hu_eq : 2 ^ e - 1 = p ^ (b - 1) * u := by
    rw [hu, mul_comm]
    exact (Nat.div_mul_cancel hpb_dvd).symm
  have hpnu : ¬ p ∣ u := by
    have h := Nat.not_dvd_ordCompl hp (n := 2 ^ e - 1) hne
    rwa [hface] at h
  have hcop : Nat.Coprime u p := ((hp.coprime_iff_not_dvd).mpr hpnu).symm
  obtain ⟨s, -, hsu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hsum : z ^ (s * u) = z := by
    have h1 : u * s = p * (u * s / p) + 1 := by
      have h := Nat.div_add_mod (u * s) p
      rw [hsu] at h
      exact h.symm
    rw [Nat.mul_comm s u, h1, pow_add, pow_mul, hzp, one_pow, one_mul, pow_one]
  refine ⟨(y : Kˣ) ^ s, ?_, ?_⟩
  · rw [← pow_mul, show s * p ^ b = p ^ b * s by ring, pow_mul]
    have hyT : (y : Kˣ) ^ p ^ b = 1 := y.2
    rw [hyT, one_pow]
  · rw [hu_eq, ← pow_mul, show s * (p ^ (b - 1) * u) = p ^ (b - 1) * (s * u) by ring,
      pow_mul, hy', hsum]

private lemma uFieldAut_pow_eq_one_imp_dvd (h : UnitaryFieldData 2 f K)
    (hX : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ f) K)) f) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {k : ℕ}
    (hk : uFieldAut h (n := 4) (by norm_num) σ ^ k = 1) : 2 * f ∣ k := by
  let Φ : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) := uFieldAut h (n := 4) (by norm_num) σ
  let N : Subgroup (MulAut (StatedProj (StatedSU 4 (2 ^ f) K))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU 4 (2 ^ f) K))
  have hΦ : ∀ α : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)),
      ∃ y : StatedProj (StatedSU 4 (2 ^ f) K), ∃ j : ℕ,
        α = MulAut.conj y * Φ ^ j := by
    intro α
    obtain ⟨y, j, hα⟩ := exists_conj_mul_uFieldAut_pow h hσ α
    exact ⟨y, j, hα⟩
  have hgen : ∀ x : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N,
      x ∈ Subgroup.zpowers (QuotientGroup.mk' N Φ) := by
    intro x
    obtain ⟨j, hj⟩ := CFSG.exists_eq_quotient_mk'_pow (H := N) hΦ le_rfl x
    rw [hj]
    exact Subgroup.npow_mem_zpowers _ j
  have hord : orderOf (QuotientGroup.mk' N Φ) =
      Nat.card (MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N) :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hgcd : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have h2dvd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := h.one_le; omega)
    have h2 : Nat.Coprime 2 (2 ^ f + 1) :=
      Nat.coprime_two_left.mpr (even_iff_two_dvd.mpr h2dvd).add_one
    have h4 : Nat.Coprime 4 (2 ^ f + 1) := by simpa using h2.pow_left 2
    exact h4
  have hcard : Nat.card (MulAut (StatedProj (StatedSU 4 (2 ^ f) K)) ⧸ N) = 2 * f := by
    have hout := CFSG.Blueprint.LieModel.card_outer_psu hX (by norm_num) (by norm_num)
    rw [hgcd, mul_one] at hout
    simpa [N, CFSG.ComponentClassification.OuterAutomorphisms.inner,
      CFSG.ComponentClassification.OuterAutomorphisms.Outer] using hout
  have hqk : (QuotientGroup.mk' N Φ) ^ k = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hk]
    exact ⟨1, map_one _⟩
  have h := orderOf_dvd_of_pow_eq_one hqk
  rwa [hord, hcard] at h

private lemma uFieldAut_pow_eq_one_iff (h : UnitaryFieldData 2 f K)
    (hX : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ f) K)) f) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {k : ℕ} :
    uFieldAut h (n := 4) (by norm_num) σ ^ k = 1 ↔ 2 * f ∣ k := by
  refine ⟨uFieldAut_pow_eq_one_imp_dvd h hX hσ, ?_⟩
  rintro ⟨m, hm⟩
  rw [hm, pow_mul, uFieldAut_pow_two_mul_eq_one h hσ, one_pow]

theorem exists_conj_eq_uFieldAut_pow (h : UnitaryFieldData 2 f K)
    (hX : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ f) K)) f) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f + 1) {e : ℕ}
    (he : uFieldAut h (n := 4) (by norm_num) σ ^ e ≠ 1)
    {x : StatedProj (StatedSU 4 (2 ^ f) K)} (hx : x ∈ u4TorusSylow (f := f) (K := K) p)
    (hxp : (MulAut.conj x * uFieldAut h (n := 4) (by norm_num) σ ^ e) ^ p = 1) :
    ∃ y ∈ u4TorusSylow (f := f) (K := K) p,
      MulAut.conj y * (MulAut.conj x * uFieldAut h (n := 4) (by norm_num) σ ^ e) *
        (MulAut.conj y)⁻¹ = uFieldAut h (n := 4) (by norm_num) σ ^ e := by
  classical
  have := h.finite
  set Φ := uFieldAut h (n := 4) (by norm_num) σ with hΦ
  set b := (2 ^ f + 1).factorization p with hb
  rw [u4TorusSylow] at hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  have hdpb : d ^ (p ^ b) = 1 := by
    simpa [MonoidHom.mem_ker, powMonoidHom_apply] using hd
  have hb1 : 1 ≤ b := by
    have h := Nat.Prime.factorization_pos_of_dvd hp (by positivity) hpf
    omega
  have hnprod : ∀ n, nprod (u4TorusHom d) (Φ ^ e) n = u4TorusHom (d ^ geomN e n) := by
    intro n
    induction n with
    | zero => simp [nprod, geomN]
    | succ n ih =>
        rw [nprod, ih, geomN]
        have hFapply : (Φ ^ e) (u4TorusHom (d ^ geomN e n)) =
            u4TorusHom ((d ^ geomN e n) ^ 2 ^ e) :=
          uFieldAut_pow_u4TorusHom h hσ e (d ^ geomN e n)
        rw [hFapply, ← map_mul]
        congr 1
        rw [pow_add, pow_one, ← pow_mul, Nat.mul_comm (geomN e n) (2 ^ e)]
  have hW : (MulAut.conj (u4TorusHom d) * Φ ^ e) ^ p =
      MulAut.conj (u4TorusHom (d ^ geomN e p)) * (Φ ^ e) ^ p := by
    rw [conj_mul_pow, hnprod p]
  rw [hW] at hxp
  have hFp_range : (Φ ^ e) ^ p ∈
      (MulAut.conj : StatedProj (StatedSU 4 (2 ^ f) K) →*
        MulAut (StatedProj (StatedSU 4 (2 ^ f) K))).range := by
    have h1 : (Φ ^ e) ^ p = (MulAut.conj (u4TorusHom (d ^ geomN e p)))⁻¹ := by
      calc (Φ ^ e) ^ p = 1 * (Φ ^ e) ^ p := (one_mul _).symm
        _ = ((MulAut.conj (u4TorusHom (d ^ geomN e p)))⁻¹ *
              MulAut.conj (u4TorusHom (d ^ geomN e p))) * (Φ ^ e) ^ p := by
            rw [inv_mul_cancel]
        _ = (MulAut.conj (u4TorusHom (d ^ geomN e p)))⁻¹ *
              (MulAut.conj (u4TorusHom (d ^ geomN e p)) * (Φ ^ e) ^ p) := by
            rw [mul_assoc]
        _ = (MulAut.conj (u4TorusHom (d ^ geomN e p)))⁻¹ := by rw [hxp, mul_one]
    exact ⟨_, by rw [h1, map_inv]⟩
  have hΦep : Φ ^ (e * p) = 1 := by
    have hmem : Φ ^ (e * p) ∈
        (MulAut.conj : StatedProj (StatedSU 4 (2 ^ f) K) →*
          MulAut (StatedProj (StatedSU 4 (2 ^ f) K))).range := by
      rw [pow_mul]
      exact hFp_range
    exact uFieldAut_pow_eq_one_of_mem_range h hX hσ hmem
  have h2f : 2 * f ∣ e * p := (uFieldAut_pow_eq_one_iff h hX hσ).mp hΦep
  have hne2f : ¬ 2 * f ∣ e := fun hdvd => he ((uFieldAut_pow_eq_one_iff h hX hσ).mpr hdvd)
  obtain ⟨hpdiv, hface⟩ := factorization_two_pow_sub_one h hp hp2 hpf h2f hne2f
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0, pow_zero] at he
      exact absurd rfl he
    · exact hpos
  have hNfac : (geomN e p).factorization p = 1 := factorization_geomN hp hp2 he1 hface hpdiv
  have hFp : (Φ ^ e) ^ p = 1 := by
    rw [← pow_mul]
    exact hΦep
  have hconj1 : MulAut.conj (u4TorusHom (d ^ geomN e p)) = 1 := by
    rw [hFp, mul_one] at hxp
    exact hxp
  have huN : u4TorusHom (d ^ geomN e p) = 1 :=
    conj_injective_of_isU4 hX (by rw [hconj1, map_one])
  have hdN : d ^ geomN e p = 1 := u4TorusHom_injective h.one_le (by rw [huN, map_one])
  have hNpos : geomN e p ≠ 0 := by
    rcases p with _ | k
    · exact absurd rfl hp.ne_zero
    · exact (geomN_pos e k).ne'
  have hdp : d ^ p = 1 := by
    have hpN : p ∣ geomN e p := by
      have h := Nat.ordProj_dvd (geomN e p) p
      rw [hNfac] at h
      simpa using h
    obtain ⟨u, hu⟩ := hpN
    have hpnu : ¬ p ∣ u := by
      intro hdvd
      have h2 : p ^ 2 ∣ geomN e p := by
        rw [hu, pow_two]
        exact mul_dvd_mul_left p hdvd
      have h3 : 2 ≤ (geomN e p).factorization p :=
        (hp.pow_dvd_iff_le_factorization hNpos).mp h2
      omega
    have hgcd : Nat.gcd (geomN e p) (p ^ b) = p := by
      rw [hu, show p ^ b = p * p ^ (b - 1) by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hb1]]
      rw [Nat.gcd_mul_left]
      have hcop : Nat.Coprime u (p ^ (b - 1)) :=
        ((hp.coprime_iff_not_dvd).mpr hpnu).symm.pow_right _
      rw [show Nat.gcd u (p ^ (b - 1)) = 1 from hcop, mul_one]
    rw [← hgcd]
    exact (pow_gcd_eq_one).mpr ⟨hdN, hdpb⟩
  have hdcomp : ∀ i, ((d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) i : Kˣ) ^ p = 1 := by
    intro i
    have h1 : (d ^ p) i = 1 := by rw [hdp]; rfl
    have h2 : (d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) i ^ p = 1 := by
      simpa using congrFun hdp i
    exact congrArg (fun x : rootsOfUnity (2 ^ f + 1) K => (x : Kˣ)) h2
  choose w hw1 hw2 using fun i =>
    exists_root_of_unity_pow h hp he1 hface hpdiv (hdcomp i)
  have hdvd_b : p ^ b ∣ 2 ^ f + 1 := by
    simpa [hb] using Nat.ordProj_dvd (2 ^ f + 1) p
  let e' : Fin 3 → rootsOfUnity (2 ^ f + 1) K := fun i => ⟨w i, by
    rw [mem_rootsOfUnity]
    obtain ⟨c, hc⟩ := hdvd_b
    rw [hc, pow_mul, hw1 i, one_pow]⟩
  have he'pb : e' ^ (p ^ b) = 1 := by
    funext i
    apply Subtype.ext
    simpa [e'] using hw1 i
  have he'lam : e' ^ (2 ^ e - 1) = d := by
    funext i
    apply Subtype.ext
    simpa [e'] using hw2 i
  let y := u4TorusHom e'
  have hy : y ∈ u4TorusSylow (f := f) (K := K) p := by
    rw [u4TorusSylow]
    refine Subgroup.mem_map_of_mem _ ?_
    simpa [MonoidHom.mem_ker, powMonoidHom_apply] using he'pb
  have hyx : y ^ (2 ^ e - 1) = u4TorusHom d := by
    rw [show y = u4TorusHom e' from rfl, ← map_pow, he'lam]
  have hFy : (Φ ^ e) y = u4TorusHom (e' ^ 2 ^ e) := by
    rw [show y = u4TorusHom e' from rfl]
    exact uFieldAut_pow_u4TorusHom h hσ e e'
  have hyx1 : y * u4TorusHom d * ((Φ ^ e) y)⁻¹ = 1 := by
    have h1 : y * u4TorusHom d = u4TorusHom (e' ^ 2 ^ e) := by
      rw [← map_mul]
      congr 1
      rw [show e' ^ 2 ^ e = e' ^ (2 ^ e - 1) * e' by
        rw [← pow_succ, Nat.sub_add_cancel (by
          have h2 : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by norm_num)
          omega)]]
      rw [he'lam, mul_comm]
    rw [h1, hFy, mul_inv_cancel]
  refine ⟨y, hy, ?_⟩
  rw [conj_mul_conj_conj, hyx1, map_one, one_mul]


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
