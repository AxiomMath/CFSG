module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.UC22U3PairQ
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

private theorem exists_lift_invPairOf {X Y : Type} [Group X] [Finite X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hK : f.ker ≤ center X) {q : ℕ} (hq : q.Prime)
    (hK2 : ¬ 2 ∣ Nat.card f.ker) (hKq : ¬ q ∣ Nat.card f.ker) {c s : Y} (hc : orderOf c = q)
    (hsc : s * c * s⁻¹ = c⁻¹) (hs2 : s ^ 2 = 1) :
    ∃ x g : X, orderOf x = q ∧ g * x * g⁻¹ = x⁻¹ ∧ ∀ b : X, f b * c = c * f b →
      f b * s = s * f b → b * x = x * b ∧ b * g = g * b := by
  haveI : Fact q.Prime := ⟨hq⟩
  set m := Nat.card f.ker with hm
  have hkm : ∀ z ∈ f.ker, z ^ m = 1 := fun z hz =>
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : f.ker)))
  have huniq : ∀ {j : ℕ}, Nat.Coprime m j → ∀ {e e' : X}, e ^ j = 1 → e' ^ j = 1 →
      f e = f e' → e = e' := fun hj e e' he he' hfe =>
    CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime f hK hj (a := 1) (b := 1)
      (by rw [pow_one]; exact he) (by rw [pow_one]; exact he') hfe
  have hcq : Nat.Coprime m q := Nat.coprime_comm.1 (hq.coprime_iff_not_dvd.2 hKq)
  have hc2 : Nat.Coprime m 2 := Nat.coprime_comm.1 (Nat.prime_two.coprime_iff_not_dvd.2 hK2)
  obtain ⟨x₀, hx₀⟩ := hf c
  obtain ⟨g₀, hg₀⟩ := hf s
  have hxq : (x₀ ^ m) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hkm _ (by rw [MonoidHom.mem_ker, map_pow, hx₀, ← hc, pow_orderOf_eq_one])
  have hx1 : x₀ ^ m ≠ 1 := fun h => hKq (by
    rw [← hc]
    exact orderOf_dvd_of_pow_eq_one (by rw [← hx₀, ← map_pow, h, map_one]))
  have hg2 : (g₀ ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hkm _ (by rw [MonoidHom.mem_ker, map_pow, hg₀, hs2])
  have hsm : s ^ m = s := by
    obtain ⟨r, hr⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hK2)
    rw [hr, pow_succ, pow_mul, hs2, one_pow, one_mul]
  have hfx : f (x₀ ^ m) = c ^ m := by rw [map_pow, hx₀]
  have hfg : f (g₀ ^ m) = s := by rw [map_pow, hg₀, hsm]
  refine ⟨x₀ ^ m, g₀ ^ m, orderOf_eq_prime hxq hx1, ?_, fun b hbc hbs => ⟨?_, ?_⟩⟩
  · refine huniq hcq (by rw [conj_pow, hxq, mul_one, mul_inv_cancel])
      (by rw [inv_pow, hxq, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hfx, hfg, ← conj_pow, hsc, inv_pow]
  · refine mul_inv_eq_iff_eq_mul.1 (huniq hcq (by rw [conj_pow, hxq, mul_one, mul_inv_cancel])
      hxq ?_)
    rw [map_mul, map_mul, map_inv, hfx, ← conj_pow, hbc, mul_inv_cancel_right]
  · refine mul_inv_eq_iff_eq_mul.1 (huniq hc2 (by rw [conj_pow, hg2, mul_one, mul_inv_cancel])
      hg2 ?_)
    rw [map_mul, map_mul, map_inv, hfg, hbs, mul_inv_cancel_right]

theorem R847E3.exists_invPairOf_index_le (hgr : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {n : ℕ} (hX : IsSU3 X n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ n + 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1)
    {P : Type} [Group P] (hexp : ∀ u : P, u ^ p = 1) (φ : P →* MulAut X)
    (hinn : φ.range ≤ (MulAut.conj : X →* MulAut X).range) :
    ∃ x g : X, orderOf x = q ∧ g * x * g⁻¹ = x⁻¹ ∧
      ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x ∧ φ u g = g := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn2, K, _, h, ⟨θ⟩⟩ := U3Loss.exists_equiv_primeFormP hX.2
  let f := θ.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hf : Function.Surjective f := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker = center X := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hK2 : ¬ 2 ∣ Nat.card f.ker := fun h2 => by
    rw [hfk] at h2
    have h3 := (h2.trans (uc22ine229_card_center_dvd hgr hX)).trans (Nat.gcd_dvd_left 3 _)
    omega
  have hKq : ¬ q ∣ Nat.card f.ker := by
    rw [hfk]
    exact uc22ine229_not_dvd_card_center hgr hX hq hq2 hqn
  have hrp : ∀ r ∈ φ.range, r ^ p = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_pow, hexp, map_one]
  by_cases hRp : Nat.card φ.range ≤ p
  ·
    obtain ⟨c, s, hc, hsc, hs2, -⟩ := U3Aut.exists_invPairOf_commute_line h hq hqn (d := 1)
      (by rw [map_one, map_one])
    obtain ⟨x, g, hx, hgx, -⟩ := exists_lift_invPairOf f hf hfk.le hq hK2 hKq hc hsc hs2
    refine ⟨x, g, hx, hgx, φ.ker, by rw [Subgroup.index_ker]; exact hRp, fun u hu => ?_⟩
    rw [MonoidHom.mem_ker.1 hu]
    exact ⟨rfl, rfl⟩
  rw [not_le] at hRp
  have hpR : IsPGroup p φ.range := fun r =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hrp _ r.2, Subgroup.coe_one])⟩
  obtain ⟨j, hj⟩ := hpR.exists_card_eq
  have hR2 : p ^ 2 ≤ Nat.card φ.range := by
    rw [hj] at hRp ⊢
    refine Nat.pow_le_pow_right hp.pos (by_contra fun hlt => ?_)
    exact absurd hRp (not_lt.2 ((Nat.pow_le_pow_right hp.pos (by omega : j ≤ 1)).trans
      (pow_one p).le))
  let ι := (UCK.innerEquivQuot X).trans θ
  let J := (φ.range.subgroupOf (MulAut.conj : X →* MulAut X).range).map ι.toMonoidHom
  have hJc : Nat.card J = Nat.card φ.range := by
    rw [Subgroup.card_map_of_injective ι.injective,
      Nat.card_congr (subgroupOfEquivOfLe hinn).toEquiv]
  have hJp : ∀ y ∈ J, y ^ p = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, show r ^ p = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, hrp _ (Subgroup.mem_subgroupOf.1 hr), Subgroup.coe_one]), map_one]
  have hJle := U3Aut.card_le_of_pow_eq_one h hn2 hp hp5 hpn hJp
  obtain ⟨t, ht, ht1, c, s, hc, hsc, hs2, hct, hst⟩ :=
    U3Aut.exists_commute_invPairOf h hn2 hp hp5 hpn hq hqn hJp (by rw [hJc]; exact hR2)
  obtain ⟨x, g, hx, hgx, hcomm⟩ := exists_lift_invPairOf f hf hfk.le hq hK2 hKq hc hsc hs2
  obtain ⟨⟨_, x₀, rfl⟩, hrR, rfl⟩ := ht
  have hft : ι.toMonoidHom ⟨MulAut.conj x₀, MonoidHom.mem_range.2 ⟨x₀, rfl⟩⟩ = f x₀ := by
    have h0 : UCK.innerEquivQuot X ⟨MulAut.conj x₀, MonoidHom.mem_range.2 ⟨x₀, rfl⟩⟩ =
        (x₀ : X ⧸ center X) := (MulEquiv.eq_symm_apply _).1 rfl
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, h0]
    rfl
  rw [hft] at hct hst ht1
  obtain ⟨hx₀x, hx₀g⟩ := hcomm x₀ hct.symm hst.symm
  have hr1 : MulAut.conj x₀ ≠ 1 := fun h1 => ht1 (by
    rw [← MonoidHom.mem_ker, hfk, mem_center_iff]
    intro y
    have hy := DFunLike.congr_fun h1 y
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hy
    exact hy.symm)
  have hrR' : MulAut.conj x₀ ∈ φ.range := Subgroup.mem_subgroupOf.1 hrR
  set r : φ.range := ⟨MulAut.conj x₀, hrR'⟩ with hr
  have hro : orderOf r = p :=
    orderOf_eq_prime (Subtype.ext (hrp _ hrR')) fun h1 => hr1 (congrArg Subtype.val h1)
  have hfix : MulAut.conj x₀ ∈
      MulAction.stabilizer (MulAut X) x ⊓ MulAction.stabilizer (MulAut X) g :=
    mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 (by
      rw [MulAut.smul_def, MulAut.conj_apply, hx₀x, mul_inv_cancel_right]),
      MulAction.mem_stabilizer_iff.2 (by
        rw [MulAut.smul_def, MulAut.conj_apply, hx₀g, mul_inv_cancel_right])⟩
  refine ⟨x, g, hx, hgx, (zpowers r).comap φ.rangeRestrict, ?_, fun u hu => ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective]
    have h1 := Subgroup.card_mul_index (zpowers r)
    rw [Nat.card_zpowers, hro] at h1
    have h2 : Nat.card φ.range ≤ p * p := by rw [← sq, ← hJc]; exact hJle
    exact Nat.le_of_mul_le_mul_left (by rw [h1]; exact h2) hp.pos
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (Subgroup.mem_comap.1 hu)
    have hk' : MulAut.conj x₀ ^ k = φ u := by
      have h1 := congrArg Subtype.val hk
      rwa [Subgroup.coe_zpow, MonoidHom.coe_rangeRestrict] at h1
    have hmem := Subgroup.zpow_mem _ hfix k
    rw [hk'] at hmem
    exact ⟨by simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 (mem_inf.1 hmem).1,
      by simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 (mem_inf.1 hmem).2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
