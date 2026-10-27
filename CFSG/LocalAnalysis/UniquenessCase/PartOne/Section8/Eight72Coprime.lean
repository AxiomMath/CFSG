module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {G : Type} [Group G] [Finite G]

theorem eight72_exists_fixed_of_coprime {K B : Subgroup G} (hBN : B ≤ normalizer (K : Set G))
    {p r : ℕ} (hp : p.Prime) (hB : IsPGroup p B) (hpK : ¬ p ∣ Nat.card (Bar2 K)) (hr : r.Prime)
    (hpr : Nat.Coprime p (r - 1)) (hrK : r ∣ Nat.card (Bar2 K))
    (hcyc : ∀ S : Sylow r (Bar2 K), IsCyclic (S : Subgroup (Bar2 K))) :
    ∃ V : Subgroup (Bar2 K), Nat.card V = r ∧
      ∀ b (hb : b ∈ B), ∀ v ∈ V, UC6S846.rhoL K ⟨b, hBN hb⟩ v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (Bar2 K) := inferInstance
  let ψ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  let : MulAction (MulAut (Bar2 K)) (Sylow r (Bar2 K)) := Sylow.pointwiseMulAction
  let : MulAction (MulAut (Bar2 K)) (Subgroup (Bar2 K)) := Subgroup.pointwiseMulAction
  let : MulAction ↥B (Sylow r (Bar2 K)) := MulAction.compHom _ ψ
  have : Finite (Sylow r (Bar2 K)) :=
    Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty (p := r) (G := Bar2 K)))
  have hnotdvd : ¬ p ∣ Nat.card (Sylow r (Bar2 K)) := by
    intro hdiv
    let P : Sylow r (Bar2 K) := Classical.choice (Sylow.nonempty (p := r) (G := Bar2 K))
    exact hpK (hdiv.trans ((Sylow.card_dvd_index P).trans
      (P : Subgroup (Bar2 K)).index_dvd_card))
  obtain ⟨S, hSfix⟩ :=
    hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r (Bar2 K)) hnotdvd
  have hSinv : ∀ b : ↥B, ((ψ b) • (S : Subgroup (Bar2 K))) = (S : Subgroup (Bar2 K)) := by
    intro b
    have hb := MulAction.mem_fixedPoints.mp hSfix b
    have h' : (↑((ψ b) • S) : Subgroup (Bar2 K)) = (S : Subgroup (Bar2 K)) := by
      rw [MulAction.compHom_smul_def] at hb
      exact congrArg (fun T : Sylow r (Bar2 K) => (T : Subgroup (Bar2 K))) hb
    rwa [Sylow.pointwise_smul_def] at h'
  have hrS : r ∣ Nat.card ↥(S : Subgroup (Bar2 K)) :=
    Sylow.dvd_card_of_dvd_card S hrK
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' r hrS
  have hScyc : IsCyclic ↥(S : Subgroup (Bar2 K)) := hcyc S
  have hmemS : ∀ b : ↥B, (ψ b) (s : Bar2 K) ∈ (S : Subgroup (Bar2 K)) := by
    intro b
    have hmem := Subgroup.smul_mem_pointwise_smul (s : Bar2 K) (ψ b)
      (S : Subgroup (Bar2 K)) s.2
    rw [hSinv b] at hmem
    simpa [MulAut.smul_def] using hmem
  have hfix_all : ∀ b : ↥B, (ψ b) (s : Bar2 K) = (s : Bar2 K) := by
    intro b
    have hord : orderOf ((ψ b) (s : Bar2 K)) = r := by
      simp [hs]
    have hcard1 : Nat.card ↥(Subgroup.zpowers
        (⟨(ψ b) (s : Bar2 K), hmemS b⟩ : ↥S)) = r := by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
      exact hord
    have hcard2 : Nat.card ↥(Subgroup.zpowers s) = r := by
      rw [Nat.card_zpowers, hs]
    have hVeq : Subgroup.zpowers (⟨(ψ b) (s : Bar2 K), hmemS b⟩ : ↥S) =
        Subgroup.zpowers s :=
      (hScyc.subgroup_eq_iff_card_eq).mpr (hcard1.trans hcard2.symm)
    have hmem : (⟨(ψ b) (s : Bar2 K), hmemS b⟩ : ↥S) ∈ Subgroup.zpowers s := by
      rw [← hVeq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (s : Bar2 K) ^ k = (ψ b) (s : Bar2 K) := by
      simpa using congrArg (fun x : ↥S => (x : Bar2 K)) hk
    have hfin : IsOfFinOrder (s : Bar2 K) := isOfFinOrder_of_finite _
    have hmem_pow : (ψ b) (s : Bar2 K) ∈ Submonoid.powers (s : Bar2 K) := by
      rw [IsOfFinOrder.mem_powers_iff_mem_zpowers hfin]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩
    obtain ⟨n, hn⟩ := hmem_pow
    have hn' : (s : Bar2 K) ^ n = (ψ b) (s : Bar2 K) := hn
    have hind : ∀ m : ℕ, ((ψ b) ^ m) (s : Bar2 K) = (s : Bar2 K) ^ (n ^ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_pow, ← hn', ← pow_mul, mul_comm,
            ← pow_succ]
    obtain ⟨e, he⟩ := hB.exists_orderOf_eq_pow b
    have hαpow : (ψ b) ^ (p ^ e) = 1 := by
      rw [← map_pow, ← he, pow_orderOf_eq_one, map_one]
    have hfixs : (ψ b) (s : Bar2 K) = (s : Bar2 K) := by
      have h1 : (s : Bar2 K) ^ (n ^ (p ^ e)) = (s : Bar2 K) := by
        have h := hind (p ^ e)
        rw [hαpow] at h
        simpa using h.symm
      have hord_s : orderOf (s : Bar2 K) = r := by rw [Subgroup.orderOf_coe, hs]
      have hmod : n ^ (p ^ e) ≡ 1 [MOD r] := by
        have h := (pow_eq_pow_iff_modEq (x := (s : Bar2 K))
          (n := n ^ (p ^ e)) (m := 1)).mp (by simpa using h1)
        simpa [hord_s] using h
      have hxpow : ((n : ZMod r) ^ (p ^ e)) = 1 := by
        rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hmod
      have hxne : (n : ZMod r) ≠ 0 := by
        intro h0
        have hzero : ((n : ZMod r) ^ (p ^ e)) = 0 := by
          rw [h0, zero_pow (pow_ne_zero e hp.ne_zero)]
        rw [hxpow] at hzero
        exact one_ne_zero hzero
      have hfermat : (n : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hxne
      have hx1 : (n : ZMod r) = 1 :=
        (pow_eq_one_iff_of_coprime (a := (n : ZMod r)) (hpr.pow_left e)).mp
          ⟨hxpow, hfermat⟩
      have hx1' : (n : ZMod r) = ((1 : ℕ) : ZMod r) := by simpa using hx1
      have hmod1 : n ≡ 1 [MOD r] := (ZMod.natCast_eq_natCast_iff n 1 r).mp hx1'
      have hpow : (s : Bar2 K) ^ n = (s : Bar2 K) ^ 1 := by
        apply (pow_eq_pow_iff_modEq (x := (s : Bar2 K))).mpr
        rwa [hord_s]
      rw [← hn', hpow, pow_one]
    exact hfixs
  refine ⟨Subgroup.zpowers (s : Bar2 K), ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hs]
  · intro b hb v hv
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hmap : (ψ ⟨b, hb⟩) v = v := by
      rw [← hm, map_zpow, hfix_all ⟨b, hb⟩]
    change (ψ ⟨b, hb⟩) v = v
    exact hmap

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
