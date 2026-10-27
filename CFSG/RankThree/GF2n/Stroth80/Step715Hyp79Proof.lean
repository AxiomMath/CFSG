module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2XActs
public import CFSG.RankThree.GF2n.Stroth80.Sec85CommMod
public import CFSG.RankThree.GF2n.Stroth80.OrderThreeOrbit
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarConj
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormLB
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIFitting
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIGen
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIHyp79
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.VBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Orbit

variable {X : Type*} [Group X]

theorem exists_commute_mul_inv_of_orbit {N Z : Subgroup X} {x y : X} (hZN : Z ≤ N)
    (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z) (hZc : ∀ a ∈ Z, ∀ b ∈ N, Commute a b)
    (hZ2 : ∀ a ∈ Z, a * a = 1) (hxN : ∀ m ∈ N, ⁅m, x⁆ ∈ Z) (hxZ : ∀ a ∈ Z, Commute a x)
    (hy3 : y ^ 3 = 1) (hyN : ∀ m ∈ N, y * m * y⁻¹ ∈ N) (hyZ : ∀ a ∈ Z, Commute y a)
    (hyC : ∀ m ∈ N, Commute y m → m ∈ Z) (hxy : ⁅x⁻¹, y⁻¹⁆ ∈ N) :
    ∃ d ∈ N, ∀ m ∈ N, Commute m (x * d⁻¹) := by
  have hyyy : y * y * y = 1 := by
    rw [← pow_three', hy3]
  have hyinv : y⁻¹ = y * y := by
    calc y⁻¹ = y⁻¹ * (y * y * y) := by rw [hyyy, mul_one]
      _ = y * y := by group
  have hyy : ∀ m : X, y⁻¹ * m * y = y * (y * m * y⁻¹) * y⁻¹ := by
    intro m
    calc y⁻¹ * m * y = (y * y) * m * (y * y)⁻¹ := by rw [← hyinv, inv_inv]
      _ = y * (y * m * y⁻¹) * y⁻¹ := by group
  have hyN' : ∀ m ∈ N, y⁻¹ * m * y ∈ N := fun m hm => by
    rw [hyy]
    exact hyN _ (hyN m hm)
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b := fun a ha b hb => hZc a ha b (hZN hb)
  have hyZ' : ∀ a ∈ Z, y * a * y⁻¹ = a := fun a ha => (hyZ a ha).mul_inv_cancel
  have hxZ' : ∀ a ∈ Z, x * a * x⁻¹ = a := fun a ha => (hxZ a ha).symm.mul_inv_cancel
  set c : X := ⁅x⁻¹, y⁻¹⁆ with hcdef
  have hcN : c ∈ N := hxy
  have hxc : y⁻¹ * x * y = x * c := by
    rw [hcdef, commutatorElement_def]
    group
  set d : X := y⁻¹ * c * y with hddef
  have hdN : d ∈ N := hyN' c hcN
  have hconj : ∀ m ∈ N, ⁅y * m * y⁻¹, x⁆ = ⁅m, x⁆ * ⁅m, c⁆ := by
    intro m hm
    have e1 : ⁅y * m * y⁻¹, x⁆ = y * ⁅m, y⁻¹ * x * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅m, x * c⁆ = ⁅m, x⁆ * ⁅m, c⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      calc ⁅m, x⁆ * x * ⁅m, c⁆ * x⁻¹ = ⁅m, x⁆ * (x * ⁅m, c⁆ * x⁻¹) := by group
        _ = ⁅m, x⁆ * ⁅m, c⁆ := by rw [hxZ' _ (hNN m hm c hcN)]
    rw [e1, hxc, e2, hyZ' _ (Z.mul_mem (hxN m hm) (hNN m hm c hcN))]
  have horbit : ∀ m ∈ N, m * (y * m * y⁻¹) * (y⁻¹ * m * y) ∈ Z := by
    intro m hm
    have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 → z = 1 := fun z hz h3 => by
      rwa [pow_three, hZ2 z hz, mul_one] at h3
    have h := orbit_prod_mem_of_order_three hZ3 hNN hy3 hyN (fun z hz => (hyZ z hz).eq)
      (fun a ha h => hyC a ha h) hm
    have e : y ^ 2 * m * (y ^ 2)⁻¹ = y⁻¹ * m * y := by rw [pow_two, ← hyinv, inv_inv]
    rwa [e] at h
  have hmul : ∀ a ∈ N, ∀ b ∈ N, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb
    rw [commutatorElement_mul_left_eq_conj_mul, (hZc _ (hxN b hb) a ha).symm.mul_inv_cancel]
    exact (hZab _ (hxN b hb) _ (hxN a ha)).eq
  have hsq3 : ∀ a ∈ Z, ∀ b ∈ Z, ∀ e : X, a * (a * b) * (a * b * e) = a * e := by
    intro a ha b hb e
    have hba : b * a = a * b := (hZab b hb a ha).eq
    calc a * (a * b) * (a * b * e) = a * a * (b * a) * b * e := by group
      _ = a * a * (a * b) * b * e := by rw [hba]
      _ = (a * a) * a * (b * b) * e := by group
      _ = a * e := by rw [hZ2 a ha, hZ2 b hb]; group
  have hkey : ∀ m ∈ N, ⁅m, x⁆ = ⁅m, d⁆ := by
    intro m hm
    have hm1 : y * m * y⁻¹ ∈ N := hyN m hm
    have hu := horbit m hm
    have h0 : ⁅m * (y * m * y⁻¹) * (y⁻¹ * m * y), x⁆ = 1 := (hxZ _ hu).commutator_eq
    rw [hmul _ (N.mul_mem hm hm1) _ (hyN' m hm), hmul _ hm _ hm1, hyy m,
      hconj _ hm1, hconj _ hm] at h0
    have haZ := hxN m hm
    have hbZ := hNN m hm c hcN
    have heZ := hNN _ hm1 c hcN
    have h1 : ⁅m, x⁆ * ⁅y * m * y⁻¹, c⁆ = 1 := by
      rw [← hsq3 _ haZ _ hbZ]
      exact h0
    have h2 : ⁅m, x⁆ = ⁅y * m * y⁻¹, c⁆ := by
      have h3 : ⁅m, x⁆ = ⁅y * m * y⁻¹, c⁆⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h3, inv_eq_of_mul_eq_one_left (hZ2 _ heZ)]
    have h4 : ⁅y * m * y⁻¹, c⁆ = y * ⁅m, d⁆ * y⁻¹ := by
      rw [hddef]
      simp only [commutatorElement_def]
      group
    rw [h2, h4, hyZ' _ (hNN m hm d hdN)]
  refine ⟨d, hdN, fun m hm => ?_⟩
  have hm' : ⁅m, d⁻¹⁆ ∈ Z := hNN m hm _ (N.inv_mem hdN)
  have hdd : ⁅m, d⁆ * ⁅m, d⁻¹⁆ = 1 := by
    have h := commutatorElement_mul_right_eq_mul_conj m d d⁻¹
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    calc ⁅m, d⁆ * ⁅m, d⁻¹⁆ = ⁅m, d⁆ * (d * ⁅m, d⁻¹⁆ * d⁻¹) := by
          rw [(hZc _ hm' d hdN).symm.mul_inv_cancel]
      _ = ⁅m, d⁆ * d * ⁅m, d⁻¹⁆ * d⁻¹ := by group
      _ = 1 := h.symm
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_mul_right_eq_mul_conj]
  calc ⁅m, x⁆ * x * ⁅m, d⁻¹⁆ * x⁻¹ = ⁅m, x⁆ * (x * ⁅m, d⁻¹⁆ * x⁻¹) := by group
    _ = ⁅m, d⁆ * ⁅m, d⁻¹⁆ := by rw [hxZ' _ hm', hkey m hm]
    _ = 1 := hdd

end Orbit

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec715_comm_CN_mem_Z0 [(Q.subgroupOf M).Normal] (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hCommN : Sec7CommNStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hIrr : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t) :
    ∀ d ∈ O2NormPre M Q Z Z0, ∀ m ∈ hc.CN t, ⁅d, m⁆ ∈ Z0 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hD2, hDK, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hsq : ∀ x ∈ hc.CN t, x ^ 2 ∈ Z0 := hopp.2.2.2.2.2.2.2.1
  have hcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := fun x hx y hy =>
    hCommN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hx hy)
  have hKN : ∀ k ∈ NormH0 M Z Z0, ∀ x ∈ hc.CN t, k * x * k⁻¹ ∈ hc.CN t := fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp
      (sec7_conj_CN_eq hZt hZcard hc hs hZ0 hk)) x).mp hx
  have hKZ : ∀ k ∈ NormH0 M Z Z0, ∀ z ∈ Z0, k * z * k⁻¹ ∈ Z0 := fun k hk z hz =>
    (Subgroup.mem_normalizer_iff.mp hk.2 z).mp hz
  have hNZ : ∀ p ∈ hc.CN t, ∀ i ∈ Z0, p * i * p⁻¹ ∈ Z0 := fun p hp i hi =>
    hKZ p (sec8_Rt_le_NormH0 hc hZ0 (Ctx.mem_CN.mp hp).1) i hi
  have hsec : SecHyp (O2NormPre M Q Z Z0) (hc.CN t) Z0 :=
    ⟨hZN, hcomm, hsq, fun d hd x hx => hKN d (hDK hd) x hx, fun d hd z hz => hKZ d (hDK hd) z hz⟩
  have hlt : Z0 < hc.CN t := by
    refine lt_of_le_of_ne hZN fun h => ?_
    have h1 := hs.large
    rw [← h, hZcard G M Q Z B hc n t hs Z0 hZ0] at h1
    exact lt_irrefl _ h1
  obtain ⟨y, hyN, hyZ, hyD⟩ := exists_fixed_sec_of_isPGroup hD2 hsec hlt
  have hZC : Z0 ≤ secCentPre (O2NormPre M Q Z Z0) (hc.CN t) Z0 hNZ := fun z hz =>
    ⟨hZN hz, fun d hd => by
      rw [commutatorElement_def]
      exact Z0.mul_mem (hKZ d (hDK hd) z hz) (Z0.inv_mem hz)⟩
  have hle : ∀ g ∈ NormH0 M Z Z0, conjSubgroup g (secCentPre (O2NormPre M Q Z Z0) (hc.CN t)
      Z0 hNZ) ≤ secCentPre (O2NormPre M Q Z Z0) (hc.CN t) Z0 hNZ := by
    intro g hg x hx
    rw [mem_conjSubgroup] at hx
    have h1 := secCentPre_conj_mem (r := g)
      (fun d hd => by simpa using conj_mem_O2NormPre ((NormH0 M Z Z0).inv_mem hg) hd)
      (fun p hp => hKN g hg p hp) (fun i hi => hKZ g hg i hi) hx
    simpa [mul_assoc] using h1
  have hCinv : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k (secCentPre (O2NormPre M Q Z Z0) (hc.CN t)
      Z0 hNZ) = secCentPre (O2NormPre M Q Z Z0) (hc.CN t) Z0 hNZ := fun k hk =>
    Subgroup.eq_of_le_of_card_ge (hle k hk) (by rw [card_conjSubgroup])
  rcases hIrr _ hZC (fun x hx => hx.1) hCinv with h | h
  · exfalso
    have hyC : y ∈ secCentPre (O2NormPre M Q Z Z0) (hc.CN t) Z0 hNZ := ⟨hyN, hyD⟩
    rw [h] at hyC
    exact hyZ hyC
  · intro d hd m hm
    have hmC : m ∈ secCentPre (O2NormPre M Q Z Z0) (hc.CN t) Z0 hNZ := by
      rw [h]
      exact hm
    exact hmC.2 d hd

theorem sec715_comm_Z0_mem_Q [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {d : G} (hdK : d ∈ NormH0 M Z Z0)
    (hd2 : ∃ k : ℕ, d ^ 2 ^ k ∈ Q) : ∀ z ∈ Z0, ⁅z, d⁆ ∈ Q := by
  classical
  obtain ⟨k, hk⟩ := hd2
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hdM : d ∈ M := hdK.1.1
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, -, hρinj, ψ, hψ, -, hAct, -⟩ :=
    sec7_linModelData h34 h310chi hc hs hZ0
      (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
      (fun u hu huQ => hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ)
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  let dm : ↥M := ⟨d, hdM⟩
  let tm : ↥M := ⟨t, htM⟩
  have hdH : ∀ j : ℕ, QuotientGroup.mk' (Q.subgroupOf M) dm ^ j ∈ bar M Q (H0 M Z) := fun j =>
    (bar M Q (H0 M Z)).pow_mem
      (Subgroup.mem_map.mpr ⟨dm, Subgroup.mem_subgroupOf.mpr hdK.1, rfl⟩) j
  have hdt : QuotientGroup.mk' (Q.subgroupOf M) dm * QuotientGroup.mk' (Q.subgroupOf M) tm *
      (QuotientGroup.mk' (Q.subgroupOf M) dm)⁻¹ ∈ bar M Q Z0 := by
    have h1 : d * t * d⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hdK.2 t).mp htZ0
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr h1, rfl⟩
  obtain ⟨c, hc'⟩ := hAct _ hdt
  have hkey : ∀ e, (ρ (QuotientGroup.mk' (Q.subgroupOf M) dm)).toAdd (ψ e) =
      c • ψ ((ρ (QuotientGroup.mk' (Q.subgroupOf M) dm)).toAdd e) := by
    intro e
    have h1 := hc' ((ρ (QuotientGroup.mk' (Q.subgroupOf M) dm)).toAdd e)
    rw [act_mul_apply, act_mul_apply, ← act_mul_apply ρ _ (QuotientGroup.mk' (Q.subgroupOf M) dm),
      inv_mul_cancel, map_one] at h1
    have h2 : (ρ (QuotientGroup.mk' (Q.subgroupOf M) tm)).toAdd e = e + ψ e := by
      rw [hψ]
      abel
    change (ρ (QuotientGroup.mk' (Q.subgroupOf M) dm)).toAdd
      ((ρ (QuotientGroup.mk' (Q.subgroupOf M) tm)).toAdd e) = _ at h1
    rw [h2, map_add] at h1
    exact add_left_cancel h1
  have hiter : ∀ j : ℕ, ∀ e, (ρ (QuotientGroup.mk' (Q.subgroupOf M) dm ^ j)).toAdd (ψ e) =
      c ^ j • ψ ((ρ (QuotientGroup.mk' (Q.subgroupOf M) dm ^ j)).toAdd e) := by
    intro j
    induction j with
    | zero => intro e; simp
    | succ j ih =>
      intro e
      rw [pow_succ, act_mul_apply, act_mul_apply, hkey, hS.lin _ (hdH j), ih, smul_smul,
        pow_succ']
  have hdk : QuotientGroup.mk' (Q.subgroupOf M) dm ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  obtain ⟨e₀, he₀⟩ : ∃ e, ψ e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) tm = 1 := hρinj _ _ fun e => by
      have := hψ e
      rw [hcon e] at this
      rw [map_one]
      exact (sub_eq_zero.mp this.symm)
    exact hs.toSec5.notQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  have hc1 : c = 1 := by
    have h1 := hiter (2 ^ k) e₀
    rw [hdk, map_one] at h1
    have h2 : (c ^ 2 ^ k - 1) • ψ e₀ = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr h1.symm
    have h3 : c ^ 2 ^ k - 1 = 0 := (smul_eq_zero.mp h2).resolve_right he₀
    have h4 : (c - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, one_pow, h3]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h4)
  intro z hz
  have hzM : z ∈ M := hc.centre_le_M t hZ0 hz
  let zm : ↥M := ⟨z, hzM⟩
  have hzbar : QuotientGroup.mk' (Q.subgroupOf M) zm ∈ bar M Q Z0 :=
    Subgroup.mem_map.mpr ⟨zm, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  obtain ⟨cz, hcz⟩ := hAct _ hzbar
  have hcomm : QuotientGroup.mk' (Q.subgroupOf M) zm * QuotientGroup.mk' (Q.subgroupOf M) dm =
      QuotientGroup.mk' (Q.subgroupOf M) dm * QuotientGroup.mk' (Q.subgroupOf M) zm := by
    refine hρinj _ _ fun e => ?_
    rw [act_mul_apply, act_mul_apply, hcz, hcz, map_add, hS.lin _ (by simpa using hdH 1),
      hkey, hc1, one_smul]
  exact (mk_commute_iff zm dm).mp hcomm

theorem sec715_CN_le_O2NormPre [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    hc.CN t ≤ O2NormPre M Q Z Z0 := by
  intro m hm
  have hmR : m ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hm).1
  have hmM : m ∈ M := hc.Rt_le_M t hmR
  have hmK : m ∈ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0 hmR
  let mm : ↥M := ⟨m, hmM⟩
  have hH : QuotientGroup.mk' (Q.subgroupOf M) mm ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨mm, Subgroup.mem_subgroupOf.mpr hmK.1, rfl⟩
  have hK : (⟨QuotientGroup.mk' (Q.subgroupOf M) mm, hH⟩ : Hbar M Q Z) ∈ MbarPrime M Q Z Z0 :=
    Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map.mpr ⟨mm, Subgroup.mem_subgroupOf.mpr hmK, rfl⟩)
  have hmem : (⟨⟨QuotientGroup.mk' (Q.subgroupOf M) mm, hH⟩, hK⟩ : ↥(MbarPrime M Q Z Z0)) ∈
      pCore 2 ↥(MbarPrime M Q Z Z0) :=
    CN_le_pCore_two_MbarPrime h34 h51 hA hZt hZcard hc hs hZ0
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨mm, Subgroup.mem_subgroupOf.mpr hm, rfl⟩)))
  exact mem_O2NormPre.mpr ⟨hmM, _, hmem, rfl⟩

theorem sec715_O2NormPre_le_CN [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hY : Sec713YStatement)
    (hCent : Sec715CentStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hIrr : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t) :
    O2NormPre M Q Z Z0 ≤ hc.CN t := by
  classical
  intro x hx
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨hD2, hDK, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hNR : ∀ m ∈ hc.CN t, m ∈ Rt M (LB M Q B) t := fun m hm => (Ctx.mem_CN.mp hm).1
  have hND : hc.CN t ≤ O2NormPre M Q Z Z0 :=
    sec715_CN_le_O2NormPre h34 h51 hA hZt hZcard hc hs hZ0
  have hxM : x ∈ M := (hDK hx).1.1
  have hxN := sec715_comm_CN_mem_Z0 h51 hA hZt hZcard hCommN hc hs hZ0 hIrr x hx
  have hx2 : ∃ k : ℕ, x ^ 2 ^ k ∈ Q := by
    obtain ⟨k, hk⟩ := hD2 ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Q.one_mem
  have hxZ := sec715_comm_Z0_mem_Q h34 h310chi hZc hZV hc hs hZ0 (hDK hx) hx2
  obtain ⟨y, hyR, -, hy3, hyC⟩ := hY G M Q Z B hc n t hs Z0 hZ0
  have hyM : y ∈ M := hRM hyR
  let xm : ↥M := ⟨x, hxM⟩
  let ym : ↥M := ⟨y, hyM⟩
  have hZN' : bar M Q Z0 ≤ bar M Q (hc.CN t) := bar_mono' hZN.le
  have hNN' : ∀ a ∈ bar M Q (hc.CN t), ∀ b ∈ bar M Q (hc.CN t), ⁅a, b⁆ ∈ bar M Q Z0 := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_bar_iff_exists_lift.mp hb
    rw [← map_commutatorElement]
    exact mem_bar_iff_exists_lift.mpr ⟨⁅a', b'⁆,
      hCommN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator ha' hb'), rfl⟩
  have hZc' : ∀ a ∈ bar M Q Z0, ∀ b ∈ bar M Q (hc.CN t), Commute a b := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_bar_iff_exists_lift.mp hb
    exact (mk_commute_iff a' b').mpr (hZ0.comm_mem ha' (hNR _ hb'))
  have hZ2' : ∀ a ∈ bar M Q Z0, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    have hsq : (a' : G) ^ 2 ∈ Q :=
      hc.sq_mem_Q_of_mem_LB (hZc G M Q Z B hc n t hs Z0 hZ0 _ ha').1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hsq))
  have hxN' : ∀ m ∈ bar M Q (hc.CN t),
      ⁅m, QuotientGroup.mk' (Q.subgroupOf M) xm⁆ ∈ bar M Q Z0 := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    rw [← map_commutatorElement]
    refine mem_bar_iff_exists_lift.mpr ⟨⁅m', xm⁆, ?_, rfl⟩
    have h := Z0.inv_mem (hxN _ hm')
    rwa [commutatorElement_inv] at h
  have hxZ' : ∀ a ∈ bar M Q Z0, Commute a (QuotientGroup.mk' (Q.subgroupOf M) xm) := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    exact (mk_commute_iff a' xm).mpr (hxZ _ ha')
  have hy3' : QuotientGroup.mk' (Q.subgroupOf M) ym ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hy3))
  have hyN' : ∀ m ∈ bar M Q (hc.CN t), QuotientGroup.mk' (Q.subgroupOf M) ym * m *
      (QuotientGroup.mk' (Q.subgroupOf M) ym)⁻¹ ∈ bar M Q (hc.CN t) := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_bar_iff_exists_lift.mpr ⟨ym * m' * ym⁻¹, hc.CN_conj_mem ht hyR hm', rfl⟩
  have hyZ' : ∀ a ∈ bar M Q Z0, Commute (QuotientGroup.mk' (Q.subgroupOf M) ym) a := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_bar_iff_exists_lift.mp ha
    exact ((mk_commute_iff a' ym).mpr (hZ0.comm_mem ha' hyR)).symm
  have hyC' : ∀ m ∈ bar M Q (hc.CN t), Commute (QuotientGroup.mk' (Q.subgroupOf M) ym) m →
      m ∈ bar M Q Z0 := by
    intro m hm hcm
    obtain ⟨m', hm', rfl⟩ := mem_bar_iff_exists_lift.mp hm
    exact mem_bar_iff_exists_lift.mpr ⟨m', hyC _ hm' ((mk_commute_iff ym m').mp hcm), rfl⟩
  have hxy' : ⁅(QuotientGroup.mk' (Q.subgroupOf M) xm)⁻¹,
      (QuotientGroup.mk' (Q.subgroupOf M) ym)⁻¹⁆ ∈ bar M Q (hc.CN t) := by
    rw [← map_inv, ← map_inv, ← map_commutatorElement]
    exact mem_bar_iff_exists_lift.mpr ⟨⁅xm⁻¹, ym⁻¹⁆, sec713_comm_Rt_of_O2 hZt hZcard hc hs hZ0
      _ ((O2NormPre M Q Z Z0).inv_mem hx) _ ((Rt M (LB M Q B) t).inv_mem hyR), rfl⟩
  obtain ⟨dbar, hdN, hcomm⟩ := exists_commute_mul_inv_of_orbit hZN' hNN' hZc' hZ2' hxN' hxZ'
    hy3' hyN' hyZ' hyC' hxy'
  have hD2bar : IsPGroup 2 ↥(bar M Q (O2NormPre M Q Z Z0)) := by
    have h1 : IsPGroup 2 ↥((O2NormPre M Q Z Z0).subgroupOf M) := hD2.comap_subtype
    exact h1.map _
  have hkD : QuotientGroup.mk' (Q.subgroupOf M) xm * dbar⁻¹ ∈ bar M Q (O2NormPre M Q Z Z0) :=
    (bar M Q (O2NormPre M Q Z Z0)).mul_mem (mem_bar_iff_exists_lift.mpr ⟨xm, hx, rfl⟩)
      ((bar M Q (O2NormPre M Q Z Z0)).inv_mem (bar_mono' hND hdN))
  have hk2 : IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' (Q.subgroupOf M) xm * dbar⁻¹)) :=
    hD2bar.to_le (Subgroup.zpowers_le.mpr hkD)
  have hkZ := hCent G M Q Z B hc n t hs (Or.inr hp) Z0 hZ0 hZN _ hk2
    (fun u hu => (hcomm u hu).eq.symm)
  have hxbar : QuotientGroup.mk' (Q.subgroupOf M) xm ∈ bar M Q (hc.CN t) := by
    have e : QuotientGroup.mk' (Q.subgroupOf M) xm =
        QuotientGroup.mk' (Q.subgroupOf M) xm * dbar⁻¹ * dbar := by group
    rw [e]
    exact (bar M Q (hc.CN t)).mul_mem (hZN' hkZ) hdN
  exact (mk_mem_bar_iff_sec4 hQN xm).mp hxbar

theorem sec715_fstar_eq_CN [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h51 : Stroth51Statement) (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) (h712 : Stroth712Statement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hO2 : O2NormPre M Q Z Z0 ≤ hc.CN t) :
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) := by
  classical
  let K : Subgroup (Mbar M Q) := bar M Q (NormH0 M Z Z0)
  let H : Subgroup (Mbar M Q) := bar M Q (H0 M Z)
  let Nbar : Subgroup (Mbar M Q) := bar M Q (hc.CN t)
  let N' : Subgroup H := Nbar.subgroupOf H
  let M' : Subgroup H := K.subgroupOf H
  have hKH : K ≤ H := MbarPrimeLe M Q Z Z0
  have hHardM' : pCore 2 ↥M' ≤ N'.subgroupOf M' := by
    intro y hy
    have hyK : ((y : Hbar M Q Z) : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
      Subgroup.mem_subgroupOf.mp y.2
    obtain ⟨x, hxK, hxy⟩ := Subgroup.mem_map.mp hyK
    have hxO : (x : G) ∈ O2NormPre M Q Z Z0 := mem_O2NormPre.mpr ⟨x.2, y, hy, hxy.symm⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hO2 hxO), hxy⟩
  have hEasyM' : N'.subgroupOf M' ≤ pCore 2 ↥M' :=
    CN_le_pCore_two_MbarPrime h34 h51 hA hZt hZcard hc hs hZ0
  have hEqM' : pCore 2 ↥M' = N'.subgroupOf M' := le_antisymm hHardM' hEasyM'
  let e : ↥M' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hmapP : (pCore 2 ↥M').map e.toMonoidHom = pCore 2 ↥K := CFSG.pCore_map_iso 2 e
  have hmapN : (N'.subgroupOf M').map e.toMonoidHom = Nbar.subgroupOf K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y.1, hKH y.2⟩, y.2⟩, hy, rfl⟩
  have hO2eq : pCore 2 ↥K = Nbar.subgroupOf K := by
    calc pCore 2 ↥K = (pCore 2 ↥M').map e.toMonoidHom := hmapP.symm
      _ = (N'.subgroupOf M').map e.toMonoidHom := by rw [hEqM']
      _ = Nbar.subgroupOf K := hmapN
  rw [h712 G M Q Z B hc n t hs Z0 hZ0]
  exact hO2eq

theorem sec715_isMaxAbNormalMod [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hIrr : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t)
    (hN' : ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q := by
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := sec8_Rt_le_NormH0 hc hZ0
  have hZK : Z0 ≤ NormH0 M Z Z0 := fun z hz => hRK (hZ0.le hz)
  have hKM : NormH0 M Z Z0 ≤ M := fun x hx => hx.1.1
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  refine ⟨hZK, fun x hx y hy => hZ0.comm_mem hx (hZ0.le hy),
    fun k hk => conjSubgroup_eq_self_iff.mpr hk.2, ?_⟩
  intro A hZA hAK hAn hAab
  have hAN : A ≤ hc.CN t := step716_le_of_fstar hKM hQN hAK hAn hAab hF
  rcases hIrr A hZA hAN hAn with h | h
  · exact h
  · exfalso
    apply hN'
    refine Subgroup.commutator_le.mpr fun x hx y hy => hAab x ?_ y ?_
    · rw [h]
      exact hx
    · rw [h]
      exact hy

theorem step7HypSub_of_irr [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hMA : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hIrr : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t)
    (hex : ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0) :
    SubConfigHyp79 M Q Z (hc.CN t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hH0M : H0 M Z ≤ M := fun x hx => hx.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hCNH0 : hc.CN t ≤ H0 M Z := hCNR.trans (hc.Rt_le_H0 t)
  haveI hN' : (Q.subgroupOf (H0 M Z)).Normal := normal_subgroupOf_of_le hQH hH0M
  have hconf := hc.tiConfig hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hMA hTI hF
  have hinj := embBar_injective hH0M hQH
  have hrange := embBar_range hH0M hQH
  have hconf' := hconf.comap (embBar M Q hH0M hQH) hinj hrange
  rw [comap_embBar_bar hH0M hQH hZ0H0, comap_embBar_bar hH0M hQH hCNH0] at hconf'
  refine ⟨hN', pCore_hat_eq_bot hc, ?_⟩
  have hcen : cen (bar (H0 M Z) Q (hc.CN t)) = bar (H0 M Z) Q Z0 := hconf'.cenIn_N_eq
  rw [hcen]
  have hq4 : 4 ≤ Nat.card ↥(bar (H0 M Z) Q Z0) := by
    have h4 := four_le_card_bar_Z0 hc hs hZcard hZ0
    rw [← map_embBar_bar hH0M hQH hZ0H0, Subgroup.card_map_of_injective hinj] at h4
    exact h4
  have hsq := sq_eq_one_hat hc hs hZc hZ0
  have hne := ne_hat hc hs hZcard hZ0
  obtain ⟨g, hg, hgN, hgne⟩ := hex
  obtain ⟨hb, hbS, hbN, hbV⟩ := exists_Hconj_of_conj hc hs hZ0 hconf hg hgN hgne
  have hex' := exists_hat_conj hQH hH0M (V := bar M Q Z0) (N := bar M Q (hc.CN t))
    (bar_mono' hZ0H0) (bar_mono' hCNH0) ⟨hb, hbS, hbN, hbV⟩
  rw [comap_embBar_bar hH0M hQH hZ0H0, comap_embBar_bar hH0M hQH hCNH0] at hex'
  have hInv' : ∀ A : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)),
      bar (H0 M Z) Q Z0 ≤ A → A ≤ bar (H0 M Z) Q (hc.CN t) →
      (∀ k ∈ NormIn ⊤ (bar (H0 M Z) Q Z0), k ∈ Subgroup.normalizer (A : Set _)) →
      A ≠ bar (H0 M Z) Q (hc.CN t) → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro A hVA hAN hAinv hANe x hx y hy
    obtain ⟨A', hQA', hA'H0, hbarA⟩ := exists_pre (M := H0 M Z) hQH A
    have hZ0A : Z0 ≤ A' := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hZ0H0 hu⟩ ∈ A :=
        hVA (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
      rw [← hbarA] at h1
      exact (mk_mem_bar_iff_sec4 hQA' _).mp h1
    have hA'N : A' ≤ hc.CN t := by
      intro u hu
      have h1 : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨u, hA'H0 hu⟩ ∈
          bar (H0 M Z) Q (hc.CN t) :=
        hAN (hbarA ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu))
      exact (mk_mem_bar_iff_sec4 hQCN _).mp h1
    have hA'ne : A' ≠ hc.CN t := fun h => hANe (by rw [← hbarA, h])
    have hKinv : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k A' = A' := by
      intro k hk
      have h1 := mk_mem_normalizer_bar_of_normalizer (M := H0 M Z) hQZ0 ⟨k, hk.1⟩ hk.2
      have h2 := hAinv _ (mem_NormIn.mpr ⟨Subgroup.mem_top _, h1⟩)
      rw [← hbarA] at h2
      exact conjSubgroup_eq_self_iff.mpr
        (mem_normalizer_of_mk_mem_normalizer_bar (M := H0 M Z) hQA' hA'H0 ⟨k, hk.1⟩ h2)
    have hA'Z0 : A' = Z0 := (hIrr A' hZ0A hA'N hKinv).resolve_right hA'ne
    have hab : ∀ x ∈ A', ∀ y ∈ A', ⁅x, y⁆ ∈ Q := by
      rw [hA'Z0]
      exact fun x hx y hy => hZ0.comm_mem hx (hZ0.le hy)
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp (hbarA ▸ hx)
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp (hbarA ▸ hy)
    exact step716_mk_mul_comm (hab _ (Subgroup.mem_subgroupOf.mp hx') _
      (Subgroup.mem_subgroupOf.mp hy'))
  have hgen := hconf'.gen_of_inv hex' hInv'
  have hKmap : (Subgroup.normalizer ((bar (H0 M Z) Q Z0 : Subgroup _) : Set _)).map
      (embBar M Q hH0M hQH) = bar M Q (NormH0 M Z Z0) := by
    have hVr : bar M Q Z0 ≤ (embBar M Q hH0M hQH).range := by
      rw [hrange]; exact bar_mono' hZ0H0
    rw [bar_NormH0_eq hc hQZ0 hZ0M]
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k ∈ Subgroup.normalizer ((((bar M Q Z0).comap (embBar M Q hH0M hQH) :
          Subgroup _)) : Set _) := by
        rw [comap_embBar_bar hH0M hQH hZ0H0]; exact hk
      refine mem_NormIn.mpr ⟨?_, (TIConfig.normalizer_comap_iff hVr k).mp hk'⟩
      rw [← hrange]; exact ⟨k, rfl⟩
    · intro hz
      obtain ⟨hzH, hzN⟩ := mem_NormIn.mp hz
      rw [← hrange] at hzH
      obtain ⟨k, rfl⟩ := hzH
      refine ⟨k, ?_, rfl⟩
      have := (TIConfig.normalizer_comap_iff hVr k).mpr hzN
      rwa [comap_embBar_bar hH0M hQH hZ0H0] at this
  have hfit1 := generalizedFitting_comap_eq (embBar M Q hH0M hQH) hinj hKmap hF
  rw [comap_embBar_bar hH0M hQH hCNH0] at hfit1
  have hfit2 := pCore_normalizer_eq hconf'
  exact hyp79_of_tiConfig hconf' hq4 hsq hne hgen (hfit1.trans hfit2.symm)

theorem step715Hyp79_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h311a : Stroth311aStatement) (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hNR : Sec7NormZ0Statement) (hCommN : Sec7CommNStatement)
    (h711S : Stroth711StrongStatement) (h712 : Stroth712Statement) (h714 : Stroth714Statement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hConj : Sec715ConjStatement)
    (hIrr : Sec715IrrStatement) : Step715Hyp79Statement := by
  intro G _ _ M Q Z B hc n t hs hp Z0 hZ0 hZN
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hn16 : n = 16 := h714 G M Q Z B hc n t hs hp
  have hnom : ¬ OmegaMinusNat hc t 2 := not_omegaMinus_two_of_cases (Or.inr (Or.inr hp))
  have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
  have hIrr' := hIrr G M Q Z B hc n t hs hp hn16 Z0 hZ0 hZN hTI
  have hO2 := sec715_O2NormPre_le_CN h34 h310chi h51 hA hZt hZcard hZc hZV hCommN hY hCent hc
    hs hp hZ0 hZN hIrr'
  have hF := sec715_fstar_eq_CN h34 h51 hA hZt hZcard h712 hc hs hZ0 hO2
  have hMA := sec715_isMaxAbNormalMod hc ht hZ0 hIrr' (h711S G M Q Z B hc n t hs) hF
  exact step7HypSub_of_irr h34 h311a hZt hZcard hZc hc hs hZ0 hMA hTI hF hIrr'
    (hConj G M Q Z B hc n t hs hp hn16 Z0 hZ0 hZN hTI)

end CFSG.RankThree.GF2n.Stroth80
