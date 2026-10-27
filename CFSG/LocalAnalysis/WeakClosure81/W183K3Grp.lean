module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Lift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183k3_exists_cent_mul {W : Type*} [Group W] [Finite W] {N : Subgroup W} [N.Normal]
    (hN : Odd (Nat.card ↥N)) {t : W} {m : ℕ} (ht : t ^ (2 ^ m) = 1) {x : W}
    (hx : x * t * x⁻¹ * t⁻¹ ∈ N) : ∃ k ∈ N, (x * k) * t = t * (x * k) := by
  have hxq : QuotientGroup.mk' N (x * t * x⁻¹ * t⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (x * t * x⁻¹ * t⁻¹)).mpr hx
  have hxq' : QuotientGroup.mk' N x * QuotientGroup.mk' N t * (QuotientGroup.mk' N x)⁻¹ *
      (QuotientGroup.mk' N t)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using hxq
  have hmem : QuotientGroup.mk' N x ∈
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (W ⧸ N)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul : QuotientGroup.mk' N x * QuotientGroup.mk' N t * (QuotientGroup.mk' N x)⁻¹ =
        QuotientGroup.mk' N t := mul_inv_eq_one.mp hxq'
    calc QuotientGroup.mk' N x * QuotientGroup.mk' N t
        = (QuotientGroup.mk' N x * QuotientGroup.mk' N t * (QuotientGroup.mk' N x)⁻¹) *
            QuotientGroup.mk' N x := by group
      _ = QuotientGroup.mk' N t * QuotientGroup.mk' N x := by rw [hmul]
  rw [← W183K3.centralizer_map_mk hN ht] at hmem
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hmem
  refine ⟨x⁻¹ * w, ?_, ?_⟩
  · refine (QuotientGroup.eq_one_iff (x⁻¹ * w)).mp ?_
    show QuotientGroup.mk' N (x⁻¹ * w) = 1
    rw [map_mul, map_inv, hwx, inv_mul_cancel]
  · have hxw : x * (x⁻¹ * w) = w := mul_inv_cancel_left x w
    rw [hxw]
    exact Subgroup.mem_centralizer_singleton_iff.mp hw

theorem w183k3_odd_card_of_forall {W : Type*} [Group W] [Finite W] {K : Subgroup W}
    (h : ∀ g ∈ K, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g = 1) : Odd (Nat.card ↥K) := by
  rw [← Nat.not_even_iff_odd]
  intro he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥K := even_iff_two_dvd.mp he
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 hdvd
  have hg2 : (g : W) ^ (2 ^ 1) = 1 := by
    have h2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    simpa using congrArg (fun x : ↥K => (x : W)) h2
  have hg1 : (g : W) = 1 := h (g : W) g.2 1 hg2
  have hgone : g = 1 := Subtype.ext hg1
  rw [hgone] at hg
  rw [orderOf_one] at hg
  omega

theorem w183k3_split_two {W : Type*} [Group W] {L₁ L₂ : Subgroup W}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (ho : Odd (Nat.card ↥(Subgroup.center ↥L₁))) {u v : W} (hu : u ∈ L₁) (hv : v ∈ L₂)
    (huv : (u * v) * (u * v) = 1) :
    ∃ x ∈ L₁, ∃ y ∈ L₂, u * v = x * y ∧ x * x = 1 ∧ y * y = 1 := by
  let N := Nat.card ↥(Subgroup.center ↥L₁)
  obtain ⟨m, hm⟩ := ho
  have hmN : N = 2 * m + 1 := hm
  have huvc : Commute u v := hcomm u hu v hv
  have hu2v2 : u ^ 2 * v ^ 2 = 1 := by
    have h : (u * v) * (u * v) = u ^ 2 * v ^ 2 := by
      calc (u * v) * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [← huvc.eq]
        _ = u ^ 2 * v ^ 2 := by rw [pow_two, pow_two]; group
    rw [← h]
    exact huv
  have hv2 : v ^ 2 = (u ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hu2v2
  have hu2L₂ : u ^ 2 ∈ L₂ := by
    have h : u ^ 2 = (v ^ 2)⁻¹ := by rw [hv2, inv_inv]
    rw [h]
    exact L₂.inv_mem (pow_mem hv 2)
  have hu2center : (⟨u ^ 2, pow_mem hu 2⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    show (a : W) * u ^ 2 = u ^ 2 * (a : W)
    exact hcomm (a : W) a.2 (u ^ 2) hu2L₂
  have hpow : (u ^ 2) ^ N = 1 := by
    have hg := pow_card_eq_one'
      (x := (⟨⟨u ^ 2, pow_mem hu 2⟩, hu2center⟩ : ↥(Subgroup.center ↥L₁)))
    have hcoe := congrArg (fun g : ↥(Subgroup.center ↥L₁) => (g : W)) hg
    exact hcoe
  have huN : u ^ N = u ^ (2 * m) * u := by rw [hmN, pow_succ]
  have hvN : v ^ N = v ^ (2 * m) * v := by rw [hmN, pow_succ]
  have hu2m : u ^ (2 * m) = (u ^ 2) ^ m := pow_mul u 2 m
  have hv2m : v ^ (2 * m) = (v ^ 2) ^ m := pow_mul v 2 m
  have huvc2 : Commute u ((v ^ 2) ^ m) := (huvc.pow_right 2).pow_right m
  have huv2m : (u ^ 2) ^ m * (v ^ 2) ^ m = 1 := by
    rw [← ((huvc.pow_right 2).pow_left 2).mul_pow m, hu2v2, one_pow]
  have huv_eq : u ^ N * v ^ N = u * v := by
    rw [huN, hvN, hu2m, hv2m]
    calc (u ^ 2) ^ m * u * ((v ^ 2) ^ m * v)
        = (u ^ 2) ^ m * (u * (v ^ 2) ^ m) * v := by group
      _ = (u ^ 2) ^ m * ((v ^ 2) ^ m * u) * v := by rw [huvc2.eq]
      _ = ((u ^ 2) ^ m * (v ^ 2) ^ m) * (u * v) := by group
      _ = u * v := by rw [huv2m, one_mul]
  have hx2 : u ^ N * u ^ N = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hpow]
  have hy2 : v ^ N * v ^ N = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hv2, inv_pow, hpow, inv_one]
  exact ⟨u ^ N, pow_mem hu N, v ^ N, pow_mem hv N, huv_eq.symm, hx2, hy2⟩

theorem w183k3_comm_of_sq {W : Type*} [Group W] (ho : Odd (Nat.card ↥(Subgroup.center W)))
    {s t : W} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center W) : s * t = t * s := by
  let c := s * t * s⁻¹ * t⁻¹
  have hc : c ∈ Subgroup.center W := hst
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hcs : s * c = c * s := Subgroup.mem_center_iff.mp hc s
  have hstc : s * t * s⁻¹ = c * t := by
    show s * t * s⁻¹ = (s * t * s⁻¹ * t⁻¹) * t
    group
  have hconj : s * (s * t * s⁻¹) * s⁻¹ = t := by
    rw [hsinv]
    calc s * (s * t * s) * s = (s * s) * t * (s * s) := by group
      _ = t := by rw [hs]; group
  have hconjc : s * (c * t) * s⁻¹ = c * c * t := by
    calc s * (c * t) * s⁻¹ = (s * c) * t * s⁻¹ := by group
      _ = (c * s) * t * s⁻¹ := by rw [hcs]
      _ = c * (s * t * s⁻¹) := by group
      _ = c * (c * t) := by rw [hstc]
      _ = c * c * t := by group
  have htc : t = c * c * t := by
    calc t = s * (s * t * s⁻¹) * s⁻¹ := hconj.symm
      _ = s * (c * t) * s⁻¹ := by rw [hstc]
      _ = c * c * t := hconjc
  have hcc : c * c = 1 := by
    have h : (1 : W) * t = (c * c) * t := by rw [one_mul]; exact htc
    exact (mul_right_cancel h).symm
  have hdvd : orderOf c ∣ Nat.card ↥(Subgroup.center W) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center W) hc
  have hodd : Odd (orderOf c) := ho.of_dvd_nat hdvd
  have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
  have hone : orderOf c = 1 := hodd.coprime_two_right.eq_one_of_dvd hdvd2
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hone
  have h1 : s * t * s⁻¹ * t⁻¹ = 1 := by
    show c = 1
    exact hc1
  have hst1 : s * t * s⁻¹ = t := mul_inv_eq_one.mp h1
  calc s * t = (s * t * s⁻¹) * s := by group
    _ = t * s := by rw [hst1]

private lemma w183k3_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

theorem W183K3.Br3TwoComp.odd_card_cent {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (h : Br3TwoComp Y T L₁ L₂) :
    Odd (Nat.card ↥(Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V)))) := by
  haveI : Finite (LGL 2 V) := w183k3_finite_lgl
  refine w183k3_odd_card_of_forall (W := LGL 2 V) ?_
  intro g hg k hgk
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgYc, hgL₂⟩ := hg
  rw [Subgroup.mem_inf] at hgYc
  obtain ⟨hgY, hgL₁⟩ := hgYc
  have h₁ : ∀ l ∈ L₁, g * l = l * g :=
    fun l hl => (Subgroup.mem_centralizer_iff.mp hgL₁ l hl).symm
  have h₂ : ∀ l ∈ L₂, g * l = l * g :=
    fun l hl => (Subgroup.mem_centralizer_iff.mp hgL₂ l hl).symm
  exact h.eq_one_of_isPGroup_cent hgY hgk h₁ h₂

end CFSG.LocalAnalysis.WeakClosure81

end
