module

public import CFSG.Monster.GMS.Leech.Forms
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
import CFSG.LargeExtraspecial.BridgeNat
import CFSG.LargeExtraspecial.S3Qa
import CFSG.Monster.NormalChain

public section

namespace CFSG.Sporadic.MI301

open CFSG.Monster.GMS CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Odd

variable {G : Type} [Group G] {z d : G}

private theorem conj_ne_mul_z_of_odd (hdz : d * z = z * d) (hz : z * z = 1) (hz1 : z ≠ 1)
    (hodd : Odd (orderOf d)) (x : G) : d * x * d⁻¹ ≠ x * z := by
  intro h
  have key : ∀ k : ℕ, d ^ k * x * (d ^ k)⁻¹ = x * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : d * z ^ k = z ^ k * d := (Commute.pow_right hdz k).eq
      calc d ^ (k + 1) * x * (d ^ (k + 1))⁻¹ = d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
        _ = d * x * d⁻¹ * (d * z ^ k) * d⁻¹ := by rw [ih]; group
        _ = x * z ^ (k + 1) := by rw [h, hc, pow_succ']; group
  obtain ⟨m, hm⟩ := hodd
  have h1 := key (orderOf d)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hm, pow_succ, pow_mul, pow_two, hz, one_pow,
    one_mul] at h1
  exact hz1 (mul_left_cancel (h1.symm.trans (mul_one x).symm))

private theorem commute_of_forall_rowR0 (L : LeechSystem z)
    (hd : d ∈ Subgroup.centralizer ({z} : Set G)) (hodd : Odd (orderOf d)) {q : G}
    (hq : q ∈ leechQ z) (hqd : q * d = d * q)
    (hc : ∀ s ∈ leechQ z, s * d = d * s → s * q = q * s) {r : G} (hr : r ∈ leechQ z) :
    r * q = q * r := by
  have hE := L.extraspecial
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 hd
  have hinv : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * q = q * g → ∀ y ∈ leechQ z,
      ⁅g * y * g⁻¹, q⁆ = ⁅y, q⁆ := by
    intro g hg hgq y hy
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have h1 : ⁅g * y * g⁻¹, q⁆ = g * ⁅y, q⁆ * g⁻¹ := by
      have hq' : q = g * q * g⁻¹ := by rw [hgq]; group
      conv_lhs => rw [hq']
      simp only [commutatorElement_def]
      group
    rw [h1]
    rcases hE.comm y hy q hq with h | h <;> rw [h]
    · group
    · rw [hgz]; group
  have key : ∀ k : ℕ, ∃ s ∈ leechQ z, d * s * d⁻¹ = r⁻¹ * s * (d ^ k * r * (d ^ k)⁻¹) ∧
      ⁅s, q⁆ = ⁅r, q⁆ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by group, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs, h1, h2⟩ := ih
      have hdk : d ^ k ∈ Subgroup.centralizer ({z} : Set G) := pow_mem hd k
      have ht := L.conj_mem' hdk hr
      refine ⟨s * (d ^ k * r * (d ^ k)⁻¹), mul_mem hs ht, ?_, ?_⟩
      · calc d * (s * (d ^ k * r * (d ^ k)⁻¹)) * d⁻¹
            = d * s * d⁻¹ * (d * (d ^ k * r * (d ^ k)⁻¹) * d⁻¹) := by group
          _ = r⁻¹ * (s * (d ^ k * r * (d ^ k)⁻¹)) * (d ^ (k + 1) * r * (d ^ (k + 1))⁻¹) := by
            rw [h1, pow_succ']; group
      · rw [hE.commutatorElement_mul_left hs ht hq, h2,
          hinv _ hdk (Commute.pow_left hqd.symm k).eq r hr, pow_succ]
  obtain ⟨s, hs, h1, h2⟩ := key (orderOf d)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h3 : d * s * d⁻¹ = s ∨ d * s * d⁻¹ = s * z := by
    have h4 : r⁻¹ * s * r = s * ⁅s⁻¹, r⁻¹⁆ := by simp only [commutatorElement_def]; group
    rw [h1, h4]
    rcases hE.comm s⁻¹ (inv_mem hs) r⁻¹ (inv_mem hr) with h | h <;> rw [h]
    · exact Or.inl (mul_one s)
    · exact Or.inr rfl
  have hsd : d * s * d⁻¹ = s :=
    h3.resolve_right (conj_ne_mul_z_of_odd hdz hE.mul_self hE.ne_one hodd s)
  have h5 : ⁅s, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hc s hs (by
    calc s * d = d * s * d⁻¹ * d := by rw [hsd]
      _ = d * s := by group))
  rw [h2] at h5
  rcases hE.comm r hr q hq with h | h
  · exact commutatorElement_eq_one_iff_mul_comm.1 h
  · obtain ⟨m, hm⟩ := hodd
    rw [h, hm, pow_succ, pow_mul, pow_two, hE.mul_self, one_pow, one_mul] at h5
    exact absurd h5 hE.ne_one

end Odd

variable {G : Type} [Group G] [Finite G] {z : G} (L : CFSG.Monster.GMS.LeechSystem z) {d : G}
  (hd : d ∈ Subgroup.centralizer ({z} : Set G)) (hodd : Odd (orderOf d))

omit [Finite G] in
include hodd in
theorem card_rowR0_leech : Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({d} : Set G)) =
    2 * (co1Fix (L.φ ⟨d, hd⟩)).ncard := by
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 hd
  have hset : ((leechQ z ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) =
      {g | g ∈ leechQ z ∧ L.vec g ∈ co1Fix (L.φ ⟨d, hd⟩)} := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_setOf_eq]
    refine and_congr_right fun hg => ⟨fun hgd => ?_, fun hfix => ?_⟩
    · show co1Act (L.φ ⟨d, hd⟩) (L.vec g) = L.vec g
      rw [← L.vec_conj' hd hg]
      congr 1
      rw [← Subgroup.mem_centralizer_singleton_iff.1 hgd]
      group
    · have h1 : L.vec (d * g * d⁻¹) = L.vec g := (L.vec_conj' hd hg).trans hfix
      rcases L.eq_or_eq_mul_z (L.conj_mem' hd hg) hg h1 with h | h
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * d = d * g * d⁻¹ * d := by rw [h]
          _ = d * g := by group
      · exact absurd h (conj_ne_mul_z_of_odd hdz L.z_mul_self L.z_ne_one hodd g)
  calc Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({d} : Set G))
      = ((leechQ z ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ = 2 * (co1Fix (L.φ ⟨d, hd⟩)).ncard := by rw [hset, L.ncard_preimage]

omit [Finite G] in
include L hd hodd in
theorem centerOf_rowR0_leech :
    S8.centerOf (leechQ z ⊓ Subgroup.centralizer ({d} : Set G)) = Subgroup.zpowers z := by
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 hd
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact L.z_mul_self) L.z_ne_one
  ext x
  unfold S8.centerOf
  rw [CFSG.Monster.mem_map_center_iff, mem_zpowers_iff_of_orderOf_two hz2]
  constructor
  · rintro ⟨hx, hxc⟩
    obtain ⟨hxQ, hxd⟩ := Subgroup.mem_inf.1 hx
    exact L.center_eq x hxQ fun p hp => commute_of_forall_rowR0 L hd hodd hxQ
      (Subgroup.mem_centralizer_singleton_iff.1 hxd) (fun s hs hsd => hxc s
        (Subgroup.mem_inf.2 ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 hsd⟩)) hp
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, fun y _ => by rw [mul_one, one_mul]⟩
    · exact ⟨Subgroup.mem_inf.2 ⟨L.z_mem, Subgroup.mem_centralizer_singleton_iff.2 hdz.symm⟩,
        fun y hy => L.extraspecial.central y (Subgroup.mem_inf.1 hy).1⟩

include hodd in
theorem isExtraSpec2_rowR0_leech (hf : 2 ≤ (co1Fix (L.φ ⟨d, hd⟩)).ncard) :
    S8.IsExtraSpec2 (leechQ z ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set R₀ := leechQ z ⊓ Subgroup.centralizer ({d} : Set G) with hR₀
  have hE := L.extraspecial
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 hd
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact L.z_mul_self) L.z_ne_one
  have hcen := centerOf_rowR0_leech L hd hodd
  have hzR : z ∈ R₀ :=
    Subgroup.mem_inf.2 ⟨L.z_mem, Subgroup.mem_centralizer_singleton_iff.2 hdz.symm⟩
  have hsq : ∀ x ∈ R₀, x ^ 2 = 1 ∨ x ^ 2 = z := fun x hx => by
    rw [pow_two]
    exact hE.sq x (Subgroup.mem_inf.1 hx).1
  have h2 : IsPGroup 2 R₀ := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 2 * 2 from rfl, pow_mul]
    rcases hsq g g.2 with h | h <;> rw [h]
    · exact one_pow 2
    · rw [pow_two]
      exact L.z_mul_self
  have hZ : ∀ x ∈ R₀, (∀ y ∈ R₀, x * y = y * x) ↔ x = 1 ∨ x = z := by
    intro x hx
    rw [← mem_zpowers_iff_of_orderOf_two hz2, ← hcen]
    unfold S8.centerOf
    rw [CFSG.Monster.mem_map_center_iff]
    exact ⟨fun h => ⟨hx, fun y hy => (h y hy).symm⟩, fun h y hy => (h.2 y hy).symm⟩
  have hnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x := by
    have hnle : ¬ R₀ ≤ Subgroup.zpowers z := fun hle => by
      have h4 := Subgroup.card_le_of_le hle
      rw [hR₀, card_rowR0_leech L hd hodd, Nat.card_zpowers, hz2] at h4
      omega
    obtain ⟨x, hx, hxz⟩ := SetLike.not_le_iff_exists.1 hnle
    by_contra hall
    push Not at hall
    exact hxz ((mem_zpowers_iff_of_orderOf_two hz2).2 ((hZ x hx).1 fun y hy => hall x hx y hy))
  exact (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2
    (CFSG.LargeExtraspecial.isExtraspecialPGroup_two_of_center h2 hzR hE.ne_one hZ
      (fun x hx y hy => hE.comm x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1) hsq hnc)

end CFSG.Sporadic.MI301

end
