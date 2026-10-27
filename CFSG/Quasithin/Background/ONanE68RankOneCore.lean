module

public import CFSG.Quasithin.Background.ONanE68LieFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.Quasithin.E6.E68Proof

namespace RankOne

open CFSG.Open CFSG.ProperTwoGeneratedCore.TheoremC
open scoped Pointwise

variable {S : Type} [Group S]

theorem omegaCenter_eq_map_center {P : Subgroup S} (h : ∀ z ∈ Subgroup.center P, z ^ 2 = 1) :
    omegaCenter P = (Subgroup.center P).map P.subtype := by
  ext z
  constructor
  · rintro ⟨hzP, hzc, -⟩
    exact ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hzc g g.2).symm, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, fun y hy => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩).symm
    · have := congrArg Subtype.val (h w hw)
      simpa [pow_two] using this

theorem card_omegaCenter {q k : ℕ} (hB : fusionBenderBorel S q k) (Q : Sylow 2 S) :
    Nat.card (omegaCenter (Q : Subgroup S)) = q := by
  rw [omegaCenter_eq_map_center (hB Q).2.2.1,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (hB Q).2.2.2.1

theorem inCenterOf_of_mem_omegaCenter {P : Subgroup S} {z : S} (hz : z ∈ omegaCenter P) :
    InCenterOf P z :=
  ⟨hz.1, fun y hy => (hz.2.1 y hy).symm⟩

theorem exists_gen_pow [Finite S] {D : Subgroup S} (hD : IsCyclic D) :
    ∃ x ∈ D, ∀ d ∈ D, ∃ j : ℕ, x ^ j = d := by
  obtain ⟨g, hg⟩ := hD.exists_generator
  refine ⟨g, g.2, fun d hd => ?_⟩
  have h1 : (⟨d, hd⟩ : D) ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg ⟨d, hd⟩)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp h1
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem commute_of_cyclic {D : Subgroup S} (hD : IsCyclic D) {a b : S} (ha : a ∈ D)
    (hb : b ∈ D) : a * b = b * a := by
  have := hD
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : D) ⟨b, hb⟩)

theorem exists_mul_of_mem_sup {Q D : Subgroup S} (hD : D ≤ Subgroup.normalizer (Q : Set S))
    {a : S} (ha : a ∈ Q ⊔ D) : ∃ p ∈ Q, ∃ d ∈ D, a = p * d := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left Q D hD
  have ha' : a ∈ (Q : Set S) * (D : Set S) := h ▸ ha
  obtain ⟨p, hp, d, hd, rfl⟩ := ha'
  exact ⟨p, hp, d, hd, rfl⟩

theorem exists_cyclic_torus {q k : ℕ} (hB : fusionBenderBorel S q k) (Q : Sylow 2 S)
    (hF : BenderBorelFacts S (Q : Subgroup S)) :
    ∃ D : Subgroup S, IsCyclic D ∧ Odd (Nat.card D) ∧ (Q : Subgroup S) ⊓ D = ⊥ ∧
      (Q : Subgroup S) ⊔ D = Subgroup.normalizer ((Q : Subgroup S) : Set S) ∧
      ∀ w w' : S, InCenterOf (Q : Subgroup S) w → w ≠ 1 → InCenterOf (Q : Subgroup S) w' →
        w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w' := by
  obtain ⟨D, hDcyc, hDodd, hQD, hsup⟩ := (hB Q).2.1
  obtain ⟨D', -, hD'N, -, htrans, -⟩ := hF.torus
  refine ⟨D, hDcyc, hDodd, hQD, hsup, fun w w' hw hw1 hw' hw'1 => ?_⟩
  obtain ⟨d, hd, hdw⟩ := htrans w w' hw hw1 hw' hw'1
  have hDN : D ≤ Subgroup.normalizer ((Q : Subgroup S) : Set S) := hsup ▸ le_sup_right
  obtain ⟨p, hp, e, he, rfl⟩ := exists_mul_of_mem_sup hDN (by rw [hsup]; exact hD'N hd)
  refine ⟨e, he, ?_⟩
  have hpw : p⁻¹ * w * p = w := by
    have := (hw.2 p⁻¹ ((Q : Subgroup S).inv_mem hp)).eq
    rw [this]
    group
  rw [← hdw]
  calc e⁻¹ * w * e = e⁻¹ * (p⁻¹ * w * p) * e := by rw [hpw]
    _ = (p * e)⁻¹ * w * (p * e) := by group

theorem quot_comm_of_sup {Q D : Subgroup S} (hD : IsCyclic D)
    (hsup : Q ⊔ D = Subgroup.normalizer (Q : Set S)) :
    ∀ a ∈ Subgroup.normalizer (Q : Set S), ∀ b ∈ Subgroup.normalizer (Q : Set S),
      a * b * a⁻¹ * b⁻¹ ∈ Q := by
  have hDN : D ≤ Subgroup.normalizer (Q : Set S) := hsup ▸ le_sup_right
  intro a ha b hb
  obtain ⟨p1, hp1, d1, hd1, rfl⟩ := exists_mul_of_mem_sup hDN (by rw [hsup]; exact ha)
  obtain ⟨p2, hp2, d2, hd2, rfl⟩ := exists_mul_of_mem_sup hDN (by rw [hsup]; exact hb)
  have hcomm := commute_of_cyclic hD hd1 hd2
  have hconj : ∀ x ∈ Subgroup.normalizer (Q : Set S), ∀ p ∈ Q, x * p * x⁻¹ ∈ Q := fun x hx p hp =>
    (Subgroup.mem_normalizer_iff.mp hx p).mp hp
  have key : p1 * d1 * (p2 * d2) * (p1 * d1)⁻¹ * (p2 * d2)⁻¹ =
      p1 * (d1 * p2 * d1⁻¹) * (d2 * p1⁻¹ * d2⁻¹) * p2⁻¹ := by
    have h : d2 * d1⁻¹ = d1⁻¹ * d2 := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    calc p1 * d1 * (p2 * d2) * (p1 * d1)⁻¹ * (p2 * d2)⁻¹
        = p1 * d1 * p2 * (d2 * d1⁻¹) * p1⁻¹ * d2⁻¹ * p2⁻¹ := by group
      _ = p1 * (d1 * p2 * d1⁻¹) * (d2 * p1⁻¹ * d2⁻¹) * p2⁻¹ := by rw [h]; group
  rw [key]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem hp1 (hconj d1 (hDN hd1) p2 hp2))
    (hconj d2 (hDN hd2) p1⁻¹ (Q.inv_mem hp1))) (Q.inv_mem hp2)

theorem singer_of_torus [Finite S] {q k : ℕ} (hB : fusionBenderBorel S q k) (Q : Sylow 2 S)
    (hF : BenderBorelFacts S (Q : Subgroup S)) :
    ∃ x ∈ Subgroup.normalizer ((Q : Subgroup S) : Set S),
      ∀ z ∈ omegaCenter (Q : Subgroup S), z ≠ 1 → ∀ w ∈ omegaCenter (Q : Subgroup S), w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w := by
  obtain ⟨D, hDcyc, -, -, hsup, htrans⟩ := exists_cyclic_torus hB Q hF
  obtain ⟨x, hxD, hx⟩ := exists_gen_pow hDcyc
  have hDN : D ≤ Subgroup.normalizer ((Q : Subgroup S) : Set S) := hsup ▸ le_sup_right
  refine ⟨x, hDN hxD, fun z hz hz1 w hw hw1 => ?_⟩
  obtain ⟨d, hd, hdz⟩ := htrans z w (inCenterOf_of_mem_omegaCenter hz) hz1
    (inCenterOf_of_mem_omegaCenter hw) hw1
  obtain ⟨j, hj⟩ := hx d⁻¹ (D.inv_mem hd)
  exact ⟨j, by rw [hj, inv_inv]; exact hdz⟩

theorem centralizer_le_of_facts {Q : Subgroup S} (hF : BenderBorelFacts S Q)
    (hZ : Subgroup.center S = ⊥) : ∀ y : S, (∀ p ∈ Q, y * p = p * y) → y ∈ Q := by
  intro y hy
  obtain ⟨r, hr, hσ⟩ := hF.aut_inner (MulAut.conj y) fun p hp => by
    simp only [MulAut.conj_apply]
    rw [hy p hp]
    group
  have hc : r⁻¹ * y ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := hσ g
    simp only [MulAut.conj_apply] at h
    calc g * (r⁻¹ * y) = r⁻¹ * (r * g * r⁻¹) * y := by group
      _ = r⁻¹ * (y * g * y⁻¹) * y := by rw [h]
      _ = r⁻¹ * y * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc ▸ hr

theorem inf_centralizer_eq_bot_of_abelian {Q : Sylow 2 S} {D : Subgroup S} (hD : IsCyclic D)
    (hQD : (Q : Subgroup S) ⊓ D = ⊥)
    (hsup : (Q : Subgroup S) ⊔ D = Subgroup.normalizer ((Q : Subgroup S) : Set S))
    (hab : ∀ x ∈ (Q : Subgroup S), ∀ y ∈ (Q : Subgroup S), x * y = y * x)
    (htrans : ∀ w w' : S, InCenterOf (Q : Subgroup S) w → w ≠ 1 → InCenterOf (Q : Subgroup S) w' →
      w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    (hcent : ∀ y : S, (∀ p ∈ (Q : Subgroup S), y * p = p * y) → y ∈ (Q : Subgroup S))
    {c : S} (hc : c ∈ Subgroup.normalizer ((Q : Subgroup S) : Set S)) (hc3 : orderOf c = 3) :
    (Q : Subgroup S) ⊓ Subgroup.centralizer ({c} : Set S) = ⊥ := by
  have hDN : D ≤ Subgroup.normalizer ((Q : Subgroup S) : Set S) := hsup ▸ le_sup_right
  obtain ⟨p0, hp0, d0, hd0, rfl⟩ := exists_mul_of_mem_sup hDN (by rw [hsup]; exact hc)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have h1 : x * (p0 * d0) = p0 * d0 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
  have hfix : d0 * x * d0⁻¹ = x := by
    calc d0 * x * d0⁻¹ = p0⁻¹ * (p0 * d0 * x) * d0⁻¹ := by group
      _ = p0⁻¹ * (x * (p0 * d0)) * d0⁻¹ := by rw [← h1]
      _ = p0⁻¹ * x * p0 := by group
      _ = p0⁻¹ * (x * p0) := by group
      _ = p0⁻¹ * (p0 * x) := by rw [hab x hxQ p0 hp0]
      _ = x := by group
  have hcomm0 : ∀ y ∈ (Q : Subgroup S), d0 * y = y * d0 := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; simp
    · obtain ⟨d, hd, rfl⟩ := htrans x y ⟨hxQ, fun q hq => (hab x hxQ q hq).symm⟩ hx1
        ⟨hy, fun q hq => (hab y hy q hq).symm⟩ hy1
      have hdd : d0 * d⁻¹ = d⁻¹ * d0 := commute_of_cyclic hD hd0 (D.inv_mem hd)
      calc d0 * (d⁻¹ * x * d) = d0 * d⁻¹ * x * d := by group
        _ = d⁻¹ * d0 * x * d := by rw [hdd]
        _ = d⁻¹ * (d0 * x * d0⁻¹) * d0 * d := by group
        _ = d⁻¹ * x * (d0 * d) := by rw [hfix]; group
        _ = d⁻¹ * x * (d * d0) := by rw [commute_of_cyclic hD hd0 hd]
        _ = (d⁻¹ * x * d) * d0 := by group
  have hd0Q : d0 ∈ (Q : Subgroup S) := hcent d0 hcomm0
  have hd01 : d0 = 1 := by
    have : d0 ∈ (Q : Subgroup S) ⊓ D := ⟨hd0Q, hd0⟩
    rw [hQD, Subgroup.mem_bot] at this
    exact this
  have hcQ : p0 * d0 ∈ (Q : Subgroup S) := by rw [hd01, mul_one]; exact hp0
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨p0 * d0, hcQ⟩
  rw [Subgroup.orderOf_mk, hc3] at hm
  cases m with
  | zero => omega
  | succ m => rw [pow_succ] at hm; omega

end RankOne

end CFSG.Quasithin.E6.E68Proof
