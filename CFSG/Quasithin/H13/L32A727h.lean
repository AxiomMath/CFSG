module

public import CFSG.Quasithin.H13.L32A727g
public import CFSG.Quasithin.H13.L32A727f

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_of_odd {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hK : Nat.card ↥K = 3) {y : X} (hy : Odd (orderOf y)) :
    y ∈ Subgroup.centralizer (K : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : IsCyclic ↥K := isCyclic_of_prime_card (p := 3) hK
  have : Finite (MulAut ↥K) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hAut : Nat.card (MulAut ↥K) = 2 := by
    rw [IsCyclic.card_mulAut, hK]
    decide
  set α : MulAut ↥K := MulAut.conjNormal y with hα
  have h1 : orderOf α ∣ orderOf y := by
    rw [hα]
    exact orderOf_map_dvd _ y
  have h2 : orderOf α ∣ 2 := hAut ▸ orderOf_dvd_natCard α
  have h3 : orderOf α = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hy)
  rw [orderOf_eq_one_iff] at h3
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h4 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) h3
  simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h4
  calc k * y = y * k * y⁻¹ * y := by rw [h4]
    _ = y * k := by group

omit [Finite G] in
theorem l1_star_le_centralizer {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} [K.Normal]
    (hK : Nat.card ↥K = 3) (hl1H : l1 T L V ≤ H) :
    modO2Image H (l1 T L V) ≤ Subgroup.centralizer (K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hle : l1 T L V ≤ pre H (Subgroup.centralizer (K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxH : x ∈ H := hl1H (Subgroup.subset_closure hx)
    refine (mem_pre ⟨x, hxH⟩).mpr (mem_centralizer_of_odd hK ?_)
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩) ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hxH]
      exact orderOf_map_dvd _ _
    exact Odd.of_dvd_nat hx.2 h1
  exact (modO2Image_mono' hle).trans (modO2Image_pre _).le

theorem false_of_card_three (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hK3 : Nat.card ↥(X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) = 3)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) : False := by
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  obtain ⟨j, hjL, hj2⟩ := exists_involution_l1_star S h1222 h1332 h1334 hL3
  have hj1 : j ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hj2
    norm_num at hj2
  have hjj : j ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hj2)
  obtain ⟨x, hx, hxF⟩ := not_fix_frattini S h76 hs hXf hjj hj1
  apply hxF
  have hjC := l1_star_le_centralizer hK3 (le_sup_left.trans S.hz.1.1) hjL
  have hc : (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j = j * x := by
    simpa using Subgroup.mem_centralizer_iff.mp hjC _ ⟨x, hx, rfl⟩
  have e : MulAut.conjNormal j x = x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc j * (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j⁻¹ = (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j * j⁻¹ := by
          rw [hc]
      _ = x := by group
  rw [e, inv_mul_cancel]
  exact Subgroup.one_mem _

end CFSG.Quasithin.H13.L32A.R727
