module

public import CFSG.Quasithin.Recognition.Kleidman.F204.NatAThree

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

def Mc {H M : Subgroup G} (d : Geo H M) (r : G) : Subgroup G :=
  Zv d ⊓ Subgroup.centralizer ({r} : Set G)

omit [Finite G] in
theorem mem_Mc {H M : Subgroup G} {d : Geo H M} {r x : G} :
    x ∈ Mc d r ↔ x ∈ Zv d ∧ x * r = r * x := by
  unfold Mc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

omit [Finite G] in
theorem mem_Mc_conj {H M : Subgroup G} (e : ↥(H ⊔ M)) (d : Geo H M) (r x : G) :
    x ∈ Mc (e • d) ((e : G) * r * (e : G)⁻¹) ↔ (e : G)⁻¹ * x * (e : G) ∈ Mc d r := by
  rw [mem_Mc, mem_Mc, Zv_smul, mem_conjSub]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    calc (e : G)⁻¹ * x * (e : G) * r = (e : G)⁻¹ * (x * ((e : G) * r * (e : G)⁻¹)) * (e : G) := by group
      _ = (e : G)⁻¹ * (((e : G) * r * (e : G)⁻¹) * x) * (e : G) := by rw [h]
      _ = r * ((e : G)⁻¹ * x * (e : G)) := by group
  · intro h
    calc x * ((e : G) * r * (e : G)⁻¹) = (e : G) * (((e : G)⁻¹ * x * (e : G)) * r) * (e : G)⁻¹ := by group
      _ = (e : G) * (r * ((e : G)⁻¹ * x * (e : G))) * (e : G)⁻¹ := by rw [h]
      _ = ((e : G) * r * (e : G)⁻¹) * x := by group

section Alike

variable (F : Frame L1 L2 S D X)
include F

theorem three_mul_QE {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) :
    ∃ E : Subgroup G, E ≤ stab δ ∧ Nat.card E = 3 ∧
      ∀ t ∈ stab δ, t ^ 3 = 1 → ∃ q ∈ Qv δ, ∃ e ∈ E, t = q * e := by
  obtain ⟨E, hEδ, hE3, -, hball⟩ := ballStab_one_false F hδ
  have hEn : E ≤ Subgroup.normalizer (Qv δ : Set G) :=
    hEδ.trans (le_normalizer_pCoreOf 2 (stab δ))
  refine ⟨E, hEδ, hE3, fun t ht ht3 => ?_⟩
  have htb : t ∈ ballStab 1 δ := by
    rw [mem_ballStab]
    intro ε hε
    rcases (dist_le_one_iff rfl).mp hε with rfl | hadj
    · exact ht
    · exact three_mem_stab_nbr F hδ hadj ht ht3
  rw [hball] at htb
  exact (F1.mem_sup_iff_exists_mul_of_normalizes hEn).mp htb

theorem Mc_eq_of_three {d : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hd : vtype d = false) {r r' : G}
    (hr : r ∈ stab d) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) (hr' : r' ∈ stab d) (hr'3 : r' ^ 3 = 1)
    (hr'1 : r' ≠ 1) : Mc d r = Mc d r' := by
  have hA := Amal.of_frame F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEd, hE3, hQE⟩ := three_mul_QE F hd
  have hQC : ∀ q ∈ Qv d, ∀ z ∈ Zv d, q * z = z * q := fun q hq z hz =>
    Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv d hz).2 q hq
  obtain ⟨q, hq, e, he, hre⟩ := hQE r hr hr3
  obtain ⟨q', hq', e', he', hre'⟩ := hQE r' hr' hr'3
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at hre
    exact hr1 (by rw [hre]; exact eq_one_of_mem_Qv_of_pow_three hq (hre ▸ hr3))
  have he'1 : e' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hre'
    exact hr'1 (by rw [hre']; exact eq_one_of_mem_Qv_of_pow_three hq' (hre' ▸ hr'3))
  have hgen : ∀ e₀ ∈ E, e₀ ≠ 1 → Subgroup.zpowers e₀ = E := by
    intro e₀ he₀ he₀1
    have he₀3 : e₀ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥E) (x := ⟨e₀, he₀⟩)
      rw [hE3] at this
      simpa using congrArg Subtype.val this
    have hord : orderOf e₀ = 3 := orderOf_eq_prime he₀3 he₀1
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₀)
      (by rw [hE3, Nat.card_zpowers, hord])
  have key : ∀ (t q₀ e₀ : G), q₀ ∈ Qv d → t = q₀ * e₀ → ∀ z ∈ Zv d,
      (z * t = t * z ↔ z * e₀ = e₀ * z) := by
    intro t q₀ e₀ hq₀ ht z hz
    rw [ht]
    have hqz := hQC q₀ hq₀ z hz
    constructor
    · intro h
      calc z * e₀ = q₀⁻¹ * (q₀ * z) * e₀ := by group
        _ = q₀⁻¹ * (z * q₀) * e₀ := by rw [hqz]
        _ = q₀⁻¹ * (z * (q₀ * e₀)) := by group
        _ = q₀⁻¹ * ((q₀ * e₀) * z) := by rw [h]
        _ = e₀ * z := by group
    · intro h
      calc z * (q₀ * e₀) = (z * q₀) * e₀ := by group
        _ = (q₀ * z) * e₀ := by rw [← hqz]
        _ = q₀ * (z * e₀) := by group
        _ = q₀ * (e₀ * z) := by rw [h]
        _ = (q₀ * e₀) * z := by group
  have hEcent : ∀ z ∈ Zv d, ∀ e₀ ∈ E, e₀ ≠ 1 → z * e₀ = e₀ * z → ∀ y ∈ E, z * y = y * z := by
    intro z hz e₀ he₀ he₀1 hze y hy
    rw [← hgen e₀ he₀ he₀1] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute z e₀ from hze) k).eq
  ext x
  rw [mem_Mc, mem_Mc]
  refine and_congr_right fun hx => ?_
  rw [key r q e hq hre x hx, key r' q' e' hq' hre' x hx]
  constructor
  · intro h
    exact hEcent x hx e he he1 h e' he'
  · intro h
    exact hEcent x hx e' he' he'1 h e he

end Alike

end CFSG.Quasithin.Kleidman.F204
