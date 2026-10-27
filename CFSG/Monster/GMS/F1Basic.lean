module

public import CFSG.Monster.GMS.TwoCentral
public import CFSG.Sporadic.Co1
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

theorem GMSLeechCentralizer.card_centralizer
    [Finite G] {z : G} (h : GMSLeechCentralizer z) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ 46 * 1982582476875 := by
  obtain ⟨-, -, hQ, ⟨φ, hφ, hker⟩, -⟩ := h
  have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, Nat.card_congr e.toEquiv,
    CFSG.Sporadic.Co1.card_Co1, hker, hQ]
  norm_num

private theorem factorization_two :
    (2 ^ 46 * 1982582476875 : ℕ).factorization 2 = 46 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem GMSLeechCentralizer.card_sylow
    [Finite G] {z : G} (h : GMSLeechCentralizer z)
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) : Nat.card S = 2 ^ 46 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [S.card_eq_multiplicity, h.card_centralizer, factorization_two]

theorem GMSLeechCentralizer.card_sylow_two
    [Finite G] {z : G} (h : GMSLeechCentralizer z)
    (P : Sylow 2 G) : Nat.card P = 2 ^ 46 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain S : Sylow 2 (Subgroup.centralizer ({z} : Set G)) := default
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_map_of_sylow_centralizer h.1 h.2.1 h.2.2.2.2 S
  have h₀ : Nat.card P₀ = 2 ^ 46 := by
    rw [show Nat.card P₀ = Nat.card (P₀ : Subgroup G) from rfl, hP₀,
      Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set G)).subtype_injective]
    exact h.card_sylow S
  rw [P.card_eq_multiplicity, ← P₀.card_eq_multiplicity, h₀]

theorem GMSLeechCentralizer.exists_sylow_center [Finite G] {z : G} (h : GMSLeechCentralizer z) :
    ∃ P : Sylow 2 G,
      (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype = Subgroup.zpowers z :=
  exists_sylow_center_map_eq_zpowers h.1 h.2.1 h.2.2.2.2

theorem GMSLeechCentralizer.exists_conj_mem_centralizer [Finite G] {z : G}
    (h : GMSLeechCentralizer z) {t : G} (ht : IsPGroup 2 (Subgroup.zpowers t)) :
    ∃ g : G, g * t * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain S : Sylow 2 (Subgroup.centralizer ({z} : Set G)) := default
  obtain ⟨P, hP⟩ := exists_sylow_eq_map_of_sylow_centralizer h.1 h.2.1 h.2.2.2.2 S
  obtain ⟨Q, hQ⟩ := ht.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  have hmem : g * t * g⁻¹ ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) (Q : Subgroup G) htQ
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [hg, hP] at hmem
  obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp hmem
  rw [← hw]
  exact w.2

end CFSG.Monster.GMS
