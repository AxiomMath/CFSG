module

public import CFSG.RankThree.PartOne.TCF.StarSimple
public import CFSG.RankThree.PartOne.TCF.Master
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.LargeReeOrder
  CFSG.RankThree.PartOne.KLR

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem layer_of_sector (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) (E : Subgroup (ModGL ReeTag.F4.tag L))
    (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (m : ℕ)
    (hE : Nat.card E = m ^ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' →
          D' = N) ∧
      (N ≠ ⊥ →
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) := by
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF m hE hp hpm
  exact component_data_of_frame D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => starSimple D ha hK w hp hp3 hordb hbT) x hx

end Sector

theorem largeRee_component_data
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' →
          D' = N) ∧
      (N ≠ ⊥ →
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hx ▸ orderOf_dvd_natCard x
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd6 : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1 →
      ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
        N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
        (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
          (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
        (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
          IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' →
            D' = N) ∧
        (N ≠ ⊥ →
          IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) := by
    intro h
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK hp hp3 h x hx
    have hodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) :=
      Nat.odd_iff.2 (by omega)
    refine ⟨⊥, bot_le, ?_, ?_, fun h => absurd rfl h⟩
    · rintro g hg ⟨k, hk⟩
      have hgo : orderOf (⟨g, hg⟩ : Subgroup.centralizer ({x} : Set _)) ∣
          Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hk] at hgo
      have hk0 : k = 0 := by
        by_contra hk0
        have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
        exact h2 (h2dvd.trans hgo)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      rw [hk]
      exact Subgroup.one_mem _
    · rintro D' ⟨hD'C, hD'q, -⟩
      exfalso
      have hodd' : Odd (Nat.card D') := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hD'C)
      have hsol : Group.IsSolvable D' := CFSG.Milestones.odd_order_solvable hodd'
      have : Group.IsPerfect D' := hD'q.1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hD'q
      exact Group.IsPerfect.not_isSolvable D' hsol
  have hdvd' := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd
  rcases hdvd' with h1 | h2 | h3 | h4 | h5
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
    exact layer_of_sector D ha hK wPhi1 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 h1) x hx
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi2 D.isFrob
    exact layer_of_sector D ha hK wPhi2 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp hp3 h2) x hx
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
      exact layer_of_sector D ha hK wPhi4p E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4p hK hp hp3 hpp) x hx
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D.isFrob
      exact layer_of_sector D ha hK wPhi4m E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4m hK hp hp3 hpm) x hx
  · exact hodd6 (Or.inl h4)
  · exact hodd6 (Or.inr h5)

end CFSG.RankThree.PartOne.TCF
