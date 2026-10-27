module

public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Background.A318PG2
public import CFSG.Quasithin.Background.A318PD4
public import CFSG.Quasithin.Background.A318PF4Frame

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.A318P CFSG.RankThree.PartTwo.KFacts

section Chevalley

theorem two_le_pRank_three_isG2 {f : ℕ} {X : Type} [Group X] [Finite X] (h : IsG2 2 f X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hKcard, ⟨e⟩⟩ := h
  have hch : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hKcard
  obtain ⟨hZ, hZA, hZZ, -⟩ := charTwo_facts_of_rankOne witnessG2 witnessG2_check
    witnessG2_orthoCheck (K := K) (fun i => rankOneZ_facts_g2 (witnessG2.simple i))
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.le_pRank_three_center_quotient (witnessG2.elemZ K) (witnessG2.elemA K)
    (fun i => (hZ i).1) (fun i => (hZ i).2.1) (fun i => (hZ i).2.2) hZA hZZ

theorem two_le_pRank_three_is3D4 {f : ℕ} {X : Type} [Group X] [Finite X] (h : Is3D4 2 f X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  classical
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨-, K, hKf, hKfin, hKcard, σ₀, hσ₀, ⟨e⟩⟩ := h
  have hK : Nat.card K = (2 ^ f) ^ 3 := by rw [hKcard]; rfl
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 3 * f)
    (by rw [hK, ← pow_mul, mul_comm])
  have hbij : Function.Bijective σ₀ :=
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨iso⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  let ψ : X ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans iso
  obtain ⟨E, hE9, hEel, -⟩ := exists_nine_d4 (K := K) σ.toRingHom (RingEquiv.refl K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) ψ]
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hEel (k := 2) (by rw [hE9]; norm_num)

theorem two_le_pRank_three_is2F4 {f : ℕ} {X : Type} [Group X] [Finite X] (h : Is2F4 f X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
  obtain ⟨E, hE9, hEel, -⟩ := exists_nine_gamma (K := K) a (RingEquiv.refl K)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (reeFixedEquivGamma a))]
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hEel (k := 2) (by rw [hE9]; norm_num)

end Chevalley

end CFSG.Quasithin.R3c3
