module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

theorem str83G4_exists_delta_two
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) {x : G} (hx : x ∈ d.D1) :
    ∃ δ ∈ d.D2, ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
  obtain ⟨hF, -, ha, -, hL2, -⟩ := hfr
  have hR : Hyp111R L2 L1 S := (Hyp111R.of_hyp111 rankOneListedFacts hF.1).symm
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hD1leB : d.D1 ≤ bigB L2 L1 S := by
    rw [bigB_comm]
    exact d.hD1hall.1.trans hB1B
  have hcomm' : ∀ y ∈ d.D2, ∀ z ∈ d.D1, y * z = z * y :=
    fun y hy z hz => (d.hcomm z hz y hy).symm
  have hBt : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  exact exists_commutator_lift hF.1.symm hR d.hD2hall d.hD2sup hD1leB hcomm' hBt
    (fun Q t ht htQ σ hσQ hσD =>
      BenderType.aut_eq_conj_cartan_linear hBt Q ht htQ σ hσQ hσD) hx

theorem str83G4_d1_sup_d2_le_conjugate_p1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    d.D1 ⊔ d.D2 ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
  have hfr' := hfr
  obtain ⟨hF, -, -, -, -, -⟩ := hfr
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  have hD1B : d.D1 ≤ bigB L1 L2 S := d.hD1hall.1.trans hB1B
  have hD2B : d.D2 ≤ bigB L1 L2 S := d.hD2hall.1.trans hB2B
  have hK2B : ∀ z : ↥(L2 ⊔ bigB L1 L2 S), z ∈ f112K2 L1 L2 S →
      (z : G) ∈ bigB L1 L2 S := by
    intro z hz
    have hinf : (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
      rw [inf_comm]
      exact f112_parabolic_inf_eq_bigB hF
    have hzX : (z : G) ∈ (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) :=
      Subgroup.normalCore_le (((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L2 ⊔ bigB L1 L2 S)) hz
    rwa [hinf] at hzX
  have hD2 : d.D2 ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
    intro x hx
    rw [CFSG.conjugate, Subgroup.mem_map]
    refine ⟨d.w * x * d.w⁻¹, ?_, ?_⟩
    · rw [d.hwInv x hx]
      exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (hD2B (d.D2.inv_mem hx))
    · change d.w⁻¹ * (d.w * x * d.w⁻¹) * (d.w⁻¹)⁻¹ = x
      group
  have hD1 : d.D1 ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
    intro x hx
    obtain ⟨y, hyD2, hy⟩ := str83G4_exists_delta_two hfr' d hx
    have hyB : y ∈ bigB L1 L2 S := hD2B hyD2
    have heB : x * y⁻¹ ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem (hD1B hx) ((bigB L1 L2 S).inv_mem hyB)
    have hwP2 : d.w ∈ L2 ⊔ bigB L1 L2 S :=
      (show L2 ⊔ S ≤ L2 ⊔ bigB L1 L2 S from
        sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
    let wP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨d.w, hwP2⟩
    let eP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨x * y⁻¹, Subgroup.mem_sup_right heB⟩
    have heK2 : eP ∈ f112K2 L1 L2 S :=
      f112_mem_K2_of_commutator_mem hF.1 heB hy
    have hconj : wP * eP * wP⁻¹ ∈ f112K2 L1 L2 S :=
      (f112K2_normal L1 L2 S).conj_mem eP heK2 wP
    have hweB : d.w * (x * y⁻¹) * d.w⁻¹ ∈ bigB L1 L2 S := by
      have h := hK2B (wP * eP * wP⁻¹) hconj
      simpa using h
    have hwxB : d.w * x * d.w⁻¹ ∈ bigB L1 L2 S := by
      have h1 : d.w * x * d.w⁻¹ =
          (d.w * (x * y⁻¹) * d.w⁻¹) * (d.w * y * d.w⁻¹) := by
        rw [show x = (x * y⁻¹) * y from by group]
        group
      rw [h1, d.hwInv y hyD2]
      exact (bigB L1 L2 S).mul_mem hweB ((bigB L1 L2 S).inv_mem hyB)
    rw [CFSG.conjugate, Subgroup.mem_map]
    exact ⟨d.w * x * d.w⁻¹, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hwxB, by
      change d.w⁻¹ * (d.w * x * d.w⁻¹) * (d.w⁻¹)⁻¹ = x
      group⟩
  exact sup_le hD1 hD2

theorem str83G4_d1_sup_d2_le_normalizer
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) ∧
      d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) ∧
      d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (CFSG.conjugate (Z1 L1 L2 S) d.w : Set G) ∧
      d.D1 ⊔ d.D2 ≤ Subgroup.normalizer
        ((str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w : Subgroup G) : Set G) := by
  have hH := str83G4_d1_sup_d2_le_conjugate_p1 hfr d
  have hconj_normalizer : ∀ {A C : Subgroup G}, A ≤ Subgroup.normalizer (C : Set G) →
      CFSG.conjugate A d.w ≤ Subgroup.normalizer (CFSG.conjugate C d.w : Set G) := by
    intro A C hAC
    calc CFSG.conjugate A d.w
        ≤ CFSG.conjugate (Subgroup.normalizer (C : Set G)) d.w := by
          exact Subgroup.map_mono (f := (MulAut.conj d.w⁻¹).toMonoidHom) hAC
      _ = Subgroup.normalizer (CFSG.conjugate C d.w : Set G) := by
          simpa [CFSG.conjugate] using
            (Subgroup.map_equiv_normalizer_eq C (MulAut.conj d.w⁻¹))
  have hQ1 : d.D1 ⊔ d.D2 ≤
      Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) :=
    hH.trans (hconj_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)))
  have hX : d.D1 ⊔ d.D2 ≤
      Subgroup.normalizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) :=
    hH.trans (hconj_normalizer (le_normalizer_str83X L1 L2 S))
  have hZ1 : d.D1 ⊔ d.D2 ≤
      Subgroup.normalizer (CFSG.conjugate (Z1 L1 L2 S) d.w : Set G) :=
    hH.trans (hconj_normalizer
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
  have hHB : d.D1 ⊔ d.D2 ≤ bigB L1 L2 S :=
    sup_le (d.hD1hall.1.trans (le_sup_left.trans le_sup_left))
      (d.hD2hall.1.trans (le_sup_right.trans le_sup_left))
  have hHX : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    hHB.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (le_normalizer_str83X L1 L2 S))
  exact ⟨hQ1, hX, hZ1,
    (le_inf hHX hQ1).trans Subgroup.inf_normalizer_le_normalizer_inf⟩

end CFSG.Quasithin.Stroth

end
