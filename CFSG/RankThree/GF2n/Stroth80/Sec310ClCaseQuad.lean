module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem quad_eq_zero_of_orth (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {e f : V} (hef : F e f = 1)
    {A : Subgroup (V ≃ₗ[K] V)} (hfull : ElationFull F (A : Set _) e)
    {Qf : QuadraticForm K V} (hQ : Qf.polarBilin = F) (hAQ : A ≤ orthSubgroup Qf) :
    Qf e = 0 := by
  have he : e ≠ 0 := ne_zero_of_form_eq_one hef
  obtain ⟨ω, hωe, hω⟩ := exists_perp_not_mem_span (F := F) hdim he
  obtain ⟨y, hye, hωy⟩ : ∃ y, F y e = 0 ∧ F ω y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc⟩ := perp_perp hnd halt e ω hcon
    exact hω c hc
  obtain ⟨g, hgA, hg⟩ := hfull (F ω) hωe
  have hQg : ∀ v, Qf (g v) = Qf v := hAQ hgA
  have h1 := hQg y
  rw [hg y hye] at h1
  have h2 : Qf (y + (F ω) y • e) = Qf y + Qf ((F ω) y • e) +
      QuadraticMap.polar Qf y ((F ω) y • e) := by
    simp only [QuadraticMap.polar]
    abel
  have h3 : QuadraticMap.polar Qf y ((F ω) y • e) = F y ((F ω) y • e) := by
    rw [← hQ]
    rfl
  have h4 : F y ((F ω) y • e) = 0 := by
    rw [map_smul, smul_eq_mul, hye, mul_zero]
  have h5 : Qf ((F ω) y • e) = (F ω y * F ω y) * Qf e := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
  rw [h2, h3, h4, h5] at h1
  have h6 : (F ω y * F ω y) * Qf e = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h6 with h7 | h7
  · exact absurd (mul_self_eq_zero.mp h7) hωy
  · exact h7

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective

theorem card_le_of_elationFull (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {e f : V} (hef : F e f = 1)
    {A : Subgroup (V ≃ₗ[K] V)} (hA : A ≤ pointRadSubgroup F e)
    (hfull : ElationFull F (A : Set _) e) : Nat.card K ^ 2 ≤ Nat.card A := by
  haveI := finite_linearEquiv (K := K) (V := V)
  have hD : (A : Set (V ≃ₗ[K] V)) ⊆ pointRad F e := fun g hg => hA hg
  obtain ⟨w, hw0, hwe, hwf⟩ := exists_perp_ne_zero (F := F) hdim e f
  obtain ⟨w', hw'e, hw'f, hww'⟩ := exists_partner hnd halt hef hwe hwf hw0
  have hw'w : F w' w = 1 := by rw [form_comm halt]; exact hww'
  have hex : ∀ p : K × K, ∃ g : A, ∃ c : K,
      (g : V ≃ₗ[K] V) f - f = p.1 • w + p.2 • w' + c • e := by
    intro p
    have hω : F (p.1 • w + p.2 • w') e = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwe, hw'e,
        smul_eq_mul, mul_zero, add_zero]
    obtain ⟨g, hg, c, hc⟩ := ElationFull.om hnd halt hef hD hfull hω
    exact ⟨⟨g, hg⟩, c, hc⟩
  choose G c hG using hex
  have hinj : Function.Injective G := by
    intro p q hpq
    have h1 : p.1 • w + p.2 • w' + c p • e = q.1 • w + q.2 • w' + c q • e := by
      rw [← hG p, ← hG q, hpq]
    have hew : F e w = 0 := by rw [form_comm halt]; exact hwe
    have hew' : F e w' = 0 := by rw [form_comm halt]; exact hw'e
    have h2 := congrArg (fun x => F x w') h1
    have h3 := congrArg (fun x => F x w) h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hww', hew',
      form_self halt, smul_eq_mul, mul_one, mul_zero, add_zero] at h2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hw'w, hew,
      form_self halt, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] at h3
    exact Prod.ext h2 h3
  have := Nat.card_le_card_of_injective G hinj
  rwa [Nat.card_prod, ← sq] at this

end CFSG.RankThree.GF2n.Stroth80.Classify
