module

public import CFSG.Quasithin.SteinbergCDExactPlaneWreathResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedGeneral
public import CFSG.Quasithin.Background.B2Thompson

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath

variable {H : Type*} [Group H]

theorem le_commutator_sup_centralizer_of_odd [Finite H] {A P : Subgroup H}
    (hAe : CFSG.Open.IsElemAbelian 2 A) (hPA : P ≤ normalizer (A : Set H))
    (hodd : Odd (Nat.card ↥P)) : A ≤ ⁅A, P⁆ ⊔ (A ⊓ centralizer (P : Set H)) := by
  classical
  let _ : CommGroup ↥A := commGroupOfElemAbelian hAe
  have : Fintype ↥P := Fintype.ofFinite _
  have hconj : ∀ p ∈ P, ∀ x ∈ A, p * x * p⁻¹ ∈ A := fun p hp x hx =>
    (mem_normalizer_iff.mp (hPA hp) x).mp hx
  intro a ha
  let φ : ↥P → (↥A →* ↥A) := fun q =>
    { toFun := fun x => ⟨q * x * q⁻¹, hconj q q.2 x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show (q : H) * ((x : H) * y) * (q : H)⁻¹ = (q * x * (q : H)⁻¹) * (q * y * (q : H)⁻¹)
        group) }
  have hφ : ∀ q : ↥P, ∀ x : ↥A, ((φ q x : ↥A) : H) = q * x * (q : H)⁻¹ := fun _ _ => rfl
  let c : ↥P → ↥A := fun p => φ p ⟨a, ha⟩
  let k : ↥P → ↥A := fun p => ⟨⁅a, (p : H)⁆, by
    have h1 : (p : H) * a⁻¹ * (p : H)⁻¹ ∈ A := hconj p p.2 _ (A.inv_mem ha)
    have e : ⁅a, (p : H)⁆ = a * ((p : H) * a⁻¹ * (p : H)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem ha h1⟩
  have hck : ∀ p, c p * k p = ⟨a, ha⟩ := by
    intro p
    apply Subtype.ext
    show (p : H) * a * (p : H)⁻¹ * ⁅a, (p : H)⁆ = a
    have hcomm : (p : H) * a * (p : H)⁻¹ * a = a * ((p : H) * a * (p : H)⁻¹) := by
      have := hAe.1
      exact setLike_mul_comm (hconj p p.2 a ha) ha
    rw [commutatorElement_def]
    calc (p : H) * a * (p : H)⁻¹ * (a * p * a⁻¹ * (p : H)⁻¹)
        = ((p : H) * a * (p : H)⁻¹ * a) * ((p : H) * a⁻¹ * (p : H)⁻¹) := by group
      _ = (a * ((p : H) * a * (p : H)⁻¹)) * ((p : H) * a⁻¹ * (p : H)⁻¹) := by rw [hcomm]
      _ = a := by group
  have hsq : (⟨a, ha⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 a ha)
  have hprod : (∏ p, c p) * (∏ p, k p) = ⟨a, ha⟩ := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun p _ => hck p, Finset.prod_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hfix : ∀ q : ↥P, φ q (∏ p, c p) = ∏ p, c p := by
    intro q
    rw [map_prod]
    have e : ∀ p, φ q (c p) = c (q * p) := fun p => Subtype.ext (by
      rw [hφ, hφ, hφ]
      push_cast
      group)
    simp_rw [e]
    exact Fintype.prod_equiv (Equiv.mulLeft q) _ _ (fun _ => rfl)
  have hx : ((∏ p, c p : ↥A) : H) ∈ A ⊓ centralizer (P : Set H) := by
    refine ⟨(∏ p, c p).2, mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 := congrArg Subtype.val (hfix ⟨q, hq⟩)
    rw [hφ] at h1
    calc q * ((∏ p, c p : ↥A) : H) = (q * ((∏ p, c p : ↥A) : H) * q⁻¹) * q := by group
      _ = ((∏ p, c p : ↥A) : H) * q := by rw [h1]
  have hy : ((∏ p, k p : ↥A) : H) ∈ ⁅A, P⁆ :=
    Finset.prod_induction k (fun z : ↥A => (z : H) ∈ ⁅A, P⁆)
      (fun z w hz hw => ⁅A, P⁆.mul_mem hz hw) ⁅A, P⁆.one_mem
      (fun p _ => commutator_mem_commutator ha p.2)
  have ha' : a = ((∏ p, c p : ↥A) : H) * ((∏ p, k p : ↥A) : H) :=
    (congrArg Subtype.val hprod).symm
  rw [ha']
  exact mul_mem (mem_sup_right hx) (mem_sup_left hy)

end SteinbergCD

open Subgroup SteinbergCD CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath

end CFSG.Quasithin
