module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTraceInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSmallInner
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

theorem exists_inner_of_linAct_of_odd
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {X : Type} [Group X] [Finite X] (φ : SL(2, F) →* X)
    (hφ : Function.Injective φ) {g : X}
    (hg : g ∈ normalizer (φ.range : Set X))
    (hgo : Odd (orderOf g)) (hlin : LinAct φ g) :
    ∃ r ∈ φ.range, ∀ x ∈ φ.range, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let e : SL(2, F) ≃* φ.range := MonoidHom.ofInjective hφ
  let act : MulAut φ.range := φ.range.normalizerMonoidHom ⟨g, hg⟩
  let α : MulAut SL(2, F) := e.trans (act.trans e.symm)
  have hact : Odd (orderOf act) := Odd.of_dvd_nat hgo (by
    have h := orderOf_map_dvd φ.range.normalizerMonoidHom
      (⟨g, hg⟩ : normalizer (φ.range : Set X))
    rw [Subgroup.orderOf_mk] at h
    exact h)
  have hαeq : α = (MulAut.congr e).symm act := (MulAut.congr_symm_apply e act).symm
  have hαodd : Odd (orderOf α) := by
    rw [hαeq, MulEquiv.orderOf_eq]
    exact hact
  have hφaction : ∀ x : SL(2, F), φ (α x) = g * φ x * g⁻¹ := by
    intro x
    have h : e (α x) = act (e x) := by simp [α]
    have hv := congrArg Subtype.val h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hv
    have h1 : ((e (α x) : φ.range) : X) = φ (α x) := MonoidHom.ofInjective_apply hφ
    have h2 : ((e x : φ.range) : X) = φ x := MonoidHom.ofInjective_apply hφ
    rw [h1, h2] at hv
    exact hv
  obtain ⟨D, hD⟩ := hlin
  have hαtrace : ∀ x : SL(2, F),
      (α x : Matrix (Fin 2) (Fin 2) F).trace =
        (x : Matrix (Fin 2) (Fin 2) F).trace := by
    intro x
    have heq : α x = glConjSL D x := hφ ((hφaction x).trans (hD x))
    rw [heq]
    exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.trace_glConjSL D x
  have hαinner : α ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
    by_cases h3 : 3 < Nat.card F
    · exact mem_range_conj_of_odd_of_trace hodd h3 α hαodd hαtrace
    · have hF : Nat.card F = 3 := by
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      exact mem_range_conj_of_odd_of_card_three hF α hαodd
  obtain ⟨r, hr⟩ := hαinner
  refine ⟨φ r, ⟨r, rfl⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc
    g * φ x * g⁻¹ = φ (α x) := (hφaction x).symm
    _ = φ ((MulAut.conj r) x) := by rw [hr]
    _ = φ r * φ x * (φ r)⁻¹ := by simp only [MulAut.conj_apply, map_mul, map_inv]

theorem exists_inner_normalizer_conj_range_of_linAct
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {X : Type} [Group X] [Finite X] (φ : SL(2, F) →* X)
    (hφ : Function.Injective φ)
    (hlin : ∀ x : X, x * φ (-1) = φ (-1) * x → LinAct φ x)
    (z : X) {g : X}
    (hg : g ∈ normalizer ((φ.range.map (MulAut.conj z).toMonoidHom : Subgroup X) : Set X))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ φ.range.map (MulAut.conj z).toMonoidHom,
      ∀ x ∈ φ.range.map (MulAut.conj z).toMonoidHom,
        g * x * g⁻¹ = r * x * r⁻¹ := by
  let ψ : SL(2, F) →* X := (MulAut.conj z).toMonoidHom.comp φ
  have hψ : Function.Injective ψ := (MulAut.conj z).injective.comp hφ
  have hψrange : ψ.range = φ.range.map (MulAut.conj z).toMonoidHom :=
    MonoidHom.range_comp _ _
  have hgψ : g ∈ normalizer (ψ.range : Set X) := by rwa [hψrange]
  have huniq := isUniqueInvolution_range_sl2 hodd hψ
  have hgc : g * ψ (-1) = ψ (-1) * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (normalizer_le_centralizer huniq hgψ)
  have hgc' : (z⁻¹ * g * z) * φ (-1) = φ (-1) * (z⁻¹ * g * z) := by
    have h := congrArg (fun x : X => z⁻¹ * x * z) hgc
    simpa [ψ, MulAut.conj_apply, mul_assoc] using h
  obtain ⟨D, hD⟩ := hlin (z⁻¹ * g * z) hgc'
  have hlinψ : LinAct ψ g := by
    refine ⟨D, fun x => ?_⟩
    change g * (z * φ x * z⁻¹) * g⁻¹ = z * φ (glConjSL D x) * z⁻¹
    calc
      g * (z * φ x * z⁻¹) * g⁻¹ =
          z * ((z⁻¹ * g * z) * φ x * (z⁻¹ * g * z)⁻¹) * z⁻¹ := by group
      _ = z * φ (glConjSL D x) * z⁻¹ := by rw [hD x]
  obtain ⟨r, hr, hconj⟩ := exists_inner_of_linAct_of_odd hodd ψ hψ hgψ hgo hlinψ
  exact ⟨r, hψrange ▸ hr, fun x hx => hconj x (hψrange.symm ▸ hx)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
