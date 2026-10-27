module

public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5O2
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
public import CFSG.LocalAnalysis.StandardType.GGTBJOmOddSign

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

@[expose] noncomputable def TBJOmData.torusAut (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    (J : Subgroup ↥(orthDerived Q)) : Subgroup (MulAut (Fin r → Multiplicative (ZMod p))) where
  carrier := {σ | ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (σ f)}
  mul_mem' := by
    rintro σ τ ⟨n, hn, hnσ⟩ ⟨n', hn', hnτ⟩
    refine ⟨n * n', J.mul_mem hn hn', fun f => ?_⟩
    calc n * n' * Δ.τΩ hA f * (n * n')⁻¹ = n * (n' * Δ.τΩ hA f * n'⁻¹) * n⁻¹ := by group
      _ = Δ.τΩ hA (σ (τ f)) := by rw [hnτ f, hnσ (τ f)]
      _ = Δ.τΩ hA ((σ * τ) f) := rfl
  one_mem' := ⟨1, J.one_mem, fun f => by simp⟩
  inv_mem' := by
    rintro σ ⟨n, hn, h⟩
    refine ⟨n⁻¹, J.inv_mem hn, fun f => ?_⟩
    have h1 := h (σ⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    rw [inv_inv, ← h1]
    group

theorem TBJOmData.torusAut_top_fixed [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hA : A ≤ orthDerived Q)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) :
    Δ.torusAut hA ⊤ = signedAut r p := by
  refine le_antisymm ?_ ?_
  · intro σ hσ
    exact mem_of_isSignedPerm
      (fun i => Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩))
      (fun a b hab =>
        Subgroup.subset_closure (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩))
      (tbjA_isSignedPerm_of_induced Δ hA hσ)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro σ (⟨i, -, hi⟩ | ⟨a, -, b, -, hab, hσ⟩)
    · rw [hi]
      obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.signMove hW i
      exact ⟨⟨w, hwΩ⟩, Subgroup.mem_top _, fun f => Subtype.ext (by simpa using hwconj f)⟩
    · rw [hσ]
      obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.swapMove a b hab
      exact ⟨⟨w, hwΩ⟩, Subgroup.mem_top _, fun f => Subtype.ext (by simpa using hwconj f)⟩

theorem TBJOmData.torusAut_top_nf [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hA : A ≤ orthDerived Q)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    Δ.torusAut hA ⊤ = evenSignedAut r p := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  have hlower : TypeDDatum.evenSignedAut r p ≤ Δ.torusAut hA ⊤ := by
    rw [TypeDDatum.evenSignedAut, TypeDDatum.evenSignedSupportedAut]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro σ (⟨a, -, b, -, hab, rfl⟩ | ⟨a, -, b, -, hab, rfl⟩)
    · obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.swapMove a b hab
      exact ⟨⟨w, hwΩ⟩, Subgroup.mem_top _, fun f =>
        Subtype.ext (by simpa [TBJOmData.τΩ] using hwconj f)⟩
    · obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.dinvMove a b hab
      refine ⟨⟨w, hwΩ⟩, Subgroup.mem_top _, fun f => Subtype.ext ?_⟩
      have h := hwconj f
      rw [← OrthExcEven.sgnAut_mul_sgnAut_apply a b f] at h
      simpa [TBJOmData.τΩ] using h
  refine le_antisymm ?_ hlower
  intro σ hσ
  by_contra hnot
  have hp : p.Prime := Fact.out
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 := coord_two_ne_zero hp hp2
    apply h2
    have h' := congrArg (fun x : ZMod p => x + 1) h
    simpa only [neg_add_cancel, ← two_mul, mul_one] using h'.symm
  obtain ⟨π, ε, hε, hu⟩ := tbjA_isSignedPerm_of_induced Δ hA hσ
  have hprodne : ∏ i, ε i ≠ 1 := by
    intro hprod
    apply hnot
    rw [TypeDDatum.evenSignedAut]
    exact tbjA_mem_evenSignedSupportedAut_of (p := p) (r := r) hp2 Finset.univ hε
      (fun i hi => absurd (Finset.mem_univ i) hi)
      (fun i hi => absurd (Finset.mem_univ i) hi) hprod hu
  have hprod_formula : ∀ (δ : Fin r → ZMod p), (∀ i, δ i = 1 ∨ δ i = -1) →
      ∏ i, δ i = (-1 : ZMod p) ^
        (Finset.univ.filter (fun i => δ i = -1)).card := by
    intro δ hδ
    let Tδ : Finset (Fin r) := Finset.univ.filter (fun i => δ i = -1)
    have hc : δ = fun i => if i ∈ Tδ then (-1 : ZMod p) else 1 := by
      funext i
      by_cases hi : i ∈ Tδ
      · rw [if_pos hi]
        exact (Finset.mem_filter.mp hi).2
      · rw [if_neg hi]
        exact (hδ i).resolve_right (by simpa [Tδ] using hi)
    rw [hc, Finset.prod_ite_mem_eq, Finset.prod_const]
    have hfilter : (Finset.univ.filter (fun i =>
        (if i ∈ Tδ then (-1 : ZMod p) else 1) = -1)) = Tδ := by
      ext i
      by_cases hi : i ∈ Tδ
      · simp [hi]
      · simp [hi]
        exact fun h => hneg h.symm
    rw [hfilter]
  let T : Finset (Fin r) := Finset.univ.filter (fun i => ε i = -1)
  have hTprod : ∏ i, ε i = (-1 : ZMod p) ^ T.card := by
    simpa [T] using hprod_formula ε hε
  have hTodd : Odd T.card :=
    Nat.not_even_iff_odd.mp fun he =>
      hprodne (by rw [hTprod, (neg_one_pow_eq_one_iff_even hneg).mpr he])
  have hex : ∃ a, ε a = -1 := by
    by_contra h
    apply hprodne
    apply Finset.prod_eq_one
    intro i _
    exact (hε i).resolve_right fun hi => h ⟨i, hi⟩
  obtain ⟨a, haε⟩ := hex
  have haT : a ∈ T := by simp [T, haε]
  obtain ⟨k, hk⟩ := hTodd
  have hcarderase : (T.erase a).card = 2 * k := by
    rw [Finset.card_erase_of_mem haT]
    omega
  let u' : MulAut (Fin r → Multiplicative (ZMod p)) := σ * sgnAut a
  let ε' : Fin r → ZMod p := Function.update ε a (-ε a)
  have hε' : ∀ i, ε' i = 1 ∨ ε' i = -1 := by
    intro i
    by_cases hia : i = a
    · rw [hia]
      left
      simp [ε', haε]
    · rw [show ε' i = ε i by simp [ε', hia]]
      exact hε i
  have hu' : ∀ f i, toAdd (u' f (π i)) = ε' i * toAdd (f i) := by
    intro f i
    by_cases hia : i = a
    · rw [hia]
      simp [u', ε', MulAut.mul_apply, hu, sgnAut_apply, haε]
    · simp [u', ε', MulAut.mul_apply, hu, sgnAut_apply, Function.update_of_ne hia, hia]
  have hsupp' : Finset.univ.filter (fun i => ε' i = -1) = T.erase a := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, T, ε']
    by_cases hia : i = a
    · rw [hia]
      simp [haε]
      exact fun h => hneg h.symm
    · simp [Function.update_of_ne hia, hia]
  have hprod' : ∏ i, ε' i = 1 := by
    rw [hprod_formula ε' hε', hsupp', hcarderase, pow_mul]
    norm_num
  have hu'even : u' ∈ TypeDDatum.evenSignedAut r p := by
    rw [TypeDDatum.evenSignedAut]
    exact tbjA_mem_evenSignedSupportedAut_of (p := p) (r := r) hp2 Finset.univ hε'
      (fun i hi => absurd (Finset.mem_univ i) hi)
      (fun i hi => absurd (Finset.mem_univ i) hi) hprod' hu'
  have hsign : sgnAut a ∈ Δ.torusAut hA ⊤ := by
    have hu'TA : u' ∈ Δ.torusAut hA ⊤ := hlower hu'even
    have hmem := (Δ.torusAut hA ⊤).mul_mem ((Δ.torusAut hA ⊤).inv_mem hσ) hu'TA
    have hcalc : σ⁻¹ * u' = sgnAut a := by
      change σ⁻¹ * (σ * sgnAut a) = sgnAut a
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rwa [hcalc] at hmem
  obtain ⟨g, -, hg⟩ := hsign
  exact Δ.not_induces_sgnAut_of_noFixed hp2 hQ hA hnf a g hg

end OrthTorus

end CFSG.StandardType

end
