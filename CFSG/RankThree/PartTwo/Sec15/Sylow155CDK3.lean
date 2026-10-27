module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec15.Sylow155B3Q
import CFSG.RankThree.PartTwo.Sec15.Sylow155KA6
import CFSG.RankThree.PartTwo.Sec15.Sylow155KA6P
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

private theorem card_alternatingGroup_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem eq_one_of_commute_of_pow_three {Q : Type} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hT : Sec4.IsTripleCover Q (alternatingGroup (Fin 6)))
    {σ τ : MulAut Q} (hσZ : ∀ z ∈ Subgroup.center Q, σ z = z)
    (hστ : σ * τ = τ * σ) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hσ3 : ¬ 3 ∣ orderOf σ) : σ = 1 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  obtain ⟨ψ⟩ := QuasithinUnique.Out21.A6.exists_psl29_equiv
  have hcard : Nat.card Q = 1080 := by
    have h1 := (Subgroup.center Q).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr e.toEquiv, hZ, card_alternatingGroup_six'] at h1
    exact h1
  let ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29 := e.trans ψ.symm
  have hβ3 : ((Sylow155B3Q.rhoQ ψ6 τ : ↥A6Models.autA6) : P10) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hτ3, map_one, Subgroup.coe_one]
  have hβ1 : ((Sylow155B3Q.rhoQ ψ6 τ : ↥A6Models.autA6) : P10) ≠ 1 := fun h =>
    hτ1 ((Sylow155B3Q.rhoQ_eq_one_iff hperf ψ6 τ).1 (Subtype.ext h))
  have hβpsl : ((Sylow155B3Q.rhoQ ψ6 τ : ↥A6Models.autA6) : P10) ∈ A6Models.psl29 :=
    (mem_psl29_of_prime_pow Nat.prime_three (by norm_num) (Sylow155B3Q.rhoQ ψ6 τ).2 hβ3 hβ1).1
  have hαβ : ((Sylow155B3Q.rhoQ ψ6 σ : ↥A6Models.autA6) : P10) *
      ((Sylow155B3Q.rhoQ ψ6 τ : ↥A6Models.autA6) : P10) =
      ((Sylow155B3Q.rhoQ ψ6 τ : ↥A6Models.autA6) : P10) *
        ((Sylow155B3Q.rhoQ ψ6 σ : ↥A6Models.autA6) : P10) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hστ]
  have hαm : ((Sylow155B3Q.rhoQ ψ6 σ : ↥A6Models.autA6) : P10) ∈ A6Models.m10 :=
    mem_m10_of_fixes_center hperf hZ hcard ψ6 hσZ (Sylow155B3Q.rhoQ ψ6 σ).2
      (Sylow155B3Q.rhoQ_spec ψ6 σ) hβpsl hβ3 hβ1 hαβ
  have hα3 : ¬ 3 ∣ orderOf ((Sylow155B3Q.rhoQ ψ6 σ : ↥A6Models.autA6) : P10) := by
    intro h
    rw [Subgroup.orderOf_coe] at h
    exact hσ3 (h.trans (orderOf_map_dvd (Sylow155B3Q.rhoQ ψ6) σ))
  have hα1 := Sylow155KA6P.eq_one_of_mem_m10_of_coprime hβpsl hβ3 hβ1 hαm hαβ hα3
  exact (Sylow155B3Q.rhoQ_eq_one_iff hperf ψ6 σ).1 (Subtype.ext hα1)

private theorem mem_normalizer_of_forall_mem {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q}
    {g : Q} (hg : ∀ x ∈ J, g * x * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set Q) :=
  Subgroup.mem_normalizer_iff.2 fun x =>
    (Sylow155KA6.apply_mem_iff_of_finite (MulAut.conj g) hg x).symm

theorem conj_eq_of_commute_of_pow_three {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q}
    (hperf : commutator ↥J = ⊤) (hT : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    {g f : Q} (hgJ : ∀ x ∈ J, g * x * g⁻¹ ∈ J) (hfJ : ∀ x ∈ J, f * x * f⁻¹ ∈ J)
    (hgZ : ∀ z ∈ Sec14.Item148PtRes.centerIn J, g * z * g⁻¹ = z)
    (hgf : g * f = f * g) (hf3 : f ^ 3 = 1) (hf1 : ∃ x ∈ J, f * x * f⁻¹ ≠ x)
    (hg3 : ¬ 3 ∣ orderOf g) : ∀ x ∈ J, g * x * g⁻¹ = x := by
  have hgN := mem_normalizer_of_forall_mem hgJ
  have hfN := mem_normalizer_of_forall_mem hfJ
  have hσ : ∀ x : ↥J, ((J.normalizerMonoidHom ⟨g, hgN⟩ x : ↥J) : Q) = g * x * g⁻¹ :=
    fun x => rfl
  have hτ : ∀ x : ↥J, ((J.normalizerMonoidHom ⟨f, hfN⟩ x : ↥J) : Q) = f * x * f⁻¹ :=
    fun x => rfl
  have h1 : J.normalizerMonoidHom ⟨g, hgN⟩ = 1 := by
    refine eq_one_of_commute_of_pow_three hperf hT (σ := J.normalizerMonoidHom ⟨g, hgN⟩)
      (τ := J.normalizerMonoidHom ⟨f, hfN⟩) (fun z hz => Subtype.ext ?_) ?_ ?_ ?_ ?_
    · rw [hσ]
      exact hgZ z (Subgroup.mem_map.2 ⟨z, hz, rfl⟩)
    · rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hgf)
    · rw [← map_pow, ← map_one J.normalizerMonoidHom]
      exact congrArg _ (Subtype.ext (by simpa using hf3))
    · intro h
      obtain ⟨x, hx, hne⟩ := hf1
      apply hne
      have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : Q)) h
      simpa [hτ] using h2
    · intro h
      refine hg3 (h.trans ?_)
      have h2 := orderOf_map_dvd J.normalizerMonoidHom (⟨g, hgN⟩ : Subgroup.normalizer (J : Set Q))
      rwa [← Subgroup.orderOf_coe] at h2
  intro x hx
  have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : Q)) h1
  simpa [hσ] using h2

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
