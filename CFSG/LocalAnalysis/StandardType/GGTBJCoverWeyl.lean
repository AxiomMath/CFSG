module

public import CFSG.LocalAnalysis.StandardType.GGTBJCoverBstar
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCover_weyl {G R : Type} [Group G] [Group R] {Bs X : Subgroup G}
    (ψ : ↥X →* R) (hψ : Function.Surjective ψ) (hZR : Subgroup.center R = ⊥)
    {E : Subgroup R} (ε : ↥Bs →* R) (hεE : ∀ b, ε b ∈ E)
    (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hN1 : ∀ g : ↥X, ψ g ∈ Subgroup.normalizer (E : Set R) →
      (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hεconj : ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
      ε ⟨_, hb⟩ = ψ g * ε b * (ψ g)⁻¹)
    (θ : ↥(ggAutomizer X Bs) ≃* ↥(ggAutomizer (⊤ : Subgroup R) E))
    (hθ : ∀ (σ : ↥(ggAutomizer X Bs)) (b : ↥Bs),
      ((θ σ : MulAut ↥E) ⟨ε b, hεE b⟩ : R) = ε ((σ : MulAut ↥Bs) b))
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (wt : GGTorusTorWit m N R (E.map (MulAut.conj : R →* MulAut R)))
    (hw : wt.Holds C M) :
    ∃ (n : Fin N → ↥X) (hn : ∀ k, (n k : G) ∈ Subgroup.normalizer (Bs : Set G))
      (f : M.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ k, ψ (n k) = wt.n k) ∧
      (∀ k, (f (M.simple k) : MulAut ↥Bs) = ggConjAut Bs (hn k)) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range fun k => ggConjAut Bs (hn k)) := by
  classical
  have hci : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAut_conj_injective hZR
  let A₀ : Subgroup (MulAut R) := E.map (MulAut.conj : R →* MulAut R)
  let P : Subgroup (MulAut ↥E) := ggAutomizer (⊤ : Subgroup R) E
  let Q : Subgroup (MulAut ↥A₀) := ggAutomizer (MulAut.conj : R →* MulAut R).range A₀
  let η : ↥E ≃* ↥A₀ := (E.equivMapOfInjective (MulAut.conj : R →* MulAut R) hci).trans
    (MulEquiv.subgroupCongr rfl)
  have hmap : Q = P.map (MulAut.congr η).toMonoidHom := by
    simpa only [Subgroup.map_top] using
      F4AutWeyl.ggAutomizer_map_eq hci (⊤ : Subgroup R) E
        (rfl : E.map (MulAut.conj : R →* MulAut R) = A₀)
  let μ : ↥P ≃* ↥Q :=
    (P.equivMapOfInjective (MulAut.congr η).toMonoidHom (MulAut.congr η).injective).trans
      (MulEquiv.subgroupCongr hmap.symm)
  have hμ : ∀ ρ : ↥P, (μ ρ : MulAut ↥A₀) = MulAut.congr η (ρ : MulAut ↥E) :=
    fun ρ => rfl
  have hnE : ∀ k, wt.n k ∈ Subgroup.normalizer (E : Set R) := by
    intro k
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have h := (Subgroup.mem_normalizer_iff.mp (wt.hn k)) (MulAut.conj e)
    simpa only [← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hci] using h
  let n : Fin N → ↥X := fun k => (hψ (wt.n k)).choose
  have hψn : ∀ k, ψ (n k) = wt.n k := fun k => (hψ (wt.n k)).choose_spec
  have hn : ∀ k, (n k : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro k
    apply hN1
    rw [hψn]
    exact hnE k
  let σ : Fin N → ↥(ggAutomizer X Bs) := fun k =>
    ⟨ggConjAut Bs (hn k), ggConjAut_mem_ggAutomizer (n k).2 (hn k)⟩
  let β : ↥Bs →* ↥E := ε.codRestrict E hεE
  have hβsurj : Function.Surjective β := by
    intro e
    obtain ⟨b, hb⟩ := hεsurj e e.2
    exact ⟨b, Subtype.ext hb⟩
  have hθn : ∀ k, (θ (σ k) : MulAut ↥E) = ggConjAut E (hnE k) := by
    intro k
    refine MulEquiv.ext fun e => ?_
    obtain ⟨b, rfl⟩ := hβsurj e
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hb : (n k : G) * b * (n k : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp (hn k)) (b : G)).mp b.2
    have hσb : (σ k : MulAut ↥Bs) b = ⟨_, hb⟩ :=
      Subtype.ext (ggConjAut_apply Bs (hn k) b)
    change ((θ (σ k) : MulAut ↥E) ⟨ε b, hεE b⟩ : R) =
      wt.n k * ε b * (wt.n k)⁻¹
    rw [hθ, hσb, hεconj, hψn]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgen, fR, hfR⟩ := hw
  let f : M.Group ≃* ↥(ggAutomizer X Bs) := (fR.trans μ.symm).trans θ.symm
  have hμθ : ∀ k, μ (θ (σ k)) = fR (M.simple k) := by
    intro k
    apply Subtype.ext
    rw [hμ, hθn, hfR]
    exact ggConjAut_map_congr (MulAut.conj : R →* MulAut R) hci rfl
      (hnE k) (wt.hn k) rfl
  have hf : ∀ k, (f (M.simple k) : MulAut ↥Bs) = ggConjAut Bs (hn k) := by
    intro k
    have h : f (M.simple k) = σ k := by
      apply θ.injective
      apply μ.injective
      rw [hμθ k]
      simp only [f, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h
  let φR : Fin N → ↥Q := fun k =>
    ⟨ggConjAut A₀ (wt.hn k), ggConjAut_mem_ggAutomizer
      (show MulAut.conj (wt.n k) ∈ (MulAut.conj : R →* MulAut R).range from ⟨wt.n k, rfl⟩)
      (wt.hn k)⟩
  have hφR : ∀ k, φR k = fR (M.simple k) := fun k => Subtype.ext (hfR k).symm
  have hsimple : Subgroup.closure (Set.range φR) = (⊤ : Subgroup ↥Q) := by
    apply Subgroup.map_injective (show Function.Injective Q.subtype from Subtype.val_injective)
    rw [MonoidHom.map_closure, Subgroup.map_top, ← Set.range_comp', Subgroup.range_subtype]
    change Subgroup.closure (Set.range fun k => ggConjAut A₀ (wt.hn k)) = Q
    exact hgen.symm
  let γ : ↥Q →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp
    (θ.symm.toMonoidHom.comp μ.symm.toMonoidHom)
  have hγrange : γ.range = ggAutomizer X Bs := by
    ext τ
    constructor
    · rintro ⟨ρ, rfl⟩
      exact (θ.symm (μ.symm ρ)).2
    · intro hτ
      refine ⟨μ (θ ⟨τ, hτ⟩), ?_⟩
      change (θ.symm (μ.symm (μ (θ ⟨τ, hτ⟩))) : MulAut ↥Bs) = τ
      simp only [MulEquiv.symm_apply_apply]
  have hγφ : ∀ k, γ (φR k) = ggConjAut Bs (hn k) := by
    intro k
    rw [hφR]
    exact hf k
  have hclos := congrArg (Subgroup.map γ) hsimple
  rw [MonoidHom.map_closure, Subgroup.map_top, ← Set.range_comp', hγrange] at hclos
  exact ⟨n, hn, f, hψn, hf, by simpa only [hγφ] using hclos.symm⟩

end CFSG.StandardType

end
