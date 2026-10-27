module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormIsometry
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {p : ℕ} [Fact p.Prime] [NeZero p]

omit [Fact p.Prime] [NeZero p] in
theorem liftConj_descAut {R L : Type} [Group R] [Group L]
    {ψ : L →* R} (hψ : Function.Surjective ψ) (hz : ψ.ker = Subgroup.center L)
    (Λ : R →* MulAut L) (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (β : MulAut L) (x : R) :
    Λ (BstarDesc.descAut hψ hz β x) = β * Λ x * β⁻¹ := by
  obtain ⟨l, rfl⟩ := hψ x
  rw [BstarDesc.descAut_apply hψ hz β l, hΛψ, hΛψ]
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply]

omit [NeZero p] in
theorem ggWNormConcl_of_centralCover_innerAction
    {R L : Type} [Group R] [Group L] [Finite L]
    (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hR : Subgroup.center R = ⊥)
    (Λ : R →* MulAut L) (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (E : Subgroup R) (A : Subgroup (MulAut L)) (hEA : E.map Λ = A)
    (hAut : ∀ β : MulAut R, ∃ r : R, ∀ e ∈ E, β e = r * e * r⁻¹)
    {ιs V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : ιs → MulAut ↥A)
    (h : ιs → V) (α : ιs → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  classical
  obtain ⟨β, -, hβN, hβs⟩ := hs
  have hz : ψ.ker = Subgroup.center L := BstarDesc.ker_eq_center hψ hker hR
  let δ : MulAut R := BstarDesc.descAut hψ hz β
  obtain ⟨r, hr⟩ := hAut δ
  obtain ⟨l, hl⟩ := hψ r
  have hact : ∀ a ∈ A,
      β * a * β⁻¹ = MulAut.conj l * a * (MulAut.conj l)⁻¹ := by
    intro a ha
    rw [← hEA] at ha
    obtain ⟨e, he, rfl⟩ := ha
    calc
      β * Λ e * β⁻¹ = Λ (δ e) := (liftConj_descAut hψ hz Λ hΛψ β e).symm
      _ = Λ (r * e * r⁻¹) := congrArg Λ (hr e he)
      _ = MulAut.conj l * Λ e * (MulAut.conj l)⁻¹ := by
        rw [map_mul, map_mul, map_inv, ← hl, hΛψ]
  have hlN : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L)) := by
    apply Subgroup.mem_normalizer_fintype
    intro a ha
    rw [← hact a ha]
    exact (Subgroup.mem_normalizer_iff.mp hβN a).mp ha
  have hinner : s ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A :=
    Subgroup.subset_closure
      ⟨MulAut.conj l, ⟨l, rfl⟩, hlN, fun a => (hβs a).trans (hact a a.2)⟩
  have hw := ggLin_mem_ggHL_of_closure ι φ h α hgen hinner
  refine ⟨⟨1, ggLin (p := p) ι s, hw, ?_⟩, fun _ => hw⟩
  intro v
  simp

theorem ggAutomizer_eq_range_of_weyl_frame {τ : Tag} {R : Type} [Group R]
    (E : Subgroup R) (t : Multiplicative (Fin τ.rank → ZMod p) →* R)
    (ht : Function.Injective t) (htr : t.range = E)
    (n : Fin τ.rank → R) (hn : ∀ i, n i ∈ Subgroup.normalizer (E : Set R))
    (hns : ∀ i v, n i * t (Multiplicative.ofAdd v) * (n i)⁻¹ =
      t (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) v)))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set R), ∃ u : WeylGroup τ,
      ∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct τ p u v))) :
    (ExcWeylOuter.torusMulAut τ p).range.map
      (MulAut.congr ((MonoidHom.ofInjective ht).trans
        (MulEquiv.subgroupCongr htr))).toMonoidHom = ggAutomizer (⊤ : Subgroup R) E := by
  let κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective ht).trans (MulEquiv.subgroupCongr htr)
  let ρ : WeylGroup τ →* MulAut ↥E :=
    (MulAut.congr κ).toMonoidHom.comp (ExcWeylOuter.torusMulAut τ p)
  have hκ : ∀ v, (κ v : R) = t v := fun _ => rfl
  have hact : ∀ u v, (ρ u (κ (Multiplicative.ofAdd v)) : R) =
      t (Multiplicative.ofAdd (TableBExc.torusAct τ p u v)) := by
    intro u v
    change (κ (ExcWeylOuter.torusMulAut τ p u
      (κ.symm (κ (Multiplicative.ofAdd v)))) : R) = _
    rw [κ.symm_apply_apply, ExcWeylOuter.torusMulAut_apply, hκ]
  have hsimple : ∀ i, ρ (simple τ i) = ggConjAut E (hn i) := by
    intro i
    apply MulEquiv.ext
    intro a
    obtain ⟨v, rfl⟩ := κ.surjective a
    apply Subtype.ext
    rw [← ofAdd_toAdd v, hact, ggConjAut_apply, hκ, hns]
  have hle : ρ.range ≤ ggAutomizer (⊤ : Subgroup R) E := by
    rw [MonoidHom.range_eq_map, ← (CFSG.LieType.Chevalley.coxeterSystem τ).subgroup_closure_range_simple,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hsimple]
    exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top _) (hn i)
  have hge : ggAutomizer (⊤ : Subgroup R) E ≤ ρ.range := by
    rw [ggAutomizer_eq]
    rintro f ⟨g, -, hg, hf⟩
    obtain ⟨u, hu⟩ := hN g hg
    refine ⟨u, ?_⟩
    apply MulEquiv.ext
    intro a
    obtain ⟨v, rfl⟩ := κ.surjective a
    apply Subtype.ext
    rw [← ofAdd_toAdd v, hact, hf, hκ, hu]
  change _ = ggAutomizer (⊤ : Subgroup R) E
  rw [← MonoidHom.range_comp]
  exact le_antisymm hle hge

theorem ggWNormConcl_of_centralCover_weylFrame
    {τ : Tag} {R L : Type} [Group R] [Group L] [Finite L]
    (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hR : Subgroup.center R = ⊥)
    (Λ : R →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛψ : ∀ l, Λ (ψ l) = MulAut.conj l)
    (E : Subgroup R) (A : Subgroup (MulAut L)) (hEA : E.map Λ = A)
    (t : Multiplicative (Fin τ.rank → ZMod p) →* R)
    (ht : Function.Injective t) (htr : t.range = E)
    (n : Fin τ.rank → R) (hn : ∀ i, n i ∈ Subgroup.normalizer (E : Set R))
    (hns : ∀ i v, n i * t (Multiplicative.ofAdd v) * (n i)⁻¹ =
      t (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) v)))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set R), ∃ u : WeylGroup τ,
      ∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct τ p u v)))
    (hAut : ∀ β : MulAut R, (∀ x, β x ∈ E ↔ x ∈ E) →
      ∃ (c : (ZMod p)ˣ) (u : WeylGroup τ), ∀ v,
        β (t (Multiplicative.ofAdd v)) =
          t (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct τ p u v)))
    (hrank : 3 ≤ τ.rank)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {ιs V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : ιs → MulAut ↥A)
    (h : ιs → V) (α : ιs → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  classical
  let κ0 : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥E :=
    (MonoidHom.ofInjective ht).trans (MulEquiv.subgroupCongr htr)
  let κE : ↥E ≃* ↥A :=
    (E.equivMapOfInjective Λ hΛ).trans (MulEquiv.subgroupCongr hEA)
  let κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A := κ0.trans κE
  have hκ : ∀ v, (κ v : MulAut L) = Λ (t v) := fun _ => rfl
  have hWE := ggAutomizer_eq_range_of_weyl_frame E t ht htr n hn hns hN
  have hΛr : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := hψ x
      exact ⟨l, (hΛψ l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨ψ l, hΛψ l⟩
  have hρ : (ExcWeylOuter.torusMulAut τ p).range.map (MulAut.congr κ).toMonoidHom =
      ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
    have hmap := F4AutWeyl.ggAutomizer_map_eq hΛ (⊤ : Subgroup R) E hEA
    rw [Subgroup.map_top, hΛr] at hmap
    rw [hmap, ← hWE, Subgroup.map_map]
    congr 1
  obtain ⟨β, -, hβN, hβs⟩ := hs
  have hz : ψ.ker = Subgroup.center L := BstarDesc.ker_eq_center hψ hker hR
  let δ : MulAut R := BstarDesc.descAut hψ hz β
  have hδ : ∀ x, Λ (δ x) = β * Λ x * β⁻¹ := liftConj_descAut hψ hz Λ hΛψ β
  have hδE : ∀ x, δ x ∈ E ↔ x ∈ E := by
    intro x
    have hm : ∀ x, Λ x ∈ A ↔ x ∈ E := by
      intro z
      rw [← hEA]
      exact Subgroup.mem_map_iff_mem hΛ
    rw [← hm (δ x), hδ, ← hm x]
    exact (Subgroup.mem_normalizer_iff.mp hβN (Λ x)).symm
  obtain ⟨c, u, hu⟩ := hAut δ hδE
  have hact : ∀ v : Fin τ.rank → ZMod p,
      s (κ (Multiplicative.ofAdd v)) =
        κ (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct τ p u v)) := by
    intro v
    apply Subtype.ext
    rw [hβs, hκ, ← hδ, hu, hκ]
  exact ggWNormConcl_of_scalar_weyl_coordinates ι φ h α κ hrank hdet hgen hρ c u hact

end CFSG.StandardType
