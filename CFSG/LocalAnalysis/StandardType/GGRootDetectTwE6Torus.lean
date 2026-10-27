module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE6
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.TwistedE6.Datum

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RootDetectTwE6

theorem toWeight_rho (γ : Fin (Tag.rank .E6) → ℤ) (j : Fin (Tag.rank .E6)) :
    MinData.toWeight (rho γ) (rhoPerm j) = MinData.toWeight γ j := by
  simp only [MinData.toWeight, rho, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp rhoPerm]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show Tag.E6.cartan (rhoPerm j) (rhoPerm x) = Tag.E6.cartan j x from
    TwistTag.cartan_perm .E6 j x]

theorem rhoPerm_rhoPerm (j : Fin (Tag.rank .E6)) : rhoPerm (rhoPerm j) = j := by
  revert j
  decide

theorem e6Root_twTorus : ∀ k : Fin 72,
    (rho (C2E6Std.e6Root k) = C2E6Std.e6Root k → ∃ j : Fin (Tag.rank .E6), rhoPerm j = j ∧
      (MinData.toWeight (C2E6Std.e6Root k) j = 1 ∨ MinData.toWeight (C2E6Std.e6Root k) j = -1)) ∧
    (rho (C2E6Std.e6Root k) ≠ C2E6Std.e6Root k → ∃ j : Fin (Tag.rank .E6),
      (MinData.toWeight (C2E6Std.e6Root k) j = 1 ∨ MinData.toWeight (C2E6Std.e6Root k) j = -1) ∧
        MinData.toWeight (C2E6Std.e6Root k) (rhoPerm j) = 0) := by
  decide +kernel

theorem exists_node_fixed {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (hfix : rho γ = γ) : ∃ j : Fin (Tag.rank .E6), rhoPerm j = j ∧
      (MinData.toWeight γ j = 1 ∨ MinData.toWeight γ j = -1) := by
  obtain ⟨k, rfl⟩ := C2E6Std.exists_e6Root_eq hγ
  exact (e6Root_twTorus k).1 hfix

theorem exists_node_pair {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (hne : rho γ ≠ γ) : ∃ j : Fin (Tag.rank .E6),
      (MinData.toWeight γ j = 1 ∨ MinData.toWeight γ j = -1) ∧
        MinData.toWeight γ (rhoPerm j) = 0 := by
  obtain ⟨k, rfl⟩ := C2E6Std.exists_e6Root_eq hγ
  exact (e6Root_twTorus k).2 hne

theorem rootChar_rho {K : Type} [Field K] (θ : K →+* K) (b : Fin (Tag.rank .E6) → Kˣ)
    (hb : ∀ i, b (rhoPerm i) = Units.map (θ : K →* K) (b i)) (γ : Fin (Tag.rank .E6) → ℤ) :
    rootChar b (rho γ) = Units.map (θ : K →* K) (rootChar b γ) := by
  simp only [rootChar, rho, permLattice, Function.comp_apply, map_prod, map_zpow]
  rw [← Equiv.prod_comp rhoPerm]
  simp only [Equiv.symm_apply_apply, hb]

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {h : G}
    (hA : h ∈ Subgroup.normalizer (A : Set G)) (hB : h ∈ Subgroup.normalizer (B : Set G)) :
    h ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) → ∀ g ∈ A ⊔ B, x * g * x⁻¹ ∈ A ⊔ B := by
    intro x hxA hxB g hg
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxA y).mp hy)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxB y).mp hy)
    exact hle hg
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key h hA hB g, fun hg => ?_⟩
  have := key h⁻¹ (inv_mem hA) (inv_mem hB) _ hg
  simpa [mul_assoc] using this

section Torus


theorem mem_ggTorus_twisted {K : Type} [Field K] (θ : K →+* K) {h : fixedGroup K θ}
    (hh : (h : e6Data_valid.minGroup K) ∈ ggTorus (e6Datum K)) :
    h ∈ ggTorus (twistedDatum K θ) := by
  simp only [ggTorus, Subgroup.mem_iInf]
  intro β hβ
  have hβ' : IsRoot .F4 β := isRoot_of_mem_twistedDatum_roots θ hβ
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ'
  have hn : ∀ γ, IsRoot .E6 γ → (h : e6Data_valid.minGroup K) ∈
      Subgroup.normalizer (e6Data_valid.rootGroup K γ : Set (e6Data_valid.minGroup K)) := by
    intro γ hγ
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh γ ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 K).mpr hγ)
  have hS := mem_normalizer_sup (hn _ hα) (hn _ (isRoot_rho hα))
  rw [Subgroup.mem_normalizer_iff]
  intro g
  change g ∈ twistedRootGroup K θ β ↔ h * g * h⁻¹ ∈ twistedRootGroup K θ β
  rw [mem_twistedRootGroup_iff θ hα hp, mem_twistedRootGroup_iff θ hα hp]
  exact Subgroup.mem_normalizer_iff.mp hS (g : e6Data_valid.minGroup K)

theorem exists_twistedTorus {K : Type} [Field K] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (b : Fin (Tag.rank .E6) → Kˣ) (hb : ∀ i, b (rhoPerm i) = Units.map (θ : K →* K) (b i))
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) :
    ∃ h : fixedGroup K θ, (h : e6Data_valid.minGroup K) ∈ ggTorus (e6Datum K) ∧
      (∀ c, (h : e6Data_valid.minGroup K) * e6Data_valid.xm K α₀ c *
        (h : e6Data_valid.minGroup K)⁻¹ = e6Data_valid.xm K α₀ ((rootChar b α₀ : K) * c)) ∧
      (∀ c, (h : e6Data_valid.minGroup K) * e6Data_valid.xm K (rho α₀) c *
        (h : e6Data_valid.minGroup K)⁻¹ =
          e6Data_valid.xm K (rho α₀) ((rootChar b (rho α₀) : K) * c)) := by
  have hρ := rootChar_rho θ b hb
  have hθθ : ∀ t : Kˣ, Units.map (θ : K →* K) (Units.map (θ : K →* K) t) = t :=
    units_map_map θ hθ
  have hT : ∀ (j : Fin (Tag.rank .E6)) (t : Kˣ),
      e6Data_valid.hm K j t ∈ ggTorus (e6Datum K) := fun j t =>
    RootDetectExc.hm_mem_ggTorus e6Data_valid isFiniteType_cartan_E6 K j t
  have hzpow : ∀ (x : Kˣ) (ε : ℤ), (ε = 1 ∨ ε = -1) → (x ^ ε) ^ ε = x := by
    intro x ε hε
    rw [← zpow_mul]
    rcases hε with rfl | rfl <;> norm_num
  by_cases hfix : rho α₀ = α₀
  ·
    obtain ⟨j, hj, hw⟩ := exists_node_fixed hα₀ hfix
    set ε := MinData.toWeight α₀ j with hε
    set t : Kˣ := rootChar b α₀ ^ ε with ht
    have hθt : Units.map (θ : K →* K) t = t := by
      rw [ht, map_zpow, ← hρ, hfix]
    have hmem : e6Data_valid.hm K j t ∈ fixedGroup K θ := by
      rw [mem_fixedGroup, sigma_hm, hj, hθt]
    refine ⟨⟨_, hmem⟩, hT j t, fun c => ?_, fun c => ?_⟩
    · change e6Data_valid.hm K j t * _ * (e6Data_valid.hm K j t)⁻¹ = _
      rw [e6Data_valid.hm_conj_xm K hα₀ j t c, ← hε, ht, hzpow _ _ hw]
    · change e6Data_valid.hm K j t * _ * (e6Data_valid.hm K j t)⁻¹ = _
      rw [hfix, e6Data_valid.hm_conj_xm K hα₀ j t c, ← hε, ht, hzpow _ _ hw]
  ·
    obtain ⟨j, hw, hw0⟩ := exists_node_pair hα₀ hfix
    set ε := MinData.toWeight α₀ j with hε
    set t : Kˣ := rootChar b α₀ ^ ε with ht
    set t' : Kˣ := Units.map (θ : K →* K) t with ht'
    have hmem : e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t' ∈ fixedGroup K θ := by
      rw [mem_fixedGroup, map_mul, sigma_hm, sigma_hm, rhoPerm_rhoPerm, ht', hθθ]
      exact (hm_commute _ _ _ _).eq
    have hw1 : MinData.toWeight (rho α₀) j = 0 := by
      rw [← rhoPerm_rhoPerm j, toWeight_rho, hw0]
    have hw2 : MinData.toWeight (rho α₀) (rhoPerm j) = ε := toWeight_rho α₀ j
    have hconj : ∀ γ, IsRoot .E6 γ → ∀ c,
        e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t' * e6Data_valid.xm K γ c *
          (e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t')⁻¹ =
        e6Data_valid.xm K γ (((t ^ MinData.toWeight γ j : Kˣ) : K) *
          (((t' ^ MinData.toWeight γ (rhoPerm j) : Kˣ) : K) * c)) := by
      intro γ hγ c
      rw [mul_inv_rev, show ∀ x y z w v : e6Data_valid.minGroup K,
        x * y * z * (w * v) = x * (y * z * w) * v from fun _ _ _ _ _ => by group,
        e6Data_valid.hm_conj_xm K hγ, e6Data_valid.hm_conj_xm K hγ]
    refine ⟨⟨_, hmem⟩, mul_mem (hT j t) (hT _ t'), fun c => ?_, fun c => ?_⟩
    · change e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t' * _ *
        (e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t')⁻¹ = _
      rw [hconj α₀ hα₀ c, ← hε, hw0, zpow_zero, Units.val_one, one_mul, ht, hzpow _ _ hw]
    · change e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t' * _ *
        (e6Data_valid.hm K j t * e6Data_valid.hm K (rhoPerm j) t')⁻¹ = _
      rw [hconj (rho α₀) (isRoot_rho hα₀) c, hw1, hw2, zpow_zero, Units.val_one, one_mul, ht',
        ht, ← map_zpow, hzpow _ _ hw, hρ]


theorem e6Isogeny_conj_of_xm {K : Type} [Field K] [Finite K] (b : Fin (Tag.rank .E6) → Kˣ)
    (h : e6Data_valid.minGroup K) {γ₁ γ₂ : Fin (Tag.rank .E6) → ℤ} (hγ₁ : IsRoot .E6 γ₁)
    (hγ₂ : IsRoot .E6 γ₂)
    (h₁ : ∀ c, h * e6Data_valid.xm K γ₁ c * h⁻¹ = e6Data_valid.xm K γ₁ ((rootChar b γ₁ : K) * c))
    (h₂ : ∀ c, h * e6Data_valid.xm K γ₂ c * h⁻¹ = e6Data_valid.xm K γ₂ ((rootChar b γ₂ : K) * c)) :
    ∀ g ∈ e6Data_valid.rootGroup K γ₁ ⊔ e6Data_valid.rootGroup K γ₂,
      ((e6Isogeny K (h * g * h⁻¹) : adjointGroup .E6 K) : ModGL .E6 K) =
        rootDiagUnit .E6 b * ((e6Isogeny K g : adjointGroup .E6 K) : ModGL .E6 K) *
          (rootDiagUnit .E6 b)⁻¹ := by
  let f₁ : e6Data_valid.minGroup K →* ModGL .E6 K :=
    (adjointGroup .E6 K).subtype.comp ((e6Isogeny K).comp (MulAut.conj h).toMonoidHom)
  let f₂ : e6Data_valid.minGroup K →* ModGL .E6 K :=
    (MulAut.conj (rootDiagUnit .E6 b)).toMonoidHom.comp
      ((adjointGroup .E6 K).subtype.comp (e6Isogeny K))
  have hroot : ∀ γ, IsRoot .E6 γ →
      (∀ c, h * e6Data_valid.xm K γ c * h⁻¹ = e6Data_valid.xm K γ ((rootChar b γ : K) * c)) →
        e6Data_valid.rootGroup K γ ≤ MonoidHom.eqLocus f₁ f₂ := by
    intro γ hγ hact g hg
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).mp hg
    change ((e6Isogeny K (h * e6Data_valid.xm K γ c * h⁻¹) : adjointGroup .E6 K) :
        ModGL .E6 K) = rootDiagUnit .E6 b *
          ((e6Isogeny K (e6Data_valid.xm K γ c) : adjointGroup .E6 K) : ModGL .E6 K) *
            (rootDiagUnit .E6 b)⁻¹
    rw [hact, e6Isogeny_xm K hγ, e6Isogeny_xm K hγ, yPar, yPar, xPar_of_isRoot hγ,
      xPar_of_isRoot hγ, RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement,
      RootDetectExc.rootDiagUnit_conj_eltUnit]
    congr 1
    ring
  intro g hg
  exact (sup_le (hroot γ₁ hγ₁ h₁) (hroot γ₂ hγ₂ h₂)) hg

theorem hdiag_twisted {K : Type} [Field K] [Finite K] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (b : Fin (Tag.rank .E6) → Kˣ) (hb : ∀ i, b (rhoPerm i) = Units.map (θ : K →* K) (b i)) :
    ∀ β ∈ (twistedDatum K θ).roots, ∃ h ∈ ggTorus (twistedDatum K θ),
      ∀ z ∈ (twistedDatum K θ).rootGroup β,
        ((e6Isogeny K ((h * z * h⁻¹ : fixedGroup K θ) : e6Data_valid.minGroup K) :
          adjointGroup .E6 K) : ModGL .E6 K) = rootDiagUnit .E6 b *
            ((e6Isogeny K (z : e6Data_valid.minGroup K) : adjointGroup .E6 K) : ModGL .E6 K) *
              (rootDiagUnit .E6 b)⁻¹ := by
  intro β hβ
  have hβ' : IsRoot .F4 β := isRoot_of_mem_twistedDatum_roots θ hβ
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ'
  obtain ⟨h, hhT, h₁, h₂⟩ := exists_twistedTorus θ hθ b hb hα
  refine ⟨h, mem_ggTorus_twisted θ hhT, fun z hz => ?_⟩
  have hz' := (mem_twistedRootGroup_iff θ hα hp z).mp hz
  exact e6Isogeny_conj_of_xm b (h : e6Data_valid.minGroup K) hα (isRoot_rho hα) h₁ h₂ _ hz'

end Torus

end RootDetectTwE6

end CFSG.StandardType
