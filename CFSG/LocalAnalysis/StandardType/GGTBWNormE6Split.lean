module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndSplit
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddToral2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl

public noncomputable section

namespace CFSG.StandardType.E6WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.StandardType.TableBExc

theorem normalizes_inner_automizer {L : Type} [Group L]
    (A : Subgroup (MulAut L)) {s : MulAut ↥A}
    (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    s ∈ Subgroup.normalizer
      (ggAutomizer (MulAut.conj : L →* MulAut L).range A : Set (MulAut ↥A)) := by
  letI : (MulAut.conj : L →* MulAut L).range.Normal := by
    constructor
    rintro a ⟨x, rfl⟩ b
    refine ⟨b x, ?_⟩
    apply MulEquiv.ext
    intro y
    change b x * y * (b x)⁻¹ = b (x * b⁻¹ y * x⁻¹)
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  exact mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs


theorem card_eq_six_of_selfCent {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian p E)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 6 := by
  let : Fact p.Prime := ⟨hp⟩
  have hEm : IsElemAbelian p (E.map (adjointGroup .E6 K).subtype) :=
    TableB.isElemAbelian_map hE _
  have hEp : IsPGroup p (E.map (adjointGroup .E6 K).subtype) := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hEm.2 (x : ModGL .E6 K) x.2)⟩
  obtain ⟨g, hg, hgt⟩ := exists_conj_le_torusGroup_E6_of_isPGroup hp hp7 hpq
    (Subgroup.map_subtype_le E) hEp
  let a : adjointGroup .E6 K := ⟨g, hg⟩
  let E' := E.map (MulAut.conj a).toMonoidHom
  have hEt : ∀ e ∈ E', (e : ModGL .E6 K) ∈ torusGroup .E6 K := by
    rintro e ⟨x, hx, rfl⟩
    exact hgt (x : ModGL .E6 K) (Subgroup.mem_map_of_mem _ hx)
  have hE' : IsElemAbelian p E' := TableB.isElemAbelian_map hE _
  have hsc' : ∀ g, (∀ e ∈ E', g * e = e * g) → g ^ p = 1 → g ∈ E' := by
    intro x hxc hxp
    have hx : a⁻¹ * x * a ∈ E := by
      apply hsc
      · intro e he
        have hh := hxc (a * e * a⁻¹) (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom he)
        change x * (a * e * a⁻¹) = (a * e * a⁻¹) * x at hh
        have hh' := congrArg (fun z : adjointGroup .E6 K => a⁻¹ * z * a) hh
        calc _ = a⁻¹ * (x * (a * e * a⁻¹)) * a := by group
          _ = e * (a⁻¹ * x * a) := by rw [hh]; group
      · change (a⁻¹ * x * (a⁻¹)⁻¹) ^ p = 1
        rw [conj_pow, hxp]; group
    exact ⟨a⁻¹ * x * a, hx, by change a * (a⁻¹ * x * a) * a⁻¹ = x; group⟩
  have hEq : E' = torusPow .E6 K p := by
    apply le_antisymm
    · intro e he
      exact ⟨hEt e he, hE'.2 e he⟩
    · intro e he
      apply hsc' e
      · intro x hx
        apply Subtype.ext
        exact CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm he.1 (hEt x hx)
      · exact he.2
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  rw [← hcard, hEq]
  exact card_torusPow_E6 hp (by omega) hpq

theorem wNormConcl_of_full_frame {L : Type} [Group L] [Finite L]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p)
    (A : Subgroup (MulAut L))
    (κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A)
    (hW : (ExcWeylOuter.torusMulAut Tag.E6 p).range.map (MulAut.congr κ).toMonoidHom =
      ggAutomizer (MulAut.conj : L →* MulAut L).range A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hgen : ggAutomizer (MulAut.conj : L →* MulAut L).range A = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L)) A) :
    GGWNormConcl ι φ h α s := by
  let W := ggAutomizer (MulAut.conj : L →* MulAut L).range A
  have hNI : NormInducesInner W := by
    apply NormInducesInner.of_mulEquiv (MulAut.congr κ).symm
      (W' := (ExcWeylOuter.torusMulAut Tag.E6 p).range)
    · intro x
      change x ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A ↔ _
      rw [← hW]
      exact Subgroup.mem_map_equiv
    · exact normInducesInner_range_torusMulAut_E6 (p := p) (by omega)
  have hZ : Subgroup.center ↥W = ⊥ := by
    have e : (ExcWeylOuter.torusMulAut Tag.E6 p).range ≃* W :=
      (MulEquiv.subgroupMap (MulAut.congr κ) _).trans (MulEquiv.subgroupCongr hW)
    have hz := center_weyl_range_eq_bot (p := p) (by omega)
    rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
  letI : Nontrivial ↥A := κ.injective.nontrivial
  letI : Nontrivial V := by
    exact ι.injective.nontrivial
  exact ggWNormConcl_of_centerless ι φ h α hgen hZ hNI
    (commutant_scalar_of_coordinates hp5 ι κ W hW)
    (normalizes_inner_automizer A hs)

theorem exists_coordinates_aligned_of_ge_five {K L : Type} [Field K] [Finite K] [Group L] [Finite L]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (A : Subgroup (MulAut L))
    (Λ : adjointGroup .E6 K →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛn : ∀ l, Λ (ψ l) = MulAut.conj l)
    (hA : (torusPow .E6 K p).map Λ = A) :
    ∃ κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A,
      (ExcWeylOuter.torusMulAut Tag.E6 p).range.map (MulAut.congr κ).toMonoidHom =
        ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let τ := chevTorus .E6 ζ hζ
  have hdet := isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
  have hτ : Function.Injective τ := chevTorus_injective hζo hζ hdet
  have hr : τ.range = torusPow .E6 K p :=
    range_chevTorus_eq_torusPow hζo hζ hdet (card_torusPow_E6 hp (by omega) hpq)
  have hκ : (Λ.comp τ).range = A := by rw [MonoidHom.range_comp, hr, hA]
  let κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A :=
    (MonoidHom.ofInjective (f := Λ.comp τ) (hΛ.comp hτ)).trans (MulEquiv.subgroupCongr hκ)
  have hk : ∀ a, (κ a : MulAut L) = Λ (τ a) := fun _ => rfl
  have hR : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨x, rfl⟩ := hψ g
      exact ⟨x, (hΛn x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ψ x, hΛn x⟩
  obtain ⟨hn, eA, heA⟩ := TBE6Ind.exists_marked hp (by omega) (by omega) hpq A Λ hΛ hA
  let ρ : WeylGroup Tag.E6 →* MulAut ↥A :=
    (MulAut.congr κ).toMonoidHom.comp (ExcWeylOuter.torusMulAut Tag.E6 p)
  have hτσ : ∀ i u, τ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u) =
      CFSG.LieType.Chevalley.weylElement .E6 K i * τ u *
        (CFSG.LieType.Chevalley.weylElement .E6 K i)⁻¹ := by
    intro i u
    have hh := weylElt_conj_chevTorus (τ := Tag.E6) ζ hζ i (Multiplicative.toAdd u)
    have he := TableBExc.torusRefl_eq_torusAct (p := p) NoOffExc.cartan_symm_E6 i
      (Multiplicative.toAdd u)
    change CFSG.LieType.Chevalley.weylElement .E6 K i * τ (Multiplicative.ofAdd (Multiplicative.toAdd u)) *
        (CFSG.LieType.Chevalley.weylElement .E6 K i)⁻¹ =
      τ (Multiplicative.ofAdd (TableBExc.torusRefl .E6 p i (Multiplicative.toAdd u))) at hh
    rw [he] at hh
    have hx : ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u =
        Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 i) (Multiplicative.toAdd u)) :=
      congrArg (fun x => ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) x)
        (ofAdd_toAdd u).symm
    rw [hx]
    change τ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) (Multiplicative.toAdd u))) = _
    rw [ofAdd_toAdd] at hh
    exact hh.symm
  have hκσ : ∀ i u, (κ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u) : MulAut L) =
      Λ (CFSG.LieType.Chevalley.weylElement .E6 K i) * (κ u : MulAut L) *
        (Λ (CFSG.LieType.Chevalley.weylElement .E6 K i))⁻¹ := by
    intro i u
    rw [hk, hτσ, map_mul, map_mul, map_inv, hk]
  have hsimple : ∀ i, ρ (simple Tag.E6 i) = ggConjAut A (hn i) := by
    intro i
    apply MulEquiv.ext
    intro a
    have hv : ρ (simple Tag.E6 i) a =
        κ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) (κ.symm a)) := by
      rw [show ρ (simple Tag.E6 i) = MulAut.congr κ
        (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i)) from rfl, MulAut.congr_apply]
      rfl
    rw [hv]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have he := hκσ i (κ.symm a)
    simpa only [κ.apply_symm_apply] using he
  have hhom : (ggAutomizer Λ.range A).subtype.comp eA.toMonoidHom =
      ρ.comp ggE6Row_coxeterGroupEquiv.toMonoidHom := by
    apply CoxeterMatrix.E₆.toCoxeterSystem.ext_simple
    intro i
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    change (eA (CoxeterMatrix.E₆.simple i) : MulAut ↥A) =
      ρ (ggE6Row_coxeterGroupEquiv (CoxeterMatrix.E₆.simple i))
    rw [heA, ggE6Row_coxeterGroupEquiv_simple]
    exact (hsimple i).symm
  have hrcomp : (ρ.comp ggE6Row_coxeterGroupEquiv.toMonoidHom).range = ρ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ggE6Row_coxeterGroupEquiv.surjective,
      Subgroup.map_top]
  have hρ : ρ.range = ggAutomizer Λ.range A := by
    rw [← hrcomp, ← hhom]
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  refine ⟨κ, ?_⟩
  rw [← hR, ← hρ]
  exact (MonoidHom.range_comp _ _).symm

theorem exists_coordinates_aligned {K L : Type} [Field K] [Finite K] [Group L] [Finite L]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (A : Subgroup (MulAut L))
    (Λ : adjointGroup .E6 K →* MulAut L) (hΛ : Function.Injective Λ)
    (hΛn : ∀ l, Λ (ψ l) = MulAut.conj l)
    (hA : (torusPow .E6 K p).map Λ = A) :
    ∃ κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A,
      (ExcWeylOuter.torusMulAut Tag.E6 p).range.map (MulAut.congr κ).toMonoidHom =
        ggAutomizer (MulAut.conj : L →* MulAut L).range A  := by
  exact exists_coordinates_aligned_of_ge_five hp (by omega) hpq ψ hψ hker A Λ hΛ hΛn hA


theorem ggTorusWNormSC_recipe_E6_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWNormSC p (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E6 K)
      (ggOutdiagPrime_E6 hp (by omega)) (ExcSplitL.ggCenterPrime_recipe_E6 hp (by omega) (by omega))
      ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E6 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  have hcard := card_eq_six_of_selfCent hp hp7 hpq E hEg hEgs
  have hA6 : p ^ 6 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective ε.injective, hEc] at hcard
    exact hcard.ge
  obtain ⟨ψa, hψa, hka, Λ, hΛ, hΛn, -, hFA⟩ :=
    TBE6Ind.exists_aligned_adjoint hp (by omega) (by omega) hpq ψ A
      ⟨hψ, hker, hperf, hA, hAI, hA6, h3, hsc⟩
  obtain ⟨κ, hW⟩ := exists_coordinates_aligned hp hp7 hpq ψa hψa hka A Λ hΛ hΛn hFA
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact wNormConcl_of_full_frame (by omega) A κ hW ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E6_split {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .E6) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E6_split hp hp7 (by rw [hK]; exact hpq)

end CFSG.StandardType.E6WNorm
