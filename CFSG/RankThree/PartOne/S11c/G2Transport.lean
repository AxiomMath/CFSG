module

public import CFSG.RankThree.PartOne.S11c.G2Involution
public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
public import CFSG.LieType.Chevalley.OddG2ToralInvolutionComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

universe u

theorem xlevel_largePrime_map {M M' : Type*} [Group M] [Group M'] (θ : M →* M')
    (hθ : Function.Injective θ) {k : Type u} [Field k] (hk : ringChar k ≠ 2) (X : Subgroup M)
    (μ : SL(2, k) × SL(2, k) →* M)
    (hμ : ∀ z ∈ μ.ker, z.1 ∈ Subgroup.center SL(2, k) ∧ z.2 ∈ Subgroup.center SL(2, k))
    (hSn : ∀ g ∈ X, ∀ s ∈ μ.range, g * s * g⁻¹ ∈ μ.range) (hsq : ∀ g ∈ X, g ^ 2 ∈ μ.range)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P U : Subgroup M'} [Finite U] (hPX : P ≤ X.map θ)
    (hUX : U ≤ X.map θ) (hPp : IsPGroup p P) (hU2 : IsPGroup 2 U)
    (hPU : ∀ a ∈ P, ∀ u ∈ U, a * u * a⁻¹ ∈ U) : ∀ a ∈ P, ∀ u ∈ U, a * u = u * a := by
  refine xlevel_largePrime hk (X.map θ) (θ.comp μ) ?_ ?_ ?_ hp hp3 hPX hUX hPp hU2 hPU
  · intro z hz
    have : μ z = 1 := hθ (by simpa using hz)
    exact hμ z this
  · intro g' hg' s' hs'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
    obtain ⟨w, rfl⟩ := hs'
    obtain ⟨w', hw'⟩ := hSn g hg (μ w) ⟨w, rfl⟩
    exact ⟨w', by simp [hw']⟩
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
    obtain ⟨w, hw⟩ := hsq g hg
    exact ⟨w, by simp [← map_pow, ← hw]⟩

variable {K : Type} [Field K]

theorem exists_g2_pair [Finite K] (hK : Odd (Nat.card K)) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1) :
    ∃ (α β : Fin Tag.G2.rank → ℤ) (h : G2SignPair α β),
      (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a) := by
  obtain ⟨-, -, hcases, hpair, -⟩ := odd_G2_toral_involution_fixed_p_components K hK a ha
  have key : ∀ (α β : Fin Tag.G2.rank → ℤ) (h : G2SignPair α β),
      rootSpan .G2 K (rootCharKernel a) =
        (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ⊔
          (rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) →
      ∃ (α β : Fin Tag.G2.rank → ℤ) (h : G2SignPair α β),
        (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a) := fun α β h hS => by
    refine ⟨α, β, h, ?_⟩
    obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
    rw [hS, g2Mul, MonoidHom.noncommCoprod_range, range_rootSL2_of_isRoot hα,
      range_rootSL2_of_isRoot hβ]
  rcases hcases with rfl | h | h | h
  · exact absurd rfl ha1
  · exact key _ _ (Or.inl ⟨rfl, rfl⟩)
      (hpair _ _ (Or.inl ⟨h, rfl, rfl⟩)).2.2.1
  · exact key _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (hpair _ _ (Or.inr (Or.inl ⟨h, rfl, rfl⟩))).2.2.1
  · exact key _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (hpair _ _ (Or.inr (Or.inr ⟨h, rfl, rfl⟩))).2.2.1

theorem exists_comap_equiv {M M' : Type*} [Group M] [Group M'] (ψ ι : M →* M')
    (hψ : Function.Injective ψ) (hι : Function.Injective ι) (R : Subgroup M)
    (h : R.map ψ ≤ ι.range) : ∃ R₀ : Subgroup M, R₀.map ι = R.map ψ ∧ Nonempty (R ≃* R₀) := by
  have e : ((R.map ψ).comap ι).map ι = R.map ψ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 h]
  exact ⟨(R.map ψ).comap ι, e, ⟨(Subgroup.equivMapOfInjective R ψ hψ).trans
    ((MulEquiv.subgroupCongr e.symm).trans (Subgroup.equivMapOfInjective _ ι hι).symm)⟩⟩

theorem exists_involution_transport [Finite K] (hK : Odd (Nat.card K)) {t : ModGL .G2 K}
    (ht : t ∈ adjointGroup .G2 K) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ (b : Fin Tag.G2.rank → Kˣ) (L : Type) (_ : Field L) (ψ ι : ModGL .G2 K →* ModGL .G2 L),
      (∀ i, b i = 1 ∨ b i = -1) ∧ b ≠ 1 ∧ Function.Injective ψ ∧ Function.Injective ι ∧
        (adjointGroup .G2 K ⊓ Subgroup.centralizer {t}).map ψ =
          (toralCentralizer .G2 K b).map ι ∧ ψ t = ι (rootDiagUnit .G2 b) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  obtain ⟨hinj, -, -, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .G2 K hK L (algebraMap K L)
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .G2 K hK L Fr hFr
  have hxR := hHR ⟨t, ht, rfl⟩
  have hx2 : (baseChangeGL (algebraMap K L) t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  obtain ⟨h, -, a, ha, hhx, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components .G2 K L (Or.inl rfl) hK Fr
      hFr hxR hx2
  set b : Fin Tag.G2.rank → Kˣ := fun i => if a i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap K L).toMonoidHom (b i)) = a := by
    funext i
    by_cases h1 : a i = 1
    · simp [hb_def, h1]
    · have h2 : a i = -1 := (ha i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap K L) b
  rw [hab] at hXK
  have hdb : baseChangeGL (algebraMap K L) (rootDiagUnit .G2 b) = rootDiagUnit .G2 a := by
    rw [baseChangeGL_rootDiagUnit, hab]
  have hAt : (adjointGroup .G2 K ⊓ Subgroup.centralizer {t}).map (baseChangeGL (algebraMap K L)) =
      (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) ⊓
        Subgroup.centralizer {baseChangeGL (algebraMap K L) t} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, ⟨hg, hgc⟩, rfl⟩
      refine ⟨⟨g, hg, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul, hgc]
    · rintro ⟨⟨g, hg, rfl⟩, hgc⟩
      refine ⟨g, ⟨hg, ?_⟩, rfl⟩
      rw [← map_mul, ← map_mul] at hgc
      exact hinj hgc
  refine ⟨b, L, inferInstance, (MulAut.conj h).toMonoidHom.comp (baseChangeGL (algebraMap K L)),
    baseChangeGL (algebraMap K L), hb, ?_, (MulAut.conj h).injective.comp hinj, hinj, ?_, ?_⟩
  · intro hb1
    apply ht1
    have ha1 : a = 1 := by rw [← hab, hb1]; funext i; simp
    rw [ha1, rootDiagUnit_one] at hhx
    apply hinj
    rw [map_one]
    calc baseChangeGL (algebraMap K L) t = h⁻¹ * (h * baseChangeGL (algebraMap K L) t * h⁻¹) * h :=
        by group
      _ = 1 := by rw [hhx]; group
  · rw [← Subgroup.map_map, hAt, hCh, hXK]
  · change h * baseChangeGL (algebraMap K L) t * h⁻¹ = _
    rw [hhx, hdb]

theorem ringChar_ne_two_of_odd_card [Finite K] (hK : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  intro h2
  have : Fintype K := Fintype.ofFinite K
  have h := (FiniteField.even_card_iff_char_two (F := K)).1 h2
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hK
  omega

theorem exists_corresponding_subgroup {M' : Type*} [Group M'] {M : Type*} [Group M]
    {ψ ι : M →* M'} (hψ : Function.Injective ψ) (hι : Function.Injective ι) {Y Z : Subgroup M}
    (himg : Y.map ψ = Z.map ι) {R : Subgroup M} (hR : R ≤ Y) :
    ∃ R₀ : Subgroup M, R₀ ≤ Z ∧ R₀.map ι = R.map ψ ∧ Nonempty (R ≃* R₀) := by
  have hrange : R.map ψ ≤ ι.range := fun y hy => by
    have : y ∈ Y.map ψ := Subgroup.map_mono hR hy
    rw [himg] at this
    obtain ⟨z, -, rfl⟩ := this
    exact ⟨z, rfl⟩
  obtain ⟨R₀, h0, he⟩ := exists_comap_equiv ψ ι hψ hι R hrange
  refine ⟨R₀, ?_, h0, he⟩
  have h1 : R₀.map ι ≤ Z.map ι := by
    rw [h0, ← himg]
    exact Subgroup.map_mono hR
  exact (Subgroup.map_le_map_iff_of_injective hι).1 h1

theorem g2_involution_largePrime [Finite K] (hK : Odd (Nat.card K)) {t : ModGL .G2 K}
    (ht : t ∈ adjointGroup .G2 K) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {P U : Subgroup (ModGL .G2 K)} [Finite U]
    (hP : P ≤ adjointGroup .G2 K ⊓ Subgroup.centralizer {t})
    (hU : U ≤ adjointGroup .G2 K ⊓ Subgroup.centralizer {t}) (hPp : IsPGroup p P)
    (hU2 : IsPGroup 2 U) (hPU : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∀ x ∈ P, ∀ u ∈ U, x * u = u * x := by
  obtain ⟨b, L, _, ψ, ι, hb, hb1, hψ, hι, himg, -⟩ := exists_involution_transport hK ht ht2 ht1
  have hK2 := ringChar_ne_two_of_odd_card hK
  obtain ⟨α, β, h, hS⟩ := exists_g2_pair hK hb hb1
  obtain ⟨P₀, hP₀X, hP₀, ⟨eP⟩⟩ := exists_corresponding_subgroup hψ hι himg hP
  obtain ⟨U₀, hU₀X, hU₀, ⟨eU⟩⟩ := exists_corresponding_subgroup hψ hι himg hU
  have : Finite U₀ := Finite.of_equiv U eU.toEquiv
  have hmem : ∀ {R R₀ : Subgroup (ModGL .G2 K)}, R₀.map ι = R.map ψ → ∀ x ∈ R,
      ∃ x₀ ∈ R₀, ι x₀ = ψ x := fun {R R₀} hR x hx => by
    have : ψ x ∈ R₀.map ι := hR ▸ Subgroup.mem_map_of_mem ψ hx
    obtain ⟨x₀, hx₀, h'⟩ := this
    exact ⟨x₀, hx₀, h'⟩
  have hmem' : ∀ {R R₀ : Subgroup (ModGL .G2 K)}, R₀.map ι = R.map ψ → ∀ x₀ ∈ R₀,
      ∃ x ∈ R, ψ x = ι x₀ := fun {R R₀} hR x₀ hx₀ => by
    have : ι x₀ ∈ R.map ψ := hR ▸ Subgroup.mem_map_of_mem ι hx₀
    obtain ⟨x, hx, h'⟩ := this
    exact ⟨x, hx, h'⟩
  have key := g2_toral_largePrime hK2 hb h hS hp hp3 hP₀X hU₀X (hPp.of_equiv eP)
    (hU2.of_equiv eU) (fun x₀ hx₀ u₀ hu₀ => by
      obtain ⟨x, hx, hxe⟩ := hmem' hP₀ x₀ hx₀
      obtain ⟨u, hu, hue⟩ := hmem' hU₀ u₀ hu₀
      have hw : ψ (x * u * x⁻¹) = ι (x₀ * u₀ * x₀⁻¹) := by
        rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hxe, hue]
      obtain ⟨w, hw0, hwe⟩ := hmem hU₀ _ (hPU x hx u hu)
      have : w = x₀ * u₀ * x₀⁻¹ := hι (by rw [hwe, hw])
      exact this ▸ hw0)
  intro x hx u hu
  obtain ⟨x₀, hx₀, hxe⟩ := hmem hP₀ x hx
  obtain ⟨u₀, hu₀, hue⟩ := hmem hU₀ u hu
  apply hψ
  rw [map_mul, map_mul, ← hxe, ← hue, ← map_mul, ← map_mul, key x₀ hx₀ u₀ hu₀]

end CFSG.RankThree.PartOne
