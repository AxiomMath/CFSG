module

public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonLine
public import CFSG.RankThree.PartOne.KC.OrthogonalIndependentNormPlanes
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneBasic

public section

open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

section Bridge

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem supportedOrthDerived_eq_supportedDerived (R : Submodule K V) :
    supportedOrthDerived Q R = supportedDerived Q R := by
  ext g
  constructor
  · rintro ⟨g', hg', hgR, hgp⟩
    exact ⟨fun v hv => hgp v hv, g', hg', fun w => (hgR w).symm⟩
  · rintro ⟨hgp, h, hh, hgR⟩
    exact ⟨h, hh, fun r => (hgR r).symm, fun v hv => hgp v hv⟩

end Bridge

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def IsNormPlane (Atil : Subgroup (orthDerived Q)) {E : Type} [Field E] [Algebra K E]
    (ζ : E) (φ : E →ₗ[K] V) (χ : Atil →* Multiplicative (ZMod p)) : Prop :=
  Function.Injective φ ∧
    (∀ z, algebraMap K E (Q (φ z)) = z * z ^ Nat.card K) ∧
    (∀ z, (∀ w, QuadraticMap.polar Q (φ z) (φ w) = 0) → z = 0) ∧
    ∀ (y : Atil) z, (((y : Atil) : orthDerived Q) : V ≃ₗ[K] V) (φ z) =
      φ (ζ ^ (χ y).toAdd.val * z)

end Plane

section Pair

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem pair_fix (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (Atil : Subgroup (orthDerived Q))
    (hAtil : Assembly.IsElemAbelian p Atil) (hAcard : Nat.card Atil = p ^ 2)
    (hAtilA : ∀ x ∈ Atil, (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hinj1 : ∀ x ∈ Atil, (QuotientGroup.mk x : ProjOrthDerived Q) = 1 → x = 1)
    {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p)
    {φ₁ φ₂ : E →ₗ[K] V} {χ₁ χ₂ : Atil →* Multiplicative (ZMod p)}
    (h₁ : IsNormPlane Atil ζ φ₁ χ₁) (h₂ : IsNormPlane Atil ζ φ₂ χ₂)
    (horth : ∀ z w, QuadraticMap.polar Q (φ₁ z) (φ₂ w) = 0)
    (hχ : ∀ m n : ZMod p, (∀ y : Atil, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0)
    (κ : MulAut (ProjOrthDerived Q))
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    (Group.IsPerfect ↥(supportedDerived Q (LinearMap.range φ₁ ⊔ LinearMap.range φ₂)) ∧
      (polarBilin (Q.comp (LinearMap.range φ₁ ⊔ LinearMap.range φ₂).subtype)).Nondegenerate ∧
      finrank K ↥(LinearMap.range φ₁ ⊔ LinearMap.range φ₂) = 4 ∧
      ∀ g : ↥(orthDerived Q),
        (g : V ≃ₗ[K] V) ∈ supportedDerived Q (LinearMap.range φ₁ ⊔ LinearMap.range φ₂) →
          κ (QuotientGroup.mk g) = QuotientGroup.mk g) ∧
    (Q (φ₁ 1) = 1 ∧ Q (φ₂ 1) = 1 ∧ polar Q (φ₁ 1) (φ₂ 1) = 0 ∧
      ∃ hg : reflect Q (φ₁ 1) * reflect Q (φ₂ 1) ∈ orthDerived Q,
        orderOf (QuotientGroup.mk (⟨reflect Q (φ₁ 1) * reflect Q (φ₂ 1), hg⟩ : orthDerived Q) :
          ProjOrthDerived Q) = 2 ∧
        ((2 : K) = 0 → reflect Q (φ₁ 1) * reflect Q (φ₂ 1) =
          eichler Q (φ₁ 1 + φ₂ 1) (φ₁ 1)) ∧
        κ (QuotientGroup.mk (⟨reflect Q (φ₁ 1) * reflect Q (φ₂ 1), hg⟩ : orthDerived Q)) =
          QuotientGroup.mk (⟨reflect Q (φ₁ 1) * reflect Q (φ₂ 1), hg⟩ : orthDerived Q)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hinj₁, hnorm₁, hreg₁, hact₁⟩ := h₁
  obtain ⟨hinj₂, hnorm₂, hreg₂, hact₂⟩ := h₂
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hq : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
  have hinj := conj_injective_projOrthDerived hQ hT
  have : FiniteDimensional K E := Module.finite_of_finrank_pos (by omega)
  set U₁ : Submodule K V := LinearMap.range φ₁ with hU₁def
  set U₂ : Submodule K V := LinearMap.range φ₂ with hU₂def
  have hU₁ : finrank K U₁ = 2 := (LinearMap.finrank_range_of_inj hinj₁).trans hE
  have hU₂ : finrank K U₂ = 2 := (LinearMap.finrank_range_of_inj hinj₂).trans hE
  have hreg : ∀ (φ : E →ₗ[K] V),
      (∀ z, (∀ w, QuadraticMap.polar Q (φ z) (φ w) = 0) → z = 0) →
      (polarBilin (Q.comp (LinearMap.range φ).subtype)).Nondegenerate := by
    intro φ hφ
    refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
    obtain ⟨z, hz⟩ := LinearMap.surjective_rangeRestrict φ v
    have hz0 : z = 0 := by
      refine hφ z fun w => ?_
      have := hv (φ.rangeRestrict w)
      rwa [polar_comp_subtype_eq, ← hz] at this
    rw [← hz, hz0, map_zero]
  have hU₁reg := hreg φ₁ hreg₁
  have hU₂reg := hreg φ₂ hreg₂
  have hU₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, QuadraticMap.polar Q x y = 0 := by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    exact horth z w
  have hU₁inv : ∀ y ∈ Atil, ∀ x ∈ U₁, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₁ := by
    rintro y hy _ ⟨z, rfl⟩
    rw [hact₁ ⟨y, hy⟩ z]
    exact ⟨_, rfl⟩
  have hU₂inv : ∀ y ∈ Atil, ∀ x ∈ U₂, ((y : orthDerived Q) : V ≃ₗ[K] V) x ∈ U₂ := by
    rintro y hy _ ⟨z, rfl⟩
    rw [hact₂ ⟨y, hy⟩ z]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha1, ha'⟩ := exists_ne_one_chars_eq hp hAcard χ₁ χ₂
  obtain ⟨b, hb1, hb'⟩ := exists_ne_one_chars_mul_eq_one hp hAcard χ₁ χ₂
  obtain ⟨⟨hperf, -⟩, himg, ⟨hfin4, hreg4, -⟩, -, hinv⟩ :=
    independent_orthogonal_norm_planes_split_four_local_layer_generation hQ hT hp hp3 hpl hpq D
      hD Atil hAtil hAcard hE hζ U₁ U₂ hU₁ hU₂ hU₁reg hU₂reg hU₁₂ hU₁inv hU₂inv
      φ₁.rangeRestrict φ₂.rangeRestrict hnorm₁ hnorm₂ χ₁ χ₂ hχ hact₁ hact₂ a ha1 ha' b hb1 hb'
  have hcommκ : ∀ x : Atil, x ≠ 1 → ∀ d ∈ inSubgroup layer (D ⊓ Subgroup.centralizer
      ({MulAut.conj (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q)} :
        Set (MulAut (ProjOrthDerived Q)))), d ∈ Subgroup.centralizer ({κ} : Set (MulAut _)) := by
    intro x hx1 d hd
    obtain ⟨d', hd', rfl⟩ := hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcent _ (hAtilA x x.2) (fun h => hx1 (Subtype.ext (hinj1 x x.2 h))) d' hd').symm
  have hκ : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ supportedDerived Q (U₁ ⊔ U₂) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g := by
    intro g hg
    rw [← supportedOrthDerived_eq_supportedDerived] at hg
    have hmem := himg ⟨QuotientGroup.mk g, ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩, rfl⟩
    have hle : inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ⊔ inSubgroup layer (D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk (b : orthDerived Q) : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))) ≤ Subgroup.centralizer ({κ} : Set (MulAut _)) :=
      sup_le (fun d hd => hcommκ a ha1 d hd) (fun d hd => hcommκ b hb1 d hd)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hmem)
    exact fix_of_commute_conj hinj κ _ this.symm
  obtain ⟨hu1, hv1, huv, hgR, -, heich, hg, hgord, -⟩ := hinv
  refine ⟨⟨(supportedOrthDerived_eq_supportedDerived (Q := Q) (U₁ ⊔ U₂)) ▸ hperf, hreg4, hfin4,
    hκ⟩, hu1, hv1, huv, hg, hgord, heich, ?_⟩
  exact hκ ⟨_, hg⟩ ((supportedOrthDerived_eq_supportedDerived (Q := Q) (U₁ ⊔ U₂)) ▸ hgR)

theorem pair_scalar (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (Atil : Subgroup (orthDerived Q))
    (hAtil : Assembly.IsElemAbelian p Atil) (hAcard : Nat.card Atil = p ^ 2)
    (hAtilA : ∀ x ∈ Atil, (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hinj1 : ∀ x ∈ Atil, (QuotientGroup.mk x : ProjOrthDerived Q) = 1 → x = 1)
    {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p)
    {φ₁ φ₂ : E →ₗ[K] V} {χ₁ χ₂ : Atil →* Multiplicative (ZMod p)}
    (h₁ : IsNormPlane Atil ζ φ₁ χ₁) (h₂ : IsNormPlane Atil ζ φ₂ χ₂)
    (horth : ∀ z w, QuadraticMap.polar Q (φ₁ z) (φ₂ w) = 0)
    (hχ : ∀ m n : ZMod p, (∀ y : Atil, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    σ = RingEquiv.refl K ∧ ∃ c : Kˣ, (∀ z, F (φ₁ z) = (c : K) • φ₁ z) ∧
      ∀ w, F (φ₂ w) = (c : K) • φ₂ w := by
  classical
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hq : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
  have hK2 : Nat.card K ≠ 2 := by omega
  obtain ⟨⟨hperf, hreg4, hfin4, hκ⟩, -⟩ := pair_fix hQ hT hp hp3 hpl hpq D hD A Atil hAtil hAcard
    hAtilA hinj1 hE hζ h₁ h₂ horth hχ κ hcent
  have hW4 : Nat.card K = 2 → finrank K ↥(LinearMap.range φ₁ ⊔ LinearMap.range φ₂) = 4 →
      ∀ U : Submodule K ↥(LinearMap.range φ₁ ⊔ LinearMap.range φ₂), finrank K U = 2 →
        ∃ u ∈ U, (Q.comp (LinearMap.range φ₁ ⊔ LinearMap.range φ₂).subtype) u ≠ 0 :=
    fun h2 => absurd h2 hK2
  obtain ⟨-, -, hσ, ⟨c, hc⟩, -, -⟩ :=
    supported_orthogonal_derived_semilinear_centralizer_scalar_restriction_of_automorphism Q hQ hT
      (LinearMap.range φ₁ ⊔ LinearMap.range φ₂) hreg4 (by omega) hperf hW4 σ F hFσ μ hμ hFQ κ hκF
      hκ
  exact ⟨hσ, c, fun z => hc _ (Submodule.mem_sup_left ⟨z, rfl⟩),
    fun w => hc _ (Submodule.mem_sup_right ⟨w, rfl⟩)⟩

end Pair

end CFSG.RankThree.PartOne
