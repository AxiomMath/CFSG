module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthNormIso
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSixPlaneSU
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Restrict
import CFSG.ClassicalGroups.Orthogonal.FieldTwoTransport

public section

namespace CFSG.StandardType.OrthTorus

open Module Multiplicative QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.SixPlane
open CFSG.ClassicalGroups.Orthogonal.SixPlane (V Q planeSpan supp rot rot_mem_supp)
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits
open CFSG.StandardType.QTwo
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] ZMod.algebra

noncomputable section

section PlaneCard

variable {n : ℕ}

private noncomputable def planeSpanEquiv (A : Finset (Fin n)) :
    ↥(planeSpan n A) ≃ₗ[ZMod 2] ((↥A) ⊕ (↥A) → ZMod 2) where
  toFun v x := match x with
    | Sum.inl a => (v : V n) (Sum.inl (a : Fin n))
    | Sum.inr a => (v : V n) (Sum.inr (a : Fin n))
  invFun w :=
    ⟨fun k => match k with
      | Sum.inl i => if h : i ∈ A then w (Sum.inl ⟨i, h⟩) else 0
      | Sum.inr i => if h : i ∈ A then w (Sum.inr ⟨i, h⟩) else 0, by
      rw [mem_planeSpan]
      intro k hk
      rcases k with i | i
      · have hk' : i ∉ A := by simpa [planeOf] using hk
        dsimp only
        rw [dif_neg hk']
      · have hk' : i ∉ A := by simpa [planeOf] using hk
        dsimp only
        rw [dif_neg hk']⟩
  map_add' v w := by
    ext x
    rcases x with a | a <;> simp
  map_smul' c v := by
    ext x
    rcases x with a | a <;> simp
  left_inv v := by
    ext k
    rcases k with i | i
    · by_cases h : i ∈ A
      · simp [h]
      · simp [h, mem_planeSpan.mp v.2 (Sum.inl i) h]
    · by_cases h : i ∈ A
      · simp [h]
      · simp [h, mem_planeSpan.mp v.2 (Sum.inr i) h]
  right_inv w := by
    ext x
    rcases x with a | a
    · simp [a.2]
    · simp [a.2]

private theorem natCard_planeSpan (A : Finset (Fin n)) :
    Nat.card ↥(planeSpan n A) = 4 ^ A.card := by
  rw [Nat.card_congr (planeSpanEquiv A).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_sum, Fintype.card_coe, ZMod.card]
  rw [show (4 : ℕ) = 2 * 2 by norm_num, Nat.mul_pow, ← pow_add]

end PlaneCard

section Coords

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem sixPlaneK_coords_eq_zero {ω : K} {c : Fin n → ZMod 3}
    (hω : ω ^ 2 + ω + 1 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) {v : V n} {i : Fin n}
    (h : sixPlaneK ω c v i = 0) : v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0 := by
  classical
  let v' : V n := fun k => match k with
    | Sum.inl j => if j = i then v (Sum.inl j) else 0
    | Sum.inr j => if j = i then v (Sum.inr j) else 0
  have hv' : sixPlaneK ω c v' = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [sixPlaneK_apply]
      simp only [v', if_pos rfl]
      exact h
    · rw [sixPlaneK_apply]
      simp only [v', if_neg hj]
      simp
  have hv'0 : v' = 0 := sixPlaneK_injective hω hc (by rw [hv', map_zero])
  constructor
  · have := congrFun hv'0 (Sum.inl i)
    simpa [v'] using this
  · have := congrFun hv'0 (Sum.inr i)
    simpa [v'] using this

end Coords

private abbrev ChartV (n : ℕ) : Type := CFSG.ClassicalGroups.Orthogonal.SixPlane.V n

private abbrev ChartQ (n : ℕ) : QuadraticForm (ZMod 2) (ChartV n) :=
  CFSG.ClassicalGroups.Orthogonal.SixPlane.Q n

private abbrev ChartU (n : ℕ) (A : Finset (Fin n)) : QuadraticForm (ZMod 2) ↥(planeSpan n A) :=
  (ChartQ n).restrict (planeSpan n A)

private theorem signVec_ite {n : ℕ} {A : Finset (Fin n)} {M : Type} [One M] [Neg M]
    {s : ↥A → M} (hs : ∀ i, s i = 1 ∨ s i = -1) (i : Fin n) :
    (if h : i ∈ A then s ⟨i, h⟩ else (1 : M)) = 1 ∨
      (if h : i ∈ A then s ⟨i, h⟩ else (1 : M)) = -1 := by
  by_cases h : i ∈ A
  · simpa [h] using hs ⟨i, h⟩
  · simp [h]

private theorem normOne_coe_pow {K : Type} [Field K] (σ : K ≃+* K) (ζ : normOne σ) (m : ℕ) :
    (((ζ ^ m : normOne σ) : Kˣ) : K) = ((ζ : Kˣ) : K) ^ m := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

private theorem normOne_coe_sq_add_coe_add_one {K : Type} [Field K] {σ : K ≃+* K}
    {ζ : normOne σ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ 3 = 1) :
    ((ζ : Kˣ) : K) ^ 2 + ((ζ : Kˣ) : K) + 1 = 0 := by
  have hω3 : ((ζ : Kˣ) : K) ^ 3 = 1 := by
    rw [← normOne_coe_pow σ ζ 3, hζp]
    simp
  have hω1 : ((ζ : Kˣ) : K) ≠ 1 := by
    intro h
    exact hζ1 (Subtype.ext (Units.ext h))
  have hfac : (((ζ : Kˣ) : K) - 1) * (((ζ : Kˣ) : K) ^ 2 + ((ζ : Kˣ) : K) + 1) = 0 := by
    rw [show (((ζ : Kˣ) : K) - 1) * (((ζ : Kˣ) : K) ^ 2 + ((ζ : Kˣ) : K) + 1) =
      ((ζ : Kˣ) : K) ^ 3 - 1 by ring, sub_eq_zero, hω3]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h (sub_ne_zero.mpr hω1)
  · exact h

private def chartCoordHom {K : Type} [Field K] [CharP K 2] {n r : ℕ} (ω : K)
    (c : Fin n → ZMod 3) {A : Finset (Fin n)} (π : ↥A ≃ Fin r) :
    ↥(planeSpan n A) →+ (Fin r → K) where
  toFun u j := sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n)
  map_zero' := by
    funext j
    simp
  map_add' u v := by
    funext j
    simp

private theorem chartCoordHom_apply {K : Type} [Field K] [CharP K 2] {n r : ℕ} {ω : K}
    {c : Fin n → ZMod 3} {A : Finset (Fin n)} {π : ↥A ≃ Fin r}
    (u : ↥(planeSpan n A)) (j : Fin r) :
    chartCoordHom ω c π u j =
      sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n) :=
  rfl

private theorem chartCoordHom_injective {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ}
    {ω : K} {c : Fin n → ZMod 3} (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) {A : Finset (Fin n)} (π : ↥A ≃ Fin r) :
    Function.Injective (chartCoordHom ω c π) := by
  intro u v huv
  have hzero : chartCoordHom ω c π (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hcoord : ∀ i : Fin n,
      ((u - v : ↥(planeSpan n A)) : ChartV n) (Sum.inl i) = 0 ∧
      ((u - v : ↥(planeSpan n A)) : ChartV n) (Sum.inr i) = 0 := by
    intro i
    by_cases hi : i ∈ A
    · have h0 : sixPlaneK ω c ((u - v : ↥(planeSpan n A)) : ChartV n) i = 0 := by
        have h := congrFun hzero (π ⟨i, hi⟩)
        simpa [chartCoordHom_apply, Equiv.symm_apply_apply] using h
      exact sixPlaneK_coords_eq_zero hω hc h0
    · have hmem := (u - v : ↥(planeSpan n A)).2
      exact ⟨(mem_planeSpan.mp hmem (Sum.inl i) hi),
        (mem_planeSpan.mp hmem (Sum.inr i) hi)⟩
  have hsub : (u - v : ↥(planeSpan n A)) = 0 := by
    apply Subtype.ext
    funext k
    rcases k with i | i
    · exact (hcoord i).1
    · exact (hcoord i).2
  exact sub_eq_zero.mp hsub

private theorem exists_chartCoordEquiv {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ}
    {ω : K} {c : Fin n → ZMod 3} (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) {A : Finset (Fin n)} (π : ↥A ≃ Fin r)
    (hK4 : Nat.card K = 4) (hcardA : A.card = r) :
    ∃ κ : ↥(planeSpan n A) ≃+ (Fin r → K),
      ∀ (u : ↥(planeSpan n A)) (j : Fin r),
        κ u j = sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n) := by
  have hcard : Nat.card ↥(planeSpan n A) = Nat.card (Fin r → K) := by
    rw [natCard_planeSpan A, Nat.card_fun, Nat.card_fin, hK4, hcardA]
  exact ⟨AddEquiv.ofBijective (chartCoordHom ω c π)
      ((chartCoordHom_injective hω hc π).bijective_of_nat_card_le (le_of_eq hcard.symm)),
    fun u j => chartCoordHom_apply u j⟩

private theorem chartCoord_sum {K : Type} [Field K] [Finite K] [CharP K 2] {n r : ℕ}
    {ω : K} {c : Fin n → ZMod 3} {A : Finset (Fin n)} {π : ↥A ≃ Fin r}
    {κ : ↥(planeSpan n A) → (Fin r → K)}
    (hκ : ∀ (u : ↥(planeSpan n A)) (j : Fin r),
      κ u j = sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n))
    (σ : K ≃+* K) (u : ↥(planeSpan n A)) :
    (∑ j : Fin r, κ u j * σ (κ u j)) =
      ∑ i : Fin n, sixPlaneK ω c (u : ChartV n) i * σ (sixPlaneK ω c (u : ChartV n) i) := by
  have h1 : (∑ j : Fin r, κ u j * σ (κ u j)) =
      ∑ a : ↥A, sixPlaneK ω c (u : ChartV n) (a : Fin n) *
        σ (sixPlaneK ω c (u : ChartV n) (a : Fin n)) := by
    simpa [hκ] using
      (Equiv.sum_comp (π.symm) (fun a : ↥A =>
        sixPlaneK ω c (u : ChartV n) (a : Fin n) *
          σ (sixPlaneK ω c (u : ChartV n) (a : Fin n))))
  rw [h1, Finset.sum_coe_sort A (fun i : Fin n =>
    sixPlaneK ω c (u : ChartV n) i * σ (sixPlaneK ω c (u : ChartV n) i))]
  refine Finset.sum_subset (Finset.subset_univ A) ?_
  intro i _ hi
  have h0 : sixPlaneK ω c (u : ChartV n) i = 0 := by
    rw [sixPlaneK_apply]
    have hli := mem_planeSpan.mp u.2 (Sum.inl i) hi
    have hri := mem_planeSpan.mp u.2 (Sum.inr i) hi
    rw [hli, hri]
    simp
  rw [h0, map_zero, mul_zero]

private theorem chartCoord_Qn_eq_zero_iff {F K : Type} [Field F] [Field K] [Finite K]
    [CharP K 2] [Algebra F K] {n r : ℕ} {ω : K} {c : Fin n → ZMod 3} {A : Finset (Fin n)}
    {π : ↥A ≃ Fin r} {κ : ↥(planeSpan n A) → (Fin r → K)}
    (hκ : ∀ (u : ↥(planeSpan n A)) (j : Fin r),
      κ u j = sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n))
    (hω : ω ^ 2 + ω + 1 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) (hK4 : Nat.card K = 4)
    (E : QuadExt F K (unitaryInvolution K 2 1)) (u : ↥(planeSpan n A)) :
    Qn E r (κ u) = 0 ↔ ChartU n A u = 0 := by
  let E₂ : QuadExt (ZMod 2) K (unitaryInvolution K 2 1) :=
    quadExt_of_card_of_char_two 1 (by simpa using Nat.card_zmod 2)
      (by rw [hK4]; norm_num)
  have hkey : algebraMap F K (Qn E r (κ u)) =
      algebraMap (ZMod 2) K (ChartQ n (u : ChartV n)) := by
    calc
      algebraMap F K (Qn E r (κ u))
          = ∑ j : Fin r, κ u j * unitaryInvolution K 2 1 (κ u j) := algebraMap_Qn E r (κ u)
      _ = ∑ i : Fin n, sixPlaneK ω c (u : ChartV n) i *
            unitaryInvolution K 2 1 (sixPlaneK ω c (u : ChartV n) i) :=
            chartCoord_sum hκ (unitaryInvolution K 2 1) u
      _ = algebraMap (ZMod 2) K (Qn E₂ n (sixPlaneK ω c (u : ChartV n))) :=
            (algebraMap_Qn E₂ n (sixPlaneK ω c (u : ChartV n))).symm
      _ = algebraMap (ZMod 2) K (ChartQ n (u : ChartV n)) :=
            congrArg (algebraMap (ZMod 2) K)
              (Qn_sixPlaneK (n := n) (ω := ω) (c := c) E₂ hω hc (u : ChartV n))
  constructor
  · intro h
    have h2 : algebraMap (ZMod 2) K (ChartQ n (u : ChartV n)) = 0 := by
      rw [← hkey, h, map_zero]
    exact (algebraMap (ZMod 2) K).injective (by simpa using h2)
  · intro h
    change ChartQ n (u : ChartV n) = 0 at h
    have h2 : algebraMap F K (Qn E r (κ u)) = 0 := by
      rw [hkey, h, map_zero]
    exact (algebraMap F K).injective (by simpa using h2)

private def chartScalar {n r : ℕ} {A : Finset (Fin n)} (π : ↥A ≃ Fin r) (s : ↥A → ZMod 3)
    (i : ↥A) : Fin r → Multiplicative (ZMod 3) :=
  Pi.mulSingle (π i) (Multiplicative.ofAdd (s i))

private theorem chartCoord_diagHom_rot {F K : Type} [Field F] [Field K] [Finite K] [CharP K 2]
    [Algebra F K] {n r : ℕ} {ω : K} {c : Fin n → ZMod 3} {A : Finset (Fin n)}
    {π : ↥A ≃ Fin r} {s : ↥A → ZMod 3} {κ : ↥(planeSpan n A) → (Fin r → K)}
    (hκ : ∀ (u : ↥(planeSpan n A)) (j : Fin r),
      κ u j = sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n))
    {σ : K ≃+* K} {ζ : normOne σ} (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hζpow : ∀ m : ℕ, (((ζ ^ m : normOne σ) : Kˣ) : K) = ω ^ m)
    (hcs : ∀ i : ↥A, c (i : Fin n) = s i) (i : ↥A)
    {y : ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)}
    (hy : ∀ u : ↥(planeSpan n A),
      ((y u : ↥(planeSpan n A)) : ChartV n) = rot n i (u : ChartV n))
    (u : ↥(planeSpan n A)) :
    κ (y u) = diagHom F σ r (fun j => ζ ^ (toAdd (chartScalar π s i j)).val) (κ u) := by
  have hif : ∀ j : Fin r, ((π.symm j : ↥A) : Fin n) = (i : Fin n) ↔ j = π i := by
    intro j
    constructor
    · intro h
      have h1 : π.symm j = i := Subtype.ext h
      simpa using congrArg π h1
    · intro h
      rw [h]
      simp
  funext j
  rw [hκ, hy u]
  rw [sixPlaneK_rot (ω := ω) (c := c) hω hc (i : Fin n) (u : ChartV n)]
  beta_reduce
  rw [diagHom_apply, hκ u j]
  by_cases hj : j = π i
  · have hcond : ((π.symm j : ↥A) : Fin n) = (i : Fin n) := (hif j).mpr hj
    rw [if_pos hcond, hcs i]
    have htoAdd : toAdd (chartScalar π s i j) = s i := by
      rw [hj]
      simp [chartScalar]
    rw [htoAdd, hζpow (s i).val]
  · have hcond : ¬ (((π.symm j : ↥A) : Fin n) = (i : Fin n)) :=
      fun h => hj ((hif j).mp h)
    rw [if_neg hcond, one_mul]
    have htoAdd : toAdd (chartScalar π s i j) = 0 := by
      simp [chartScalar, hj]
    rw [htoAdd]
    simp

private theorem exists_chart_transport {F K V : Type} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module F V] {σ : K ≃+* K} {E : QuadExt F K σ} {n r : ℕ}
    {A : Finset (Fin n)} {Q : QuadraticForm F V} {κ : ↥(planeSpan n A) ≃+ (Fin r → K)}
    {χ : V ≃ₗ[F] (Fin r → K)} (hF : Nat.card F = 2)
    (hκ : ∀ u : ↥(planeSpan n A), Qn E r (κ u) = 0 ↔
      ChartU n A u = 0)
    (hχ : ∀ v : V, Qn E r (χ v) = 0 ↔ Q v = 0) :
    ∃ (Θ₁ : ↥(orthDerived (ChartU n A)) ≃* ↥(orthDerived (Qn E r)))
      (Θ₂ : ↥(orthDerived Q) ≃* ↥(orthDerived (Qn E r))),
      (∀ (y : ↥(orthDerived (ChartU n A)))
        (u : ↥(planeSpan n A)),
        (Θ₁ y : (Fin r → K) ≃ₗ[F] (Fin r → K)) (κ u) =
          κ ((y : ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) u)) ∧
      (∀ (y : ↥(orthDerived Q)) (v : V),
        (Θ₂ y : (Fin r → K) ≃ₗ[F] (Fin r → K)) (χ v) = χ ((y : V ≃ₗ[F] V) v)) := by
  obtain ⟨Θ₁, hΘ₁⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_mulEquiv_orthDerived_of_addEquiv
      (F := ZMod 2) (F' := F) (Nat.card_zmod 2) hF
      (W := ↥(planeSpan n A)) (W' := Fin r → K)
      (ChartU n A) (Qn E r) κ hκ
  obtain ⟨Θ₂, hΘ₂⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_mulEquiv_orthDerived_of_addEquiv
      (F := F) (F' := F) hF hF (W := V) (W' := Fin r → K) Q (Qn E r) χ.toAddEquiv hχ
  exact ⟨Θ₁, Θ₂, hΘ₁, hΘ₂⟩

private theorem chart_rot_diag {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore 3 Bs X) {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra Φ.F K]
    {n : ℕ} {A : Finset (Fin n)} {π : ↥A ≃ Fin Φ.r} {s : ↥A → ZMod 3}
    {c : Fin n → ZMod 3} {ω : K} {κ : ↥(planeSpan n A) ≃+ (Fin Φ.r → K)}
    (hκ : ∀ (u : ↥(planeSpan n A)) (j : Fin Φ.r),
      κ u j = sixPlaneK ω c (u : ChartV n) ((π.symm j : ↥A) : Fin n))
    {σ : K ≃+* K} {ζ : normOne σ} (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hζpow : ∀ m : ℕ, (((ζ ^ m : normOne σ) : Kˣ) : K) = ω ^ m)
    (hcs : ∀ i : ↥A, c (i : Fin n) = s i)
    {R : ↥(orthDerived (ChartU n A)) ≃* ↥(supp n A)}
    (hR : ∀ (y : ↥(orthDerived (ChartU n A))) (v : ↥(planeSpan n A)),
      ((R y : ↥(supp n A)) : ChartV n ≃ₗ[ZMod 2] ChartV n) v =
        (((y : ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) v : ↥(planeSpan n A)) :
          ChartV n))
    (i : ↥A) :
    ∀ u : ↥(planeSpan n A),
      κ ((((R.symm ⟨rot n i, rot_mem_supp i.2⟩ : ↥(orthDerived (ChartU n A))) :
          ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) u)) =
        diagHom Φ.F σ Φ.r (fun j => ζ ^ (toAdd (chartScalar π s i j)).val) (κ u) := by
  classical
  let ri : ↥(supp n A) := ⟨rot n i, rot_mem_supp i.2⟩
  let y₀ : ↥(orthDerived (ChartU n A)) := R.symm ri
  have hRy : ((R y₀ : ↥(supp n A)) : ChartV n ≃ₗ[ZMod 2] ChartV n) = rot n i := by
    have h : R y₀ = ri := R.apply_symm_apply ri
    rw [h]
  have hrot : ∀ u : ↥(planeSpan n A),
      (((y₀ : ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) u : ↥(planeSpan n A)) :
        ChartV n) = rot n i (u : ChartV n) := by
    intro u
    have h := hR y₀ u
    rw [hRy] at h
    exact h.symm
  intro u
  exact chartCoord_diagHom_rot (κ := κ) (σ := σ) (ζ := ζ) hκ hω hc hζpow hcs i hrot u

private theorem chart_orthDerived_eq {F₀ F K W V : Type} [Field F₀] [Field F] [Field K]
    [Algebra F K] [AddCommGroup W] [Module F₀ W] [AddCommGroup V] [Module F V] {σ : K ≃+* K}
    {r : ℕ} {E : QuadExt F K σ} {QW : QuadraticForm F₀ W} {QV : QuadraticForm F V}
    {κ : W ≃+ (Fin r → K)} {χ : V ≃ₗ[F] (Fin r → K)}
    (Θ₁ : ↥(orthDerived QW) ≃* ↥(orthDerived (Qn E r)))
    (hΘ₁ : ∀ (y : ↥(orthDerived QW)) (w : W),
      (Θ₁ y : (Fin r → K) ≃ₗ[F] (Fin r → K)) (κ w) = κ ((y : W ≃ₗ[F₀] W) w))
    (Θ₂ : ↥(orthDerived QV) ≃* ↥(orthDerived (Qn E r)))
    (hΘ₂ : ∀ (y : ↥(orthDerived QV)) (v : V),
      (Θ₂ y : (Fin r → K) ≃ₗ[F] (Fin r → K)) (χ v) = χ ((y : V ≃ₗ[F] V) v))
    (y₀ : ↥(orthDerived QW)) (y : ↥(orthDerived QV)) {d : Fin r → normOne σ}
    (hy₀ : ∀ w : W, κ ((y₀ : W ≃ₗ[F₀] W) w) = diagHom F σ r d (κ w))
    (hy : ∀ v : V, χ ((y : V ≃ₗ[F] V) v) = diagHom F σ r d (χ v)) :
    Θ₁ y₀ = Θ₂ y := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := κ.surjective x
  rw [hΘ₁ y₀ u, hy₀ u, ← χ.apply_symm_apply (κ u), hΘ₂ y (χ.symm (κ u)),
    hy (χ.symm (κ u))]

private theorem chart_psi_rot {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore 3 Bs X) {K : Type} [Field K] [Algebra Φ.F K] {n : ℕ}
    {A : Finset (Fin n)} {σ : K ≃+* K}
    {κ : ↥(planeSpan n A) ≃+ (Fin Φ.r → K)} {E : QuadExt Φ.F K σ}
    {Θ₁ : ↥(orthDerived (ChartU n A)) ≃* ↥(orthDerived (Qn E Φ.r))}
    (hΘ₁ : ∀ (y : ↥(orthDerived (ChartU n A))) (u : ↥(planeSpan n A)),
      (Θ₁ y : (Fin Φ.r → K) ≃ₗ[Φ.F] (Fin Φ.r → K)) (κ u) =
        κ ((y : ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) u))
    {χ : Φ.V ≃ₗ[Φ.F] (Fin Φ.r → K)}
    {Θ₂ : ↥(orthDerived Φ.Q) ≃* ↥(orthDerived (Qn E Φ.r))}
    (hΘ₂ : ∀ (y : ↥(orthDerived Φ.Q)) (v : Φ.V),
      (Θ₂ y : (Fin Φ.r → K) ≃ₗ[Φ.F] (Fin Φ.r → K)) (χ v) = χ ((y : Φ.V ≃ₗ[Φ.F] Φ.V) v))
    {R : ↥(orthDerived (ChartU n A)) ≃* ↥(supp n A)} (i : ↥A)
    {d : Fin Φ.r → normOne σ}
    (hy₀ : ∀ u : ↥(planeSpan n A),
      κ ((((R.symm ⟨rot n i, rot_mem_supp i.2⟩ : ↥(orthDerived (ChartU n A))) :
          ↥(planeSpan n A) ≃ₗ[ZMod 2] ↥(planeSpan n A)) u)) = diagHom Φ.F σ Φ.r d (κ u))
    (y : ↥(orthDerived Φ.Q))
    (hyχ : ∀ v : Φ.V, χ ((y : Φ.V ≃ₗ[Φ.F] Φ.V) v) = diagHom Φ.F σ Φ.r d (χ v)) :
    Φ.ψ (Θ₂.symm (Θ₁ (R.symm ⟨rot n i, rot_mem_supp i.2⟩))) = Φ.ψ y := by
  have hΘeq : Θ₁ (R.symm ⟨rot n i, rot_mem_supp i.2⟩) = Θ₂ y :=
    chart_orthDerived_eq Θ₁ hΘ₁ Θ₂ hΘ₂ (R.symm ⟨rot n i, rot_mem_supp i.2⟩) y hy₀ hyχ
  show Φ.ψ (Θ₂.symm (Θ₁ (R.symm ⟨rot n i, rot_mem_supp i.2⟩))) = Φ.ψ y
  rw [hΘeq, MulEquiv.symm_apply_apply]

theorem OrthFrameCore.exists_sixPlane_chart {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2) {n : ℕ}
    {A : Finset (Fin n)} (π : ↥A ≃ Fin Φ.r) (s : ↥A → ZMod p) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∃ φ : ↥(CFSG.ClassicalGroups.Orthogonal.SixPlane.supp n A) →* G,
    Function.Injective φ ∧ φ.range = X ∧
      ∀ (i : ↥A) (y : ↥(orthDerived Φ.Q)),
        (y : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ (Pi.mulSingle (π i) (Multiplicative.ofAdd (s i))) →
          φ ⟨CFSG.ClassicalGroups.Orthogonal.SixPlane.rot n i,
            CFSG.ClassicalGroups.Orthogonal.SixPlane.rot_mem_supp i.2⟩ = Φ.ψ y := by
  classical
  obtain rfl : p = 3 := Φ.p_eq_three hF
  obtain ⟨inst, E, χ, ζ, hζ1, hζp, hχQ, hχτ⟩ := Φ.exists_normIso hF
  letI := inst
  let K := GaloisField 2 2
  let σ : K ≃+* K := unitaryInvolution K 2 1
  let ω : K := ((ζ : Kˣ) : K)
  have hω : ω ^ 2 + ω + 1 = 0 := normOne_coe_sq_add_coe_add_one (σ := σ) hζ1 hζp
  have hζpow : ∀ m : ℕ, (((ζ ^ m : normOne σ) : Kˣ) : K) = ω ^ m := normOne_coe_pow σ ζ
  have hK4 : Nat.card K = 4 := by
    change Nat.card (GaloisField 2 2) = 4
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let c : Fin n → ZMod 3 := fun i => if h : i ∈ A then s ⟨i, h⟩ else 1
  have hc : ∀ i, c i = 1 ∨ c i = -1 := signVec_ite hs
  have hcardA : A.card = Φ.r := by
    simpa using Fintype.card_congr π
  obtain ⟨κ, κ_apply⟩ := exists_chartCoordEquiv (K := K) (π := π) hω hc hK4 hcardA
  have hκQ : ∀ u : ↥(planeSpan n A),
      Qn E Φ.r (κ u) = 0 ↔ ChartU n A u = 0 :=
    chartCoord_Qn_eq_zero_iff (κ := κ) (π := π) (ω := ω) (c := c) κ_apply hω hc hK4 E
  obtain ⟨Θ₁, Θ₂, hΘ₁, hΘ₂⟩ :=
    exists_chart_transport (Q := Φ.Q) (χ := χ) (E := E) (κ := κ) hF hκQ
      (fun v => by rw [hχQ v])
  have hA3 : 3 ≤ A.card := le_trans (by norm_num) (le_trans Φ.hr (le_of_eq hcardA.symm))
  obtain ⟨R, hR⟩ :=
    CFSG.ClassicalGroups.Orthogonal.SixPlane.exists_mulEquiv_orthDerived_restrict (S := A) hA3
  let φ : ↥(supp n A) →* G :=
    Φ.ψ.comp (Θ₂.symm.toMonoidHom.comp (Θ₁.toMonoidHom.comp R.symm.toMonoidHom))
  refine ⟨φ, Φ.hinj.comp (Θ₂.symm.injective.comp (Θ₁.injective.comp R.symm.injective)),
    ?_, ?_⟩
  · change (Φ.ψ.comp (Θ₂.symm.toMonoidHom.comp
      (Θ₁.toMonoidHom.comp R.symm.toMonoidHom))).range = X
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (Θ₂.symm.surjective.comp (Θ₁.surjective.comp R.symm.surjective)), Subgroup.map_top]
    exact Φ.hrange
  · intro i y hy
    have hy₀ := chart_rot_diag (Φ := Φ) (κ := κ) (π := π) (s := s) (c := c) κ_apply hω hc
      hζpow (fun j => by simp [c, j.2]) hR i
    have hyχ : ∀ v : Φ.V, χ ((y : Φ.V ≃ₗ[Φ.F] Φ.V) v) =
        diagHom Φ.F σ Φ.r (fun j => ζ ^ (toAdd (chartScalar π s i j)).val) (χ v) := by
      intro v
      rw [hy]
      exact hχτ (chartScalar π s i) v
    exact chart_psi_rot (Φ := Φ) (κ := κ) hΘ₁ hΘ₂ i hy₀ y hyχ

end

end CFSG.StandardType.OrthTorus

end
