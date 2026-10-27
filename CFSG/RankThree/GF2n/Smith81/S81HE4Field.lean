module

public import CFSG.RankThree.GF2n.Smith81.S81HOrthRank
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualField

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.SeitzReduction.OmegaPilot
  (plusFieldPart plusRealization plusImage_eq_top orthAutFieldPart_kappa
    orthAutFieldPart_eq_one_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (unitMultiplierPairs mem_unitMultiplierPairs_iff)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

theorem plusFieldPart_eq_one_of_card {X : Type*} [Group X] [Finite X] {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) = ⊥) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : ↥F ≃* matrixProjectiveDerived (coordinateQuadPlus 6 K)) {A : Subgroup X}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hcard : 2 ^ (13 * f + 1) < Nat.card A) {a : X} (ha : a ∈ A) :
    plusFieldPart hf hK (by norm_num) (MulAut.congr e (MulAut.conjNormal a)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := plusRealization (K := K) (n := 6) hf hK (by norm_num)
  have hE := plusImage_eq_top (K := K) (n := 6) (by norm_num)
  set fp := plusFieldPart (K := K) (n := 6) hf hK (by norm_num) with hfp
  have hfpκ : ∀ g : similarityPairs (coordinateQuadPlus 6 K),
      fp (matrixProjectiveConjugationHom (coordinateQuadPlus 6 K) g) = g.val.right :=
    fun g => orthAutFieldPart_kappa _ _ g
  set β : X →* MulAut (matrixProjectiveDerived (coordinateQuadPlus 6 K)) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hβdef
  change fp (β a) = 1
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : MulAut.conjNormal x = (1 : MulAut ↥F) :=
      (MulAut.congr e).injective (by rw [map_one]; exact hx)
    have hc : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun φ : MulAut ↥F => ((φ ⟨y, hy⟩ : ↥F) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc y * x = x * y * x⁻¹ * x := by rw [h2]
        _ = x * y := by group
    rwa [hC, Subgroup.mem_bot] at hc
  obtain ⟨Φ, hΦ⟩ := hR.2.2.1
  obtain ⟨-, -, -, -, hinv⟩ := hR.2.2.2.2
  have hmemE : ∀ x, β x ∈ matrixProjectiveImage (coordinateQuadPlus 6 K) := fun x => by
    rw [hE]
    exact Subgroup.mem_top _
  set ψ : X →* unitMultiplierPairs (coordinateQuadPlus 6 K) :=
    Φ.symm.toMonoidHom.comp (β.codRestrict (matrixProjectiveImage (coordinateQuadPlus 6 K)) hmemE)
    with hψdef
  have hκψ : ∀ x, matrixProjectiveConjugationHom (coordinateQuadPlus 6 K) (ψ x) = β x := fun x => by
    rw [← hΦ]
    change ((Φ (Φ.symm ⟨β x, hmemE x⟩) : matrixProjectiveImage (coordinateQuadPlus 6 K)) :
      MulAut _) = β x
    rw [MulEquiv.apply_symm_apply]
  set g : X → coordinateSemilinearGroup (2 * 6) K := fun x =>
    ((ψ x : similarityPairs (coordinateQuadPlus 6 K)) :
    coordinateSemilinearGroup (2 * 6) K) with hgdef
  have hfpg : ∀ x, fp (β x) = (g x).right := fun x => by rw [← hκψ, hfpκ]
  have hgmul : ∀ x y, g (x * y) = g x * g y := fun x y => by
    simp only [hgdef, map_mul, Subgroup.coe_mul]
  have hgone : g 1 = 1 := by simp only [hgdef, map_one, OneMemClass.coe_one]
  have hTmul : ∀ x y v, coordinateSemilinearMap (g (x * y)) v =
      coordinateSemilinearMap (g x) (coordinateSemilinearMap (g y) v) := fun x y v => by
    rw [hgmul, coordinateSemilinearMap_mul]
  have hTiso : ∀ x v, coordinateQuadPlus 6 K (coordinateSemilinearMap (g x) v) =
      (g x).right (coordinateQuadPlus 6 K v) :=
    fun x => (mem_unitMultiplierPairs_iff (coordinateQuadPlus 6 K) _).1 (ψ x).2
  have hinvx : ∀ x ∈ A, fp (β x) ≠ 1 → (∀ v, coordinateSemilinearMap (g x)
      (coordinateSemilinearMap (g x) v) = v) ∧ orderOf (g x).right = 2 ∧
      ∀ τ : K ≃+* K, orderOf τ = 2 → τ = (g x).right := by
    intro x hx hne
    have hβ1 : β x ≠ 1 := fun h => hne (by rw [h, map_one])
    have hord : orderOf (β x) = 2 :=
      orderOf_eq_prime (by rw [← map_pow, hA x hx, map_one]) hβ1
    obtain ⟨-, hTT, hσ⟩ := hinv (β x) (hmemE x) hord (ψ x) (ψ x).2 (hκψ x)
    rw [hfpg] at hne
    obtain ⟨h2, huniq, -⟩ := hσ.resolve_left hne
    exact ⟨hTT, h2, huniq⟩
  by_contra hne
  obtain ⟨hTT, hσ2, -⟩ := hinvx a ha hne
  set σ := (g a).right with hσdef
  have hσne : σ ≠ 1 := by
    rw [hσdef, ← hfpg]
    exact hne
  have hdich : ∀ b ∈ A, fp (β b) = 1 ∨ fp (β b) = σ := by
    intro b hb
    by_cases h1 : fp (β b) = 1
    · exact Or.inl h1
    · obtain ⟨-, -, huniq⟩ := hinvx b hb h1
      exact Or.inr (by rw [hfpg, ← huniq σ hσ2])
  set φ : ↥A →* (K ≃+* K) := fp.comp (β.comp A.subtype) with hφ
  have hrange : Nat.card φ.range ≤ 2 := by
    have hinj : Function.Injective (fun r : φ.range => decide ((r : K ≃+* K) = 1)) := by
      rintro ⟨_, b, rfl⟩ ⟨_, b', rfl⟩ h
      simp only [decide_eq_decide] at h
      apply Subtype.ext
      change fp (β b) = fp (β b')
      rcases hdich b b.2 with h1 | h1 <;> rcases hdich b' b'.2 with h2 | h2
      · rw [h1, h2]
      · exact absurd (h.1 h1) (show ¬ fp (β b') = 1 by rw [h2]; exact hσne)
      · exact absurd (h.2 h2) (show ¬ fp (β b) = 1 by rw [h1]; exact hσne)
      · rw [h1, h2]
    simpa using Nat.card_le_card_of_injective _ hinj
  have hright : ∀ y : φ.ker, (g ((y : ↥A) : X)).right = 1 := fun y => by
    rw [← hfpg]
    exact y.2
  have hlin : ∀ y : φ.ker, ∀ v, coordinateSemilinearMap (g ((y : ↥A) : X)) v =
      Matrix.mulVec (g ((y : ↥A) : X)).left.val v := fun y v => by
    rw [coordinateSemilinearMap_apply, hright y]
    rfl
  let ρ : Representation K φ.ker (Fin (2 * 6) → K) :=
    { toFun := fun y =>
        { toFun := coordinateSemilinearMap (g ((y : ↥A) : X))
          map_add' := map_add _
          map_smul' := fun c v => by
            rw [coordinateSemilinearMap_smul, hright y]
            rfl }
      map_one' := LinearMap.ext fun v => by
        change coordinateSemilinearMap (g 1) v = v
        rw [hgone, coordinateSemilinearMap_one]
      map_mul' := fun y y' => LinearMap.ext fun v => hTmul _ _ v }
  have hρapp : ∀ y v, ρ y v = coordinateSemilinearMap (g ((y : ↥A) : X)) v := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hv : ∀ v, Matrix.mulVec (g ((y : ↥A) : X)).left.val v = v := fun v => by
      rw [← hlin, ← hρapp, hy, Module.End.one_apply]
    have hleft : (g ((y : ↥A) : X)).left = 1 :=
      Units.ext (Matrix.mulVec_injective (funext fun v => by
        rw [hv, Units.val_one, Matrix.one_mulVec]))
    have hg1 : g ((y : ↥A) : X) = 1 := SemidirectProduct.ext hleft (hright y)
    have hψ1 : ψ ((y : ↥A) : X) = 1 := Subtype.ext (Subtype.ext hg1)
    have hy1 : ((y : ↥A) : X) = 1 :=
      hβinj (by rw [← hκψ, hψ1, OneMemClass.coe_one, map_one, map_one])
    exact Subtype.ext (Subtype.ext hy1)
  have hiso : ∀ y v, (coordinateQuadPlus 6 K) (ρ y v) = (coordinateQuadPlus 6 K) v := fun y v => by
    rw [hρapp, hTiso, hright y]
    rfl
  have hcomm : ∀ y v, ρ y (coordinateSemilinearMap (g a) v) =
      coordinateSemilinearMap (g a) (ρ y v) := fun y v => by
    have hinvA : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA x hx)
    have hyA : ((y : ↥A) : X) ∈ A := (y : ↥A).2
    have hcomm : ((y : ↥A) : X) * a = a * ((y : ↥A) : X) := by
      calc ((y : ↥A) : X) * a = (((y : ↥A) : X) * a)⁻¹ := (hinvA _ (A.mul_mem hyA ha)).symm
        _ = a⁻¹ * ((y : ↥A) : X)⁻¹ := mul_inv_rev _ _
        _ = a * ((y : ↥A) : X) := by rw [hinvA _ hyA, hinvA a ha]
    rw [hρapp, hρapp, ← hTmul, ← hTmul, hcomm]
  have h2 : ∀ y : φ.ker, y * y = 1 := fun y => Subtype.ext (Subtype.ext (by
    change ((y : ↥A) : X) * ((y : ↥A) : X) = 1
    rw [← sq]
    exact hA _ (y : ↥A).2))
  have hker := OrthRank.card_le_of_semilinear_involution hf hK (V := Fin (2 * 6) → K)
    (by rw [Module.finrank_fin_fun]) (regular_coordinateQuadPlus (K := K) (n := 6) (by norm_num)).1
    σ hσ2 (coordinateSemilinearMap (g a)) (fun c v => coordinateSemilinearMap_smul _ c v) hTT
    (hTiso a) hρinj hiso hcomm h2
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h3 : Nat.card A ≤ 2 ^ (13 * f + 1) := by
    rw [← h1, pow_succ]
    exact Nat.mul_le_mul hker hrange
  omega

theorem mem_range_isometryConjugationHom_of_card {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    [F.Normal] (hC : Subgroup.centralizer (F : Set X) = ⊥) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : ↥F ≃* matrixProjectiveDerived (coordinateQuadPlus 6 K)) {A : Subgroup X}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hcard : 2 ^ (13 * f + 1) < Nat.card A) {a : X} (ha : a ∈ A) :
    MulAut.congr e (MulAut.conjNormal a) ∈
      (isometryConjugationHom (coordinateQuadPlus 6 K)).range :=
  (orthAutFieldPart_eq_one_iff _ _ _).1 (plusFieldPart_eq_one_of_card hC hf hK e hA hcard ha)

end CFSG.RankThree.GF2n.Smith81
