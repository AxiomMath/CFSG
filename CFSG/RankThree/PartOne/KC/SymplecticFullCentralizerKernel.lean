module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open Module TensorProduct Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open scoped IsMulCommutative

section Skew

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Γ : Type*} [Group Γ] [Fintype Γ] {ρ : Γ →* Module.End K V} {p : ℕ}

open _root_.Classical in
theorem range_lineIdem_some_skew (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (hBskew : ∀ u v, B v u = -B u v) (hBnd : ∀ u, (∀ v, B u v = 0) → u = 0)
    (M : {M : Subgroup Γ // Nat.card M = p}) :
    LinearMap.range (lineIdem ρ p (some M)) =
      fixSub ρ M.1 ⊓ LinearMap.BilinForm.orthogonal B (fixSub ρ ⊤) := by
  have htop := card_top_ne_zero (K := K) hΓ hpK
  have hMK := card_line_ne_zero (K := K) M.2 hpK
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    simp only [lineIdem, LinearMap.sub_apply]
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [map_sub, apply_avgOp hd, apply_avgOp (Subgroup.mem_top d)]
    · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [map_sub, ← bilin_avgOp B hB, ← bilin_avgOp B hB,
        avgOp_apply_of_fixed hMK (fun d _ => hu d (Subgroup.mem_top d)),
        avgOp_apply_of_fixed htop hu, sub_self]
  · rintro ⟨hw1, hw2⟩
    refine ⟨w, ?_⟩
    have h1 : avgOp ρ M.1 w = w := avgOp_apply_of_fixed hMK hw1
    have h2 : avgOp ρ ⊤ w = 0 := by
      apply hBnd
      intro x
      have hy : avgOp ρ ⊤ x ∈ fixSub ρ ⊤ := fun d _ => apply_avgOp (Subgroup.mem_top d) x
      have h3 : B (avgOp ρ ⊤ x) w = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp hw2 _ hy
      rw [bilin_avgOp B hB ⊤ w x, hBskew (avgOp ρ ⊤ x) w, h3, neg_zero]
    simp only [lineIdem, LinearMap.sub_apply, h1, h2, sub_zero]

open _root_.Classical in
theorem lineIdem_restrict_nondegenerate_skew (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (hBskew : ∀ u v, B v u = -B u v) (hBnd : ∀ u, (∀ v, B u v = 0) → u = 0)
    (i : Option {M : Subgroup Γ // Nat.card M = p}) :
    (B.restrict (LinearMap.range (lineIdem ρ p i))).Nondegenerate := by
  have key : ∀ x ∈ LinearMap.range (lineIdem ρ p i),
      (∀ y ∈ LinearMap.range (lineIdem ρ p i), B x y = 0) → x = 0 := by
    rintro _ ⟨u, rfl⟩ h
    apply hBnd
    intro v
    have := h (lineIdem ρ p i v) ⟨v, rfl⟩
    rwa [lineIdem_selfAdjoint B hB, ← Module.End.mul_apply, lineIdem_mul_self hΓ hpK,
      ← lineIdem_selfAdjoint B hB] at this
  constructor
  · intro x hx
    exact Subtype.ext (key x x.2 fun y hy => hx ⟨y, hy⟩)
  · intro y hy
    refine Subtype.ext (key y y.2 fun x hx => ?_)
    rw [hBskew x y]
    have := hy ⟨x, hx⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this
    rw [this, neg_zero]

end Skew

section Plane

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spRep (Ahat : Subgroup (StatedSp r K)) :
    ↥Ahat →* Module.End K (Fin r ⊕ Fin r → K) :=
  (Units.coeHom (Module.End K (Fin r ⊕ Fin r → K))).comp ((spLin r K).comp Ahat.subtype)

theorem spRep_apply (Ahat : Subgroup (StatedSp r K)) (x : ↥Ahat) (v : Fin r ⊕ Fin r → K) :
    spRep Ahat x v = ((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) *ᵥ v := rfl

theorem spRep_isometry (Ahat : Subgroup (StatedSp r K)) (g : ↥Ahat) (u w : Fin r ⊕ Fin r → K) :
    spForm r K (spRep Ahat g u) (spRep Ahat g w) = spForm r K u w :=
  (mem_sesqUnitaryGroup.mp (spLin_mem (g : StatedSp r K))) u w

theorem spRep_injective (Ahat : Subgroup (StatedSp r K)) {g : ↥Ahat} (hg : spRep Ahat g = 1) :
    g = 1 := by
  have h1 : spLin r K (g : StatedSp r K) = 1 := Units.ext hg
  exact Subtype.ext (spLin_injective (by rw [h1, Subgroup.coe_one, map_one]))

@[expose] noncomputable def spPlaneFix (Ahat : Subgroup (StatedSp r K)) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  fixSub (spRep Ahat) ⊤

@[expose] noncomputable def spLineFix {Ahat : Subgroup (StatedSp r K)} (M : Subgroup ↥Ahat) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  fixSub (spRep Ahat) M

@[expose] noncomputable def spLineSpace {Ahat : Subgroup (StatedSp r K)} (M : Subgroup ↥Ahat) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  spLineFix M ⊓ LinearMap.BilinForm.orthogonal (spForm r K) (spPlaneFix Ahat)

@[expose] noncomputable def spInnerSummand (p : ℕ) (Ahat : Subgroup (StatedSp r K)) :
    Option {M : Subgroup ↥Ahat // Nat.card M = p} → Submodule K (Fin r ⊕ Fin r → K)
  | none => spPlaneFix Ahat
  | some M => spLineSpace M.1

open _root_.Classical in
theorem spInnerSummand_eq_range {p : ℕ} {Ahat : Subgroup (StatedSp r K)} [Fintype Ahat]
    (hΓ : Nat.card Ahat = p ^ 2) (hpK : (p : K) ≠ 0)
    (i : Option {M : Subgroup ↥Ahat // Nat.card M = p}) :
    spInnerSummand p Ahat i = LinearMap.range (lineIdem (spRep Ahat) p i) := by
  rcases i with _ | ⟨M, hM⟩
  · exact (range_lineIdem_none hΓ hpK).symm
  · rw [range_lineIdem_some_skew hΓ hpK (spForm r K) (spRep_isometry Ahat)
      (fun u v => (spForm_isAlt (r := r) (K := K)).neg_eq u v |>.symm)
      (fun u h => spForm_nondegenerate.1 u h)]
    rfl

end Plane

section Characters

variable {r : ℕ} {K : Type} [Field K]

open _root_.Classical in
theorem sp_bcRep_charSpace_facts {ℓ p : ℕ} [Finite K] (hℓ : ℓ.Prime) [CharP K ℓ]
    (hp : p.Prime) (hpℓ : p ≠ ℓ) {Ahat : Subgroup (StatedSp r K)} [IsMulCommutative Ahat]
    [Fintype Ahat] (hexp : ∀ x : Ahat, x ^ p = 1) (hΓ : Nat.card Ahat = p ^ 2) [NeZero p]
    [Fintype (Additive Ahat →+ ZMod p)] (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    (∀ χ : Additive Ahat →+ ZMod p, finrank L (charSpace (bcRepOf L (spRep Ahat)) ζ
        ((Nat.card K) • χ)) = finrank L (charSpace (bcRepOf L (spRep Ahat)) ζ χ)) ∧
      (∀ χ : Additive Ahat →+ ZMod p, finrank L (charSpace (bcRepOf L (spRep Ahat)) ζ (-χ)) =
        finrank L (charSpace (bcRepOf L (spRep Ahat)) ζ χ)) ∧
      AddSubgroup.closure {χ : Additive Ahat →+ ZMod p |
        χ ≠ 0 ∧ charSpace (bcRepOf L (spRep Ahat)) ζ χ ≠ ⊥} = ⊤ ∧
      ∑ χ : Additive Ahat →+ ZMod p, finrank L (charSpace (bcRepOf L (spRep Ahat)) ζ χ) =
        finrank K (Fin r ⊕ Fin r → K) ∧
      ∀ M : {M : Subgroup ↥Ahat // Nat.card M = p}, (spLineSpace M.1).baseChange L =
        ⨆ (χ : Additive Ahat →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M.1),
          charSpace (bcRepOf L (spRep Ahat)) ζ χ := by
  have := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).mpr hpK
  have hΓL : (Fintype.card Ahat : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hΓ, Nat.cast_pow]
    exact pow_ne_zero 2 hpL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  let σ : L ≃+* L := iterateFrobeniusEquiv L ℓ n
  have hσ : ∀ x : L, σ x = x ^ Nat.card K := fun x => by
    rw [Nat.card_eq_fintype_card, hn, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσK : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c := fun c => by
    rw [hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hfaith : ∀ g : Ahat, bcRepOf L (spRep Ahat) g = 1 → g = 1 := fun g hg =>
    spRep_injective Ahat (eq_of_baseChange_eq L (by
      rw [← bcRepOf_apply, hg, LinearMap.baseChange_one]))
  have hBL : ∀ (g : Ahat) (s t : L ⊗[K] (Fin r ⊕ Fin r → K)),
      LinearMap.BilinForm.baseChange L (spForm r K)
        (bcRepOf L (spRep Ahat) g s) (bcRepOf L (spRep Ahat) g t) =
        LinearMap.BilinForm.baseChange L (spForm r K) s t :=
    fun g s t => baseChange_apply_baseChange L (spForm r K) (spRep Ahat g)
      (spRep_isometry Ahat g) s t
  have hBnd : ∀ s : L ⊗[K] (Fin r ⊕ Fin r → K),
      (∀ t, LinearMap.BilinForm.baseChange L (spForm r K) s t = 0) → s = 0 :=
    bilin_baseChange_separatingLeft L (spForm r K) spForm_nondegenerate
  refine ⟨fun χ => finrank_charSpace_nsmul hζ.pow_eq_one σ (fieldAutTensor L σ hσK)
      (fieldAutTensor_smul σ hσK) (fun g t => fieldAutTensor_baseChange σ hσK _ t) _ (hσ ζ) χ,
    fun χ => finrank_charSpace_neg hp hζ hexp hΓL _ hBL hBnd χ,
    closure_support_charSpace_eq_top hp hζ hexp hΓL hfaith,
    by rw [sum_finrank_charSpace hp hζ hexp hΓL, Module.finrank_baseChange], fun M => ?_⟩
  have hl : spLineSpace M.1 = LinearMap.range (lineIdem (spRep Ahat) p (some M)) :=
    spInnerSummand_eq_range hΓ hpK (some M)
  rw [hl, ← range_baseChange_eq, range_lineIdem_baseChange hp hexp hΓ hpL hζ M]

end Characters

section Decomposition

variable {r : ℕ} {K : Type} [Field K]

open _root_.Classical in
theorem symplectic_plane_kernel_line_decomposition {ℓ p : ℕ} [Finite K] (hℓ : ℓ.Prime)
    [CharP K ℓ] (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {Ahat : Subgroup (StatedSp r K)}
    (hA : IsElementaryAbelian p Ahat) (hAc : Nat.card Ahat = p ^ 2) :
    DirectSum.IsInternal (spInnerSummand p Ahat) ∧
    (∀ i j, i ≠ j → ∀ u ∈ spInnerSummand p Ahat i, ∀ v ∈ spInnerSummand p Ahat j,
      spForm r K u v = 0) ∧
    (∀ i, ((spForm r K).restrict (spInnerSummand p Ahat i)).Nondegenerate) ∧
    (∀ M : Subgroup ↥Ahat, Nat.card M = p → ∀ a ∈ M, a ≠ 1 →
      LinearMap.ker (spEnd (a : StatedSp r K) - 1) = spLineFix M ∧
        spLineFix M = spPlaneFix Ahat ⊔ spLineSpace M) ∧
    (∃ M₁ M₂ : Subgroup ↥Ahat, Nat.card M₁ = p ∧ Nat.card M₂ = p ∧ M₁ ≠ M₂ ∧
      spLineSpace M₁ ≠ ⊥ ∧ spLineSpace M₂ ≠ ⊥) ∧
    (∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      0 < finrank K (spLineSpace M) ∧
        Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ∣ finrank K (spLineSpace M)) ∧
    Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤ r := by
  have := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have := hA
  have hexp : ∀ x : Ahat, x ^ p = 1 := fun x => by
    have h1 : (x : StatedSp r K) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (x : StatedSp r K) x.2
    exact Subtype.ext (by simpa using h1)
  have hΓ : Nat.card Ahat = p ^ 2 := hAc
  have : Fintype Ahat := Fintype.ofFinite _
  set ρ := spRep Ahat with hρ
  set B := spForm r K with hBdef
  have hρB : ∀ g u w, B (ρ g u) (ρ g w) = B u w := fun g u w => spRep_isometry Ahat g u w
  have hBskew : ∀ u v, B v u = -B u v := fun u v =>
    ((spForm_isAlt (r := r) (K := K)).neg_eq u v).symm
  have hBnd : ∀ u, (∀ v, B u v = 0) → u = 0 := fun u h => spForm_nondegenerate.1 u h
  have hsummand : ∀ i, spInnerSummand p Ahat i = LinearMap.range (lineIdem ρ p i) :=
    spInnerSummand_eq_range hΓ hpK
  have hplane : spPlaneFix Ahat = fixSub ρ ⊤ := rfl
  have hline : ∀ M : Subgroup Ahat, spLineFix M = fixSub ρ M := fun M => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hfun : spInnerSummand p Ahat = fun i => LinearMap.range (lineIdem ρ p i) :=
      funext hsummand
    rw [hfun]
    exact isInternal_range_of_orthogonal_idempotents _ (lineIdem_mul_self hΓ hpK)
      (fun i j h => lineIdem_mul_of_ne hp hexp hΓ hpK h) (sum_lineIdem hp hexp hΓ hpK)
  · intro i j hij u hu v hv
    rw [hsummand] at hu hv
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    exact lineIdem_orthogonal B hp hexp hΓ hpK hρB hij u' v'
  · intro i
    rw [hsummand]
    exact lineIdem_restrict_nondegenerate_skew hΓ hpK B hρB hBskew hBnd i
  · intro M hM a haM ha1
    have hMeq : M = Subgroup.zpowers a := eq_zpowers_of_natCard_eq_prime_of_mem hp hexp hM ha1 haM
    refine ⟨?_, ?_⟩
    · ext v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hline,
        mem_fixSub]
      constructor
      · intro hv
        let S : Subgroup Ahat :=
          { carrier := {d | ρ d v = v}
            mul_mem' := fun {x y} hx hy => by
              change ρ (x * y) v = v
              rw [map_mul, Module.End.mul_apply, show ρ y v = v from hy, show ρ x v = v from hx]
            one_mem' := by
              change ρ 1 v = v
              rw [map_one, Module.End.one_apply]
            inv_mem' := fun {x} hx => by
              change ρ x⁻¹ v = v
              conv_lhs => rw [← show ρ x v = v from hx]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply] }
        have hle : M ≤ S := hMeq ▸ (Subgroup.zpowers_le).mpr (show ρ a v = v from hv)
        exact fun d hd => hle hd
      · intro h
        exact h a haM
    · have hMK := card_line_ne_zero (K := K) hM hpK
      apply le_antisymm
      · rw [hline, ← range_avgOp_eq_fixSub hMK]
        have hsum : avgOp ρ M = lineIdem ρ p none + lineIdem ρ p (some ⟨M, hM⟩) := by
          simp only [lineIdem]
          abel
        rw [hsum]
        refine (LinearMap.range_add_le _ _).trans (sup_le_sup ?_ ?_)
        · rw [← hsummand]
          rfl
        · rw [← hsummand]
          rfl
      · refine sup_le ?_ inf_le_left
        rw [hplane, hline]
        exact fun v hv d _ => hv d trivial
  ·
    have : NeZero p := ⟨hp.ne_zero⟩
    have : Finite (Additive Ahat →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
    have : Fintype (Additive Ahat →+ ZMod p) := Fintype.ofFinite _
    have : IsMulCommutative Ahat := inferInstance
    have hDcard : Nat.card (Additive Ahat →+ ZMod p) = p ^ 2 := by rw [natCard_char hp hexp, hΓ]
    have hq : ¬p ∣ Nat.card K := by
      obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
      rw [Nat.card_eq_fintype_card, hn]
      exact fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h))
    have hpL : (p : AlgebraicClosure K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
      exact (map_ne_zero _).mpr hpK
    have hΓL : (Fintype.card Ahat : AlgebraicClosure K) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, hΓ, Nat.cast_pow]
      exact pow_ne_zero 2 hpL
    have : NeZero (p : K) := ⟨hpK⟩
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
    obtain ⟨hfrob, hneg, hcl, hsum, hlines⟩ :=
      sp_bcRep_charSpace_facts hℓ hp hpℓ hexp hΓ (AlgebraicClosure K) hζ₀
    have hS : AddSubgroup.closure {χ : Additive Ahat →+ ZMod p | χ ≠ 0 ∧
        finrank (AlgebraicClosure K) (charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ) ≠ 0} =
          ⊤ := by
      have hset : {χ : Additive Ahat →+ ZMod p | χ ≠ 0 ∧
          finrank (AlgebraicClosure K) (charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ) ≠ 0} =
          {χ | χ ≠ 0 ∧ charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ ≠ ⊥} := by
        ext χ
        exact and_congr_right fun _ => not_congr Submodule.finrank_eq_zero
      rw [hset]
      exact hcl
    have hdim : ∀ M : {M : Subgroup Ahat // Nat.card M = p}, finrank K (spLineSpace M.1) =
        ∑ χ ∈ Finset.univ.filter (fun χ : Additive Ahat →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1),
          finrank (AlgebraicClosure K) (charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ) := by
      intro M
      have h1 := finrank_biSup_of_iSupIndep
        (iSupIndep_charSpace (ρ := bcRepOf (AlgebraicClosure K) ρ) hζ₀ hΓL)
        (Finset.univ.filter fun χ : Additive Ahat →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1)
      have h2 : (⨆ (χ : Additive Ahat →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M.1),
          charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ) =
          ⨆ χ ∈ Finset.univ.filter (fun χ : Additive Ahat →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1),
            charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ :=
        iSup_congr fun χ => iSup_congr_Prop (by rw [Finset.mem_filter]; simp) fun _ => rfl
      rw [← finrank_submodule_baseChange (AlgebraicClosure K), hlines M, h2, h1]
    have hnebot : ∀ χ : Additive Ahat →+ ZMod p, χ ≠ 0 →
        charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ ≠ ⊥ → spLineSpace (charKer χ) ≠ ⊥ := by
      intro χ hχ hV hbot
      apply hV
      have h1 := hlines ⟨charKer χ, natCard_charKer hp hΓ hχ⟩
      rw [hbot, Submodule.baseChange_bot] at h1
      exact eq_bot_iff.mpr ((le_iSup₂_of_le (f := fun (ψ : Additive Ahat →+ ZMod p)
        (_ : ψ ≠ 0 ∧ charKer ψ = charKer χ) =>
          charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ ψ) χ ⟨hχ, rfl⟩ le_rfl).trans h1.symm.le)
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨χ₁, hχ₁, χ₂, hχ₂, hne⟩ := exists_charKer_ne hp hexp hΓ hcl fun χ hχ => hχ.1
      exact ⟨charKer χ₁, charKer χ₂, natCard_charKer hp hΓ hχ₁.1, natCard_charKer hp hΓ hχ₂.1,
        hne, hnebot χ₁ hχ₁.1 hχ₁.2, hnebot χ₂ hχ₂.1 hχ₂.2⟩
    · intro M hM hne
      refine ⟨Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h), ?_⟩
      rw [hdim ⟨M, hM⟩]
      exact lcm_dvd_sum_filter_charKer hp hp2 hΓ hq
        (fun χ => finrank (AlgebraicClosure K) (charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ))
        hfrob hneg M
    · have h2 := two_mul_lcm_le_sum hp hp2 hDcard hq
        (fun χ => finrank (AlgebraicClosure K) (charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ₀ χ))
        hfrob hneg hS
      rw [hsum, Module.finrank_fintype_fun_eq_card] at h2
      simp only [Fintype.card_sum, Fintype.card_fin] at h2
      omega

end Decomposition

end CFSG.RankThree.PartOne.KCSpFull
