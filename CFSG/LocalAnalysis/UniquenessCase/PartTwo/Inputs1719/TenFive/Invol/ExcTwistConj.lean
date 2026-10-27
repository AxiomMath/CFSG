module

public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction
public import CFSG.LieType.Chevalley.RationalToralSignDiagram
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.ToralSign

open scoped CFSG.ConvolutionPoints

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_conj_toral_twist_of_reps
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {D : ModGL τ k}
    (hD : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (ρ : Equiv.Perm (Fin τ.rank))
    (hFd : ∀ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
      frobTwistGL τ k p e D (rootDiagUnit τ b) = rootDiagUnit τ fun i => b (ρ.symm i))
    (reps : List (SignRep τ))
    (hfix : ∀ r ∈ reps, permChar ρ (signMaskChar τ r.mask) = signMaskChar τ r.mask)
    (hrep : ∀ χ, permChar ρ χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar τ r.mask))
    (hΩ : ∀ r ∈ reps, (kernelPosStabilizer (signMaskChar τ r.mask) : Set (WeylGroup τ)) =
      {w | ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = w})
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hx : x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ l ∈ r.omegaWords, ∃ g₁ ∈ adjointGroup τ k,
      g₁ * x * g₁⁻¹ = rootDiagUnit τ (signCharTuple (k := k) (signMaskChar τ r.mask)) ∧
      g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = wordWeylMatrix τ k l := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set F := frobTwistGL τ k p e D with hF
  set R := fixedPointsIn (adjointGroup τ k) F with hR
  have hFG : ∀ g ∈ adjointGroup τ k, F g ∈ adjointGroup τ k := fun g hg =>
    conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hg)
  obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hx
  obtain ⟨g, hg, r, hr, hgx, hFt⟩ :=
    exists_conj_eq_rootDiagUnit_of_reps hp ρ F hFG hFd reps hfix hrep hxG hxF hx2
  set χ := signMaskChar τ r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit τ a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hcZ : g * (F g)⁻¹ ∈ toralCentralizer τ k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    calc rootDiagUnit τ a * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ =
        (g * x * g⁻¹) * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by rw [hgx]
      _ = g * (F g)⁻¹ * (F g * x * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
      _ = g * (F g)⁻¹ := by rw [hFgx]; group
  obtain ⟨-, -, ⟨hMZ, -, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk a ha
  obtain ⟨q, hq⟩ := eW.surjective (QuotientGroup.mk ⟨_, hcZ⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hwχ : w ∈ charStabilizer χ := (mem_rootCharStabilizer_signCharTuple hk χ).1 hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  set ω := w * u with hω_def
  have huW : u ∈ kernelReflectionGroup a := by
    rw [kernelReflectionGroup_signCharTuple hk]
    exact hu
  have hωa : ω ∈ rootCharStabilizer a :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hωΩ)
  have hmk : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        QuotientGroup.mk ⟨ω, hωa⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change w⁻¹ * (w * u) ∈ kernelReflectionGroup a
    rw [inv_mul_cancel_left]
    exact huW
  rw [hmk, heW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  change (canonicalRep (coxeterSystem τ) k ω)⁻¹ * (g * (F g)⁻¹) ∈ toralRootGroup τ k a at hq
  obtain ⟨l, hl, hlω⟩ : ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = ω := by
    have h1 : ω ∈ (kernelPosStabilizer χ : Set (WeylGroup τ)) := hωΩ
    rw [hΩ r hr] at h1
    exact h1
  set N := wordWeylMatrix τ k l with hN_def
  set n := canonicalRep (coxeterSystem τ) k ω with hn_def
  have hh₀ : N * n⁻¹ ∈ torusGroup τ k := by
    refine mem_torusGroup_of_mapsRootLines_one (mul_mem (wordWeylMatrix_mem_monomialSubgroup l)
      (inv_mem (canonicalRep_mem_monomialSubgroup k ω))) ?_
    have h := (mapsRootLines_wordWeylMatrix (k := k) l).mul
      (mapsRootLines_canonicalRep (R := k) ω).inv
    rwa [hlω, mul_inv_cancel] at h
  have hnZ : n ∈ toralCentralizer τ k a := canonicalRep_mem_toralCentralizer hωa
  have hNZ : N ∈ toralCentralizer τ k a := by
    have h := mul_mem (torusGroup_le_toralCentralizer a hh₀) hnZ
    rwa [inv_mul_cancel_right] at h
  have hcv : ∃ m ∈ toralRootGroup τ k a, g * (F g)⁻¹ = m * N := by
    refine ⟨(N * n⁻¹)⁻¹ * (N * (n⁻¹ * (g * (F g)⁻¹)) * N⁻¹), mul_mem
      (inv_mem (le_sup_left (a := torusGroup τ k) hh₀))
      ((Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hNZ) _).1 hq), ?_⟩
    group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  obtain ⟨z, hzM, hzv, -⟩ := rational_centralizer_cocycle_reduction_of_map_conj p
    hp he hD hRfin hRsub ha hg hgx hFt hNZ hcv
  obtain ⟨hzG, hzt⟩ := mem_toralCentralizer.1 (hMZ hzM)
  refine ⟨r, hr, l, hl, z * g, mul_mem hzG hg, ?_, hzv⟩
  calc z * g * x * (z * g)⁻¹ = z * (g * x * g⁻¹) * z⁻¹ := by group
    _ = (rootDiagUnit τ a * z * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a * z⁻¹ := by
      rw [hgx, hzt]
    _ = rootDiagUnit τ a := by group

theorem exists_conj_toral_twist_E7
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {x : ModGL Tag.E7 k}
    (hx : x ∈ fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)) (hx2 : x ^ 2 = 1) :
    ∃ r ∈ e7SignDiagramReps, ∃ l ∈ r.omegaWords, ∃ g₁ ∈ adjointGroup .E7 k,
      g₁ * x * g₁⁻¹ = rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)) ∧
      g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k l := by
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  refine exists_conj_toral_twist_of_reps p hp he (map_conj_one_adjointGroup _ k) 1
    (fun b hb => ?_) e7SignDiagramReps h7.permChar_eq h7.exists_rep
    h7.coe_kernelPosStabilizer
    (finite_fixedPointsIn_frobTwistGL p he le_rfl (map_one _) (one_pow 1)) hx hx2
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p e hb, one_mul, inv_one,
    mul_one]
  rfl

theorem exists_conj_toral_twist_E6tw
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))) (hx2 : x ^ 2 = 1) :
    ∃ r ∈ e6SignDiagramReps, ∃ l ∈ r.omegaWords, ∃ g₁ ∈ adjointGroup TwistTag.E6.tag k,
      g₁ * x * g₁⁻¹ = rootDiagUnit TwistTag.E6.tag
        (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag r.mask)) ∧
      g₁ * (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) g₁)⁻¹ =
        wordWeylMatrix TwistTag.E6.tag k l := by
  obtain ⟨-, h, -⟩ := rational_toral_sign_diagram_arithmetic
  exact exists_conj_toral_twist_of_reps p hp he (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl))
    TwistTag.E6.perm (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 e hb)
    e6SignDiagramReps h.permChar_eq h.exists_rep h.coe_kernelPosStabilizer
    (finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.E6 k)) hx hx2

theorem exists_conj_toral_twist_D4tw
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))) (hx2 : x ^ 2 = 1) :
    ∃ r ∈ d4SignDiagramReps, ∃ l ∈ r.omegaWords, ∃ g₁ ∈ adjointGroup TwistTag.D4.tag k,
      g₁ * x * g₁⁻¹ = rootDiagUnit TwistTag.D4.tag
        (signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask)) ∧
      g₁ * (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) g₁)⁻¹ =
        wordWeylMatrix TwistTag.D4.tag k l := by
  obtain ⟨-, -, h⟩ := rational_toral_sign_diagram_arithmetic
  exact exists_conj_toral_twist_of_reps p hp he (map_conj_diagramMap TwistTag.D4 k (Or.inl rfl))
    TwistTag.D4.perm (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.D4 e hb)
    d4SignDiagramReps h.permChar_eq h.exists_rep h.coe_kernelPosStabilizer
    (finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)) hx hx2

omit [IsAlgClosed k] in
theorem conj_mem_fixedPointsIn_of_cocycle {e : ℕ} {D N g₁ : ModGL τ k}
    (hg₁ : g₁ ∈ adjointGroup τ k) (hc : g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = N) {v : ModGL τ k}
    (hv : v ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e (N * D))) :
    g₁⁻¹ * v * g₁ ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) := by
  obtain ⟨hvG, hvS⟩ := mem_fixedPointsIn.1 hv
  refine mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hg₁) hvG) hg₁, ?_⟩
  have hFg : frobTwistGL τ k p e D g₁ = N⁻¹ * g₁ := by
    rw [← hc]
    group
  rw [frobTwistGL_apply] at hvS
  rw [map_mul, map_mul, map_inv, hFg, frobTwistGL_apply]
  calc (N⁻¹ * g₁)⁻¹ * (D * entrywiseFrobGL τ k p e v * D⁻¹) * (N⁻¹ * g₁) =
      g₁⁻¹ * (N * D * entrywiseFrobGL τ k p e v * (N * D)⁻¹) * g₁ := by group
    _ = g₁⁻¹ * v * g₁ := by rw [hvS]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
