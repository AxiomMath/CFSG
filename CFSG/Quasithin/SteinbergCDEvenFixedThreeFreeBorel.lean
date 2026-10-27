module

public import CFSG.LieType.Chevalley.GraphFixedMinimalBorel
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] [CharP K 2]

theorem orderOf_orbitX_one_mul_orbitY_one
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    orderOf ((orbitX t K σ a 1 : ModGL t.tag K) * (orbitY t K σ a 1 : ModGL t.tag K)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm : orbitRankOneHom t K σ a (uSL 1 * vSL 1) =
      (orbitX t K σ a 1 : ModGL t.tag K) * (orbitY t K σ a 1 : ModGL t.tag K) := by
    rw [map_mul, orbitRankOneHom_uSL, orbitRankOneHom_vSL]
  have h2 : (1 : orbitField t K σ a) + 1 = 0 := by
    rw [one_add_one_eq_two]
    ext
    simp [CharTwo.two_eq_zero]
  have hm3 : (uSL (1 : orbitField t K σ a) * vSL 1) ^ 3 = 1 := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [pow_succ, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two, h2]
  rw [← hm]
  refine orderOf_eq_prime (by rw [← map_pow, hm3, map_one]) fun h => ?_
  obtain ⟨l, -, hl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom (MonoidHom.mem_ker.2 h)
  have h01 := congrFun (congrFun hl 0) 1
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem le_graphFixedRootBorel_of_orderOf_ne_three
    {σ : K →+* K} (hσ : Function.Surjective σ)
    {D : Subgroup (ModGL t.tag K)} (hDC : D ≤ graphFixedRootGroup t K σ)
    (hUD : graphFixedPosUnipotent t K σ ≤ D) (h3 : ∀ g ∈ D, orderOf g ≠ 3) :
    D ≤ graphFixedRootBorel t K σ := by
  intro g hg
  have hg' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hDC hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
  have hbUH : b ∈ (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) *
      (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul' hσ]
    exact hb
  have hbHU : b' ∈ (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul hσ]
    exact hb'
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := Set.mem_mul.1 hbUH
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := Set.mem_mul.1 hbHU
  set n := canonicalRep (coxeterSystem t.tag) K w with hn
  set z := h₁ * n * h₂ with hz
  have hzD : z ∈ D := by
    have h := mul_mem (mul_mem (inv_mem (hUD hu₁)) hg) (inv_mem (hUD hu₂))
    have e : u₁⁻¹ * (u₁ * h₁ * n * (h₂ * u₂)) * u₂⁻¹ = z := by
      rw [hz]
      group
    rwa [e] at h
  by_cases hw1 : w = 1
  · have hn1 : n = 1 := by
      rw [hn, hw1, canonicalRep_one]
    rw [hn1, mul_one]
    exact mul_mem hb hb'
  exfalso
  obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t (inv_mem hw) (inv_ne_one.2 hw1)
  set E : Set (Fin t.tag.rank → ℤ) :=
    (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) with hE
  set O : Set (Fin t.tag.rank → ℤ) :=
    (fun i => -(w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ))) '' ↑(t.orbit a) with hO
  have hEroot : ∀ α ∈ E, IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_neg_single _ i
  have hOpos : ∀ α ∈ O, IsRoot t.tag α ∧ 0 < height α := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨IsRoot.neg (IsRoot.smul (isRoot_single _ i) w⁻¹), ?_⟩
    rw [height_neg]
    exact neg_pos.2 (ha i hi)
  have hwO : (fun α => w • α) '' O = E := by
    rw [hO, hE, Set.image_image]
    refine Set.image_congr fun i _ => ?_
    rw [smul_neg, smul_inv_smul]
  set y : ModGL t.tag K := (orbitY t K σ a 1 : ModGL t.tag K) with hy
  obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 ((mem_rootSpan_negSimpleOrbitRoots_iff a).2 ⟨1, rfl⟩ :
    y ∈ rootSpan t.tag K E ⊓ twistedFixedGroup t K σ)
  obtain ⟨⟨hh₁H, hh₁Γ⟩, -⟩ := Subgroup.mem_inf.1 hh₁
  obtain ⟨⟨hh₂H, hh₂Γ⟩, -⟩ := Subgroup.mem_inf.1 hh₂
  have hnΓ : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  have hy₁ := (Subgroup.mem_normalizer_iff.1
    (torusGroup_le_normalizer_rootSpan hEroot (inv_mem hh₁H)) _).1 hyS
  rw [← hwO, ← (canonical_weyl_root_transport t.tag K).1 w O fun α hα => (hOpos α hα).1] at hy₁
  obtain ⟨u, hu, hue⟩ := hy₁
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hn] at hue
  have huΓ : u ∈ twistedFixedGroup t K σ := by
    have e : u = n⁻¹ * (h₁⁻¹ * y * h₁⁻¹⁻¹) * n := by
      rw [← hue]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnΓ) (mul_mem (mul_mem (inv_mem hh₁Γ) hyΓ)
      (inv_mem (inv_mem hh₁Γ)))) hnΓ
  have hu' := (Subgroup.mem_normalizer_iff.1
    (torusGroup_le_normalizer_rootSpan (fun α hα => (hOpos α hα).1) (inv_mem hh₂H)) _).1 hu
  have huD : h₂⁻¹ * u * h₂⁻¹⁻¹ ∈ D :=
    hUD (Subgroup.mem_inf.2 ⟨rootSpan_le_posUnipotent hOpos hu',
      mul_mem (mul_mem (inv_mem hh₂Γ) huΓ) (inv_mem (inv_mem hh₂Γ))⟩)
  have e : y = z * (h₂⁻¹ * u * h₂⁻¹⁻¹) * z⁻¹ := by
    have e' : y = h₁ * (n * u * n⁻¹) * h₁⁻¹ := by
      rw [hue]
      group
    rw [e', hz]
    group
  have hyD : y ∈ D := by
    rw [e]
    exact mul_mem (mul_mem hzD huD) (inv_mem hzD)
  exact h3 _ (mul_mem (hUD (orbitX_mem_graphFixedPosUnipotent t σ a 1)) hyD)
    (orderOf_orbitX_one_mul_orbitY_one σ a)

theorem even_diagram_fixed_three_free_posUnipotent_overgroups_le_borel
    (t : TwistTag)
    (K : Type) [Field K] [CharP K 2] (σ : K ≃+* K) {D : Subgroup (ModGL t.tag K)}
    (hDC : D ≤ graphFixedRootGroup t K σ.toRingHom)
    (hUD : graphFixedPosUnipotent t K σ.toRingHom ≤ D) (h3 : ¬ 3 ∣ Nat.card D) :
    D ≤ graphFixedRootBorel t K σ.toRingHom :=
  le_graphFixedRootBorel_of_orderOf_ne_three σ.surjective hDC hUD fun _ hg hg3 =>
    h3 (hg3 ▸ Subgroup.orderOf_dvd_natCard D hg)

end CFSG.Quasithin.SteinbergCD
