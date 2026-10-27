module

public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularSL3
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity

public noncomputable section

namespace CFSG.RankThree.Chevalley

variable {G : Type*} [Group G]

theorem zpow_mem_of_pow_mem_mul {H T : Subgroup G} (hTH : T ≤ H)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (B : G →* G) (hBH : ∀ x ∈ H, B x ∈ H)
    (hBT : ∀ x ∈ T, B x ∈ T) (q : ℕ) (ε : ℤ)
    (hquad : ∀ x ∈ H, B (B x) * B x ^ ε * x = 1) {t s : G} (ht : t ∈ H) (hs : s ∈ T)
    (hfix : B t ^ q = t * s) : t ^ ((q : ℤ) ^ 2 + ε * q + 1) ∈ T := by
  let _ : CommGroup H := { (inferInstance : Group H) with
    mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let BH : H →* H := (B.comp H.subtype).codRestrict H fun x => hBH x x.2
  have hBH_apply : ∀ x : H, (BH x : G) = B x := fun _ => rfl
  set x : H := ⟨t, ht⟩ with hx
  set y : H := ⟨s, hTH hs⟩ with hy
  have h1 : BH (BH x) * BH x ^ ε * x = 1 := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hBH_apply, Subgroup.coe_one]
    exact hquad t ht)
  have h2 : BH x ^ q = x * y := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, hBH_apply]
    exact hfix)
  have h3 : BH (BH x) ^ q = BH x * BH y := by rw [← map_pow, h2, map_mul]
  have E1 : Additive.ofMul (BH (BH x)) + ε • Additive.ofMul (BH x) + Additive.ofMul x = 0 := by
    have := congrArg Additive.ofMul h1
    rwa [ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_one] at this
  have E2 : (q : ℤ) • Additive.ofMul (BH x) = Additive.ofMul x + Additive.ofMul y := by
    have := congrArg Additive.ofMul h2
    rwa [ofMul_pow, ofMul_mul, ← natCast_zsmul] at this
  have E3 : (q : ℤ) • Additive.ofMul (BH (BH x)) =
      Additive.ofMul (BH x) + Additive.ofMul (BH y) := by
    have := congrArg Additive.ofMul h3
    rwa [ofMul_pow, ofMul_mul, ← natCast_zsmul] at this
  have E : ((q : ℤ) ^ 2 + ε * q + 1) • Additive.ofMul x =
      (-(1 + ε * q)) • Additive.ofMul y + (-(q : ℤ)) • Additive.ofMul (BH y) := by
    linear_combination (norm := module) ((q : ℤ) ^ 2) • E1 - (q : ℤ) • E3 - (ε * q + 1) • E2
  have hxy : x ^ ((q : ℤ) ^ 2 + ε * q + 1) = y ^ (-(1 + ε * q)) * BH y ^ (-(q : ℤ)) :=
    Additive.ofMul.injective (by rw [ofMul_zpow, ofMul_mul, ofMul_zpow, ofMul_zpow, E])
  have hcoe := congrArg Subtype.val hxy
  simp only [Subgroup.coe_zpow, Subgroup.coe_mul, hBH_apply] at hcoe
  rw [show t = (x : G) from rfl, hcoe]
  exact mul_mem (zpow_mem hs _) (zpow_mem (hBT s hs) _)

theorem exists_mul_pow_eq {N : Subgroup G} {t u : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hu : u ∈ N) (n : ℕ) :
    ∃ u' ∈ N, (t * u) ^ n = t ^ n * u' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨u', hu', h⟩ := ih
    refine ⟨t⁻¹ * u' * t * u, mul_mem ?_ hu, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) u').1 hu'
      simpa using this
    · rw [pow_succ, h, pow_succ]
      group

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Matrix Pointwise

variable {Ω : Type} [Field Ω]

theorem tsM_mem_normalizer_torusGroup :
    tsM Ω ∈ Subgroup.normalizer (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) := by
  have hw : ∀ i : Fin Tag.D4.rank,
      weylElt Tag.D4 Ω i 1 ∈ Subgroup.normalizer (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) :=
    fun i => by
      rw [← canonicalRep_simple (coxeterSystem Tag.D4) Ω i]
      exact canonicalRep_mem_normalizer _
  have hP : diagramMap TwistTag.D4 Ω ∈
      Subgroup.normalizer (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) :=
    mem_normalizer_of_map_eq (map_conj_diagramMap_torusGroup TwistTag.D4)
  exact mul_mem (mul_mem (hw 2) (hw 0)) hP

theorem rootChar_tuple_zpow {τ : Tag} (b : Fin τ.rank → Ωˣ) (n : ℤ) (l : Fin τ.rank → ℤ) :
    rootChar (b ^ n) l = rootChar b l ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem tuple_eq_one_of_rootChar {b : Fin Tag.D4.rank → Ωˣ}
    (h : ∀ μ : Fin Tag.D4.rank → ℤ, rootChar b μ = 1) : b = 1 :=
  funext fun i => by rw [← rootChar_single_D4 b i, h, Pi.one_apply]

theorem tsM_conj_quad
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {t : ModGL Tag.D4 Ω}
    (ht : t ∈ torusGroup Tag.D4 Ω) :
    (MulAut.conj (tsM Ω ^ threeSixExp ε)).toMonoidHom
        ((MulAut.conj (tsM Ω ^ threeSixExp ε)).toMonoidHom t) *
      (MulAut.conj (tsM Ω ^ threeSixExp ε)).toMonoidHom t ^ ε * t = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set k := threeSixExp ε
  set ψ : (Fin Tag.D4.rank → Ωˣ) → (Fin Tag.D4.rank → Ωˣ) := fun b => trialityPsi^[k] b
    with hψ
  have hB : ∀ b : Fin Tag.D4.rank → Ωˣ,
      (MulAut.conj (tsM Ω ^ k)).toMonoidHom (rootDiagUnit Tag.D4 b) =
        rootDiagUnit Tag.D4 (ψ b) := fun b =>
    trialityM_pow_conj_rootDiagUnit k b
  have hχ : ∀ (b : Fin Tag.D4.rank → Ωˣ) (l : Fin Tag.D4.rank → ℤ),
      rootChar (ψ b) (tsW ε *ᵥ l) = rootChar b l := fun b l =>
    rootChar_trialityPsi_iterate k b l
  have h3 := threeSixW_mul_mul hε
  have h2 := threeSixW_mul_add hε
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hμ : ∀ μ : Fin Tag.D4.rank → ℤ, tsW ε *ᵥ (tsW ε *ᵥ (ε • (tsW ε *ᵥ μ))) = μ := fun μ => by
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3,
      Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, hε2, one_smul]
  have hzero : ∀ l : Fin Tag.D4.rank → ℤ, l + ε • (tsW ε *ᵥ l) + tsW ε *ᵥ (tsW ε *ᵥ l) = 0 :=
    fun l => by
      have := congrArg (fun A : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ => A *ᵥ l) h2
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
        ← Matrix.mulVec_mulVec] at this
      rw [← this]
      abel
  have hc : ψ (ψ a) * ψ a ^ ε * a = 1 := by
    refine tuple_eq_one_of_rootChar fun μ => ?_
    rw [rootChar_mul_tuple, rootChar_mul_tuple, rootChar_tuple_zpow, ← hμ μ, hχ, hχ, hχ,
      ← rootChar_zsmul, ← rootChar_add, ← rootChar_add, hzero, rootChar_zero]
  have e : ∀ b : Fin Tag.D4.rank → Ωˣ, rootDiagUnitHom Tag.D4 Ω b = rootDiagUnit Tag.D4 b :=
    fun _ => rfl
  have h := congrArg (rootDiagUnitHom Tag.D4 Ω) hc
  rw [map_mul, map_mul, map_zpow, e, e, e, map_one] at h
  rw [hB, hB]
  exact h

theorem pow_mem_d4A2Qv_of_fixed
    (Fr : Ω →+* Ω) (hFrs : Function.Surjective Fr) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma)
    {d : ℕ} (hd : (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) {y : ModGL Tag.D4 Ω}
    (hy : y ∈ (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω v : Set (ModGL Tag.D4 Ω)))
    (hyF : tsFrob Ω Fr ε y = y) : y ^ d ∈ d4A2Qv Ω v := by
  obtain ⟨t, ht, u, hu, rfl⟩ := hy
  set B := (MulAut.conj (tsM Ω ^ threeSixExp ε)).toMonoidHom with hBdef
  have hinf := d4A2Qv_inf_torusGroup (K := Ω) v
  have hTH : d4A2Tv Ω v ≤ torusGroup Tag.D4 Ω := hinf ▸ inf_le_right
  have hTQ : d4A2Tv Ω v ≤ d4A2Qv Ω v := hinf ▸ inf_le_left
  have hBH : ∀ x ∈ torusGroup Tag.D4 Ω, B x ∈ torusGroup Tag.D4 Ω := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (pow_mem tsM_mem_normalizer_torusGroup _) x).1 hx
  have hBmap : (d4A2Qv Ω v).map B = d4A2Qv Ω v := by
    have h := map_conj_tsM_pow_rootSpan (Ω := Ω) ε
      (S := ((fun β => v • β) '' d4A2Sigma : Set (Fin Tag.D4.rank → ℤ)))
      fun α hα => isRoot_of_mem_image_d4A2Sigma hα
    rw [image_threeSixW_eq hε v hstab] at h
    rw [d4A2Qv_eq_rootSpan]
    exact h
  have hBQ : ∀ x ∈ d4A2Qv Ω v, B x ∈ d4A2Qv Ω v := fun x hx => hBmap.le ⟨x, hx, rfl⟩
  have hBT : ∀ x ∈ d4A2Tv Ω v, B x ∈ d4A2Tv Ω v := fun x hx => by
    rw [← hinf] at hx ⊢
    exact Subgroup.mem_inf.2 ⟨hBQ x (Subgroup.mem_inf.1 hx).1, hBH x (Subgroup.mem_inf.1 hx).2⟩
  have hFt : tsFrob Ω Fr ε t = B t ^ q := by
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [tsFrob_eq_conj, entrywise_frob_rootDiagUnit Fr hFr, ← rootDiagUnit_pow, hBdef,
      MulEquiv.coe_toMonoidHom, ← map_pow, MulAut.conj_apply]
  have hFQ := (map_threeSixFrob_d4A2Qv Fr hFrs hε v hstab).le
  have hs : t⁻¹ * tsFrob Ω Fr ε t ∈ d4A2Tv Ω v := by
    rw [← hinf]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem ht) (hFt ▸ pow_mem (hBH t ht) q)⟩
    have h1 : t⁻¹ * tsFrob Ω Fr ε t = u * (tsFrob Ω Fr ε u)⁻¹ := by
      have h2 : tsFrob Ω Fr ε t * tsFrob Ω Fr ε u = t * u := by rw [← map_mul, hyF]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2]
      group
    rw [h1]
    exact mul_mem hu (inv_mem (hFQ ⟨u, hu, rfl⟩))
  have hfix : B t ^ q = t * (t⁻¹ * tsFrob Ω Fr ε t) := by rw [mul_inv_cancel_left, hFt]
  have htd := zpow_mem_of_pow_mem_mul hTH (fun x hx y hy => torusGroup_mul_comm hx hy) B hBH hBT
    q ε (fun x hx => tsM_conj_quad hε hx) ht hs hfix
  rw [← hd, zpow_natCast] at htd
  obtain ⟨u', hu', he⟩ := exists_mul_pow_eq (torusGroup_le_normalizer_d4A2Qv v ht) hu d
  rw [he]
  exact mul_mem (hTQ htd) hu'

end D4

end CFSG.RankThree.Chevalley
