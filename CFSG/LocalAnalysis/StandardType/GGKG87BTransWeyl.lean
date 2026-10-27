module

public import CFSG.LocalAnalysis.StandardType.GGKG87BTransDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate13657
import all CFSG.LocalAnalysis.StandardType.GGKG87BTransWeylAux

public section

namespace CFSG.StandardType.KG87B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

theorem thirdWeyl_mem_adjointGroup
    (Ω : Type) [Field Ω] : thirdWeyl Ω ∈ adjointGroup Tag.E6 Ω :=
  canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω thirdCox

theorem commute_thirdWeyl_of_mem_blockGroup
    {Ω : Type} [Field Ω] [CharP Ω 2] {g : ModGL Tag.E6 Ω} (hg : g ∈ blockGroup Ω) :
    thirdWeyl Ω * g = g * thirdWeyl Ω := by
  have hle : blockGroup Ω ≤
      Subgroup.centralizer {canonicalRep (coxeterSystem Tag.E6) Ω thirdCox} := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω thirdCox hγ.1
    have hε1 : ε = 1 := by
      have h2 : (2 : Ω) = 0 := CharTwo.two_eq_zero
      have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    have h' := h c
    rw [hε1, one_mul, thirdCox_smul_of_eq_zero hγ.2.1 hγ.2.2] at h'
    calc pinnedX Tag.E6 Ω γ c * canonicalRep (coxeterSystem Tag.E6) Ω thirdCox
        = (canonicalRep (coxeterSystem Tag.E6) Ω thirdCox * pinnedX Tag.E6 Ω γ c *
            (canonicalRep (coxeterSystem Tag.E6) Ω thirdCox)⁻¹) *
          canonicalRep (coxeterSystem Tag.E6) Ω thirdCox := by rw [h']
      _ = canonicalRep (coxeterSystem Tag.E6) Ω thirdCox * pinnedX Tag.E6 Ω γ c := by group
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem thirdWeyl_conj_mem_thirdTorus
    {Ω : Type} [Field Ω] {s : ModGL Tag.E6 Ω} (hs : s ∈ thirdTorus Ω) :
    thirdWeyl Ω * s * (thirdWeyl Ω)⁻¹ ∈ thirdTorus Ω := by
  obtain ⟨a, h0, h2, h4, h5, rfl⟩ := hs
  have hfix : ∀ i : Fin Tag.E6.rank, i ≠ 1 → i ≠ 3 → wTuple thirdCox a i = a i := fun i h1 h3 => by
    rw [wTuple_apply, inv_smul_eq_iff.2 (thirdCox_smul_single h1 h3).symm, rootChar_single]
  exact ⟨wTuple thirdCox a, (hfix _ (by decide) (by decide)).trans h0,
    (hfix _ (by decide) (by decide)).trans h2, (hfix _ (by decide) (by decide)).trans h4,
    (hfix _ (by decide) (by decide)).trans h5, conj_rootDiagUnit thirdCox a⟩

theorem commute_of_mem_thirdTorus
    {Ω : Type} [Field Ω] {s x : ModGL Tag.E6 Ω} (hs : s ∈ thirdTorus Ω)
    (hx : x ∈ thirdTorus Ω ⊔ blockGroup Ω) : s * x = x * s := by
  obtain ⟨a, h0, h2, h4, h5, rfl⟩ := hs
  have hle : thirdTorus Ω ⊔ blockGroup Ω ≤ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    refine sup_le ?_ ?_
    · rintro _ ⟨b, -, -, -, -, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
        mul_comm]
    · refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hχ : rootChar a γ = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        by_cases h1 : i = 1
        · rw [h1, show γ 1 = 0 from hγ.2.1, zpow_zero]
        by_cases h3 : i = 3
        · rw [h3, show γ 3 = 0 from hγ.2.2, zpow_zero]
        rw [eq_one_of_shape h0 h2 h4 h5 h1 h3, one_zpow]
      have h := rootDiagUnit_conj_pinnedX a hγ.1 c
      rw [hχ, Units.val_one, one_mul] at h
      calc pinnedX Tag.E6 Ω γ c * rootDiagUnit Tag.E6 a
          = (rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω γ c * (rootDiagUnit Tag.E6 a)⁻¹) *
            rootDiagUnit Tag.E6 a := by rw [h]
        _ = rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω γ c := by group
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem commutator_thirdWeyl_mem_closure
    {Ω : Type} [Field Ω] [CharP Ω 2] {ω : Ωˣ} (hω : orderOf ω = 3) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ thirdTorus Ω ⊔ blockGroup Ω) (hx3 : x ^ 3 = 1) :
    thirdWeyl Ω * x * (thirdWeyl Ω)⁻¹ * x⁻¹ ∈ Subgroup.closure
      ({rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω),
        rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2))} : Set (ModGL Tag.E6 Ω)) := by
  set n := thirdWeyl Ω
  have hSN : thirdTorus Ω ≤ Subgroup.normalizer (blockGroup Ω : Set (ModGL Tag.E6 Ω)) :=
    le_trans (fun t ht => Subgroup.mem_centralizer_iff.2 fun g hg =>
      (commute_of_mem_thirdTorus ht (Subgroup.mem_sup_right hg)).symm)
      (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((thirdTorus Ω ⊔ blockGroup Ω : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω)) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSN] at hx'
  obtain ⟨t, ht, g, hg, rfl⟩ := hx'
  have htg' : t * g = g * t := commute_of_mem_thirdTorus ht (Subgroup.mem_sup_right hg)
  have htg : Commute t g := htg'
  have hng : n * g = g * n := commute_thirdWeyl_of_mem_blockGroup hg
  have hgn : g * n⁻¹ = n⁻¹ * g := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hng, ← mul_assoc, inv_mul_cancel, one_mul]
  have hc : n * (t * g) * n⁻¹ * (t * g)⁻¹ = n * t * n⁻¹ * t⁻¹ := by
    calc n * (t * g) * n⁻¹ * (t * g)⁻¹ = n * t * (g * n⁻¹) * g⁻¹ * t⁻¹ := by group
      _ = n * t * (n⁻¹ * g) * g⁻¹ * t⁻¹ := by rw [hgn]
      _ = n * t * n⁻¹ * t⁻¹ := by group
  rw [hc]
  have hu : n * t * n⁻¹ ∈ thirdTorus Ω := thirdWeyl_conj_mem_thirdTorus ht
  have ht3 : t ^ 3 ∈ blockGroup Ω := by
    have h := hx3
    rw [htg.mul_pow] at h
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem (pow_mem hg 3)
  have hnt3 : n * t ^ 3 * n⁻¹ = t ^ 3 := by
    rw [commute_thirdWeyl_of_mem_blockGroup ht3, mul_inv_cancel_right]
  have hut' : n * t * n⁻¹ * t⁻¹ = t⁻¹ * (n * t * n⁻¹) :=
    commute_of_mem_thirdTorus hu (Subgroup.mem_sup_left (inv_mem ht))
  have hut : Commute (n * t * n⁻¹) t⁻¹ := hut'
  have hcube : (n * t * n⁻¹ * t⁻¹) ^ 3 = 1 := by
    rw [hut.mul_pow, conj_pow, hnt3, inv_pow, mul_inv_cancel]
  obtain ⟨c, hc0, hc2, hc4, hc5, hceq⟩ := mul_mem hu (inv_mem ht)
  rw [hceq] at hcube ⊢
  have hc3 : c ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := Ω)
    rw [← rootDiagUnit_pow, hcube, rootDiagUnit_one]
  have hprim : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.iff_orderOf.2 hω
  have hroot : ∀ i, ∃ k : ℤ, ω ^ k = c i := fun i => by
    have hi : c i ∈ rootsOfUnity 3 Ω := by
      rw [mem_rootsOfUnity]
      exact congrFun hc3 i
    rw [← hprim.zpowers_eq] at hi
    exact Subgroup.mem_zpowers_iff.1 hi
  obtain ⟨m, hm⟩ := hroot 1
  obtain ⟨k, hk⟩ := hroot 3
  have hω3 : ω ^ 3 = 1 := hprim.pow_eq_one
  have h4k : (ω ^ 2) ^ (2 * k) = ω ^ k := by
    rw [← zpow_natCast, ← zpow_mul, show ((2 : ℕ) : ℤ) * (2 * k) = k + 3 * k by push_cast; ring,
      zpow_add, zpow_mul, show ω ^ (3 : ℤ) = 1 from (zpow_natCast ω 3).trans hω3, one_zpow,
      mul_one]
  have hcexp : c = Pi.mulSingle 1 ω ^ (m - 2 * k) *
      (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) ^ (2 * k) := by
    funext i
    simp only [Pi.mul_apply, Pi.pow_apply]
    by_cases h1 : i = 1
    · subst h1
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (1 : Fin Tag.E6.rank) ≠ 3),
        mul_one, ← zpow_add, sub_add_cancel]
      exact hm.symm
    by_cases h3 : i = 3
    · subst h3
      rw [Pi.mulSingle_eq_of_ne (by decide : (3 : Fin Tag.E6.rank) ≠ 1), Pi.mulSingle_eq_same,
        one_zpow, one_mul, one_mul, h4k]
      exact hk.symm
    rw [Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h3, one_zpow, mul_one, one_zpow, mul_one]
    exact eq_one_of_shape hc0 hc2 hc4 hc5 h1 h3
  have hsplit : rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω ^ (m - 2 * k) *
      (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) ^ (2 * k)) =
        rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω) ^ (m - 2 * k) *
          rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) ^ (2 * k) := by
    rw [rootDiagUnit_zpow, rootDiagUnit_zpow, ← rootDiagUnit_mul]
  rw [hcexp, hsplit]
  exact mul_mem (zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
    (zpow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)

theorem thirdWeyl_conj_not_mem_zpowers
    {Ω : Type} [Field Ω] {ω : Ωˣ} (hω : orderOf ω = 3) :
    thirdWeyl Ω * rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω) * (thirdWeyl Ω)⁻¹ ∉
      Subgroup.zpowers (rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω)) := by
  rintro ⟨k, hk⟩
  have hk' : rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω ^ k) =
      rootDiagUnit Tag.E6 (wTuple thirdCox (Pi.mulSingle 1 ω)) := by
    rw [← rootDiagUnit_zpow, ← conj_rootDiagUnit]
    exact hk
  have h3 := congrFun (rootDiagUnit_injective hk') 3
  rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne (by decide : (3 : Fin Tag.E6.rank) ≠ 1), one_zpow,
    wTuple_apply, rootChar_mulSingle, thirdCox_inv_smul_coord, zpow_one] at h3
  rw [← h3, orderOf_one] at hω
  exact absurd hω (by decide)

theorem twistHom_thirdWeyl
    {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) :
    twistHom TwistTag.E6 Ω Fr (thirdWeyl Ω) = thirdWeyl Ω := by
  have h := twistHom_canonicalRep TwistTag.E6 Ω Fr thirdCox
  rw [weylTwist_thirdCox] at h
  exact h

theorem exists_inv_thirdTorus_commute_thirdWeyl
    (Ω : Type) [Field Ω] [CharP Ω 2] :
    ∃ ν ∈ adjointGroup Tag.E6 Ω, (∀ s ∈ thirdTorus Ω, ν * s * ν⁻¹ = s⁻¹) ∧
      ν * thirdWeyl Ω * ν⁻¹ = thirdWeyl Ω := by
  refine ⟨canonicalRep (coxeterSystem Tag.E6) Ω ((coxeterSystem Tag.E6).wordProd e6W0Word),
    canonicalRep_mem_adjointGroup _ Ω _, ?_, ?_⟩
  · rintro _ ⟨a, h0, h2, h4, h5, rfl⟩
    rw [conj_rootDiagUnit, rootDiagUnit_inv, wTuple_w0_of_shape h0 h2 h4 h5]
  · rw [mul_inv_eq_iff_eq_mul, thirdWeyl, ← canonicalRep_mul_two, ← canonicalRep_mul_two,
      w0_mul_thirdCox]

end CFSG.StandardType.KG87B

end
