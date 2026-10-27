module

public import CFSG.RankThree.PartOne.K133H.D4Plane
import CFSG.RankThree.PartOne.Q1327T.Item7D4W
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
public import CFSG.RankThree.PartOne.K133H.TorusImage

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane

namespace Res417Eight

theorem g2FoldRoots_not_three_dvd : ∀ μ ∈ g2FoldRoots, μ.1 % 3 ≠ 0 ∨ μ.2 % 3 ≠ 0 := by
  decide

theorem weylCands_three : ∀ P ∈ weylCands, (P.1.1 - 1) % 3 = 0 → P.1.2 % 3 = 0 →
    P.2.1 % 3 = 0 → (P.2.2 - 1) % 3 = 0 → P = ((1, 0), (0, 1)) := by
  decide

theorem emod_three_eq_zero {x : ℤ} (h : ((3 : ℕ) : ℤ) ∣ x) : x % 3 = 0 :=
  Int.emod_eq_zero_of_dvd (by exact_mod_cast h)

section Certs


variable {K : Type} [Field K]

theorem rootCharKernel_outer_inter_middle_three {z : Kˣ} (hz : orderOf z = 3) :
    rootCharKernel (outerTuple z) ∩ rootCharKernel (middleTuple z) = ∅ := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h₁ h₂
  rw [mem_rootCharKernel_iff rfl rfl rfl rfl] at h₁ h₂
  obtain ⟨hdv1, hdv2⟩ := dvd_of_foldChar_eq_one hz h₁.2 h₂.2
  rcases g2FoldRoots_not_three_dvd _ (fold_mem_of_isRoot h₁.1) with h | h
  · exact h (emod_three_eq_zero hdv1)
  · exact h (emod_three_eq_zero hdv2)

theorem eq_one_of_mem_rootCharStabilizer_three {z : Kˣ} (hz : orderOf z = 3)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (h₁ : w ∈ rootCharStabilizer (outerTuple z)) (h₂ : w ∈ rootCharStabilizer (middleTuple z)) :
    w = 1 := by
  have hx₁ : foldChar (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) ((foldPair w).1 - (1, 0)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (2 : ℤ)) (B := z ^ (-3 : ℤ)) rfl rfl rfl rfl h₁ i0
    rwa [fold_single0] at h
  have hy₁ : foldChar (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) ((foldPair w).2 - (0, 1)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (2 : ℤ)) (B := z ^ (-3 : ℤ)) rfl rfl rfl rfl h₁ i2
    rwa [fold_single2] at h
  have hx₂ : foldChar (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) ((foldPair w).1 - (1, 0)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (-1 : ℤ)) (B := z ^ (2 : ℤ)) rfl rfl rfl rfl h₂ i0
    rwa [fold_single0] at h
  have hy₂ : foldChar (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) ((foldPair w).2 - (0, 1)) = 1 := by
    have h := foldChar_foldPair_sub (A := z ^ (-1 : ℤ)) (B := z ^ (2 : ℤ)) rfl rfl rfl rfl h₂ i2
    rwa [fold_single2] at h
  obtain ⟨hX1, hX2⟩ := dvd_of_foldChar_eq_one hz hx₁ hx₂
  obtain ⟨hY1, hY2⟩ := dvd_of_foldChar_eq_one hz hy₁ hy₂
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hX1 hX2 hY1 hY2
  exact eq_one_of_foldPair hw (weylCands_three _ (foldPair_mem hw) (emod_three_eq_zero hX1)
    (emod_three_eq_zero hX2) (emod_three_eq_zero hY1) (emod_three_eq_zero hY2))

theorem exists_rootDiagUnit_mem_d4Torsion_three [Finite K] (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    (h3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1) :
    ∃ z : Kˣ, orderOf z = 3 ∧
      rootDiagUnit TwistTag.D4.tag (outerTuple z) ∈ K133H.d4Torsion σ.toRingHom 3 ∧
      rootDiagUnit TwistTag.D4.tag (middleTuple z) ∈ K133H.d4Torsion σ.toRingHom 3 := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have : Finite (trialityFixedField K σ.toRingHom) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [Nat.card_units]
    exact h3
  have hFinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hzo : orderOf (trialityFixedUnit K σ ζ₀) = 3 := by
    rw [orderOf_injective _ hFinj ζ₀, hζ₀]
  have hσz₀ := units_map_trialityFixedUnit (σ := σ) ζ₀
  have hx₁ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ₀ ^ (1 : ℤ)) *
      trialityMiddleTorus K σ (ζ₀ ^ (0 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (outerTuple (trialityFixedUnit K σ ζ₀)) := by
    simp only [trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, hσz₀, one_pow,
      inv_one, mul_one]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  have hx₂ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ₀ ^ (0 : ℤ)) *
      trialityMiddleTorus K σ (ζ₀ ^ (1 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (middleTuple (trialityFixedUnit K σ ζ₀)) := by
    simp only [trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, one_pow, inv_one,
      mul_one, one_mul]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  have hmem : ∀ (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ), a ^ 3 = 1 → b ^ 3 = 1 →
      trialityOuterTorus K σ a * trialityMiddleTorus K σ b ∈ K133H.d4Torsion σ.toRingHom 3 := by
    intro a b ha hb
    rw [← he]
    refine ⟨(e (a, b)).2, ?_⟩
    have h1 : e (a, b) ^ 3 = 1 := by
      rw [← map_pow, Prod.pow_mk, ha, hb]
      exact map_one e
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hz3 : trialityFixedUnit K σ ζ₀ ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hζ3 : ζ₀ ^ 3 = 1 := by rw [← hζ₀]; exact pow_orderOf_eq_one _
  refine ⟨trialityFixedUnit K σ ζ₀, hzo, ?_, ?_⟩
  · rw [← hx₁]
    exact hmem _ _ (by rw [zpow_one]; exact hz3) (by rw [zpow_zero, one_pow])
  · rw [← hx₂]
    exact hmem _ _ (by rw [zpow_zero, one_pow]) (by rw [zpow_one]; exact hζ3)

theorem nonempty_torusImage_d4Torsion_three_mulEquiv [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ ^ 3 = 1) (h3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1) :
    Nonempty (torusImage ((K133H.d4Torsion σ.toRingHom 3).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊤ ≃* DihedralGroup 6) := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
  set V := K133H.d4Torsion σ.toRingHom 3 with hV
  set T := V.subgroupOf C with hT
  have hmemT : ∀ x : C, x ∈ T ↔ (x : ModGL TwistTag.D4.tag K) ∈ V := fun x =>
    Subgroup.mem_subgroupOf
  have hHT : H ≤ torusGroup TwistTag.D4.tag K := fun x hx =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  have hVH : V ≤ H := fun x hx => hx.1
  have hVT : V ≤ torusGroup TwistTag.D4.tag K := hVH.trans hHT
  have hVC : V ≤ C := hVH.trans (graphFixedRootTorus_le _ _ _)
  obtain ⟨z, hz, hd₁V, hd₂V⟩ := exists_rootDiagUnit_mem_d4Torsion_three σ hσ3 h3
  have hdisj := rootCharKernel_outer_inter_middle_three hz
  have hHN : H ≤ graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial _ _ _)
  have hnV : ∀ w ∈ relWeylTwist TwistTag.D4, ∀ x ∈ V,
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ ∈ V := by
    intro w hw x hx
    have hn := canonicalRep_mem_graphFixedRootMonomial TwistTag.D4 K σ.toRingHom hw
    refine ⟨?_, ?_⟩
    · have h := (graphFixedRootTorus_subgroupOf_normal TwistTag.D4 K σ.toRingHom).conj_mem
        ⟨x, hHN (hVH hx)⟩ (Subgroup.mem_subgroupOf.2 (hVH hx)) ⟨_, hn⟩
      exact Subgroup.mem_subgroupOf.1 h
    · rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  set ρ : WeylGroup TwistTag.D4.tag →* ModGL TwistTag.D4.tag K :=
    { toFun := canonicalRep (coxeterSystem TwistTag.D4.tag) K
      map_one' := canonicalRep_one _ _
      map_mul' := Q1327T.canonicalRep_mul_charTwo } with hρ
  have hρapp : ∀ w, ρ w = canonicalRep (coxeterSystem TwistTag.D4.tag) K w := fun w => rfl
  set ι₀ : relWeylTwist TwistTag.D4 →* C :=
    (ρ.comp (relWeylTwist TwistTag.D4).subtype).codRestrict C
      (fun w => canonicalRep_mem_graphFixedRootGroup w.2) with hι₀def
  have hι₀ : ∀ w, ((ι₀ w : C) : ModGL TwistTag.D4.tag K) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w := fun w => rfl
  have hN : ∀ w, ι₀ w ∈ Subgroup.normalizer (T : Set C) := by
    intro w
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemT, hmemT]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hι₀]
    refine ⟨hnV w w.2 x, fun hx => ?_⟩
    have h1 := hnV (w : WeylGroup TwistTag.D4.tag)⁻¹ (inv_mem w.2) _ hx
    have e : canonicalRep (coxeterSystem TwistTag.D4.tag) K (w : WeylGroup TwistTag.D4.tag)⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ := by
      rw [← hρapp, ← hρapp, map_inv]
    rw [e, inv_inv] at h1
    have e2 : (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * (x : ModGL TwistTag.D4.tag K) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K w = x := by group
    rwa [e2] at h1
  set ι : relWeylTwist TwistTag.D4 →* Subgroup.normalizer (T : Set C) :=
    ι₀.codRestrict _ hN with hιdef
  set Ψ : relWeylTwist TwistTag.D4 →* MulAut T := T.normalizerMonoidHom.comp ι with hΨdef
  have hΨapp : ∀ w (t : T), (((Ψ w t : T) : C) : ModGL TwistTag.D4.tag K) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * t *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ := fun w t => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hfix : ∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = x := by
      intro x hx
      have h1 := congrArg (fun φ : MulAut T =>
        (((φ ⟨⟨x, hVC hx⟩, (hmemT _).mpr hx⟩ : T) : C) : ModGL TwistTag.D4.tag K)) hw
      simp only [MulAut.one_apply] at h1
      rw [hΨapp] at h1
      exact h1
    have hstab : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ, rootDiagUnit TwistTag.D4.tag a ∈ V →
        (w : WeylGroup TwistTag.D4.tag) ∈ rootCharStabilizer a := fun a ha => by
      refine (conj_canonicalRep_eq_iff a _).1 ?_
      have h := hfix _ ha
      calc rootDiagUnit TwistTag.D4.tag a * canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            (rootDiagUnit TwistTag.D4.tag a)⁻¹
          = (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootDiagUnit TwistTag.D4.tag a *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) *
            canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            (rootDiagUnit TwistTag.D4.tag a)⁻¹ := by rw [h]
        _ = canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by group
    have hw1 := eq_one_of_mem_rootCharStabilizer_three hz w.2 (hstab _ hd₁V) (hstab _ hd₂V)
    rw [Subgroup.mem_bot]
    exact Subtype.ext hw1
  have hrange : Ψ.range = torusImage T ⊤ := by
    ext φ'
    rw [K133H.mem_torusImage_iff]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨ι₀ w, hN w, Subgroup.mem_top _, rfl⟩
    · rintro ⟨n, hn, -, rfl⟩
      have hnV' : (n : ModGL TwistTag.D4.tag K) ∈
          Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)) := by
        refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
        · have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hVC hx⟩).mp ((hmemT _).mpr hx)
          rw [hmemT] at h1
          simpa using h1
        · have hyC : (n : ModGL TwistTag.D4.tag K) * x * (n : ModGL TwistTag.D4.tag K)⁻¹ ∈ C :=
            hVC hx
          have hxC : x ∈ C := by
            have : x = (n : ModGL TwistTag.D4.tag K)⁻¹ *
                ((n : ModGL TwistTag.D4.tag K) * x * (n : ModGL TwistTag.D4.tag K)⁻¹) *
                (n : ModGL TwistTag.D4.tag K) := by group
            rw [this]
            exact mul_mem (mul_mem (inv_mem n.2) hyC) n.2
          have h1 : n * ⟨x, hxC⟩ * n⁻¹ ∈ T := by
            rw [hmemT]
            simpa using hx
          exact (hmemT _).mp ((Subgroup.mem_normalizer_iff.mp hn ⟨x, hxC⟩).mpr h1)
      obtain ⟨h, hh, w, hw, hnw⟩ :=
        exists_eq_mul_canonicalRep_of_mem_normalizer σ hdisj hVT hd₁V hd₂V n.2 hnV'
      refine ⟨⟨w, hw⟩, MulEquiv.ext fun t => Subtype.ext (Subtype.ext ?_)⟩
      rw [hΨapp]
      change _ = (n : ModGL TwistTag.D4.tag K) * ((t : C) : ModGL TwistTag.D4.tag K) *
        (n : ModGL TwistTag.D4.tag K)⁻¹
      have htV : ((t : C) : ModGL TwistTag.D4.tag K) ∈ V := (hmemT _).mp t.2
      have hsV := hnV w hw _ htV
      rw [hnw]
      calc canonicalRep (coxeterSystem TwistTag.D4.tag) K w * ((t : C) : ModGL TwistTag.D4.tag K) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
          h * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
            ((t : C) : ModGL TwistTag.D4.tag K) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) * h⁻¹ := by
            rw [mul_comm_of_mem_torusGroup' (hHT hh) (hVT hsV), mul_inv_cancel_right]
        _ = _ := by group
  have e₁ : relWeylTwist TwistTag.D4 ≃* WeylGroup Tag.G2 := foldedWeylEquiv TwistTag.D4
  obtain ⟨e₂⟩ := Res417Seven.nonempty_weylGroup_G2_mulEquiv_dihedral (K := K)
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hΨinj).symm).trans
    (e₁.trans e₂)⟩

end Certs

end Res417Eight

end CFSG.RankThree.PartTwo.Sec4
