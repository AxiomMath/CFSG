module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Alg
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Act
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec21.Item219LieProof
open scoped Matrix MatrixGroups Pointwise commutatorElement

section Linear


variable {X : Type} [Field X] [Finite X]

theorem layerSub_conj_mem (σ : X ≃+* X) (x : C0 σ) {g d : C0 σ} (hg : g ∈ cenX σ x)
    (hd : d ∈ layerSub σ x) : g * d * g⁻¹ ∈ layerSub σ x := by
  have hle : layerSub σ x ≤ (layerSub σ x).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    show (MulAut.conj g) ⁅a, b⁆ ∈ layerSub σ x
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      ((cenX σ x).mul_mem ((cenX σ x).mul_mem hg ha) ((cenX σ x).inv_mem hg))
      ((cenX σ x).mul_mem ((cenX σ x).mul_mem hg hb) ((cenX σ x).inv_mem hg))
  have := hle hd
  rwa [Subgroup.mem_comap] at this

set_option maxHeartbeats 400000 in
theorem layer_embedding_of_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (σ : X ≃+* X) (hK : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra X Ω] [IsAlgClosure X Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ}
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : C0 σ)
    (hx : threeSixEmb X Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹)
    (hε : ε = 1 ∨ ε = -1) (hFrs : Function.Surjective Fr)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma, tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma)
    (hD : layerSub σ x = threeSixSingularR Ω X σ Fr ε v g) :
    ∃ s : layerSub σ x →* Matrix.SpecialLinearGroup (Fin 3) Ω, Function.Injective s ∧
      (∀ X' : Matrix.SpecialLinearGroup (Fin 3) Ω, X' ∈ s.range ↔
        X' ∈ CFSG.RankThree.Classical2.fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) ∧
      ∀ y ∈ cenX σ x, ∃ N : GL (Fin 3) Ω, ∀ d d' : layerSub σ x,
        (d' : C0 σ) = y * d * y⁻¹ → Matrix.SpecialLinearGroup.toGL (s d') =
          N * Matrix.SpecialLinearGroup.toGL (s d) * N⁻¹ := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed X
  have : CharP Ω ℓ := charP_of_card_cube (K := X) hℓ hf hK
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω ℓ]
    exact hℓ3
  obtain ⟨-, hset, hQM, -, -, -, -, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK a hord v hv.symm
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω := fun u hu =>
    (Subgroup.mem_inf.1 (hQM hu)).1
  have hR := threeSixSingularR_eq_comap hrange hgG hFg v
  have hC := CFSG.RankThree.Chevalley.centralizer_eq_comap hrange hgG hFg hx
  have hDQ : ∀ d : layerSub σ x, threeSixEmb' Ω X σ g (d : C0 σ) ∈ tsQv Ω v := by
    intro d
    have h1 : (d : C0 σ) ∈ threeSixSingularR Ω X σ Fr ε v g := by
      rw [← hD]
      exact d.2
    rw [hR, Subgroup.mem_comap] at h1
    exact h1
  let ιD : layerSub σ x →* ModGL TwistTag.D4.tag Ω :=
    (threeSixEmb' Ω X σ g).comp (layerSub σ x).subtype
  let s : layerSub σ x →* Matrix.SpecialLinearGroup (Fin 3) Ω :=
    (tsQvEquiv v).toMonoidHom.comp (ιD.codRestrict (tsQv Ω v) hDQ)
  have hs : Function.Injective s := by
    intro d d' h
    have h1 := (tsQvEquiv v).injective h
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext (threeSixEmb'_injective g h2)
  have hΦfix : ∀ X' : Matrix.SpecialLinearGroup (Fin 3) Ω, X' ∈ s.range ↔
      X' ∈ CFSG.RankThree.Classical2.fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab) := by
    intro X'
    rw [mem_fixSubgroup_threeSixPhi Fr hFrs hε v hstab X']
    constructor
    · rintro ⟨d, rfl⟩
      have hfix := ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨(d : C0 σ), rfl⟩).2
      have h2 : (d4A2QvEquiv v).symm (s d) = ⟨threeSixEmb' Ω X σ g d, hDQ d⟩ :=
        (d4A2QvEquiv v).symm_apply_apply _
      rw [h2]
      exact hfix
    · intro hfixed
      set y1 := (d4A2QvEquiv v).symm X' with hy1
      have hy1G : y1.1 ∈ adjointGroup TwistTag.D4.tag Ω := hQG y1.2
      obtain ⟨y0, hy0⟩ := (mem_range_threeSixEmb' hrange hgG hFg _).2 ⟨hy1G, hfixed⟩
      have hy0R : y0 ∈ threeSixSingularR Ω X σ Fr ε v g := by
        rw [hR, Subgroup.mem_comap, hy0]
        exact y1.2
      have hy0D : y0 ∈ layerSub σ x := by
        rw [hD]
        exact hy0R
      refine ⟨⟨y0, hy0D⟩, ?_⟩
      have h3 : (⟨threeSixEmb' Ω X σ g y0, hDQ ⟨y0, hy0D⟩⟩ : d4A2Qv Ω v) = y1 := Subtype.ext hy0
      change d4A2QvEquiv v ⟨threeSixEmb' Ω X σ g y0, hDQ ⟨y0, hy0D⟩⟩ = X'
      rw [h3, hy1]
      exact (d4A2QvEquiv v).apply_symm_apply X'
  refine ⟨s, hs, hΦfix, ?_⟩
  intro y hy
  have hy' : threeSixEmb' Ω X σ g y ∈ toralCentralizer TwistTag.D4.tag Ω a := by
    have h1 : y ∈ Subgroup.centralizer ({x} : Set (C0 σ)) := hy
    rw [hC, Subgroup.mem_comap] at h1
    exact h1
  have hm : threeSixEmb' Ω X σ g y ∈
      (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω v : Set (ModGL Tag.D4 Ω)) := by
    rw [← hset]
    exact hy'
  obtain ⟨N, hN⟩ := action_of_prod_Qv v hm
  refine ⟨N, fun d d' hdd' => ?_⟩
  exact hN ⟨_, hDQ d⟩ ⟨_, hDQ d'⟩ (by
    show threeSixEmb' Ω X σ g (d' : C0 σ) = threeSixEmb' Ω X σ g y *
      threeSixEmb' Ω X σ g (d : C0 σ) * (threeSixEmb' Ω X σ g y)⁻¹
    rw [hdd', map_mul, map_mul, map_inv])

set_option maxHeartbeats 400000 in
theorem layerLinearModel_of_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq4 : 4 ≤ ℓ ^ f) (hq3 : 3 ∣ ℓ ^ f - 1)
    (σ : X ≃+* X) (hK : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra X Ω] [IsAlgClosure X Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω 1) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr 1)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : C0 σ)
    (hx : threeSixEmb X Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    LayerLinearModel σ x := by
  classical
  have hε : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed X
  have : CharP Ω ℓ := charP_of_card_cube (K := X) hℓ hf hK
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hstab := threeSix_stab hFr hε ha hv
  have hD := (threeSix_split_model hℓ hℓ3 hf X hK σ hσ Ω Fr hFr g hgG hFg a ha hord v hv x hx).1
  obtain ⟨s, hs, hΦfix, hact⟩ := layer_embedding_of_model hℓ hℓ3 hf σ hK hσ Ω Fr hFr g hgG hFg a
    hord v hv x hx hε hFrs hstab hD
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  have h₁ := natCard_eqLocusField_frob (Ω := Ω) hℓ hf hFr
  haveI := hcl
  set k₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id X) with hk₀
  obtain ⟨π, b, hb⟩ := threeSix_phi_split Fr hFrs v hstab
  obtain ⟨-, ⟨H₀, hH₀⟩, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split (k := k₀) hℓ hf h₀ π
      (threeSixPhi Ω Fr hFrs (Or.inl rfl) v hstab) b
      (fun i j hij t => by rw [hb i j hij t, hFr])
  have hrangeS : ∀ X' : Matrix.SpecialLinearGroup (Fin 3) Ω,
      X' ∈ s.range ↔ X' ∈ (conjMapSL (k := k₀) H₀).range := by
    intro X'
    rw [hΦfix X', hH₀ X', MonoidHom.mem_range]
    constructor
    · rintro ⟨Y, hY⟩
      exact ⟨Y, by rw [conjMapSL_apply]; exact hY.symm⟩
    · rintro ⟨Y, hY⟩
      exact ⟨Y, by rw [← conjMapSL_apply]; exact hY.symm⟩
  have hfix : ∀ z : Ω, Fr z = z → ∃ c : k₀, algebraMap k₀ Ω c = z := by
    intro z hz
    have hz' : z ∈ RingHom.eqLocusField Fr (RingHom.id Ω) := by
      rw [RingHom.mem_eqLocusField]
      exact hz
    obtain ⟨c, hc⟩ := (threeSixFieldEquiv hσ hFr h₀ h₁ hq0).surjective ⟨z, hz'⟩
    refine ⟨c, ?_⟩
    have h2 := congrArg Subtype.val hc
    rw [coe_threeSixFieldEquiv] at h2
    exact h2
  have hk : ∀ c : k₀, Fr (algebraMap k₀ Ω c) = algebraMap k₀ Ω c := by
    intro c
    exact (threeSixFieldHom hσ hFr c).2
  obtain ⟨e, he⟩ := linear_layer_model_of_interface (layerSub σ x) (cenX σ x)
    (fun g hg d hd => layerSub_conj_mem σ x hg hd) (k := k₀) (Ω := Ω) (q := ℓ ^ f)
    (by omega) Fr hFr hk hfix s hs H₀ hrangeS hact
  exact ⟨↥k₀, inferInstance, inferInstance, by rw [h₀]; exact hq4, by rw [h₀]; exact hq3, e, he⟩

end Linear

end CFSG.RankThree.PartTwo.Sec4.E27
