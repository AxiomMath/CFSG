module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Toral
public import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Even
public import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Plane
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS167D4Model

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec4.Res417Seven CFSG.RankThree.PartTwo.Sec4.Res417Eight
  CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane

variable {K : Type} [Field K] [Finite K]

private theorem d4Tuple_map_units (f : Kˣ →* Kˣ) (x₀ x₁ x₂ x₃ : Kˣ) :
    (fun i => f (d4Tuple x₀ x₁ x₂ x₃ i)) = d4Tuple (f x₀) (f x₁) (f x₂) (f x₃) := by
  funext i
  obtain ⟨k, hk⟩ := i
  have hk4 : k < 4 := hk
  interval_cases k <;> rfl

section Certs


section ExtraCerts


theorem eq_bot_of_le_normalizer_of_odd {X : Type} [Group X] {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n) {E T : Subgroup X}
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : 9 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set X)) : T = ⊥ := by
  by_contra hTne
  obtain ⟨K, _, _, _, σ, hK, -, hσ3, -, -, ⟨φ⟩⟩ :=
    exists_graphFixedRootGroup_of_trialityD4 hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set ψ : X →* ModGL TwistTag.D4.tag K := C.subtype.comp φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψC : ∀ x, ψ x ∈ C := fun x => (φ x).2
  have hT'1 : T.map ψ ≠ ⊥ := fun h =>
    hTne ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hT'C : T.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hE'C : E.map ψ ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hE'T' : E.map ψ ≤ Subgroup.normalizer ((T.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map ψ)
  have hE'3 : ∀ y ∈ E.map ψ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE3 x hx, map_one]
  have hE'p : IsPGroup 3 (E.map ψ) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE'3 _ y.2)⟩
  obtain ⟨x, -, J, hJ, hle⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 hE'C hE'p hT'C (hT.map ψ) hT'1 hE'T'
  have hcard := card_le_three_of_le_graphFixedParabolicLevi σ hσ3
    (not_three_dvd_card_units_of_odd hn hK) hJ hle (by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE'3 y hy, map_one])
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
    Subgroup.card_map_of_injective hψ] at hcard
  omega

end ExtraCerts

theorem mem_graphFixedRootTorus_of_commute_d4Torsion_three (σ : K ≃+* K)
    (hσ3 : σ ^ 3 = 1) (h3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1)
    {g : ModGL TwistTag.D4.tag K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgV : ∀ v ∈ K133H.d4Torsion σ.toRingHom 3, g * v = v * g) :
    g ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom
  set V := K133H.d4Torsion σ.toRingHom 3
  obtain ⟨z, hz, hd₁V, hd₂V⟩ := exists_rootDiagUnit_mem_d4Torsion_three σ hσ3 h3
  have hdisj := rootCharKernel_outer_inter_middle_three hz
  have hHT : H ≤ torusGroup TwistTag.D4.tag K := fun x hx =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  have hVH : V ≤ H := fun x hx => hx.1
  have hVT : V ≤ torusGroup TwistTag.D4.tag K := hVH.trans hHT
  have hfix : ∀ x ∈ V, g * x * g⁻¹ = x := by
    intro x hx
    rw [hgV x hx]
    group
  have hfix' : ∀ x ∈ V, g⁻¹ * x * g = x := by
    intro x hx
    have h : g * x = x * g := hgV x hx
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * x) := by rw [h]
      _ = x := by group
  have hgN : g ∈ Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hfix x hx]
      exact hx
    · intro hx
      have h := hfix' (g * x * g⁻¹) hx
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, h]
      exact hx
  obtain ⟨h, hh, w, hw, rfl⟩ :=
    exists_eq_mul_canonicalRep_of_mem_normalizer σ hdisj hVT hd₁V hd₂V hg hgN
  have hHcent : ∀ a ∈ H, ∀ x ∈ V, x * a = a * x := fun a ha x hx =>
    K133H.graphFixedRootTorus_comm σ.toRingHom (hVH hx) ha
  have hnw : ∀ x ∈ V, x * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x := by
    intro x hx
    have h1 : x * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) =
        h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x := (hgV x hx).symm
    have h2 : x * h = h * x := hHcent h hh x hx
    have h4 : h * (x * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) =
        h * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * x) := by
      rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
    exact mul_left_cancel h4
  have hstab : ∀ a : Fin TwistTag.D4.tag.rank → Kˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ V → w ∈ rootCharStabilizer a := by
    intro a ha
    refine (conj_canonicalRep_eq_iff a w).1 ?_
    rw [hnw _ ha, mul_inv_cancel_right]
  have hw1 : w = 1 :=
    eq_one_of_mem_rootCharStabilizer_three hz hw (hstab _ hd₁V) (hstab _ hd₂V)
  rw [hw1, canonicalRep_one, mul_one]
  exact hh

section ExtraCerts


theorem exists_map_conj_eq_d4Torsion_three {n : ℕ} (hev : Even n) (hn : 1 ≤ n) [CharP K 2]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσ3 : σ ^ 3 = 1)
    {F T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hF3 : ∀ x ∈ F, x ^ 3 = 1) (hF9 : Nat.card F = 9) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hFT : F ≤ Subgroup.normalizer (T : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      F.map (MulAut.conj g).toMonoidHom =
        (K133H.d4Torsion σ.toRingHom 3).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let V := K133H.d4Torsion σ.toRingHom 3
  have hF'C : F.map C.subtype ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hT'C : T.map C.subtype ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hT'1 : T.map C.subtype ≠ ⊥ := by
    intro h
    rw [eq_bot_iff] at h
    exact hT1 (eq_bot_iff.2 fun t ht => Subtype.ext (Subgroup.mem_bot.1 (h ⟨t, ht, rfl⟩)))
  have hFT' : F.map C.subtype ≤ Subgroup.normalizer
      ((T.map C.subtype : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map C.subtype)
  have hF'3 : ∀ y ∈ F.map C.subtype, y ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hF3 y hy, map_one]
  have hF'p : IsPGroup 3 (F.map C.subtype) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF'3 _ y.2)⟩
  obtain ⟨x, hxC, J, hJ, hle⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 (r := 2)
    (p := 3) (by norm_num) σ hσ3 hF'C hF'p hT'C (hT.map C.subtype) hT'1 hFT'
  obtain ⟨a, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ n) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have h3L : ∀ b, 3 ∣ Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) - 1 := fun b => by
    rw [card_orbitField_D4_orientation Nat.prime_two hn hK (Or.inl rfl) hσ' b]
    exact three_dvd_two_pow_pow_sub_one hev _
  obtain ⟨y, hyM, hyH⟩ := exists_conj_le_graphFixedRootTorus σ hσ3 a (h3L a)
    (hle.trans (graphFixedParabolicLevi_mono _ haJ)) (by
      rintro _ ⟨u, hu, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hF'3 u hu, map_one])
  have hyC : y ∈ C := (range_le_graphFixedParabolicLevi σ.toRingHom a hyM).2
  let g : C := ⟨y * x, mul_mem hyC hxC⟩
  have hgVle : ∀ d ∈ F, g * d * g⁻¹ ∈ V.subgroupOf C := by
    intro d hd
    rw [Subgroup.mem_subgroupOf]
    have hH : y * (x * (d : ModGL TwistTag.D4.tag K) * x⁻¹) * y⁻¹ ∈
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
      hyH ⟨x * (d : ModGL TwistTag.D4.tag K) * x⁻¹,
        ⟨(d : ModGL TwistTag.D4.tag K), ⟨d, hd, rfl⟩, rfl⟩, rfl⟩
    have hd3 : (d : ModGL TwistTag.D4.tag K) ^ 3 = 1 :=
      congrArg (fun z : C => (z : ModGL TwistTag.D4.tag K)) (hF3 d hd)
    have e : ((g * d * g⁻¹ : C) : ModGL TwistTag.D4.tag K) =
        y * (x * (d : ModGL TwistTag.D4.tag K) * x⁻¹) * y⁻¹ := by
      simp only [g, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      group
    rw [e]
    refine ⟨hH, ?_⟩
    rw [conj_pow, conj_pow, hd3, mul_one, mul_inv_cancel, mul_one, mul_inv_cancel]
  have hVel : CFSG.Assembly.IsElemAbelian 3 (V.subgroupOf C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · exact Subtype.ext (Subtype.ext (K133H.graphFixedRootTorus_comm σ.toRingHom
        (Subgroup.mem_subgroupOf.1 a.2).1 (Subgroup.mem_subgroupOf.1 b.2).1))
    · exact Subtype.ext (Subgroup.mem_subgroupOf.1 hz).2
  have hV9 : Nat.card (V.subgroupOf C) ≤ 9 :=
    Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hn hK hσ _ hVel
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro z hz
    obtain ⟨d, hd, rfl⟩ := hz
    exact hgVle d hd
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hF9]
    exact hV9

end ExtraCerts

theorem exists_fieldActor_fixed_mem_graphFixedRootTorus {n : ℕ} (hn : 3 ≤ n)
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσ3 : σ ^ 3 = 1) :
    ∃ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (s : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
      fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ≠ 1 ∧ Nat.Coprime (orderOf s) 3 ∧
      s ^ (2 ^ n - 1) = 1 := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, ⟨e, he⟩, -, hL2, -, -, -, -, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n := by
    rw [← hL2, card_orbitField_D4_orientation Nat.prime_two hn1 hK (Or.inl rfl)
      (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) ⟨1, by decide⟩,
      show (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1
        by decide, pow_one]
  have hex : ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ r ≠ 3 := by
    by_contra hcon
    have hall : ∀ d, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
      intro d hd hdv
      by_contra hne
      exact hcon ⟨d, hd, hdv, hne⟩
    have hm0 : 2 ^ n - 1 ≠ 0 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hpow : 2 ^ n - 1 = 3 ^ (2 ^ n - 1).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdv => hall d hd hdv)
    have hm8 : (2 ^ n - 1) % 8 = 7 := by
      have h2n : 2 ^ n = 8 * 2 ^ (n - 3) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (n - 3) = n by omega]
      have h1 : 1 ≤ 2 ^ (n - 3) := Nat.one_le_pow _ _ (by norm_num)
      have e8 : 8 * 2 ^ (n - 3) - 1 = 7 + (2 ^ (n - 3) - 1) * 8 := by
        generalize 2 ^ (n - 3) = a at h1 ⊢
        omega
      rw [h2n, e8, Nat.add_mul_mod_self_right]
    rw [hpow] at hm8
    have h3mod : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
      intro k
      induction k with
      | zero => left; norm_num
      | succ k ih =>
        rcases ih with h | h
        · right; rw [pow_succ, Nat.mul_mod, h]
        · left; rw [pow_succ, Nat.mul_mod, h]
    rcases h3mod _ with h | h
    · rw [h] at hm8; omega
    · rw [h] at hm8; omega
  obtain ⟨r, hr, hrdvd, hr3⟩ := hex
  haveI : Fact r.Prime := ⟨hr⟩
  have : Finite (trialityFixedField K σ.toRingHom) := Subtype.finite
  have hkr : r ∣ Nat.card ((trialityFixedField K σ.toRingHom)ˣ) := by
    rw [Nat.card_units, hk]
    exact hrdvd
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hkr
  set a : Kˣ := trialityFixedUnit K σ ζ with ha
  have hσa : Units.map σ.toRingHom.toMonoidHom a = a := units_map_trialityFixedUnit ζ
  have hFinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have horda : orderOf a = r := by
    rw [ha, orderOf_injective (trialityFixedUnit K σ) hFinj ζ, hζ]
  have hordp : orderOf (a, (1 : (trialityFixedField K σ.toRingHom)ˣ)) = r := by
    let f : Kˣ →* Kˣ × (trialityFixedField K σ.toRingHom)ˣ :=
      { toFun := fun x => (x, 1), map_one' := rfl, map_mul' := fun x y => by
          rw [Prod.mk_mul_mk, mul_one] }
    have h : orderOf (f a) = orderOf a :=
      orderOf_injective f (fun x y hxy => congrArg Prod.fst hxy) a
    have hfa : f a = (a, (1 : (trialityFixedField K σ.toRingHom)ˣ)) := rfl
    rw [hfa] at h
    rw [h, horda]
  let s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ⟨((e (a, 1) : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K),
      graphFixedRootTorus_le _ _ _ (e (a, 1)).2⟩
  have hm1 : trialityMiddleTorus K σ (1 : (trialityFixedField K σ.toRingHom)ˣ) =
      (1 : ModGL TwistTag.D4.tag K) := by
    rw [trialityMiddleTorus]
    exact CFSG.Blueprint.Chevalley.torusElt_one ⟨2, by decide⟩
  have hsCoe : (s : ModGL TwistTag.D4.tag K) = trialityOuterTorus K σ a := by
    have h1 := he a 1
    show ((e (a, 1) : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ a
    rw [h1, hm1, mul_one]
  have hsH : (s : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    (e (a, 1)).2
  have hord : orderOf s = r := by
    have hsa : ((s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) =
        ((e (a, 1) : graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) := rfl
    have h1 : orderOf (e.toMonoidHom (a, 1)) = r := by
      rw [orderOf_injective e.toMonoidHom e.injective (a, 1), hordp]
    rw [← Subgroup.orderOf_coe s, hsa, Subgroup.orderOf_coe (e (a, 1))]
    exact h1
  have hfield : fieldActor (t := TwistTag.D4) σ σ s = s := by
    refine Subtype.ext ?_
    rw [coe_fieldActor, hsCoe, trialityOuterTorus_eq_rootDiagUnit,
      units_map_entrywiseHom_rootDiagUnit, d4Tuple_map_units]
    refine congrArg (fun b : Fin TwistTag.D4.tag.rank → Kˣ =>
      rootDiagUnit TwistTag.D4.tag b) (vec4_eq ?_ ?_ ?_ ?_)
    all_goals simp only [hσa, map_pow, map_mul, map_inv]
  have hsne : s ≠ 1 := by
    have hr2 := hr.two_le
    intro h
    have h1 : orderOf s = 1 := by rw [h, orderOf_one]
    omega
  have hpow : s ^ (2 ^ n - 1) = 1 := by
    have h : orderOf s ∣ 2 ^ n - 1 := by rw [hord]; exact hrdvd
    exact orderOf_dvd_iff_pow_eq_one.1 h
  exact ⟨s, hsH, hfield, hsne, by
    rw [hord]
    exact (Nat.coprime_primes hr Nat.prime_three).2 hr3, hpow⟩

end Certs

end CFSG.RankThree.PartTwo.KFacts.KS167D4Model
