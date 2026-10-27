module

public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularTools
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularIso
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularOdd

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped Matrix Pointwise MatrixGroups commutatorElement

section Conj

variable {Ω : Type} [Field Ω]

theorem d4A2Subsystem_le_adjointGroup :
    subsystemGroup Tag.D4 Ω d4SuppA2 ≤ adjointGroup Tag.D4 Ω :=
  (Subgroup.closure_le _).2 fun _ ⟨i, _, c, hg⟩ => by
    rcases hg with rfl | rfl
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c

variable (Ω) in
@[expose] def d4A2RepInv (J : SL(3, Ω)) : subsystemGroup Tag.D4 Ω d4SuppA2 :=
  (MulEquiv.ofBijective (d4A2Rep Ω) ⟨d4A2Rep_injective, d4A2Rep_surjective⟩).symm J

theorem d4A2Rep_d4A2RepInv (J : SL(3, Ω)) : d4A2Rep Ω (d4A2RepInv Ω J) = J :=
  (MulEquiv.ofBijective (d4A2Rep Ω) ⟨d4A2Rep_injective, d4A2Rep_surjective⟩).apply_symm_apply J

variable (Ω) in
@[expose] def threeSixConjRep (v : WeylGroup Tag.D4) (J : SL(3, Ω)) :
    ModGL TwistTag.D4.tag Ω :=
  canonicalRep (coxeterSystem Tag.D4) Ω v * (d4A2RepInv Ω J : ModGL Tag.D4 Ω)

theorem threeSixConjRep_mem_adjointGroup (v : WeylGroup Tag.D4) (J : SL(3, Ω)) :
    threeSixConjRep Ω v J ∈ adjointGroup TwistTag.D4.tag Ω :=
  mul_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.D4) Ω v)
    (d4A2Subsystem_le_adjointGroup (d4A2RepInv Ω J).2)

theorem d4A2QvEquiv_conj (v : WeylGroup Tag.D4) (w : subsystemGroup Tag.D4 Ω d4SuppA2)
    (h : canonicalRep (coxeterSystem Tag.D4) Ω v * (w : ModGL Tag.D4 Ω) *
      (canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹ ∈ d4A2Qv Ω v) :
    d4A2QvEquiv v ⟨_, h⟩ = d4A2Rep Ω w := by
  refine Subtype.ext ?_
  rw [coe_d4A2QvEquiv, coe_d4A2Rep]
  congr 1
  group

theorem conj_tsIota_mem_threeSixRΩ (Fr : Ω →+* Ω) (hFrs : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) (J : SL(3, Ω)) (A : SL(2, Ω))
    (hJ : J * (blockSL Ω 2 1 A : SL(3, Ω)) * J⁻¹ ∈
      fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) :
    threeSixConjRep Ω v J * tsIota Ω A * (threeSixConjRep Ω v J)⁻¹ ∈ threeSixRΩ Ω Fr ε v := by
  set w : subsystemGroup Tag.D4 Ω d4SuppA2 :=
    d4A2RepInv Ω J * d4A2Iota Ω A * (d4A2RepInv Ω J)⁻¹ with hw
  have hu : threeSixConjRep Ω v J * tsIota Ω A * (threeSixConjRep Ω v J)⁻¹ =
      (canonicalRep (coxeterSystem Tag.D4) Ω v * (w : ModGL Tag.D4 Ω) *
        (canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹ : ModGL Tag.D4 Ω) := by
    change canonicalRep (coxeterSystem Tag.D4) Ω v * (d4A2RepInv Ω J : ModGL Tag.D4 Ω) *
        ((d4A2Iota Ω A : subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω) *
        (canonicalRep (coxeterSystem Tag.D4) Ω v * (d4A2RepInv Ω J : ModGL Tag.D4 Ω))⁻¹ = _
    rw [hw, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hQ : canonicalRep (coxeterSystem Tag.D4) Ω v * (w : ModGL Tag.D4 Ω) *
      (canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹ ∈ d4A2Qv Ω v :=
    Subgroup.mem_map.2 ⟨w, w.2, rfl⟩
  have hΨ : d4A2QvEquiv v ⟨_, hQ⟩ = J * sl2BlockSL3 Ω A * J⁻¹ := by
    rw [d4A2QvEquiv_conj, hw, map_mul, map_mul, map_inv, d4A2Rep_d4A2RepInv, d4A2Rep_d4A2Iota]
  have hmem : d4A2QvEquiv v ⟨_, hQ⟩ ∈ fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab) := by
    rw [hΨ, ← blockSL_eq_sl2BlockSL3]
    exact hJ
  have hF := (mem_fixSubgroup_threeSixPhi Fr hFrs hε v hstab _).1 hmem
  rw [MulEquiv.symm_apply_apply] at hF
  rw [hu]
  exact Subgroup.mem_inf.2 ⟨hQ, hF⟩

end Conj

theorem exists_threeSixEmb_eq_conj {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {ε : ℤ} {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) {h : ModGL TwistTag.D4.tag Ω}
    (hh : h ∈ threeSixTorus Ω Fr ε) :
    ∃ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, threeSixEmb K Ω σ x = g * h * g⁻¹ := by
  have hhG : h ∈ adjointGroup TwistTag.D4.tag Ω :=
    ((Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2 :
      torusGroup TwistTag.D4.tag Ω ≤ adjointGroup TwistTag.D4.tag Ω) (Subgroup.mem_inf.1 hh).1
  have hhF : threeSixFrob Ω Fr ε h = h := (Subgroup.mem_inf.1 hh).2
  have hmem : g * h * g⁻¹ ∈ (threeSixEmb K Ω σ).range := by
    rw [range_threeSixEmb hℓ hf hK hσ Fr hFr]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG hhG) (inv_mem hgG), ?_⟩
    change trialityFrob Ω Fr (g * h * g⁻¹) = g * h * g⁻¹
    rw [trialityFrob_conj hFg, hhF]
  exact hmem

theorem triality_three_six_singular_fixed_centralizers {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ d) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    (toralCentralizer TwistTag.D4.tag Ω a : Set (ModGL TwistTag.D4.tag Ω)) =
        (torusGroup TwistTag.D4.tag Ω : Set (ModGL TwistTag.D4.tag Ω)) *
          (tsQv Ω v : Set (ModGL TwistTag.D4.tag Ω)) ∧
    (tsQv Ω v).map (threeSixFrob Ω Fr ε) = tsQv Ω v ∧
    ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ =
        threeSixSingularR Ω K σ Fr ε v g ∧
    (ε = 1 → ∃ e : threeSixSingularR Ω K σ Fr ε v g ≃*
        SL(3, RingHom.eqLocusField Fr (RingHom.id Ω)),
      ∀ y, y ∈ center (threeSixSingularR Ω K σ Fr ε v g) ↔
        ∃ c, ((e y : SL(3, RingHom.eqLocusField Fr (RingHom.id Ω))) :
          Matrix (Fin 3) (Fin 3) (RingHom.eqLocusField Fr (RingHom.id Ω))) =
            Matrix.scalar (Fin 3) c) ∧
    (ε = -1 → ∃ U : Subgroup (GL (Fin 3) Ω), (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
      ∃ e : threeSixSingularR Ω K σ Fr ε v g ≃* U,
        ∀ y, y ∈ center (threeSixSingularR Ω K σ Fr ε v g) ↔
          ∃ c : Ω, (((e y : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
            Matrix.scalar (Fin 3) c) ∧
    CFSG.IsQuasisimple (threeSixSingularR Ω K σ Fr ε v g) ∧
    Nat.card (center (threeSixSingularR Ω K σ Fr ε v g)) = Int.gcd 3 ((ℓ ^ f : ℕ) - ε) ∧
    (∀ y ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      y ^ d ∈ threeSixSingularR Ω K σ Fr ε v g) ∧
    Odd ((threeSixSingularR Ω K σ Fr ε v g).relIndex
      (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ∧
    Nat.card (RingHom.eqLocusField Fr (RingHom.id Ω)) = ℓ ^ f ∧
    ∃ z ∈ adjointGroup TwistTag.D4.tag Ω,
      ∃ X : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        X ⊆ threeSixSingularR Ω K σ Fr ε v g ∧
        (∀ y ∈ X, ∃ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)), threeSixEmb K Ω σ y =
          z * tsIota Ω (Matrix.SpecialLinearGroup.map
            (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) * z⁻¹) ∧
        (∀ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)), ∃ y ∈ X, threeSixEmb K Ω σ y =
          z * tsIota Ω (Matrix.SpecialLinearGroup.map
            (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) * z⁻¹) ∧
        Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
          LinearMap.trace Ω (RootModule TwistTag.D4.tag Ω)
            ((threeSixEmb K Ω σ r : ModGL TwistTag.D4.tag Ω) :
              Module.End Ω (RootModule TwistTag.D4.tag Ω))) '' X) =
          RingHom.eqLocusField Fr (RingHom.id Ω) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have h1q : 1 ≤ ℓ ^ f := Nat.one_le_iff_ne_zero.2 hq0
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hstab := threeSix_stab hFr hε ha hv
  have hp2 : p ≠ 2 := by omega
  have hpK : ringChar Ω ≠ p := by
    rw [ringChar.eq Ω ℓ]
    intro h
    have hpdZ : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
      rw [← hd]
      exact Int.natCast_dvd_natCast.2 hpd
    refine (threeSix_prime_not_dvd hε hp hp3 hpdZ).1 ?_
    rw [← h]
    exact Int.natCast_dvd_natCast.2 (dvd_pow_self ℓ (by omega))
  have hdodd : Odd d := by
    rw [← Int.odd_coe_nat]
    rcases hε with rfl | rfl
    · obtain ⟨r, hr⟩ := Int.even_mul_succ_self ((ℓ ^ f : ℕ) : ℤ)
      exact ⟨r, by rw [hd]; linear_combination hr⟩
    · obtain ⟨r, hr⟩ := Int.even_mul_succ_self (((ℓ ^ f : ℕ) : ℤ) - 1)
      exact ⟨r, by rw [hd]; linear_combination hr⟩
  obtain ⟨-, hMset, hQM, hQMn, -, -, hMder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω p hp hp2 hpK a hord v hv.symm
  have hfix : CFSG.IsQuasisimple (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) ∧
      Nat.card (center (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab))) =
        Int.gcd 3 ((ℓ ^ f : ℕ) - ε) ∧
      (∃ J : SL(3, Ω), ∀ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)),
        J * (blockSL Ω 2 1 (SpecialLinearGroup.map
          (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) : SL(3, Ω)) * J⁻¹ ∈
            fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) ∧
      (ε = 1 → Nonempty (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab) ≃*
        SL(3, RingHom.eqLocusField Fr (RingHom.id Ω)))) ∧
      (ε = -1 → ∃ U : Subgroup (GL (Fin 3) Ω),
        (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
        ∃ e : fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab) ≃* U,
          ∀ X, X ∈ center (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) ↔
            ∃ c : Ω, (((e X : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
              scalar (Fin 3) c) := by
    rcases hε with rfl | rfl
    · obtain ⟨π, b, hb⟩ := threeSix_phi_split Fr hFrs v hstab
      obtain ⟨he, hQ, hcard, hJ⟩ := threeSix_fix_split hℓ hf hK hσ hFr _ π b hb
      refine ⟨hQ, ?_, hJ, fun _ => he, fun h => absurd h (by decide)⟩
      rw [hcard, ← Int.gcd_natCast_natCast, Nat.cast_sub h1q]
      rfl
    · have hq2 : 2 < ℓ ^ f := by
        have h2 : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
        by_contra h
        have h3 : ℓ ^ f = 2 := by omega
        rw [h3] at hd
        have hd3 : d = 3 := by norm_num at hd; exact_mod_cast hd
        have := Nat.le_of_dvd (by norm_num) (hd3 ▸ hpd)
        omega
      obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
      obtain ⟨⟨U, hU, e, he⟩, hQ, hcent, hcard, hJ⟩ :=
        threeSix_fix_unitary hℓ hf hK hσ hFr hq2 _ π b hb
      refine ⟨hQ, ?_, hJ, fun h => absurd h (by decide), fun _ => ⟨U, hU, e, fun X =>
        (hcent X).trans (he X)⟩⟩
      rw [hcard, ← Int.gcd_natCast_natCast, Nat.cast_add, sub_neg_eq_add]
      rfl
  obtain ⟨hQS, hZcard, ⟨J, hJ⟩, hsplit, hunit⟩ := hfix
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω := fun u hu =>
    (Subgroup.mem_inf.1 (hQM hu)).1
  have hrange' : (threeSixEmb' Ω K σ g).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (threeSixFrob Ω Fr ε).eqLocus (MonoidHom.id _) := by
    ext u
    exact mem_range_threeSixEmb' hrange hgG hFg u
  have hRΩ : tsQv Ω v ⊓ (threeSixEmb' Ω K σ g).range = threeSixRΩ Ω Fr ε v := by
    rw [hrange', ← inf_assoc, inf_eq_left.2 hQG]
    rfl
  have hR := threeSixSingularR_eq_comap hrange hgG hFg v
  have hD := centralizer_eq_comap hrange hgG hFg hx
  have hRmem : ∀ y, y ∈ threeSixSingularR Ω K σ Fr ε v g ↔
      threeSixEmb' Ω K σ g y ∈ tsQv Ω v := fun y => by
    rw [hR, Subgroup.mem_comap]
  have hfixι : ∀ y, threeSixFrob Ω Fr ε (threeSixEmb' Ω K σ g y) = threeSixEmb' Ω K σ g y :=
    fun y => ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  have hperf : ⁅threeSixRΩ Ω Fr ε v, threeSixRΩ Ω Fr ε v⁆ = threeSixRΩ Ω Fr ε v := by
    have hP := (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (threeSixRΩEquivFix Fr hFrs hε v hstab).symm hQS).1
    rw [Group.isPerfect_def] at hP
    rw [← Subgroup.map_subtype_commutator, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eR : threeSixSingularR Ω K σ Fr ε v g ≃* threeSixRΩ Ω Fr ε v :=
    MulEquiv.ofBijective (((threeSixEmb' Ω K σ g).comp
      (threeSixSingularR Ω K σ Fr ε v g).subtype).codRestrict (threeSixRΩ Ω Fr ε v)
        fun y => Subgroup.mem_inf.2 ⟨(hRmem y).1 y.2, hfixι y⟩)
      ⟨fun y y' h => Subtype.ext (threeSixEmb'_injective g (congrArg Subtype.val h)), fun u => by
        obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg u).2
          ⟨hQG (Subgroup.mem_inf.1 u.2).1, (Subgroup.mem_inf.1 u.2).2⟩
        refine ⟨⟨y, (hRmem y).2 ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact (Subgroup.mem_inf.1 u.2).1⟩
  let eRF := eR.trans (threeSixRΩEquivFix Fr hFrs hε v hstab)
  have hpow : ∀ y ∈ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      y ^ d ∈ threeSixSingularR Ω K σ Fr ε v g := by
    intro y hy
    rw [hD, Subgroup.mem_comap] at hy
    rw [hRmem, map_pow]
    have hy' : threeSixEmb' Ω K σ g y ∈
        (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) * (d4A2Qv Ω v : Set (ModGL Tag.D4 Ω)) := by
      rw [← hMset]
      exact hy
    exact pow_mem_d4A2Qv_of_fixed Fr hFrs hFr hε v hstab hd hy' (hfixι y)
  have hRD : threeSixSingularR Ω K σ Fr ε v g ≤
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [hR, hD]
    exact Subgroup.comap_mono hQM
  have hN : ((threeSixSingularR Ω K σ Fr ε v g).subgroupOf
      (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRD]
    intro r y hr hy
    rw [hRmem] at hr ⊢
    rw [hD, Subgroup.mem_comap] at hy
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.normal_subgroupOf_iff hQM).1 hQMn _ _ hr hy
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  have : Finite (ModGL TwistTag.D4.tag K) := inferInstance
  have hk := natCard_eqLocusField_frob hℓ hf hFr
  refine ⟨hMset, map_threeSixFrob_d4A2Qv Fr hFrs hε v hstab, ?_, fun h1 => ?_, fun h1 => ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eRF.symm hQS, ?_, hpow,
    odd_relIndex_of_pow_mem hN hdodd hpow, hk, ?_⟩
  ·
    apply Subgroup.map_injective (threeSixEmb'_injective (K := K) (σ := σ) g)
    rw [Subgroup.map_commutator, hD, hR, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
      inf_comm _ (toralCentralizer TwistTag.D4.tag Ω a), inf_comm _ (tsQv Ω v)]
    exact commutator_inf_eq hQM hMder (by rw [hRΩ]; exact hperf)
  ·
    obtain ⟨e₁⟩ := hsplit h1
    exact ⟨eRF.trans e₁, fun y =>
      (mem_center_iff_of_mulEquiv (eRF.trans e₁) y).trans (mem_center_SL_iff _)⟩
  ·
    obtain ⟨U, hU, e₁, he₁⟩ := hunit h1
    exact ⟨U, hU, eRF.trans e₁, fun y => (mem_center_iff_of_mulEquiv eRF y).trans (he₁ _)⟩
  ·
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.centerCongr eRF).toEquiv
  ·
    have : Finite (RingHom.eqLocusField Fr (RingHom.id Ω)) :=
      Nat.finite_of_card_ne_zero (by rw [hk]; exact hq0)
    have hu : ∀ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)),
        ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          threeSixEmb K Ω σ y = g * threeSixConjRep Ω v J * tsIota Ω (SpecialLinearGroup.map
            (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) * (g * threeSixConjRep Ω v J)⁻¹ ∧
          y ∈ threeSixSingularR Ω K σ Fr ε v g := by
      intro A
      have hmem := conj_tsIota_mem_threeSixRΩ Fr hFrs hε v hstab J _ (hJ A)
      obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg _).2
        ⟨hQG (Subgroup.mem_inf.1 hmem).1, (Subgroup.mem_inf.1 hmem).2⟩
      refine ⟨y, ?_, (hRmem y).2 (by rw [hy]; exact (Subgroup.mem_inf.1 hmem).1)⟩
      rw [threeSixEmb'_apply] at hy
      calc threeSixEmb K Ω σ y = g * (g⁻¹ * threeSixEmb K Ω σ y * g) * g⁻¹ := by group
        _ = _ := by rw [hy]; group
    refine ⟨g * threeSixConjRep Ω v J, mul_mem hgG (threeSixConjRep_mem_adjointGroup v J),
      {y | ∃ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)), threeSixEmb K Ω σ y =
        g * threeSixConjRep Ω v J * tsIota Ω (SpecialLinearGroup.map
          (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) * (g * threeSixConjRep Ω v J)⁻¹},
      ?_, fun y hy => hy, fun A => ?_, ?_⟩
    · rintro y ⟨A, hA⟩
      obtain ⟨y', hy', hy'R⟩ := hu A
      have hyy : y = y' := ((baseChangeGL_injective (τ := TwistTag.D4.tag)
        (algebraMap K Ω)).comp Subtype.val_injective) (hA.trans hy'.symm)
      rw [hyy]
      exact hy'R
    · obtain ⟨y, hy, -⟩ := hu A
      exact ⟨y, ⟨A, hy⟩, hy⟩
    · refine Eq.trans ?_ (closure_traces_eq (RingHom.eqLocusField Fr (RingHom.id Ω))
        (g * threeSixConjRep Ω v J))
      congr 1
      ext t
      constructor
      · rintro ⟨y, ⟨A, hA⟩, rfl⟩
        exact ⟨A, congrArg (fun u : ModGL TwistTag.D4.tag Ω => LinearMap.trace Ω
          (RootModule TwistTag.D4.tag Ω) (u : Module.End Ω (RootModule TwistTag.D4.tag Ω))) hA⟩
      · rintro ⟨A, rfl⟩
        obtain ⟨y, hy, -⟩ := hu A
        exact ⟨y, ⟨A, hy⟩, congrArg (fun u : ModGL TwistTag.D4.tag Ω => LinearMap.trace Ω
          (RootModule TwistTag.D4.tag Ω) (u : Module.End Ω (RootModule TwistTag.D4.tag Ω))) hy⟩

end CFSG.RankThree.Chevalley
