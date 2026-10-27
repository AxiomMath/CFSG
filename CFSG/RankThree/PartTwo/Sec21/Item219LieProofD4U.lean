module

public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Matrix Pointwise MatrixGroups commutatorElement


theorem mem_center_mulEquiv {G H : Type} [Group G] [Group H] (φ : G ≃* H) (x : G) :
    x ∈ Subgroup.center G ↔ φ x ∈ Subgroup.center H := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    obtain ⟨g₀, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, h g₀]
  · intro h g
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ g)

theorem threeSix_unitary_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq2 : 2 < ℓ ^ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ =
        threeSixSingularR Ω K σ Fr (-1) v g ∧
    CFSG.IsQuasisimple (threeSixSingularR Ω K σ Fr (-1) v g) ∧
    ∃ U : Subgroup (GL (Fin 3) Ω), (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
      ∃ e : threeSixSingularR Ω K σ Fr (-1) v g ≃* U,
        ∀ X : threeSixSingularR Ω K σ Fr (-1) v g,
          X ∈ Subgroup.center (threeSixSingularR Ω K σ Fr (-1) v g) ↔
            ∃ c : Ω, (((e X : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
              Matrix.scalar (Fin 3) c := by
  classical
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hstab := threeSix_stab hFr hε ha hv
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω ℓ]
    exact hℓ3
  obtain ⟨-, -, hQM, -, -, -, hMder, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK a hord v
      hv.symm
  obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
  obtain ⟨⟨U, hU, e, he⟩, hQS, hZs, -, -⟩ := threeSix_fix_unitary hℓ hf hK hσ hFr hq2 _ π b hb
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω := fun u hu =>
    (Subgroup.mem_inf.1 (hQM hu)).1
  have hrange' : (threeSixEmb' Ω K σ g).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (threeSixFrob Ω Fr (-1)).eqLocus (MonoidHom.id _) := by
    ext u
    exact mem_range_threeSixEmb' hrange hgG hFg u
  have hRΩ : tsQv Ω v ⊓ (threeSixEmb' Ω K σ g).range = threeSixRΩ Ω Fr (-1) v := by
    rw [hrange', ← inf_assoc, inf_eq_left.2 hQG]
    rfl
  have hR := threeSixSingularR_eq_comap hrange hgG hFg v
  have hD := CFSG.RankThree.Chevalley.centralizer_eq_comap hrange hgG hFg hx
  have hRmem : ∀ y, y ∈ threeSixSingularR Ω K σ Fr (-1) v g ↔
      threeSixEmb' Ω K σ g y ∈ tsQv Ω v := fun y => by
    rw [hR, Subgroup.mem_comap]
  have hfixι : ∀ y, threeSixFrob Ω Fr (-1) (threeSixEmb' Ω K σ g y) =
      threeSixEmb' Ω K σ g y :=
    fun y => ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  have hperf : ⁅threeSixRΩ Ω Fr (-1) v, threeSixRΩ Ω Fr (-1) v⁆ = threeSixRΩ Ω Fr (-1) v := by
    have hP := (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (threeSixRΩEquivFix Fr hFrs hε v hstab).symm hQS).1
    rw [Group.isPerfect_def] at hP
    rw [← Subgroup.map_subtype_commutator, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eR : threeSixSingularR Ω K σ Fr (-1) v g ≃* threeSixRΩ Ω Fr (-1) v :=
    MulEquiv.ofBijective (((threeSixEmb' Ω K σ g).comp
      (threeSixSingularR Ω K σ Fr (-1) v g).subtype).codRestrict (threeSixRΩ Ω Fr (-1) v)
        fun y => Subgroup.mem_inf.2 ⟨(hRmem y).1 y.2, hfixι y⟩)
      ⟨fun y y' h => Subtype.ext (threeSixEmb'_injective g (congrArg Subtype.val h)), fun u => by
        obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg u).2
          ⟨hQG (Subgroup.mem_inf.1 u.2).1, (Subgroup.mem_inf.1 u.2).2⟩
        refine ⟨⟨y, (hRmem y).2 ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact (Subgroup.mem_inf.1 u.2).1⟩
  let eRF := eR.trans (threeSixRΩEquivFix Fr hFrs hε v hstab)
  have hiff : ∀ X : threeSixSingularR Ω K σ Fr (-1) v g,
      X ∈ Subgroup.center (threeSixSingularR Ω K σ Fr (-1) v g) ↔
        ∃ c : Ω, (((eRF.trans e X : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          Matrix.scalar (Fin 3) c := fun X => by
    rw [mem_center_mulEquiv eRF X, hZs (eRF X)]
    exact he (eRF X)
  refine ⟨?_, CFSG.LocalCores.isQuasisimple_of_mulEquiv eRF.symm hQS, U, hU, eRF.trans e, hiff⟩
  apply Subgroup.map_injective (threeSixEmb'_injective (K := K) (σ := σ) g)
  rw [Subgroup.map_commutator, hD, hR, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    inf_comm _ (toralCentralizer TwistTag.D4.tag Ω a), inf_comm _ (tsQv Ω v)]
  exact commutator_inf_eq hQM hMder (by rw [hRΩ]; exact hperf)

theorem exists_threeA_model_unitary {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) (hq2 : 2 < ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ = R ∧
        x ∈ R ∧ CFSG.IsQuasisimple R ∧
        ∃ U : Subgroup (GL (Fin 3) (AlgebraicClosure K)),
          (U : Set (GL (Fin 3) (AlgebraicClosure K))) = unitarySet (ℓ ^ f) 3 ∧
          ∃ e : R ≃* U, ∀ X : R, X ∈ Subgroup.center R ↔
            ∃ μ : AlgebraicClosure K,
              (((e X : U) : GL (Fin 3) (AlgebraicClosure K)) :
                Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) = Matrix.scalar (Fin 3) μ := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
    rw [← ZMod.natCast_mod, hq1]
    rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L (-1))
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L (-1) := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG hFg' ha
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · obtain ⟨hcomm, hquasi, U, hU, hne⟩ := threeSix_unitary_model hℓp hℓ3 hf hq2 K hK σ hσ L Fr
      hFr g hgG hFg' (tup ζ gT) ha hord vT hv x hx
    refine ⟨_, hcomm, ?_, hquasi, U, hU, hne⟩
    have hrange := range_threeSixEmb hℓp hf hK hσ Fr hFr
    rw [threeSixSingularR_eq_comap hrange hgG hFg' vT, Subgroup.mem_comap,
      threeSixEmb'_apply, hx]
    have e1 : g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹) * g =
        rootDiagUnit TwistTag.D4.tag (tup ζ gT) := by group
    rw [e1]
    exact rootDiagUnit_tup_gT_mem_tsQv hζ

theorem d4_threeA_model_unitary
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) (hq2 : 2 < ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      c * z * c⁻¹ ∈ R ∧
      R ≤ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      (∀ a ∈ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        ∀ b ∈ centralizer ({c * z * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          a * b * a⁻¹ * b⁻¹ ∈ R) ∧
      CFSG.IsQuasisimple R ∧
      ∃ U : Subgroup (GL (Fin 3) (AlgebraicClosure K)),
        (U : Set (GL (Fin 3) (AlgebraicClosure K))) = unitarySet (ℓ ^ f) 3 ∧
        ∃ e : R ≃* U, ∀ X : R, X ∈ Subgroup.center R ↔
          ∃ μ : AlgebraicClosure K,
            (((e X : U) : GL (Fin 3) (AlgebraicClosure K)) :
              Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) = Matrix.scalar (Fin 3) μ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  obtain ⟨x, k, hk, hxk, R, hRc, hxR, hRq, U, hU, hRU⟩ :=
    exists_threeA_model_unitary hf hℓ3 hq1 hq2 hK hσ hζ
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  refine ⟨c, R, ?_, ?_, ?_, hRq, U, hU, hRU⟩
  · rw [hc]
    exact hxR
  · rw [hc, ← hRc]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ≤
          centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hy)
  · rw [hc, ← hRc]
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rwa [commutatorElement_def] at h1

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
