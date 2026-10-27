module

public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.KLAY.RootSL2
public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.RankThree.PartOne.KGD.D4Weyl
public import CFSG.RankThree.PartOne.KF.D4Sylow

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KFU CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (rootList mem_rootList)

open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}

theorem exists_fixedField (hP : D4Param p f K σ) :
    ∃ k : Subfield K, (∀ c : K, c ∈ k ↔ σ c = c) ∧ Nat.card k = 2 ^ f := by
  obtain ⟨σ', -, -, -, -, k, hk, hkc, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hP.one_le K hP.card
  refine ⟨k, fun c => ?_, hkc⟩
  have : c ∈ k ↔ c ^ 2 ^ f = c := by
    rw [← SetLike.mem_coe, hk]
    rfl
  rw [this, hP.frob]

theorem perm_d4i2 : TwistTag.D4.perm KFU.d4i2 = KFU.d4i2 := perm_D4_values.2.2.2

theorem twistHom_rootSL2_two (σ : K →+* K) (B : SL2 K) :
    twistHom TwistTag.D4 K σ (rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) B) =
      rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) (Matrix.SpecialLinearGroup.map σ B) := by
  have h : (twistHom TwistTag.D4 K σ).comp (rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1)) =
      (rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1)).comp
        (Matrix.SpecialLinearGroup.map σ) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change twistHom TwistTag.D4 K σ (rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) (uSL c)) =
        rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) (Matrix.SpecialLinearGroup.map σ (uSL c))
      rw [rootSL2_single, simpleRootSL2_uSL, twistHom_xUnit, perm_d4i2, map_uSL,
        simpleRootSL2_uSL]
    · change twistHom TwistTag.D4 K σ (rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) (vSL c)) =
        rootSL2 TwistTag.D4.tag K (Pi.single KFU.d4i2 1) (Matrix.SpecialLinearGroup.map σ (vSL c))
      rw [rootSL2_single, simpleRootSL2_vSL, twistHom_yUnit, perm_d4i2, map_vSL,
        simpleRootSL2_vSL]
  exact DFunLike.congr_fun h B

theorem exists_unit_of_mem (k : Subfield K) (u : Kˣ) (hu : (u : K) ∈ k) :
    ∃ χ : (↥k)ˣ, Units.map (k.subtype : ↥k →* K) χ = u :=
  ⟨Units.mk0 ⟨u, hu⟩ (fun h => u.ne_zero (congrArg Subtype.val h)), Units.ext rfl⟩

theorem exists_map_of_entries_mem (k : Subfield K) (B : SL2 K)
    (hB : ∀ i j, (B : Matrix (Fin 2) (Fin 2) K) i j ∈ k) :
    ∃ B' : SL2 ↥k, Matrix.SpecialLinearGroup.map k.subtype B' = B := by
  let M' : Matrix (Fin 2) (Fin 2) ↥k := fun i j => ⟨(B : Matrix (Fin 2) (Fin 2) K) i j, hB i j⟩
  have hdet : M'.det = 1 := by
    apply k.subtype.injective
    rw [map_one, RingHom.map_det]
    have : k.subtype.mapMatrix M' = (B : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [this, B.2]
  refine ⟨⟨M', hdet⟩, Subtype.ext ?_⟩
  rfl

theorem exists_map_of_map_eq (k : Subfield K) (hk : ∀ c : K, c ∈ k ↔ σ c = c) (B : SL2 K)
    (hB : Matrix.SpecialLinearGroup.map σ B = B) :
    ∃ B' : SL2 ↥k, Matrix.SpecialLinearGroup.map k.subtype B' = B := by
  refine exists_map_of_entries_mem k B fun i j => (hk _).2 ?_
  have := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) i j) hB
  simpa using this

theorem rootChar_d4 (a : Fin TwistTag.D4.tag.rank → Kˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a v = a KFU.d4i0 ^ v KFU.d4i0 * a KFU.d4i1 ^ v KFU.d4i1 * a KFU.d4i2 ^ v KFU.d4i2 *
      a KFU.d4i3 ^ v KFU.d4i3 :=
  Fin.prod_univ_four (fun j => a j ^ v j)

set_option maxRecDepth 100000 in
theorem d4_root_check_two :
    ∀ β ∈ rootList TwistTag.D4.tag,
      (β KFU.d4i0 + β KFU.d4i1 + β KFU.d4i3).natAbs ≤ 3 ∧
        (β KFU.d4i0 + β KFU.d4i1 + β KFU.d4i3 = 0 →
          β = Pi.single KFU.d4i2 1 ∨ β = -Pi.single KFU.d4i2 1) := by
  decide +kernel

theorem d4_kernel_two (h5 : 5 ≤ p) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    rootCharKernel (d4Tuple ζ 1) ⊆ {Pi.single KFU.d4i2 1, -Pi.single KFU.d4i2 1} := by
  rintro β ⟨hβ, hχ⟩
  rw [rootChar_d4, d4Tuple_zero, d4Tuple_one, d4Tuple_two, d4Tuple_three, one_zpow, mul_one,
    ← zpow_add, ← zpow_add] at hχ
  have hdvd := (hζ.zpow_eq_one_iff_dvd _).1 hχ
  obtain ⟨hle, hzero⟩ := d4_root_check_two β ((mem_rootList).2 hβ)
  have hn : β KFU.d4i0 + β KFU.d4i1 + β KFU.d4i3 = 0 := by
    have h1 : p ∣ (β KFU.d4i0 + β KFU.d4i1 + β KFU.d4i3).natAbs := Int.natCast_dvd.1 hdvd
    have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega
  exact hzero hn

theorem d4_centralizer_mem_two (hp : p.Prime) (h5 : 5 ≤ p)
    {a : Fin TwistTag.D4.tag.rank → Kˣ} (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1)
    (hker : rootCharKernel a ⊆ {Pi.single KFU.d4i2 1, -Pi.single KFU.d4i2 1})
    {y : ModGL TwistTag.D4.tag K} (hy : y ∈ adjointGroup TwistTag.D4.tag K)
    (hc : y * rootDiagUnit TwistTag.D4.tag a = rootDiagUnit TwistTag.D4.tag a * y) :
    y ∈ (torusGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) *
      (rootRankOneGroup TwistTag.D4.tag K (Pi.single KFU.d4i2 1) :
        Set (ModGL TwistTag.D4.tag K)) :=
  KE.mem_torus_mul_rootRankOne_of_commute hp (KGD.not_dvd_card_weylGroup_D4 hp (by omega)) hap ha1
    (IsRoot.basis _) hker hy hc

theorem rootSL2Map_mem_graphFixed_two (k : Subfield K) (hk : ∀ c ∈ k, σ c = c)
    (A : SL2 ↥k) :
    rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype A ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
  have h : (graphFixedRootGroup TwistTag.D4 K σ).comap
      (rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype) = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype (uSL c) ∈
        graphFixedRootGroup TwistTag.D4 K σ
      rw [rootSL2Map_apply, rootSL2_single, map_uSL, simpleRootSL2_uSL]
      exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (xUnit_mem_graphFixedPosUnipotent perm_d4i2 (hk _ c.2))
    · change rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype (vSL c) ∈
        graphFixedRootGroup TwistTag.D4 K σ
      rw [rootSL2Map_apply, rootSL2_single, map_vSL, simpleRootSL2_vSL]
      exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (yUnit_mem_graphFixedNegUnipotent perm_d4i2 (hk _ c.2))
  have hA : A ∈ (graphFixedRootGroup TwistTag.D4 K σ).comap
      (rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype) := by
    rw [h]
    exact Subgroup.mem_top A
  exact hA

@[expose] noncomputable def d4Phi (k : Subfield K) (hk : ∀ c ∈ k, σ c = c) :
    SL2 ↥k →* ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  (rootSL2Map TwistTag.D4.tag (Pi.single KFU.d4i2 1) k.subtype).codRestrict
    (graphFixedRootGroup TwistTag.D4 K σ) (rootSL2Map_mem_graphFixed_two k hk)

theorem d4_SL2Torus_two (hP : D4Param p f K σ) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (k : Subfield K) (hkmem : ∀ c : K, c ∈ k ↔ σ c = c) :
    SL2Torus p (d4Phi k fun c hc => (hkmem c).1 hc) (Tp3 hP) := by
  have hθ : IsRoot TwistTag.D4.tag (Pi.single KFU.d4i2 1) := IsRoot.basis _
  have hfix : ∀ x : Kˣ, x ^ p = 1 → (x : K) ∈ k := fun x hx => (hkmem _).2 (hP.sigma_fix x hx)
  refine SL2Torus.of_rootDiag hθ k.subtype _ (fun A => rfl) (fun t ht => Tp3_exp hP t ht) ?_ ?_ ?_
  · rintro t ⟨b, rfl⟩
    have hb0 : ((b 0 : rootsOfUnity p K) : Kˣ) ^ p = 1 :=
      (mem_rootsOfUnity p _).1 (b 0).2
    obtain ⟨χ, hχ⟩ := exists_unit_of_mem k _ (hfix _ hb0)
    refine ⟨d4Tuple ((b 1 : rootsOfUnity p K) : Kˣ) ((b 0 : rootsOfUnity p K) : Kˣ), χ, rfl, ?_⟩
    rw [rootChar_single, d4Tuple_two, hχ]
  · intro s hs
    have hmem : ∀ n : ℤ, (Units.map (k.subtype : ↥k →* K) s) ^ n ∈ rootsOfUnity p K := fun n => by
      rw [mem_rootsOfUnity, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← map_pow, hs, map_one, one_zpow]
    refine ⟨![⟨(Units.map (k.subtype : ↥k →* K) s) ^ (2 : ℤ), hmem 2⟩,
      ⟨(Units.map (k.subtype : ↥k →* K) s) ^ (-1 : ℤ), hmem (-1)⟩], ?_⟩
    apply Subtype.ext
    change tp3Hom p K _ = rootSL2Map _ _ _ (HSL s)
    rw [rootSL2Map_single_HSL, tp3Hom_apply]
    congr 1
    funext j
    rcases KFU.fin_D4_cases j with rfl | rfl | rfl | rfl
    · simp [d4Tuple_zero, show TwistTag.D4.tag.cartan KFU.d4i2 KFU.d4i0 = -1 by decide]
    · simp [d4Tuple_one, show TwistTag.D4.tag.cartan KFU.d4i2 KFU.d4i1 = -1 by decide]
    · simp [d4Tuple_two, show TwistTag.D4.tag.cartan KFU.d4i2 KFU.d4i2 = 2 by decide]
    · simp [d4Tuple_three, show TwistTag.D4.tag.cartan KFU.d4i2 KFU.d4i3 = -1 by decide]
  · have hz : ζ ^ p = 1 := hζ.pow_eq_one
    let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hz⟩
    obtain ⟨χ, hχ⟩ := exists_unit_of_mem k ζ (hfix ζ hz)
    refine ⟨tp3M hP ![z, 1], ⟨_, rfl⟩, d4Tuple 1 ζ, χ, rfl, ?_, ?_⟩
    · rw [rootChar_single, d4Tuple_two, hχ]
    · intro h1
      rw [h1, map_one] at hχ
      exact hζ.ne_one (by have := hP.five_le; omega) hχ.symm

section Main

theorem d4_layerD_two (hP : D4Param p f K σ) {z : rootsOfUnity p K}
    (hz : IsPrimitiveRoot (z : Kˣ) p) (k : Subfield K) (hkmem : ∀ c : K, c ∈ k ↔ σ c = c)
    (hkcard : Nat.card k = 2 ^ f) :
    layerD (tp3M hP ![1, z]) = (d4Phi k fun c hc => (hkmem c).1 hc).range := by
  classical
  have : Finite K := hP.finite
  have hp := hP.prime
  have h5 := hP.five_le
  have hk : ∀ c ∈ k, σ c = c := fun c hc => (hkmem c).1 hc
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hζ1 : (z : Kˣ) ≠ 1 := hz.ne_one (by omega)
  have h4 : 4 ≤ Nat.card ↥k := by
    have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := f) (by have := hP.one_le; omega)
      omega) hP.dvd
    rw [hkcard]
    omega
  have hθ : IsRoot TwistTag.D4.tag (Pi.single KFU.d4i2 1) := IsRoot.basis _
  let a₀ : Fin TwistTag.D4.tag.rank → Kˣ := d4Tuple (z : Kˣ) 1
  set bM : ↥(graphFixedRootGroup TwistTag.D4 K σ) := tp3M hP ![1, z] with hbM
  have hbMd : ((bM : ↥(graphFixedRootGroup TwistTag.D4 K σ)) : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag a₀ := rfl
  have hap : ∀ i, a₀ i ^ p = 1 := fun i => by
    rcases KFU.fin_D4_cases i with rfl | rfl | rfl | rfl
    · rw [show a₀ KFU.d4i0 = (z : Kˣ) from d4Tuple_zero _ _]; exact hζp
    · rw [show a₀ KFU.d4i1 = (z : Kˣ) from d4Tuple_one _ _]; exact hζp
    · rw [show a₀ KFU.d4i2 = 1 from d4Tuple_two _ _]; exact one_pow p
    · rw [show a₀ KFU.d4i3 = (z : Kˣ) from d4Tuple_three _ _]; exact hζp
  have ha1 : a₀ ≠ 1 := fun h => hζ1 (by
    have := congrFun h KFU.d4i0
    rwa [show a₀ KFU.d4i0 = (z : Kˣ) from d4Tuple_zero _ _] at this)
  have hθa : rootChar a₀ (Pi.single KFU.d4i2 1) = 1 := by
    rw [rootChar_single, show a₀ KFU.d4i2 = 1 from d4Tuple_two _ _]
  have hSL := d4_SL2Torus_two hP hz k hkmem
  refine inSubgroup_perfectResidual_centralizer_eq (graphFixedRootGroup TwistTag.D4 K σ) bM
    (torusGroup TwistTag.D4.tag K)
    (rootRankOneGroup TwistTag.D4.tag K (Pi.single KFU.d4i2 1))
    (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).1
    (KE.torusGroup_le_normalizer_rootRankOneGroup hθ) ?_ ?_ (d4Phi k hk).range ?_
    (hSL.isQuasisimple_range h4).1
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_rootSL2 a₀ hθ A
    rw [hθa, conjSL_diagUnitOne_one] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro y hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
    have hyadj : (y : ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).1
        (graphFixedRootGroup_le TwistTag.D4 K σ y.2)).1
    exact d4_centralizer_mem_two hp h5 hap ha1 (d4_kernel_two h5 hz) hyadj hc
  · ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨(d4Phi k hk A).2, ⟨Matrix.SpecialLinearGroup.map k.subtype A, rfl⟩⟩
    · rintro ⟨hxM, B, rfl⟩
      have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ).1
        (graphFixedRootGroup_le TwistTag.D4 K σ hxM)).2
      rw [twistHom_rootSL2_two] at hfix
      obtain ⟨B', rfl⟩ := exists_map_of_map_eq k hkmem B
        (rootSL2_injective_of_field _ hfix)
      exact ⟨d4Phi k hk B', ⟨B', rfl⟩, rfl⟩

theorem d4_side_two (hP : D4Param p f K σ) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ bM ∈ Tp3 hP, bM ^ p = 1 ∧ bM ≠ 1 ∧ MSide p f (Tp3 hP) bM := by
  classical
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hp := hP.prime
  have h5 := hP.five_le
  obtain ⟨k, hkmem, hkcard⟩ := exists_fixedField hP
  have hkchar : CharP ↥k 2 := inferInstance
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have h4 : 4 ≤ Nat.card ↥k := by
    have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := f) (by have := hP.one_le; omega)
      omega) hP.dvd
    rw [hkcard]
    omega
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩
  set bM : ↥(graphFixedRootGroup TwistTag.D4 K σ) := tp3M hP ![1, z] with hbM
  have hbMT : bM ∈ Tp3 hP := tp3M_mem_Tp3 hP _
  have hbM1 : bM ≠ 1 := fun h => hζ1 (by
    have h1 : (![1, z] : Fin 2 → rootsOfUnity p K) = 1 :=
      tp3M_injective hP (h.trans (map_one _).symm)
    have := congrFun h1 1
    exact congrArg (fun x : rootsOfUnity p K => ((x : Kˣ))) this)
  refine ⟨bM, hbMT, Tp3_exp hP bM hbMT, hbM1, ?_⟩
  have hSL := d4_SL2Torus_two hP hζ k hkmem
  have hD := d4_layerD_two hP (z := z) hζ k hkmem hkcard
  obtain ⟨χ, hχ⟩ := exists_unit_of_mem k ζ ((hkmem _).2 (hP.sigma_fix ζ hζp))
  have hζ' : IsPrimitiveRoot χ p := by
    refine IsPrimitiveRoot.of_map_of_injective (f := Units.map (k.subtype : ↥k →* K)) ?_
      (Units.map_injective k.subtype.injective)
    rw [hχ]
    exact hζ
  exact MSide.of_SL2Torus hSL hp ⟨χ, hζ'⟩ hkcard h4 hD

end Main

end CFSG.RankThree.PartOne.KLAY
