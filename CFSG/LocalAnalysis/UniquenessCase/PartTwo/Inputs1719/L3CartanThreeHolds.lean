module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFactsSmallRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418IndexTwo
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSL
public import CFSG.HardMathSupport.Solomon.Proving.HopfLiftPrime
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3M
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Eight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PerfectCover
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.D42 (dHom_injective dHom_mem_upperTriangular)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open TauCeti.Subgroup (normalizerQuotient)

noncomputable def l3ThreeTorus (F : Type) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
  ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F)).map (dHom (k := F))

theorem l3ThreeTorus_le_upperTriangular {F : Type} [Field F] :
    l3ThreeTorus F ≤ upperTriangular 3 F := by
  rintro _ ⟨p, -, rfl⟩
  exact dHom_mem_upperTriangular p

theorem l3ThreeTorus_pow_three {F : Type} [Field F] {x : Matrix.SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ l3ThreeTorus F) : x ^ 3 = 1 := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hp1 : p.1 ^ 3 = 1 := (mem_rootsOfUnity 3 p.1).mp hp.1
  have hp2 : p.2 ^ 3 = 1 := (mem_rootsOfUnity 3 p.2).mp hp.2
  rw [← map_pow]
  have hp3 : p ^ 3 = 1 := by
    apply Prod.ext
    · simpa using hp1
    · simpa using hp2
  rw [hp3, map_one]

theorem isElemAbelian_l3ThreeTorus {F : Type} [Field F] :
    IsElemAbelian 3 (l3ThreeTorus F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨p, hp, hpa⟩ := a.2
    obtain ⟨q, hq, hqa⟩ := b.2
    change ((a : Matrix.SpecialLinearGroup (Fin 3) F) *
        (b : Matrix.SpecialLinearGroup (Fin 3) F)) =
      ((b : Matrix.SpecialLinearGroup (Fin 3) F) *
        (a : Matrix.SpecialLinearGroup (Fin 3) F))
    rw [← hpa, ← hqa, ← map_mul, ← map_mul, mul_comm]
  · intro x hx
    exact l3ThreeTorus_pow_three hx

theorem exists_sl3_cover
    {K : Type} [Group K] [Finite K] {f : ℕ}
    (hadm : StatedLieAdmissible .PSL 3 2 f) (hf : Even f)
    (hL : LieModel (K ⧸ Subgroup.center K) .PSL 3 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ α : Matrix.SpecialLinearGroup (Fin 3) F →* K,
        Function.Surjective α ∧
          α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFin, hF, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  refine ⟨F, hField, hFin, hF, ?_⟩
  by_cases hf2 : f = 2
  ·
    subst hf2
    have hM48 : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = 48 := by
      obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four
        (K ⧸ Subgroup.center K) hL
      rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd,
        Nat.card_prod, Nat.card_prod]
      norm_num
    have hdvd48 : Nat.card (Subgroup.center K) ∣ 48 := by
      have hq' : CFSG.IsQuasisimple K :=
        CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.isQuasisimple_of_open hq
      have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier
        (X := K ⧸ Subgroup.center K) hq' (MulEquiv.refl _)
      rwa [hM48] at h
    have hdvd3 : Nat.card (Subgroup.center K) ∣ 3 := by
      have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) (2 ^ 4) :=
        Nat.Coprime.pow_right 4 (Odd.coprime_two_right hodd)
      have hdvd' : Nat.card (Subgroup.center K) ∣ 3 * 2 ^ 4 := by
        rw [show 3 * 2 ^ 4 = 48 by norm_num]
        exact hdvd48
      exact hcop.dvd_of_dvd_mul_right hdvd'
    have hEp : IsPGroup 3 (Subgroup.center K) := by
      rw [isPGroup_iff_card_dvd_pow]
      exact ⟨1, by simpa using hdvd3⟩
    have hSL3perf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
      CFSG.LinearGroups.special_linear_isPerfect (n := 3) (by norm_num) (Or.inl (by norm_num))
    have hKperf : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
    have hk₀ : (proj 3 F).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [ker_proj, scalars_eq_center]
    let q : K →* projectiveSL 3 F :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
    have hqsurj : Function.Surjective q :=
      e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hqker : q.ker = Subgroup.center K := by
      apply le_antisymm
      · intro x hx
        have h1 : e (QuotientGroup.mk' (Subgroup.center K) x) = 1 := hx
        have h2 : QuotientGroup.mk' (Subgroup.center K) x = 1 := e.injective (by simpa using h1)
        exact (QuotientGroup.eq_one_iff x).1 h2
      · intro x hx
        rw [MonoidHom.mem_ker]
        show e (QuotientGroup.mk' (Subgroup.center K) x) = 1
        have h1 : QuotientGroup.mk' (Subgroup.center K) x = 1 := by
          simpa using (QuotientGroup.eq_one_iff x).2 hx
        rw [h1, map_one]
    have hEp' : IsPGroup 3 q.ker := by
      rw [hqker]
      exact hEp
    have hker3 : Nat.card (proj 3 F).ker = 3 := by
      rw [ker_proj, CFSG.Quasithin.H13.P31X.l3_card_scalars, hF]
      norm_num
    have hcardSL : Nat.card (hopfMultiplier (projectiveSL 3 F)) = 48 := by
      rw [← CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr e, hM48]
    have hcard : Nat.card (hopfMultiplier (projectiveSL 3 F)) =
        Nat.card (proj 3 F).ker * 16 := by
      rw [hcardSL, hker3]
    obtain ⟨α, hαsurj, hαeq⟩ :=
      CFSG.HardMathSupport.Solomon.Proving.exists_lift_of_coprime_index
        (p := 3) hSL3perf hKperf (proj 3 F) (proj_surjective 3 F) hk₀ q hqsurj hqker.le hEp'
        16 (by norm_num) hcard
    refine ⟨α, hαsurj, ?_⟩
    intro x hx
    have h1 : (proj 3 F) x = 1 := by
      have h := congrArg
        (fun g : Matrix.SpecialLinearGroup (Fin 3) F →* projectiveSL 3 F => g x) hαeq
      simp only [MonoidHom.comp_apply] at h
      rw [show α x = 1 from hx, map_one] at h
      exact h.symm
    have h1' : x ∈ (proj 3 F).ker := MonoidHom.mem_ker.2 h1
    rwa [ker_proj, scalars_eq_center] at h1'

  ·
    have hf4 : 4 ≤ f := by
      obtain ⟨k, hk⟩ := hf
      have h1 : 1 ≤ f := hadm.2.1
      omega
    have hK5 : 5 ≤ Nat.card F := by
      rw [hF]
      calc 5 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_slCover
      (m := 2) (by norm_num) hK5 hq e

theorem le_pRank_cartan_of_sl3_cover {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : Even f)
    {K : Type} [Group K] [Finite K]
    (α : Matrix.SpecialLinearGroup (Fin 3) F →* K) (hαsurj : Function.Surjective α)
    (hαker : α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    (if 3 ∣ Nat.card (Subgroup.center K) then 2 else 1) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (normalizerQuotient
        ((unitriangular 3 F).map α))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_charP_two (n := f) hF
  have hSL3perf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (n := 3) (by norm_num) (Or.inl (by norm_num))
  have hZ3 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [← scalars_eq_center, CFSG.Quasithin.H13.P31X.l3_card_scalars, hF]
    exact Nat.gcd_eq_left (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xo_three_dvd_sub_one hf)
  have hcenter_map : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)).map α =
      Subgroup.center K :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel α hαsurj hαker
  let ψ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) →* Subgroup.center K :=
    { toFun := fun x => ⟨α (x : Matrix.SpecialLinearGroup (Fin 3) F),
        hcenter_map ▸ Subgroup.mem_map_of_mem α x.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun x y => Subtype.ext (map_mul α
        (x : Matrix.SpecialLinearGroup (Fin 3) F)
        (y : Matrix.SpecialLinearGroup (Fin 3) F)) }
  have hψrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : K) ∈ (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)).map α := by
      rw [hcenter_map]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hψker : Nat.card ψ.ker =
      Nat.card α.ker := by
    have hker_eq : ψ.ker =
        α.ker.subgroupOf (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
      ext x
      simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hαker).toEquiv
  have hrel : Nat.card α.ker * Nat.card (Subgroup.center K) = 3 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, Subgroup.card_top, hψker, hZ3] at h
    exact h
  have hαker_dvd : Nat.card α.ker ∣ 3 := ⟨Nat.card (Subgroup.center K), hrel.symm⟩
  have hZ_dvd : Nat.card (Subgroup.center K) ∣ 3 :=
    ⟨Nat.card α.ker, by rw [mul_comm]; exact hrel.symm⟩
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) 2 (n := 3) (by norm_num)
  have hUsyl : IsSylowTwoOf (unitriangular 3 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hUp : IsPGroup 2 (unitriangular 3 F) := hUsyl.2.1
  have hSp : IsPGroup 2 ((unitriangular 3 F).map α) := hUp.map α
  have hSsyl : IsSylowTwoOf ((unitriangular 3 F).map α) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hUsyl α hαsurj
  have hTcard : Nat.card (l3ThreeTorus F) = 9 := by
    rw [l3ThreeTorus, Subgroup.card_map_of_injective (f := dHom (k := F)) dHom_injective,
      Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity 3 F) (rootsOfUnity 3 F)).toEquiv,
      Nat.card_prod]
    have hmu : Nat.card (rootsOfUnity 3 F) = 3 := by
      let : Fintype F := Fintype.ofFinite F
      rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd,
        Fintype.card_eq_nat_card, hF]
      exact Nat.gcd_eq_left
        (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xo_three_dvd_sub_one hf)
    rw [hmu]
  have hTelem : IsElemAbelian 3 (l3ThreeTorus F) := isElemAbelian_l3ThreeTorus
  have hTnorm : l3ThreeTorus F ≤
      Subgroup.normalizer (unitriangular 3 F : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular]
    exact l3ThreeTorus_le_upperTriangular
  have hTN : (l3ThreeTorus F).map α ≤
      Subgroup.normalizer (((unitriangular 3 F).map α : Subgroup K) : Set K) :=
    (Subgroup.map_mono hTnorm).trans (Subgroup.le_normalizer_map α)
  have hle : (if 3 ∣ Nat.card (Subgroup.center K) then 2 else 1) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (normalizerQuotient
        ((unitriangular 3 F).map α))) := by
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center K)
    ·
      have hZ : Nat.card (Subgroup.center K) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hZ_dvd with h | h
        · rw [h] at h3
          norm_num at h3
        · exact h
      have hker1 : Nat.card α.ker = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hαker_dvd with h | h
        · exact h
        · rw [h, hZ] at hrel
          norm_num at hrel
      have hinj : Function.Injective α := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact Subgroup.eq_bot_of_card_eq _ hker1
      have hcardTmap : Nat.card ((l3ThreeTorus F).map α) = 3 ^ 2 := by
        rw [Subgroup.card_map_of_injective (f := α) hinj, hTcard]
        norm_num
      have h := le_pRank_normalizerQuotient_of_le_normalizer
        (ℓ := 3) (k := 2) Nat.prime_three (by norm_num) hSp hTN (hTelem.map α) hcardTmap
      rw [if_pos h3]
      exact h.1
    ·
      have hZ : Nat.card (Subgroup.center K) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hZ_dvd with h | h
        · exact h
        · exact absurd (by rw [h]) h3
      have hker3 : Nat.card α.ker = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hαker_dvd with h | h
        · rw [h] at hrel
          have hZ3 : Nat.card (Subgroup.center K) = 3 := by omega
          exact absurd (by rw [hZ3]) h3
        · exact h
      obtain ⟨ζ, hζ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_zeta
        (p := 3) Nat.prime_three (by rw [hF]; exact
          CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xo_three_dvd_sub_one hf)
      let x : Matrix.SpecialLinearGroup (Fin 3) F := dHom (k := F) (ζ, (1 : Fˣ))
      have hζ3 : ζ ^ 3 = 1 := by
        simpa [hζ] using pow_orderOf_eq_one ζ
      have hx3 : x ^ 3 = 1 := by
        have hpair : (ζ, (1 : Fˣ)) ^ 3 = 1 := by
          apply Prod.ext
          · simpa using hζ3
          · simp
        have hmap : dHom (k := F) ((ζ, (1 : Fˣ)) ^ 3) = 1 := by
          rw [hpair, map_one]
        rw [show x = dHom (k := F) (ζ, (1 : Fˣ)) from rfl, ← map_pow]
        exact hmap
      have hxupper : x ∈ upperTriangular 3 F := dHom_mem_upperTriangular (ζ, (1 : Fˣ))
      have hxcenter : x ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
        intro hx
        rw [← scalars_eq_center] at hx
        obtain ⟨c, -, hc⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars).1 hx
        have h00 := congrFun (congrFun hc 0) 0
        have h11 := congrFun (congrFun hc 1) 1
        simp only [x, coe_dHom, coe_dSL, Matrix.diagonal_apply_eq, Matrix.scalar_apply,
          Fin.isValue] at h00 h11
        have hζ1 : ζ = 1 := Units.ext (h00.trans h11.symm)
        rw [hζ1, orderOf_one] at hζ
        norm_num at hζ
      have hxker : x ∉ α.ker := fun hx => hxcenter (hαker hx)
      have hxN : x ∈ Subgroup.normalizer
          (unitriangular 3 F : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular]
        exact hxupper
      have hαxN : α x ∈ Subgroup.normalizer
          (((unitriangular 3 F).map α : Subgroup K) : Set K) :=
        Subgroup.le_normalizer_map α ⟨x, hxN, rfl⟩
      have hαx3 : (α x) ^ 3 = 1 := by
        rw [← map_pow, hx3, map_one]
      have hαx1 : α x ≠ 1 := fun h => hxker (MonoidHom.mem_ker.2 h)
      have horder : orderOf (α x) = 3 := orderOf_eq_prime hαx3 hαx1
      have hcardZ : Nat.card (Subgroup.zpowers (α x)) = 3 ^ 1 := by
        rw [Nat.card_zpowers, horder]
        norm_num
      have hE : IsElemAbelian 3 (Subgroup.zpowers (α x)) :=
        CFSG.Open.isElemAbelian_zpowers (p := 3) hαx3
      have hEN : Subgroup.zpowers (α x) ≤ Subgroup.normalizer
          (((unitriangular 3 F).map α : Subgroup K) : Set K) :=
        Subgroup.zpowers_le.mpr hαxN
      have h := le_pRank_normalizerQuotient_of_le_normalizer
        (ℓ := 3) (k := 1) Nat.prime_three (by norm_num) hSp hEN hE hcardZ
      rw [if_neg h3]
      exact h.1
  exact hle

theorem k_L3CartanThree_holds :
    K_L3CartanThree := by
  intro K _ _ f hadm hf hL hq hodd S hS
  obtain ⟨F, hField, hFin, hF, α, hαsurj, hαker⟩ :=
    exists_sl3_cover hadm hf hL hq hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_charP_two (n := f) hF
  have hmain := le_pRank_cartan_of_sl3_cover (K := K) hF hf α hαsurj hαker
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) 2 (n := 3) (by norm_num)
  have hUsyl : IsSylowTwoOf (unitriangular 3 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hSsyl : IsSylowTwoOf ((unitriangular 3 F).map α) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hUsyl α hαsurj
  obtain ⟨eN⟩ :=
    normalizerQuotient_equiv_of_isSylowTwoOf
      (MulEquiv.refl K) hSsyl hS
  have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eN
  rw [hEq] at hmain
  have hcoeeq : CFSG.pRank 3 ↥(⊤ : Subgroup (normalizerQuotient S)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (normalizerQuotient S)) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 _).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
  rw [hcoeeq]
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
