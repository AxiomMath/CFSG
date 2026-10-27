module

public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3ProofCover

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KS1012CoverThree : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ (C : Subgroup E) [C.Normal],
    Group.IsSolvable C → ∀ Z : Subgroup E, Z ≤ Subgroup.center E → Nat.card Z ∣ 3 →
    (∀ x ∈ C, x ^ 3 = 1 → x ∈ Z) →
    (Sec4.IsSLThreePiAt (E ⧸ C) 4 ∨ Sec4.IsTripleCover (E ⧸ C) (alternatingGroup (Fin 6))) →
    ¬ 3 ∣ Nat.card C

@[expose] def Step1012KAutSolv : Prop :=
  Sec4.Item4_5 → Sec9.Item97 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ∀ S ∈ maxInvariantPiSubgroups
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
        sec10U L a ≤ S → S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a →
        S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ → IsMulCommutative S →
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) →
        w * a * w⁻¹ = a → w * d * w⁻¹ = d → w * c * w⁻¹ = c * d →
      ∀ V : Subgroup G, IsPGroup 2 V → A ≤ Subgroup.normalizer (V : Set G) →
        V ≤ Subgroup.normalizer (S : Set G) →
        V ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) →
        V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (sec10U L a : Set G)) →
        ¬ V ≤ Subgroup.centralizer (S : Set G) →
        ¬ V ≤ inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) →
      (Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
        Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
          (alternatingGroup (Fin 6))) →
      (∀ x ∈ Subgroup.centralizer (S : Set G) ⊓
          Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G),
        x ^ 3 = 1 → x ∈ Subgroup.zpowers a) →
      ∃ J : Subgroup G,
        J ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (S : Set G) ∧
        Group.IsPerfect J ∧
        Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (J : Set G) ∧
        inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S) ≤
          Sec4.autIn J S ∧
        Group.IsSolvable (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G)

open Item1012Res3Proof in
theorem step1012KAutJ_of_solv (hK : KS1012CoverThree) (hSol : Step1012KAutSolv) :
    Step1012KAutJ := by
  intro h45 h97 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc V
    hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  obtain ⟨J, hJN, hJperf, hJnorm, hJcov, hJs⟩ := hSol h45 h97 G A c L a R h d hdL hUθ hUmax S hS
    hUS hSc hSd hSab w hwA hwS hwa hwd hwc V hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  refine ⟨J, hJN, hJperf, hJnorm, hJcov, hJs, ?_⟩
  set H := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hHdef
  set P := inSubgroup perfectResidual (Sec4.autIn H S) with hPdef
  have hJH : J ≤ H := hJN.trans inf_le_left
  have hJS : J ≤ Subgroup.normalizer (S : Set G) := hJN.trans inf_le_right
  have hJP : Sec4.autIn J S = P := le_antisymm (autIn_le_perfectResidual hJH hJS hJperf) hJcov
  set C := (J ⊓ Subgroup.centralizer (S : Set G)).subgroupOf J with hCdef
  have hCmem : ∀ j : J, j ∈ C ↔ (j : G) ∈ Subgroup.centralizer (S : Set G) := fun j =>
    ⟨fun hj => (Subgroup.mem_subgroupOf.mp hj).2, fun hj => Subgroup.mem_subgroupOf.mpr ⟨j.2, hj⟩⟩
  have hCn : C.Normal := ⟨fun j hj g => by
    rw [hCmem] at hj ⊢
    have hgN : (g : G) ∈ Subgroup.normalizer
        ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
      Sec10XSteps.normalizer_le_normalizer_centralizer_of (hJS g.2)
    simpa using (Subgroup.mem_normalizer_iff.mp hgN _).mp hj⟩
  set eC : C ≃* (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe inf_le_left with heC
  have hCs : Group.IsSolvable C :=
    Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
  set Z := (Subgroup.zpowers a).subgroupOf J with hZdef
  have hZc : Z ≤ Subgroup.center J := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hga : (g : G) * a = a * g :=
      (Step1012ClaimProof.mem_centralizer_closure_pair_iff.mp (hJH g.2)).1
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact ((show Commute (g : G) a from hga).zpow_right k).eq
  have hZ3 : Nat.card Z ∣ 3 := by
    let ι : Z →* Subgroup.zpowers a :=
      { toFun := fun z => ⟨((z : J) : G), Subgroup.mem_subgroupOf.mp z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun z z' hzz' => by
      have h1 : ((ι z : Subgroup.zpowers a) : G) = ((ι z' : Subgroup.zpowers a) : G) :=
        congrArg Subtype.val hzz'
      exact Subtype.ext (Subtype.ext h1)
    refine (Subgroup.card_dvd_of_injective ι hι).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (h.pow_three h.a_mem)
  have hC3 : ∀ x ∈ C, x ^ 3 = 1 → x ∈ Z := by
    intro x hx hx3
    exact Subgroup.mem_subgroupOf.mpr
      (hm3 _ ⟨(hCmem x).mp hx, hJH x.2⟩ (by simpa using congrArg Subtype.val hx3))
  set ξ₀ : J →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hJS) with hξ₀
  have hξ₀P : ∀ j : J, ξ₀ j ∈ P := fun j => by
    rw [← hJP]
    exact Sec4.mem_autIn_iff.mpr ⟨j, hJS j.2, j.2, rfl⟩
  set ξ : J →* P := ξ₀.codRestrict P hξ₀P with hξ
  have hξs : Function.Surjective ξ := by
    rintro ⟨σ, hσ⟩
    have hσ' := hσ
    rw [← hJP] at hσ'
    obtain ⟨j, hjN, hjJ, hj⟩ := Sec4.mem_autIn_iff.mp hσ'
    exact ⟨⟨j, hjJ⟩, Subtype.ext hj⟩
  have hker : ξ.ker = C := by
    ext j
    rw [MonoidHom.mem_ker, hCmem]
    constructor
    · intro h1
      have h2 : S.normalizerMonoidHom ⟨(j : G), hJS j.2⟩ = 1 := congrArg Subtype.val h1
      have h3 := (MonoidHom.mem_ker).mpr h2
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
      exact h3
    · intro h1
      apply Subtype.ext
      change S.normalizerMonoidHom ⟨(j : G), hJS j.2⟩ = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact h1
  have e : J ⧸ C ≃* P := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ξ hξs)
  have h3 := hK J hJperf C hCs Z hZc hZ3 hC3 (type_of_mulEquiv e.symm hauto)
  rwa [Nat.card_congr eC.toEquiv] at h3

theorem step1012ClaimKd_of_solv (hK : KS1012CoverThree) (hSol : Step1012KAutSolv) :
    Step1012ClaimKd :=
  step1012ClaimKd_of_autJ (step1012KAutJ_of_solv hK hSol)

end CFSG.RankThree.PartTwo.Sec10
