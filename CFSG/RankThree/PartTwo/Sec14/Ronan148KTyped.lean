module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KSub
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KMult
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KTypes
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (descAut descAut_eq_one_iff)

theorem type429_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : Main148.Type429 Y) : Main148.Type429 X := by
  rcases h with ⟨p, e, hp, he, hiso⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact Or.inl ⟨p, e, hp, he, Main148.isoLThreePi_congr φ.symm hiso⟩
  · exact Or.inr (Or.inl ⟨φ.trans ψ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨φ.trans ψ⟩)))

theorem center_eq_of_le_of_center_quotient_eq_bot {K : Type*} [Group K] {N : Subgroup K}
    [N.Normal] (hN : N ≤ Subgroup.center K) (hZ : Subgroup.center (K ⧸ N) = ⊥) :
    Subgroup.center K = N := by
  refine le_antisymm (fun z hz => ?_) hN
  have hz' : (QuotientGroup.mk z : K ⧸ N) ∈ Subgroup.center (K ⧸ N) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    induction y using QuotientGroup.induction_on with
    | H y => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hz y]
  rw [hZ, Subgroup.mem_bot] at hz'
  exact (QuotientGroup.eq_one_iff z).mp hz'

theorem isQuasisimple_of_quotient_center {K T : Type*} [Group K] [Group T]
    (hKp : Group.IsPerfect K) (e : K ⧸ Subgroup.center K ≃* T) (hT : IsSimpleGroup T)
    (hnc : ∃ a b : T, a * b ≠ b * a) : IsQuasisimple K := by
  haveI : IsSimpleGroup T := hT
  refine ⟨hKp, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem pCore_two_eq_center {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (h2 : IsPGroup 2 (Subgroup.center K)) : CFSG.pCore 2 K = Subgroup.center K :=
  le_antisymm (Sec4.RonanK429.pCore_two_le_center hK)
    (le_sSup ⟨Subgroup.normal_of_characteristic _, h2⟩)

theorem theta_eq_bot_of_le_of_normalizer {Γ : Type} [Group Γ] [Finite Γ] {C L : Subgroup Γ}
    (hCθ : aschbacherSolvableCore 3 ↥C = ⊥) (hLC : L ≤ C) (hLq : IsQuasisimple ↥L)
    (hLn : C ≤ Subgroup.normalizer (L : Set Γ)) : aschbacherSolvableCore 3 ↥L = ⊥ := by
  let eL : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have hL'n : (L.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hLn
  have hL' : IsComponent (L.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq, hL'n.isSubnormal⟩
  have h1 := Sec4.RonanK429.theta_eq_bot_of_isComponent hCθ hL'
  rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL, h1,
    Subgroup.map_bot]

theorem false_of_faithful_e9_l32 {Γ : Type} [Group Γ] [Finite Γ] {A K : Subgroup Γ} {c : Γ}
    (hKp : Group.IsPerfect ↥K) (hAK : A ≤ Subgroup.normalizer (K : Set Γ)) (hA : Late.IsE27 A)
    (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K : Set Γ))
    (φ : ↥K ⧸ Subgroup.center ↥K ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1)) : False := by
  set ι := (descAut K).comp (Subgroup.inclusion hAK) with hι
  have hker : ∀ a : ↥A, ι a = 1 ↔ (a : Γ) ∈ Subgroup.zpowers c := by
    intro a
    rw [hι, MonoidHom.comp_apply, descAut_eq_one_iff hKp, hcent]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hc3 : orderOf c = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA3 c hcA) hc1
  have hcard : Nat.card ι.range = 9 := by
    have hzA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    have hker' : ι.ker = (Subgroup.zpowers c).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
    have hk3 : Nat.card ι.ker = 3 := by
      rw [hker', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers,
        hc3]
    have h1 := Subgroup.card_mul_index ι.ker
    rw [Subgroup.index_ker, hk3, hA.2] at h1
    omega
  have hexp : ∀ y ∈ ι.range, y ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hA3 a a.2), map_one]
  exact false_of_e9_le_mulAut_l32 φ ι.range hcard hexp

section Main

theorem kf148ThetaTyped_of (h429 : Sec4.Item4_29) (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF148ThetaTyped := by
  intro Γ _ _ C hC4 hCθ hCE A L K c hAC hLC hA hcA hc1 hLq hLn hLc hK hAK hcent hθZ hT
  have hKLc : K ≤ L ⊓ Subgroup.centralizer {c} := le_of_mem_thetaComponentsIn hK
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal :=
    (mem_thetaComponentsIn_iff.mp hK).2.2.1
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hTp : Group.IsPerfect (↥K ⧸ aschbacherSolvableCore 3 ↥K) := hKq.1
  obtain ⟨hTs, hTnc⟩ := isSimpleGroup_of_type148 hTp hT
  have hTZ : Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) = ⊥ :=
    center_eq_bot_of_type148 hTp hT
  have hZθ : Subgroup.center ↥K = aschbacherSolvableCore 3 ↥K :=
    center_eq_of_le_of_center_quotient_eq_bot hθZ hTZ
  let eZ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
    QuotientGroup.quotientMulEquivOfEq hZθ
  have hKqs : IsQuasisimple ↥K := isQuasisimple_of_quotient_center hKp eZ hTs hTnc
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
    rw [hZθ]
    exact (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  suffices hZ : Subgroup.center ↥K = ⊥ by rw [← hZθ]; exact hZ
  rcases type148_wrongSign_or_type429 hT with h429T | ⟨p, f, hp, hp3, hf, hW⟩
  ·
    have h2 : IsPGroup 2 (Subgroup.center ↥K) :=
      isPGroup_two_center_of_type429 hGA hKqs eZ h429T hZ3
    have hO2 : CFSG.pCore 2 ↥K = Subgroup.center ↥K := pCore_two_eq_center hKqs h2
    let e2 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hO2).trans eZ
    have htype : Main148.Type429 (↥K ⧸ CFSG.pCore 2 ↥K) := type429_of_mulEquiv e2 h429T
    rcases item4_29_of_le_quasi h429 C hC4 hCθ hCE hAC hLC hA hcA hc1 hLq hLn hKLc hKqs hKsub
        htype hcent with hKL | ⟨⟨φ⟩⟩ | ⟨n, hn, hK2⟩
    ·
      rw [hZθ]
      subst hKL
      exact theta_eq_bot_of_le_of_normalizer hCθ hLC hLq hLn
    ·
      exact Sec4.RonanK429.center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2
    ·
      haveI := hKp
      haveI : Nontrivial ↥K := by
        haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hKqs.2.1.toNontrivial
        exact (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
      exact Sec4.RonanK429.center_eq_bot_of_isoLThreePi hn hK2
  · rcases hW with ⟨hq, ⟨φ⟩⟩ | ⟨hq, hq2, ⟨φ⟩⟩
    · by_cases hq2 : p ^ f = 2
      ·
        exfalso
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
          (hq2 ▸ dvd_pow_self p (by omega : f ≠ 0))
        subst hp2
        have hf1 : f = 1 := Nat.pow_right_injective (le_refl 2) (hq2.trans (pow_one 2).symm)
        subst hf1
        exact false_of_faithful_e9_l32 hKp hAK hA hcA hc1 hcent (eZ.trans φ)
      · exact center_eq_bot_of_wrong_sign_sl hGA hKqs hf hq hq2 (eZ.trans φ)
    · exact center_eq_bot_of_wrong_sign_su hGA hKqs hf hq hq2 (eZ.trans φ)

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
