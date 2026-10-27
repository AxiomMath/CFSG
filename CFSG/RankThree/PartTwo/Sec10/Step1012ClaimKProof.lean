module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofStatements
import CFSG.RankThree.PartTwo.Sec12.Item122
import CFSG.RankThree.PartTwo.Sec4.Item426RestSetup
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step1012ClaimKM3 : Prop :=
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
      ∀ x ∈ Subgroup.centralizer (S : Set G) ⊓
          Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G),
        x ^ 3 = 1 → x ∈ Subgroup.zpowers a

@[expose] def Step1012ClaimKd : Prop :=
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
      ∃ K ∈ thetaComponentsIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)),
        (Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
        d ∈ K

namespace Step1012ClaimKProof

section General

variable {G : Type} [Group G] [Finite G]

theorem pCore_center_eq_zpowers {K : Subgroup G} {d : G}
    (hKd : K ≤ Subgroup.centralizer ({d} : Set G)) (hdK : d ∈ K) (hd3 : orderOf d = 3)
    (hZK : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3) :
    inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := K ⊓ Subgroup.centralizer (K : Set G) with hZ
  set P := inSubgroup (CFSG.pCore 3) Z with hP
  have hdC : d ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKd hk)
  have hdZ : d ∈ Z := ⟨hdK, hdC⟩
  have hZcomm : ∀ x y : Z, x * y = y * x := fun x y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2.2 x x.2.1)
  have hdP : d ∈ P := by
    refine ⟨⟨d, hdZ⟩, ?_, rfl⟩
    have hN : (Subgroup.zpowers (⟨d, hdZ⟩ : Z)).Normal :=
      ⟨fun n hn g => by rw [hZcomm g n, mul_inv_cancel_right]; exact hn⟩
    have hp : IsPGroup 3 (Subgroup.zpowers (⟨d, hdZ⟩ : Z)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hd3, pow_one])
    exact (le_sSup ⟨hN, hp⟩ : Subgroup.zpowers _ ≤ CFSG.pCore 3 Z) (Subgroup.mem_zpowers _)
  have hP3 : Nat.card P ≤ 3 := by
    have hPK : P ≤ K := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2.1
    have hPC : P ≤ Subgroup.centralizer (K : Set G) := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2.2
    set P' := P.subgroupOf K with hP'
    have hP'card : Nat.card P' = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    have hP'3 : IsPGroup 3 P' :=
      (Sec4.Item426Rest.isPGroup_pCore_center K).of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
    have hinj := injOn_mk_of_isPGroup Nat.prime_three hP'3
    let f : P' → Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := fun p =>
      ⟨QuotientGroup.mk' _ (p : K), by
        rw [Subgroup.mem_center_iff]
        intro q
        induction q using QuotientGroup.induction_on with
        | H k =>
          rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPC p.2) k k.2)⟩
    have hf : Function.Injective f := fun p q hpq =>
      Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val hpq))
    calc Nat.card P = Nat.card P' := hP'card.symm
      _ ≤ Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) :=
        Nat.card_le_card_of_injective f hf
      _ = 3 := hZK
  symm
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdP)
    (by rw [Nat.card_zpowers, hd3]; exact hP3)

end General

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

end Step1012ClaimKProof

open Step1012ClaimKProof in
theorem step1012ClaimK_of (hM3 : Step1012ClaimKM3) (hKd : Step1012ClaimKd) :
    Step1012ClaimK := by
  intro h45 h97 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc V
    hV2 hVA hVS hVB hVθU hVS' hVθ hauto
  have hm3 := hM3 h45 h97 G A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd
    hwc V hV2 hVA hVS hVB hVθU hVS' hVθ hauto
  obtain ⟨K, hK, htype, hdK⟩ := hKd h45 h97 G A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab
    w hwA hwS hwa hwd hwc V hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  refine ⟨K, hK, htype, ?_⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hKd' : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hkB := (mem_thetaComponentsIn_iff.mp hK).1 hk
    rw [Subgroup.mem_centralizer_iff] at hkB
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hkB d (Subgroup.subset_closure (by simp))).symm
  have hZK : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3 := by
    rcases htype with h4 | h6
    · exact Sec12.card_center_eq_three_of_isSLThreePi ⟨4, h4⟩
    · exact h6.1
  rw [pCore_center_eq_zpowers hKd' hdK hd3 hZK]
  refine ⟨fun hb => hd1 ?_, ?_⟩
  · rw [← Subgroup.mem_bot, ← hb]
    exact Subgroup.mem_zpowers d
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx

end CFSG.RankThree.PartTwo.Sec10
