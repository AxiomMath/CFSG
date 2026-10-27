module

public import CFSG.RankThree.PartOne.U5E.InnLayerP5
public import CFSG.RankThree.PartOne.K159.CompGenFive

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K

variable {G : Type} [Group G] [Finite G]

theorem thetaComponentsAt_empty (hEin : U5EInndiag) (hPerf : K159.KFPerfNormalizerFive)
    (hLR5 : S15K.LayerRowFive) (hGen : K159.KFCompGenFive) (hAt : KFU5At) {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E)) {e : G}
    (heE : e ∈ E) (he1 : e ≠ 1) (hN : ∀ t ∈ reflectionSet p E, e ∉ autFixedInG E t)
    (hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) :
    ∀ Z : Subgroup G, Z ∉ thetaComponentsAt p e := by
  classical
  intro Z hZ
  have h := h15.h12
  have hp := h.prime
  obtain ⟨f, hf, hpf, ⟨e₀⟩, -, hcardE, -⟩ := id hout
  have hZI : Z ≤ lieGenerated p E :=
    U5E.thetaComponents_le_lieGenerated hEin hPerf h15 hF hout hLN Z hZ
  set I := lieGenerated p E with hI
  have hLD : S15K.LayerDataW p E I := hLR5 G p A c L E h15 hF hout
  obtain ⟨ι, Q, hQH, hQc, hperf, -⟩ := hLD e heE he1
  have hempty : {x : G | ∃ t ∈ reflectionSet p E, ∃ K : Subgroup G, IsKt p E t K ∧
      K ≤ Subgroup.centralizer ({e} : Set G) ∧ x ∈ K} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨t, ht, K, hK, hKC, -⟩ := hx
    have hAtt : KFAt p E f t := hAt G p A c L E f h15 hF hout hf hpf ⟨e₀⟩ t ht
    have hKeq : K = kZero p E t := (isKt_iff_of_nonexceptional hAtt.1).1 hK
    have : e ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
      refine ⟨heE, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      rw [← hKeq] at hk
      exact Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
    rw [hAtt.2.2.1] at this
    exact hN t ht this
  have hQbot : ∀ i, Q i ≤ ⊥ := fun i => by
    have := hGen G p A c L E h15 hF hout e heE he1 (Q i) (hQH i) (hQc i)
    rwa [hempty, Subgroup.closure_empty] at this
  have hY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      Group.IsPerfect ↥P → P ≤ ⊥ := fun P hP hPperf =>
    (hperf P hP hPperf).trans (iSup_le hQbot)
  have hZbot : Z ≤ ⊥ :=
    hY₀ Z (le_inf hZI (mem_thetaComponentsAt_iff.1 hZ).1) (isPerfect_of_mem_thetaComponentsAt hZ)
  have hZne : Z.subgroupOf (Subgroup.centralizer ({e} : Set G)) ≠ ⊥ := by
    intro hbot
    have hY := (mem_thetaComponentsAt_iff.1 hZ).2
    rw [hbot] at hY
    obtain ⟨-, -, a, b, hab⟩ := hY.2.2
    have : Subsingleton (↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G)))) := inferInstance
    have hs : Subsingleton (↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G))) ⧸
        aschbacherSolvableCore p ↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G)))) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
    have hs' : Subsingleton ((↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G))) ⧸
        aschbacherSolvableCore p ↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G)))) ⧸
        Subgroup.center (↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G))) ⧸
        aschbacherSolvableCore p ↥(⊥ : Subgroup ↥(Subgroup.centralizer ({e} : Set G))))) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
    exact hab (Subsingleton.elim _ _)
  apply hZne
  rw [le_bot_iff.1 hZbot]
  exact Subgroup.bot_subgroupOf _

end CFSG.RankThree.PartOne.K1510R
