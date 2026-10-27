module

public import CFSG.RankThree.PartOne.N143.CaseB1
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}

theorem caseM_false {Q : (X : Type) → [Group X] → Prop} (hSchreier : SchreierFor InCatalog)
    (h613 : Item613With Q) (h64W : KF64WWith Q)
    (hJ : JFacts) (hpair : KF134Pair) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (hcard : Nat.card (reflectionGroup p A) = 54) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    (M : Subgroup G) (hMtop : M ≠ ⊤) (hJM : ∀ J ∈ thetaCompZeroStarE p A, J ≤ M) (hAM : A ≤ M) :
    False := by
  classical
  have hp : p.Prime := hctx.hyp.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le hctx.hyp
  have hp3 : 3 < p := by omega
  obtain ⟨k, hk1, hk3, -⟩ := hspec.z_scalar
  have hp7 : 7 ≤ p := seven_le_of_cube_root hp hp5 hk1 hk3
  have hJ' := hJ
  obtain ⟨-, -, -, -, -, hKt1, -, -⟩ := hJ'
  have hmods := models_at hKt1 hctx hpair hgood hf hm
  have hMK : CFSG.IsKGroup ↥M := hctx.hyp.setup.2.2.1 M hMtop
  have hMe : evenRank ↥M ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans hctx.hyp.evenRank_eq.le
  have hemb : ∀ J ∈ thetaCompZeroStarE p A, ∃ K ∈ thetaComponents p ↥M, J.subgroupOf M ≤ K := by
    intro J hJF
    obtain ⟨c', hJg⟩ := hgood J hJF
    have hcM : c' ∈ M := hAM hJg.hyp.c_mem
    have hres := restrict_thetaComponentsAt hp hcM (hJg.hyp.L_mem).2 (hJM J hJF)
    have hxord : orderOf (⟨c', hcM⟩ : ↥M) = p := by
      rw [← Subgroup.orderOf_coe]
      exact Sec12Three.orderOf_c hJg.hyp
    exact local_theta_component_embedding_frontier hSchreier ↥M hMK hMe p hp hp3 ⟨c', hcM⟩ hxord
      _ hres
  choose! Kf hKmem hKle using hemb
  have hmoved : ∀ t ∈ reflectionSet p A, Nat.card (autMovedInG A t) = p := fun t ht =>
    (hctx.facts13.reflection t ht).2.2
  have hshare : ∀ J ∈ thetaCompZeroStarE p A, ∀ J' ∈ thetaCompZeroStarE p A,
      ∀ t ∈ reflectionSet p A, t ∈ torusImage A J → t ∈ torusImage A J' → Kf J = Kf J' := by
    intro J hJF J' hJ'F t ht htJ htJ'
    obtain ⟨c1, h1⟩ := hgood J hJF
    obtain ⟨c2, h2⟩ := hgood J' hJ'F
    have hheq : Kof A J t = Kof A J' t :=
      Kof_eq_of_share hKt1 h1 h2 hmoved ht htJ htJ' hf (hmods J hJF) hf (hmods J' hJ'F)
    obtain ⟨hperf, hne⟩ := isPerfect_Kof hKt1 h1 ht htJ hf (hmods J hJF)
    have hKJ : Kof A J t ≤ J := Kof_le_self J t
    have hKJ' : Kof A J t ≤ J' := hheq ▸ Kof_le_self J' t
    have hKM : Kof A J t ≤ M := hKJ.trans (hJM J hJF)
    refine theta_component_eq_of_perfect_le hp (hKmem J hJF) (hKmem J' hJ'F)
      (P := (Kof A J t).subgroupOf M) (subgroupOf_ne_bot hKM hne) (isPerfect_subgroupOf hKM hperf)
      ?_ ?_
    · intro g hg
      exact hKle J hJF (Subgroup.mem_subgroupOf.2 (hKJ (Subgroup.mem_subgroupOf.1 hg)))
    · intro g hg
      exact hKle J' hJ'F (Subgroup.mem_subgroupOf.2 (hKJ' (Subgroup.mem_subgroupOf.1 hg)))
  have hconn : ∀ J ∈ thetaCompZeroStarE p A, ∀ J' ∈ thetaCompZeroStarE p A, Kf J = Kf J' := by
    intro J hJF J' hJ'F
    obtain ⟨c1, h1⟩ := hgood J hJF
    obtain ⟨c2, h2⟩ := hgood J' hJ'F
    obtain ⟨s, hs, hsJ⟩ := h1.exists_reflection
    obtain ⟨s', hs', hs'J'⟩ := h2.exists_reflection
    by_cases hss : s = s'
    · subst hss
      exact hshare J hJF J' hJ'F s hs hsJ hs'J'
    · have hnc : s * s' ≠ s' * s := hctx.hess s hs s' hs' hss
      obtain ⟨I, hI, hsI, hs'I⟩ := hpair G p A c L A hctx.hyp hctx.facts12 hctx.facts13
        hctx.notFive (Or.inr ⟨rfl, hctx.allL3⟩) s hs s' hs' hnc
      exact (hshare J hJF I hI s hs hsJ hsI).trans (hshare I hI J' hJ'F s' hs' hs'I hs'J')
  have hLF : L ∈ thetaCompZeroStarE p A := hctx.facts13.inZeroStar
  set K₀ : Subgroup ↥M := Kf L with hK₀
  have hK₀mem : K₀ ∈ thetaComponents p ↥M := hKmem L hLF
  have hJK : ∀ J ∈ thetaCompZeroStarE p A, J ≤ K₀.map M.subtype := by
    intro J hJF j hj
    have hjM : j ∈ M := hJM J hJF hj
    have h1 : (⟨j, hjM⟩ : ↥M) ∈ Kf J := hKle J hJF (Subgroup.mem_subgroupOf.2 hj)
    rw [hconn J hJF L hLF] at h1
    exact ⟨⟨j, hjM⟩, h1, rfl⟩
  obtain ⟨cL, hLg⟩ := hgood L hLF
  have hTne : Tof A L ≠ ⊥ := by
    intro h
    have := hLg.card_Tof
    rw [h, Subgroup.card_bot] at this
    have : p ^ 2 = 1 := this.symm
    exact hp.one_lt.ne' (by simpa using this)
  have hAK0 : A ≤ K₀.map M.subtype := by
    refine A_le_of_Tof_le hctx.facts13.irreducible hLF hTne
      (fun w hw J hJ => conjBy_mem_thetaCompZeroStarE hp hw hJ) fun J hJ => ?_
    obtain ⟨c', hJg⟩ := hgood J hJ
    exact hJg.Tof_le_self.trans (hJK J hJ)
  have hAK : A.subgroupOf M ≤ K₀ := by
    intro a ha
    obtain ⟨k, hk, hka⟩ := hAK0 ha
    have : k = a := Subtype.ext hka
    rw [← this]
    exact hk
  obtain ⟨-, S₀, hS₀L, hS₀1, hS₀2, hS₀N, hS₀eq⟩ := Sec12Three.L_mem_zero hLg.hyp
  have hS₀M : S₀ ≤ M := hS₀L.trans (hJM L hLF)
  have hS₀K : S₀ ≤ K₀.map M.subtype := hS₀L.trans (hJK L hLF)
  have hAel : IsElementaryAbelian p A := hctx.hyp.E_elem
  have : Fact p.Prime := ⟨hp⟩
  have hE₁elem : IsElementaryAbelian p (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
  have hE₁card : Nat.card (A.subgroupOf M) = p ^ 3 := by
    rw [card_subgroupOf_of_le hAM]
    exact hctx.hyp.A_card
  have hS₁K : S₀.subgroupOf M ≤ K₀ := by
    intro s hs
    obtain ⟨k, hk, hks⟩ := hS₀K (Subgroup.mem_subgroupOf.1 hs)
    have : k = s := Subtype.ext hks
    rw [← this]
    exact hk
  have hE₁S₁ : A.subgroupOf M ≤ Subgroup.normalizer ((S₀.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    normalizer_subgroupOf_of_le hS₀N
  have hS₁comm : ⁅S₀.subgroupOf M, A.subgroupOf M⁆ = S₀.subgroupOf M := by
    rw [commutator_subgroupOf hS₀M hAM, ← hS₀eq]
  have hnotθ : ¬ (S₀.subgroupOf M).subgroupOf K₀ ≤ aschbacherSolvableCore p ↥K₀ := by
    intro hθ
    have hLM : L ≤ M := hJM L hLF
    have hLK : L.subgroupOf M ≤ K₀ := hKle L hLF
    let φ : ↥L →* ↥K₀ :=
      { toFun := fun g => ⟨⟨g, hLM g.2⟩, hLK (Subgroup.mem_subgroupOf.2 g.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφinj : Function.Injective φ := fun a b h =>
      Subtype.ext (congrArg (fun k : ↥K₀ => ((k : ↥M) : G)) h)
    let N : Subgroup ↥L := (aschbacherSolvableCore p ↥K₀).comap φ
    have hNn : N.Normal := (aschbacherSolvableCore_normal p ↥K₀).comap φ
    have hNs : Group.IsSolvable ↥N := by
      have hθs : Group.IsSolvable ↥(aschbacherSolvableCore p ↥K₀) :=
        (solvable_prime_complement_core_characterization hp (H := ↥K₀)).1
      exact Group.isSolvable_of_isSolvable_injective
        (f := (φ.comp N.subtype).codRestrict (aschbacherSolvableCore p ↥K₀) (fun x => x.2))
        (fun a b h => Subtype.ext (hφinj (congrArg Subtype.val h)))
    have hNZ : N ≤ Subgroup.center ↥L := normal_solvable_le_center hLg.generic.quasisimple hNn hNs
    have hSZ : ∀ s ∈ S₀, ∀ g ∈ L, g * s = s * g := by
      intro s hs g hg
      have hsL : s ∈ L := hS₀L hs
      have hsM : s ∈ M := hS₀M hs
      have hsN : (⟨s, hsL⟩ : ↥L) ∈ N := by
        show φ ⟨s, hsL⟩ ∈ aschbacherSolvableCore p ↥K₀
        exact hθ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hs))
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 (hNZ hsN) ⟨g, hg⟩)
    have hAcomm : ∀ s ∈ S₀, ∀ a ∈ A, ⁅s, a⁆ = 1 := by
      intro s hs a ha
      have hsL : s ∈ L := hS₀L hs
      rw [hLg.A_eq.1] at ha
      obtain ⟨k, hk, t, ht, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
        (fun k hk l hl => Sec12Three.mul_comm_of_mem_A hLg.hyp
          ((Subgroup.zpowers_le).2 hLg.hyp.c_mem hk) (Tof_le A L hl)) ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have htL : t ∈ L := hLg.Tof_le_self ht
      have hc : ∀ g ∈ L, cL ^ i * g = g * cL ^ i := fun g hg =>
        (Commute.zpow_left (Sec12Three.comm_c_L hLg.hyp g hg : Commute cL g) i).eq
      have h1 : cL ^ i * s = s * cL ^ i := hc s hsL
      have h2 : t * s = s * t := hSZ s hs t htL
      have hcomm : (cL ^ i * t) * s = s * (cL ^ i * t) := by
        calc (cL ^ i * t) * s = cL ^ i * (t * s) := by rw [mul_assoc]
          _ = cL ^ i * (s * t) := by rw [h2]
          _ = (cL ^ i * s) * t := by rw [mul_assoc]
          _ = (s * cL ^ i) * t := by rw [h1]
          _ = s * (cL ^ i * t) := by rw [mul_assoc]
      rw [commutatorElement_def]
      calc s * (cL ^ i * t) * s⁻¹ * (cL ^ i * t)⁻¹
          = ((cL ^ i * t) * s) * s⁻¹ * (cL ^ i * t)⁻¹ := by rw [← hcomm]
        _ = 1 := by group
    have hbot : ⁅S₀, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro s hs a ha
      rw [Subgroup.mem_bot]
      exact hAcomm s hs a ha
    exact hS₀1 (hS₀eq.trans hbot)
  have hEven : Q ((↥K₀ ⧸ aschbacherSolvableCore p ↥K₀) ⧸
      Subgroup.center (↥K₀ ⧸ aschbacherSolvableCore p ↥K₀)) :=
    h613 hSchreier ↥M hMK hMe p hp hp7 K₀ hK₀mem (A.subgroupOf M) hE₁elem
      (by rw [hE₁card]; exact Nat.pow_le_pow_right hp.pos (by norm_num)) hAK
      ⟨S₀.subgroupOf M, subgroupOf_ne_bot hS₀M hS₀1, isPGroup_subgroupOf hS₀M hS₀2, hS₁K, hnotθ,
        hE₁S₁, hS₁comm⟩
  have hK₀e : evenRank ↥K₀ ≤ 3 := (Sec9A.evenRank_subgroup_le K₀).trans hMe
  have hE₂card : Nat.card ((A.subgroupOf M).subgroupOf K₀) = p ^ 3 := by
    rw [card_subgroupOf_of_le hAK, hE₁card]
  have hE₂elem : IsElementaryAbelian p ((A.subgroupOf M).subgroupOf K₀) :=
    IsElementaryAbelian.subgroupOf hAK
  have hW := h64W ↥K₀ (isKGroup_subgroup hMK K₀) hK₀e hK₀mem.1 p hp hp7 hK₀mem.2.2 hEven
    ((A.subgroupOf M).subgroupOf K₀) hE₂elem hE₂card
    ⟨(S₀.subgroupOf M).subgroupOf K₀,
      subgroupOf_ne_bot hS₁K (subgroupOf_ne_bot hS₀M hS₀1),
      isPGroup_subgroupOf hS₁K (isPGroup_subgroupOf hS₀M hS₀2),
      normalizer_subgroupOf_of_le hE₁S₁⟩
  have hX : reflectionGroup p A ≤ torusImage A (K₀.map M.subtype) := by
    refine (Subgroup.closure_le _).2 fun t ht => ?_
    obtain ⟨-, X, hXF, htX⟩ := ht
    obtain ⟨w, hwX, hwN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 htX
    exact Sec12Three.mem_torusImage_iff.2 ⟨w, hJK X hXF hwX, hwN, rfl⟩
  have h3 := three_le_factorization_torusWeyl hAM hAK hcard hX
  omega

theorem caseSupProper_false {Q : (X : Type) → [Group X] → Prop} (hSchreier : SchreierFor InCatalog)
    (h613 : Item613With Q) (h64W : KF64WWith Q)
    (hJ : JFacts) (hpair : KF134Pair) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (hcard : Nat.card (reflectionGroup p A) = 54) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    (hsup : sSup (thetaCompZeroStarE p A) ≠ ⊤) : False := by
  classical
  have hp : p.Prime := hctx.hyp.prime
  have hLF : L ∈ thetaCompZeroStarE p A := hctx.facts13.inZeroStar
  obtain ⟨cL, hLg⟩ := hgood L hLF
  have hJI : ∀ J ∈ thetaCompZeroStarE p A, J ≤ sSup (thetaCompZeroStarE p A) := fun J hJ =>
    le_sSup hJ
  have hTne : Tof A L ≠ ⊥ := by
    intro h
    have := hLg.card_Tof
    rw [h, Subgroup.card_bot] at this
    have : p ^ 2 = 1 := this.symm
    exact hp.one_lt.ne' (by simpa using this)
  have hAI : A ≤ sSup (thetaCompZeroStarE p A) := by
    refine A_le_of_Tof_le hctx.facts13.irreducible hLF hTne
      (fun w hw J hJ => conjBy_mem_thetaCompZeroStarE hp hw hJ) fun J hJ => ?_
    obtain ⟨c', hJg⟩ := hgood J hJ
    exact hJg.Tof_le_self.trans (hJI J hJ)
  have : IsSimpleGroup G := hctx.hyp.setup.1
  have hMtop : Subgroup.normalizer ((sSup (thetaCompZeroStarE p A) : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : (sSup (thetaCompZeroStarE p A)).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sSup (thetaCompZeroStarE p A)) with
      hbot | htop'
    · apply hTne
      rw [eq_bot_iff]
      intro t ht
      have : t ∈ sSup (thetaCompZeroStarE p A) := (hLg.Tof_le_self.trans (hJI L hLF)) ht
      rw [hbot] at this
      exact this
    · exact hsup htop'
  exact caseM_false hSchreier h613 h64W hJ hpair hctx hgood hspec hcard hf hm
    (Subgroup.normalizer ((sSup (thetaCompZeroStarE p A) : Subgroup G) : Set G)) hMtop
    (fun J hJF => (hJI J hJF).trans Subgroup.le_normalizer) (hAI.trans Subgroup.le_normalizer)

end Main

@[expose] def Node143CommB2Sup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ThreeTranspD p E → HessianCase p E →
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f ∧ 2 ^ f % 3 = 2) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set G)) →
    sSup (thetaCompZeroStarE p E) = ⊤ →
    ∀ x z : G, x ∈ L ⊓ torusNormalizer A → orderOf x = 3 → IsScalarOrderThree p A z →
      x * z = z * x →
        (Nat.card (Subgroup.centralizer
          ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G))).factorization 3 ≤
          (Nat.card L).factorization 3

theorem node143CommB2_of_sup {Q : (X : Type) → [Group X] → Prop} (hSchreier : SchreierFor InCatalog) (hRow1 : KF123Row 1)
    (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122) (hpair : KF134Pair)
    (hJ : JFacts) (h613 : Item613With Q) (h64W : KF64WWith Q) (hB2 : Node143CommB2Sup) :
    Node143CommB2 := by
  intro G _ _ p A c L E hyp h12 h13 hnotFive hEA hallL3 hthree hess hmodel hC3 x z hxL hx3 hz hxz
  subst hEA
  by_cases hsup : sSup (thetaCompZeroStarE p E) = ⊤
  · exact hB2 G p E c L E hyp h12 h13 hnotFive rfl hallL3 hthree hess hmodel hC3 hsup x z hxL hx3
      hz hxz
  · exfalso
    have hctx : HessCtx p E c L := ⟨hyp, h12, h13, hnotFive, hallL3, hthree, hess⟩
    have hgood : ∀ J ∈ thetaCompZeroStarE p E, ∃ c' : G, JGood p E c' J := fun J hJm =>
      jGood_of_mem hRow1 h107 h109 h122 hctx hJm
    have hp : p.Prime := hyp.prime
    have : Fact p.Prime := ⟨hp⟩
    have : IsElementaryAbelian p E := hyp.E_elem
    obtain ⟨cL, hLg⟩ := hgood L h13.inZeroStar
    obtain ⟨s, hs, -⟩ := hLg.exists_reflection
    obtain ⟨hcard, P, z', hspec⟩ := hessianGeometry hyp.A_card (Sec12Three.five_le hyp) hthree
      h13.irreducible ⟨s, hs⟩ hess
    obtain ⟨f, -, hf, hm, -⟩ := hmodel
    exact caseSupProper_false hSchreier h613 h64W hJ hpair hctx hgood hspec hcard hf hm hsup

end CFSG.RankThree.PartOne.N143
