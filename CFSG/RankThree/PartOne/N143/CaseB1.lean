module

public import CFSG.RankThree.PartOne.N143.CaseB1Theta
public import CFSG.RankThree.PartOne.N143.CaseAFinal
public import CFSG.RankThree.PartOne.N143.JSetup
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

section Prelim

theorem seven_le_of_cube_root {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk1 : k % p ≠ 1)
    (hk3 : k ^ 3 % p = 1) : 7 ≤ p := by
  by_contra hlt
  have h6 : p ≠ 6 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hp5' : p = 5 := by omega
  subst hp5'
  have h1 : k ^ 3 % 5 = (k % 5) ^ 3 % 5 := Nat.pow_mod k 3 5
  have hlt5 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : k % 5 <;> simp_all

end Prelim

section Tof

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}

omit [Finite G] in
theorem conj_mem_Tof {J : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) {t : G}
    (ht : t ∈ Tof A J) : w * t * w⁻¹ ∈ Tof A (conjBy w J) := by
  have hle : (Tof A J).map (MulAut.conj w).toMonoidHom ≤ Tof A (conjBy w J) := by
    rw [Subgroup.map_le_iff_le_comap, Tof, Subgroup.commutator_le]
    intro a ha x hx
    show w * ⁅a, x⁆ * w⁻¹ ∈ Tof A (conjBy w J)
    have e : w * ⁅a, x⁆ * w⁻¹ = ⁅w * a * w⁻¹, w * x * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.commutator_mem_commutator ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.1 hw a).1 ha
    · exact ⟨⟨x, hx.1, rfl⟩, Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hx.2) (Subgroup.inv_mem _ hw)⟩
  exact hle ⟨t, ht, rfl⟩

omit [Finite G] in
theorem A_le_of_Tof_le (hirr : torusIrreducible A) {F : Set (Subgroup G)} {J₀ : Subgroup G}
    (hJ₀ : J₀ ∈ F) (hne : Tof A J₀ ≠ ⊥)
    (hinv : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ J ∈ F, conjBy w J ∈ F) {K : Subgroup G}
    (hK : ∀ J ∈ F, Tof A J ≤ K) : A ≤ K := by
  set TF : Subgroup G := ⨆ (J : Subgroup G) (_ : J ∈ F), Tof A J with hTF
  have hTFA : TF ≤ A := iSup₂_le fun J _ => Tof_le A J
  have hTFinv : torusInvariant A ⊤ TF := by
    intro w hw b hb
    have hwN : w ∈ Subgroup.normalizer (A : Set G) := hw.2
    have hle : TF ≤ TF.comap (MulAut.conj w).toMonoidHom := by
      refine iSup₂_le fun J hJ t ht => ?_
      show w * t * w⁻¹ ∈ TF
      exact (le_iSup₂ (f := fun (J : Subgroup G) (_ : J ∈ F) => Tof A J) (conjBy w J)
        (hinv w hwN J hJ)) (conj_mem_Tof hwN ht)
    exact hle hb
  have hTFne : TF ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, ← h]
    exact le_iSup₂ (f := fun (J : Subgroup G) (_ : J ∈ F) => Tof A J) J₀ hJ₀
  have hTFeq : TF = A := (hirr TF hTFA hTFinv).resolve_left hTFne
  rw [← hTFeq]
  exact iSup₂_le hK

end Tof

section Weyl

variable {G : Type} [Group G] [Finite G]

theorem three_le_factorization_torusWeyl {A M : Subgroup G} (hAM : A ≤ M) {K₀ : Subgroup ↥M}
    (hAK : A.subgroupOf M ≤ K₀) {Xs : Subgroup (MulAut A)} (hXs54 : Nat.card Xs = 54)
    (hX : Xs ≤ torusImage A (K₀.map M.subtype)) :
    3 ≤ (Nat.card (torusWeyl ((A.subgroupOf M).subgroupOf K₀))).factorization 3 := by
  classical
  set E : Subgroup ↥K₀ := (A.subgroupOf M).subgroupOf K₀ with hE
  let φ : ↥E ≃* ↥A := (Subgroup.subgroupOfEquivOfLe hAK).trans (Subgroup.subgroupOfEquivOfLe hAM)
  let Ψ : MulAut ↥A ≃* MulAut ↥E := MulAut.congr φ.symm
  have hmem : ∀ t ∈ Xs, Ψ t ∈ torusWeyl E := by
    intro t ht
    obtain ⟨w, hw, hwN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 (hX ht)
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hw
    set k' : ↥K₀ := ⟨k, hk⟩ with hk'
    have hk'N : k' ∈ Subgroup.normalizer (E : Set ↥K₀) := by
      refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have he' : e ∈ E := he
      show k' * e * k'⁻¹ ∈ (E : Set ↥K₀)
      have h1 : ((e : ↥K₀) : ↥M).1 ∈ A := he'
      have h2 : (M.subtype k) * ((e : ↥K₀) : ↥M).1 * (M.subtype k)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 hwN _).1 h1
      have h3 : ((k' * e * k'⁻¹ : ↥K₀) : ↥M).1 =
          (M.subtype k) * ((e : ↥K₀) : ↥M).1 * (M.subtype k)⁻¹ := rfl
      show ((k' * e * k'⁻¹ : ↥K₀) : ↥M).1 ∈ A
      rw [h3]
      exact h2
    refine ⟨⟨k', hk'N⟩, ?_⟩
    ext e
    rfl
  have hsub : Xs.map Ψ.toMonoidHom ≤ torusWeyl E := by
    rintro _ ⟨t, ht, rfl⟩
    exact hmem t ht
  have hcard : Nat.card (Xs.map Ψ.toMonoidHom) = 54 := by
    rw [Subgroup.card_map_of_injective Ψ.injective, hXs54]
  have hdvd : 54 ∣ Nat.card (torusWeyl E) := hcard ▸ Subgroup.card_dvd_of_le hsub
  have hne : Nat.card (torusWeyl E) ≠ 0 := Nat.card_pos.ne'
  have h27 : 3 ^ 3 ∣ Nat.card (torusWeyl E) := (show 3 ^ 3 ∣ 54 by norm_num).trans hdvd
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 h27

end Weyl

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}

theorem caseB1_false {Q : (X : Type) → [Group X] → Prop} (hSchreier : SchreierFor InCatalog)
    (h613 : Item613With Q) (h64W : KF64WWith Q)
    (hJ : JFacts) (hpair : KF134Pair) (hctx : HessCtx p A c L)
    (hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J)
    {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hspec : HessianSpec p A Ps zs)
    (hcard : Nat.card (reflectionGroup p A) = 54) {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) (h2mod : 2 ^ f % 3 = 2)
    (hC : 3 ∣ Nat.card (Subgroup.centralizer (A : Set G))) : False := by
  classical
  have hp : p.Prime := hctx.hyp.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le hctx.hyp
  have hp3 : 3 < p := by omega
  obtain ⟨k, hk1, hk3, hk⟩ := hspec.z_scalar
  have hp7 : 7 ≤ p := seven_le_of_cube_root hp hp5 hk1 hk3
  have hJ' := hJ
  obtain ⟨-, -, -, -, -, hKt1, h42, -⟩ := hJ'
  have hmods := models_at hKt1 hctx hpair hgood hf hm
  obtain ⟨z0, hz0N, hz03, hz0π⟩ := exists_z hJ hctx hgood hspec
  have hz0act : ∀ a ∈ A, z0 * a * z0⁻¹ = a ^ k := action_of_pi_eq hk hz0N hz0π
  have hp3f : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (A : Set G))) 3 hC
  have hy0C : (y' : G) ∈ Subgroup.centralizer (A : Set G) := y'.2
  have hy0ord : orderOf (y' : G) = 3 := by
    have := Subgroup.orderOf_coe y'
    rw [hy'] at this
    exact this
  obtain ⟨y0, hy0C, hy0ord⟩ : ∃ y0 : G, y0 ∈ Subgroup.centralizer (A : Set G) ∧ orderOf y0 = 3 :=
    ⟨y', hy0C, hy0ord⟩
  have hy03 : y0 ^ 3 = 1 := by
    rw [← hy0ord]
    exact pow_orderOf_eq_one y0
  have hy01 : y0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy0ord
    omega
  have hy0J : ∀ J ∈ thetaCompZeroStarE p A, J ≤ Subgroup.centralizer ({y0} : Set G) := by
    intro J hJF
    obtain ⟨c', hJg⟩ := hgood J hJF
    have hz0N' : z0 ∈ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A :=
      ⟨hJg.mem_normalizer_of_scalar hz0N ⟨k, hz0act⟩, hz0N⟩
    have hy0N : y0 ∈ Subgroup.normalizer (J : Set G) := hJg.centralizer_A_le_normalizer hy0C
    have h := h42 G p A c' J hJg f hf (hmods J hJF) h2mod z0 hz0N' hz03 k hk1 hk3
      (fun a ha => hz0act a (Tof_le A J ha)) y0 hy0N hy0C ⟨1, by simpa using hy03⟩
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 h j hj
  set M : Subgroup G := Subgroup.centralizer ({y0} : Set G) with hM
  have : IsSimpleGroup G := hctx.hyp.setup.1
  have hMtop : M ≠ ⊤ :=
    EmbeddingFixedResidual.centralizer_ne_top_of_simple hctx.hyp.setup.2.1 hy01
  have hMK : CFSG.IsKGroup ↥M := hctx.hyp.setup.2.2.1 M hMtop
  have hMe : evenRank ↥M ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans hctx.hyp.evenRank_eq.le
  have hAM : A ≤ M := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hy0C a ha)
  have hemb : ∀ J ∈ thetaCompZeroStarE p A, ∃ K ∈ thetaComponents p ↥M, J.subgroupOf M ≤ K := by
    intro J hJF
    obtain ⟨c', hJg⟩ := hgood J hJF
    have hcM : c' ∈ M := hAM hJg.hyp.c_mem
    have hres := restrict_thetaComponentsAt hp hcM (hJg.hyp.L_mem).2 (hy0J J hJF)
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
    have hKM : Kof A J t ≤ M := hKJ.trans (hy0J J hJF)
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
    have hjM : j ∈ M := hy0J J hJF hj
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
  have hS₀M : S₀ ≤ M := hS₀L.trans (hy0J L hLF)
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
    have hLM : L ≤ M := hy0J L hLF
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

end Main

end CFSG.RankThree.PartOne.N143
