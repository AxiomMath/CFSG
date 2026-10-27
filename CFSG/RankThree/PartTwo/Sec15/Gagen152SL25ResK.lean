module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResCtx
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoON
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.CGT.PushingUpLit.Glue.SixSixteenRel

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L M X B : Subgroup G}
  {b d : G} {Lb : Subgroup G} {p : ℕ} {P : Subgroup G} {e : G}

theorem ResCtx.exists_K
    (h48 : Sec4.Item4_8) (h134 : Item134) (hcomp : Step143HJCompOne)
    (h : ResCtx A c L M X B b d Lb p P e) :
    ∃ K ∈ thetaComponentsAt 3 e, lB A B ≤ K ∧
      K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K := by
  have hS : Sec14Std G A c L := h.sec15R.toSec14Std
  obtain ⟨K, hKmem, hBK⟩ :=
    Ronan148D.exists_mem_lbMembers h48 hS h.mem_A h.ne_one h.not_mem_omegaA h.hyp h.mem_e h.config
  refine ⟨K, hKmem.1, hBK, ?_⟩
  by_cases hne : Subgroup.zpowers e ≠ Subgroup.zpowers d
  · exact hcomp G A c L hS e h.mem_A h.ne_one h.not_mem_omegaA B b d Lb h.hyp h.mem_e
      h.config hne K hKmem.1 hBK
  · push Not at hne
    rcases Ronan148D.member_cases h134 hS h.hyp h.config hne hKmem.1 hBK with
      ⟨heq, -, -⟩ | ⟨-, h12⟩
    · exact heq
    · rw [h.omega, Set.ncard_singleton] at h12
      norm_num at h12

theorem le_normalizer_of_cover_of_perfect {c : G} {K D X : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 c) (hDX : D ≤ X) (hDK : D ≤ K)
    (hDcov : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hnt : Nontrivial (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set θX : Subgroup ↥X := aschbacherSolvableCore 3 ↥X with hθX
  set π : ↥X →* (↥X ⧸ θX) := QuotientGroup.mk' θX with hπ
  intro g hg
  obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Dg : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hDg
  have hKg : K.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c :=
    Sec6.map_conj_mem_thetaComponentsAt hgC hK
  have hcomm : ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) C :=
    Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hKg (Ne.symm hne)
  have hXg : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  have hDgX : Dg ≤ X := by
    rw [hDg, ← hXg]
    exact Subgroup.map_mono hDX
  have hDgK : Dg ≤ K.map (MulAut.conj g).toMonoidHom := by
    rw [hDg]
    exact Subgroup.map_mono hDK
  set J : Subgroup G := ⁅D, Dg⁆ with hJ
  have hJX : J ≤ X := Subgroup.commutator_le_of_le hDX hDgX
  have hJθ : J ≤ inSubgroup (aschbacherSolvableCore 3) C :=
    (Subgroup.commutator_mono hDK hDgK).trans hcomm
  have hDgmap : (Dg.subgroupOf X).map π = ⊤ := by
    have hsub : Dg.subgroupOf X =
        (D.subgroupOf X).map (MulAut.conj (⟨g, hgX⟩ : ↥X)).toMonoidHom := by
      ext x
      constructor
      · intro hx
        obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        refine Subgroup.mem_map.mpr ⟨⟨d, hDX hd⟩, hd, ?_⟩
        exact Subtype.ext (by
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
            Subgroup.coe_inv] using hdx)
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(y : G), ?_, ?_⟩)
        · exact Subgroup.mem_subgroupOf.mp hy
        · have := congrArg (Subtype.val) hyx
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
            Subgroup.coe_inv] using this
    calc (Dg.subgroupOf X).map π
        = ((D.subgroupOf X).map (MulAut.conj (⟨g, hgX⟩ : ↥X)).toMonoidHom).map π := by
          rw [hsub]
      _ = ((D.subgroupOf X).map π).map
            (MulAut.conj (π ⟨g, hgX⟩)).toMonoidHom :=
          Subgroup.map_map_conj _ _ _
      _ = ⊤ := by
          rw [hDcov, Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective]
  have hJmap : (J.subgroupOf X).map π = ⊤ := by
    rw [hJ, ← CFSG.CGT.PushingUpLit.Glue.subgroupOf_commutator_eq hDX hDgX,
      Subgroup.map_commutator, hDcov, hDgmap, ← commutator_def]
    exact hperf.commutator_eq_top
  have hJC : J ≤ C := hJθ.trans (Subgroup.map_subtype_le _)
  have hJsolv : Group.IsSolvable ↥J := by
    haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥C) :=
      (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).1
    have hJsub : J.subgroupOf C ≤ aschbacherSolvableCore 3 ↥C := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hJθ (Subgroup.mem_subgroupOf.mp hx))
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    haveI : Group.IsSolvable ↥(J.subgroupOf C) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJsub)
        (Subgroup.inclusion_injective hJsub)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hJC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).symm.injective
  have hJsolvX : Group.IsSolvable ↥(J.subgroupOf X) := by
    haveI : Group.IsSolvable ↥J := hJsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hJX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJX).injective
  have hsurj : Function.Surjective (π.comp (J.subgroupOf X).subtype) := by
    intro q
    have hq : q ∈ (J.subgroupOf X).map π := by rw [hJmap]; exact Subgroup.mem_top q
    obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨j, hj⟩, hje⟩
  haveI : Group.IsSolvable (↥X ⧸ θX) := by
    haveI : Group.IsSolvable ↥(J.subgroupOf X) := hJsolvX
    exact Group.isSolvable_of_surjective (f := π.comp (J.subgroupOf X).subtype) hsurj
  haveI : Group.IsPerfect (↥X ⧸ θX) := hperf
  haveI : Nontrivial (↥X ⧸ θX) := hnt
  exact Group.IsPerfect.not_isSolvable (↥X ⧸ θX) inferInstance

theorem ResCtx.le_normalizer_of_cover (h : ResCtx A c L M X B b d Lb p P e) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 e) {D : Subgroup G} (hDX : D ≤ X) (hDK : D ≤ K)
    (hDcov : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    X ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hXq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    isQuasisimple_theta_of_mem_thetaComponentsIn h.ctx.mem_comp
  exact le_normalizer_of_cover_of_perfect hK hDX hDK hDcov hXq.1
    (CFSG.LocalCores.isQuasisimple_nontrivial hXq)

theorem ResCtx.A_le_normalizer
    (h : ResCtx A c L M X B b d Lb p P e) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 e) (hBK : lB A B ≤ K) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  intro a ha
  exact Ronan148D.mem_normalizer_of_normalizes_lB h.sec15R.toSec14Std h.hyp h.config hK hBK
    (h.le_centralizer_A ha)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.A_le_normalizer_lB ha))

theorem theta_le_pPrimeCoreOf {e : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 e) :
    inSubgroup (aschbacherSolvableCore 3) K ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) := by
  set C := Subgroup.centralizer ({e} : Set G) with hC
  obtain ⟨L, hL, rfl⟩ := hK
  have hLsub : CFSG.Open.IsSubnormal L (⊤ : Subgroup ↥C) :=
    CFSG.Open.IsSubnormal.of_mathlib hL.2.1
  have hsub : CFSG.Open.IsSubnormal (L.map C.subtype) C := by
    have h := hLsub.map C.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  exact Proof155P.inSubgroup_theta_le_pPrimeCoreOf hsub

theorem pCoreOf_le_theta_of_eq_sup {K T : Subgroup G} (hTK : T ≤ K)
    (hK : K = T ⊔ inSubgroup (aschbacherSolvableCore 3) K) :
    CFSG.Open.pCoreOf 2 T ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : Subgroup ↥K := aschbacherSolvableCore 3 ↥K
  let π : ↥K →* (↥K ⧸ θ) := QuotientGroup.mk' θ
  let inc : ↥T →* ↥K := Subgroup.inclusion hTK
  let φ : ↥T →* (↥K ⧸ θ) := π.comp inc
  let Q : Subgroup ↥T := CFSG.pCore 2 ↥T
  let P : Subgroup (↥K ⧸ θ) := Q.map φ
  have hTKsup : T.subgroupOf K ⊔ θ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTK, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hK.symm
  have hTmapTop : (T.subgroupOf K).map π = ⊤ := by
    have h1 : (T.subgroupOf K ⊔ θ).map π = ⊤ := by
      rw [hTKsup]
      exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective θ)
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have hφrange : φ.range = (T.subgroupOf K).map π := by
    rw [show φ = π.comp inc from rfl, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, hφrange, hTmapTop]
  have hPnormal : P.Normal := by
    have hbase : (Q.map φ).Normal := Subgroup.Normal.map (inferInstance : Q.Normal) φ hφsurj
    simpa [P] using hbase
  have hQ2 : IsPGroup 2 Q := by
    simpa [Q] using (CFSG.pCore_isPGroup (p := 2) (G := ↥T))
  have hP2 : IsPGroup 2 P := by
    have hbase : IsPGroup 2 (Q.map φ) := IsPGroup.map (p := 2) hQ2 φ
    simpa [P] using hbase
  have hPsolv : Group.IsSolvable ↥P := by
    haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
    exact IsNilpotent.to_isSolvable
  let M : Subgroup ↥K := P.comap π
  have hθM : θ ≤ M := by
    intro x hx
    show π x ∈ P
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact P.one_mem
  have hMmap : M.map π = P := by
    simpa [M] using Subgroup.map_comap_eq_self_of_surjective
      (f := π) (QuotientGroup.mk'_surjective θ) (H := P)
  have hMnormal : M.Normal := by
    simpa [M] using hPnormal.comap π
  let g : ↥M →* ↥P := (π.comp M.subtype).codRestrict P fun m => m.2
  have hgker : g.ker = θ.subgroupOf M := by
    ext m
    constructor
    · intro hm
      have h1 : π (m : ↥K) = 1 := by
        have h2 := congrArg (fun y : ↥P => (y : ↥K ⧸ θ)) hm
        exact h2
      exact (QuotientGroup.eq_one_iff (m : ↥K)).mp h1
    · intro hm
      refine Subtype.ext ?_
      show π (m : ↥K) = 1
      exact (QuotientGroup.eq_one_iff (m : ↥K)).mpr hm
  have hgsurj : Function.Surjective g := by
    intro p
    have hp : (p : ↥K ⧸ θ) ∈ M.map π := by rw [hMmap]; exact p.2
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hp
    exact ⟨⟨x, hx⟩, Subtype.ext hxeq⟩
  obtain ⟨hθsolv, -, hθ3, hmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hMsolv : Group.IsSolvable ↥M := by
    haveI : Group.IsSolvable ↥θ := hθsolv
    haveI : Group.IsSolvable ↥(θ.subgroupOf M) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hθM).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hθM).injective
    haveI : Group.IsSolvable ↥P := hPsolv
    refine Group.isSolvable_of_ker_le_range (f := Subgroup.inclusion hθM) (g := g) ?_
    rw [hgker, Subgroup.inclusion_range]
  have hP3 : ¬ 3 ∣ Nat.card ↥P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hM3 : ¬ 3 ∣ Nat.card ↥M := by
    have hcard : Nat.card ↥M =
        Nat.card (↥M ⧸ θ.subgroupOf M) * Nat.card ↥(θ.subgroupOf M) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (θ.subgroupOf M)
    have hquot : Nat.card (↥M ⧸ θ.subgroupOf M) = Nat.card ↥P := by
      rw [← hgker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgsurj).toEquiv
    have hsub : Nat.card ↥(θ.subgroupOf M) = Nat.card ↥θ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθM).toEquiv
    rw [hcard, hquot, hsub]
    exact fun h => (Nat.Prime.dvd_mul Nat.prime_three).mp h |>.elim hP3 hθ3
  have hMleθ : M ≤ θ := hmax M hMnormal hMsolv hM3
  have hPbot : P = ⊥ := by
    rw [← hMmap]
    exact le_bot_iff.mp ((Subgroup.map_mono hMleθ).trans
      (le_of_eq (QuotientGroup.map_mk'_self θ)))
  intro x hx
  change x ∈ (CFSG.pCore 2 ↥T).map T.subtype at hx
  change x ∈ (aschbacherSolvableCore 3 ↥K).map K.subtype
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  have hqP : φ q ∈ P := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hPbot] at hqP
  have hφq : φ q = 1 := Subgroup.mem_bot.mp hqP
  have hincθ : inc q ∈ θ := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [φ, π] using hφq
  exact Subgroup.mem_map.mpr ⟨inc q, hincθ, rfl⟩

end Gagen152SL25Res

end CFSG.RankThree.PartTwo.Sec15
