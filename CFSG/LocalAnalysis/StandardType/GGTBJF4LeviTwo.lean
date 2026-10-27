module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviPlus
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Two
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433 CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Bal207

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace F4Two

theorem f4Two_hA2
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ} {v : WeylGroup Tag.F4} {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = CFSG.ComponentClassification.CatLeafProof.f4LeviC3)
    (hroots : componentRoots χ i = (fun α => v • α) '' parabolicRoots Tag.F4 J) :
    ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
      iform α α = iform δ δ ∧ iform α δ ≠ 0 := by
  obtain ⟨j, k, hj, hk, hjk, hlen, hnz⟩ : ∃ j k : Fin Tag.F4.rank, j ∈ J ∧ k ∈ J ∧ j ≠ k ∧
      iform (Pi.single j 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1) =
        iform (Pi.single k 1 : Fin Tag.F4.rank → ℤ) (Pi.single k 1) ∧
      iform (Pi.single j 1 : Fin Tag.F4.rank → ℤ) (Pi.single k 1) ≠ 0 := by
    rcases hJ with rfl | rfl
    · exact ⟨0, 1, ⟨0, rfl⟩, ⟨1, rfl⟩, by decide, by decide, by decide⟩
    · exact ⟨2, 3, ⟨1, rfl⟩, ⟨0, rfl⟩, by decide, by decide, by decide⟩
  have hpar : ∀ l ∈ J, (Pi.single l 1 : Fin Tag.F4.rank → ℤ) ∈ parabolicRoots Tag.F4 J :=
    fun l hl => ⟨isRoot_single Tag.F4 l, fun m hm => by
      rw [Pi.single_apply, if_neg (show m ≠ l from fun h => hm (by rw [h]; exact hl))]⟩
  have hmem : ∀ l ∈ J, v • (Pi.single l 1 : Fin Tag.F4.rank → ℤ) ∈ componentRoots χ i :=
    fun l hl => by rw [hroots]; exact ⟨_, hpar l hl, rfl⟩
  refine ⟨v • Pi.single j 1, hmem j hj, v • Pi.single k 1, hmem k hk, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' := congrFun (MulAction.injective v h) k
    simp [Pi.single_apply, hjk.symm] at h'
  · intro h
    rw [← smul_neg] at h
    have h' := congrFun (MulAction.injective v h) k
    simp [Pi.single_apply, hjk.symm] at h'
  · rw [iform_smul, iform_smul]
    exact hlen
  · rw [iform_smul]
    exact hnz

theorem rootSL2_WSL_mem_rationalComponent_F4_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hq2 : S.D.q = 2) (hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = -γ)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hRns : ¬ Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i) :
    rootSL2 Tag.F4 L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  have hk0 : ∃ j, k j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [show a = 1 from funext fun j => by rw [hak j, hcon j, pow_zero]; rfl, rootDiagUnit_one]
  rcases classify_kernel k hk3 hk0 with he | hA2
  · obtain ⟨hcard, hconn⟩ := FamF42.kernel_conn_of_orth k hk3 hk0 he
    have huniq : ∀ i j : KernelComponent (rootCharHom a), i = j :=
      FamF42.eq_of_kernel_conn hω3 hω1 hak hconn
    have hker : kernelRoots (rootCharHom a) = {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0} :=
      Set.ext fun γ => and_congr_right fun _ => rootChar_eq_one_iff hω3 hω1 hak γ
    have hroots_eq : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
      Set.ext fun γ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, huniq _ _⟩⟩
    have hn18 : (componentRoots (rootCharHom a) i).ncard = 18 := by
      rw [hroots_eq, hker]
      exact hcard
    have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1)) := by
      rintro ⟨-, h2⟩
      rw [hn18] at h2
      generalize compRank (componentRoots (rootCharHom a) i) = r at h2
      have hr : r ≤ 4 := by nlinarith
      interval_cases r <;> omega
    have hℓp : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one Nat.prime_three hap h1
    have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne Nat.prime_three hℓp
    rcases f4_nonA_casesP Nat.prime_three (by norm_num) S hpL
        (rootDiagUnit_pow_eq_one_of_forall hap) h1 i hnonA with
      ⟨-, hn⟩ | ⟨v, J, hJ, hroots, hr3, -⟩
    · rw [hn18] at hn
      omega
    have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength_eq_one
        (Set.finite_of_ncard_ne_zero (by rw [hn18]; norm_num)) fun γ hγ => by
          rw [hρ γ (hΨ.isRoot γ hγ)]
          exact hΨ.neg_mem γ hγ
    have hinner := twistInner_of_shape S hT i 3 18 hr3 hn18 (by decide) (by decide) (by decide)
      (by decide)
    rw [hs1, Function.iterate_one] at hinner
    obtain ⟨w, hw, hwγ⟩ := hinner
    exact LangRat.rootSL2_WSL_mem_rationalComponent_of_neg_two S hq2 hT i
      (fun γ hγ => hρ γ (hΨ.isRoot γ hγ))
      ⟨w, hw, fun γ hγ => by rw [← hwγ γ hγ, hρ γ (hΨ.isRoot γ hγ)]⟩
      (fun F hF => isPerfect_componentRootSpan_F4_two hF i (f4Two_hA2 hJ hroots)) hα
  · exact absurd (FamF42.isSolvable_rationalComponent_of_a2a2 S hT hap hω3 hω1 hk3 hk0 hak hA2
      hq2 i) hRns

end F4Two

theorem f4Two_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian 3 E)
    (hSC : ∀ g : adjointGroup .F4 K, (∀ c ∈ E, g * c = c * g) → g ^ 3 = 1 → g ∈ E)
    (h4 : 3 ^ 4 ≤ Nat.card E) : GGF4LeviFrame 3 E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpK : 3 ∣ Nat.card K + 1 := by rw [hK]
  obtain ⟨ζ, hζ, ιT, nk, S, ι, hζo, hιTinj, hιTrange, hact, hSq, hιinj, hιrange, hιιT, hT, hρ,
    wt, hwn, hwt⟩ := f4Enn_frame (K := K) hpK E hE hSC (Or.inr ⟨rfl, h4⟩)
  have hq2 : S.D.q = 2 := by rw [hSq, hK]
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  refine ⟨AlgebraicClosure K, inferInstance, ζ, hζ, ιT, nk, _, wt, hζo, hιTinj, hιTrange, hact,
    hwn, hwt, fun t ht Y hY => ?_⟩
  obtain ⟨i, hi, hCENT⟩ := e8Enn_class (K := K) (by norm_num) S ι hιinj hιrange hιιT hT
    (fun γ hγ => Or.inr (hρ γ hγ)) ht hY
  refine ⟨i, hCENT, fun _ _ _ _ c hc => LangRat.realizes_rootReflection_of_mem S ι hιinj hιιT i hi
    ((isRootComponent_componentRoots i).isRoot c hc) ?_⟩
  have hTt : rootDiagUnit .F4 (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t)) ∈
      S.D.torus := hT t
  have hRns : ¬ Group.IsSolvable ↥(rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))) i) := by
    intro hs
    have hYs : Group.IsSolvable ↥Y := solvable_of_solvable_injective
      (f := ((Y.equivMapOfInjective ι hιinj).trans (MulEquiv.subgroupCongr hi)).toMonoidHom)
      ((Y.equivMapOfInjective ι hιinj).trans (MulEquiv.subgroupCongr hi)).injective
    obtain ⟨-, -, hperf, hsimp⟩ := hY
    have htop :=
      CFSG.Timmesfeld.Bridge.Asc72.top_eq_bot_of_isSolvable_of_commutator_eq_top hYs hperf
    haveI : Subsingleton ↥Y := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥Y) := htop ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥Y) := htop ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    haveI : Subsingleton (↥Y ⧸ Subgroup.center ↥Y) := inferInstance
    exact hsimp.toNontrivial.exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  have h1 : rootDiagUnit .F4 (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t)) ≠
      1 := by
    intro h
    apply ht
    apply hιinj
    rw [hιιT, map_one]
    exact h
  have hpow : TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t) ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := .F4)
      (K := AlgebraicClosure K)
    rw [← rootDiagUnit_pow]
    simpa [ExcFrames.frameDiag, rootDiagUnit_one] using
      ExcFrames.frameDiag_pow (τ := .F4) ζ hζ t
  have hap : ∀ j, TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t) j ^ 3 = 1 :=
    fun j => by simpa using congrFun hpow j
  exact F4Two.rootSL2_WSL_mem_rationalComponent_F4_two S hq2 hρ hTt hap h1 i hRns hc

theorem ggF4Two_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (hZ : Subgroup.center ↥L = ⊥) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ∧
      ∃ (e : ↥L ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  subst hp3
  have hΛ : LargeEvenInLambda2 (⟨.F4, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, hN, hinner⟩ :=
    ggF4_model' hRig (Or.inr hZ) hΛ hH.2.2.1.1 hL
  have hlb : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    ggF4Three_rank_of_res hRig hH hH.2.2.1.1 hΛ hL (by norm_num) hN
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hN hlb
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, by rw [hFqcard, pow_one], e, E, hEel,
    hEcard, hEsc, hArange⟩

theorem ggF4Two_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (hZ : Subgroup.center ↥K = ⊥) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ∧
      ∃ (e : ↥K ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  subst hp3
  have hΛ : LargeEvenInLambda2 (⟨.F4, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  have hinn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZK, hN, hinner⟩ :=
    ggF4_model' hRig (Or.inr hZ) hΛ hinn hK
  have hlb : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    ggF4Three_rank_of_res hRig hH hinn hΛ hK (by norm_num) hN
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZK hinner hN hlb
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, by rw [hFqcard, pow_one], e, E, hEel,
    hEcard, hEsc, hArange⟩

theorem ggTBJF4LeviL_two
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (hZ : Subgroup.center ↥L = ⊥) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ :=
    ggF4Two_model_L hRig hH hL hp3 hZ
  subst hp3
  exact ggTBJF4LeviL_of_model hH ⟨hN, adjointGroup .F4 Fq, inferInstance,
    center_adjointGroup_eq_bot, e, E, hA, f4Two_leviFrame hFqcard E hE hEself hE4⟩

theorem ggTBJF4LeviK_two
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K)
    (hK : GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (hZ : Subgroup.center ↥K = ⊥) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ :=
    ggF4Two_model_K hRig hH hK hp3 hZ
  subst hp3
  exact ggTBJF4LeviK_of_model hH hJK ⟨hN, adjointGroup .F4 Fq, inferInstance,
    center_adjointGroup_eq_bot, e, E, hA, f4Two_leviFrame hFqcard E hE hEself hE4⟩

theorem f4Two_center_pow_eq_one
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {Fq : Type} [Field Fq]
    (hFq : Nat.card Fq = 2) (π : X →* adjointGroup .F4 Fq) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ z ∈ Subgroup.center X, z ^ p = 1 → z = 1 := by
  intro z hz hzp
  by_contra hz1
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Nat.card π.ker ≤ 2 :=
    CFSG.LieType.Steinberg.CentralExt.F4Two.f4_two_card_ker_le_two hFq π hπ hker.le
  have hzk : z ∈ π.ker := hker ▸ hz
  have hdvd : orderOf z ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hzk
  rw [orderOf_eq_prime hzp hz1] at hdvd
  have hle' : p ≤ 2 := (Nat.le_of_dvd Nat.card_pos hdvd).trans hle
  have h2 := hp.two_le
  omega

@[expose] def GGTBJF4LeviLThreeTwoCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs L → GGResXDatum p Bs L →
    GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) → p = 3 →
    Subgroup.center ↥L ≠ ⊥ →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
          GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J

@[expose] def GGTBJF4LeviKThreeTwoCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs K → GGResXDatum p Bs K →
    GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) → p = 3 →
    Subgroup.center ↥K ≠ ⊥ →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
          GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J

theorem ggTBJF4LeviLThreeTwoCover_holds
    (hRig : GGLabelRigidInput) : GGTBJF4LeviLThreeTwoCover := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ hhas hp3 _ _ _ _
  subst hp3
  have hΛ : LargeEvenInLambda2 (⟨.F4, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  obtain ⟨Fq, _, _, _, hFq, π, hπ, hker, hperf, hN, hinner⟩ :=
    ggF4_quotModel hRig hΛ hH.2.2.1.1 hhas
  have hFq2 : Nat.card Fq = 2 := by rw [hFq, pow_one]
  haveI := hperf
  have hZp : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 → z = 1 :=
    f4Two_center_pow_eq_one hFq2 π hπ hker Nat.prime_three (by norm_num)
  obtain ⟨E, hE, hEcard, hEsc, hA⟩ := ggCover_innerModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN hZp π hπ
    hker.le center_adjointGroup_eq_bot hinner
  have h4 : 3 ^ 4 ≤ Nat.card E := by
    rw [hEcard]
    exact ggF4Three_rank_of_res hRig hH hH.2.2.1.1 hΛ hhas (by norm_num) hN
  exact ggTBJF4LeviL_of_cover hH hN hZp center_adjointGroup_eq_bot π hπ hker.le hA
    (f4Two_leviFrame hFq2 E hE hEsc h4)

theorem ggTBJF4LeviKThreeTwoCover_holds
    (hRig : GGLabelRigidInput) : GGTBJF4LeviKThreeTwoCover := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ hhas hp3 _ _ _ _
  subst hp3
  have hΛ : LargeEvenInLambda2 (⟨.F4, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  have hinn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨Fq, _, _, _, hFq, π, hπ, hker, hperf, hN, hinner⟩ := ggF4_quotModel hRig hΛ hinn hhas
  have hFq2 : Nat.card Fq = 2 := by rw [hFq, pow_one]
  haveI := hperf
  have hZp : ∀ z ∈ Subgroup.center ↥K, z ^ 3 = 1 → z = 1 :=
    f4Two_center_pow_eq_one hFq2 π hπ hker Nat.prime_three (by norm_num)
  obtain ⟨E, hE, hEcard, hEsc, hA⟩ := ggCover_innerModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN hZp π hπ
    hker.le center_adjointGroup_eq_bot hinner
  have h4 : 3 ^ 4 ≤ Nat.card E := by
    rw [hEcard]
    exact ggF4Three_rank_of_res hRig hH hinn hΛ hhas (by norm_num) hN
  exact ggTBJF4LeviK_of_cover hH hJK hN hZp center_adjointGroup_eq_bot π hπ hker.le hA
    (f4Two_leviFrame hFq2 E hE hEsc h4)

theorem ggTBJF4LeviLThreeTwo_of_cover
    (hRig : GGLabelRigidInput) (h : GGTBJF4LeviLThreeTwoCover) : GGTBJF4LeviLThreeTwo := by
  intro G _ _ p B Bs x L D J y K hH _ hL hX hhas hp3 labJ hΛJ hhasJ
  by_cases hZ : Subgroup.center ↥L = ⊥
  · exact ggTBJF4LeviL_two hRig hH hhas hp3 hZ
  · exact h G p B Bs x L D J y K hH hL hX hhas hp3 hZ labJ hΛJ hhasJ

theorem ggTBJF4LeviKThreeTwo_of_cover
    (hRig : GGLabelRigidInput) (h : GGTBJF4LeviKThreeTwoCover) : GGTBJF4LeviKThreeTwo := by
  intro G _ _ p B Bs x L D J y K hH hJK _ hK hX hhas hp3 labJ hΛJ hhasJ
  by_cases hZ : Subgroup.center ↥K = ⊥
  · exact ggTBJF4LeviK_two hRig hH hJK hhas hp3 hZ
  · exact h G p B Bs x L D J y K hH hJK hK hX hhas hp3 hZ labJ hΛJ hhasJ

end CFSG.StandardType

end
