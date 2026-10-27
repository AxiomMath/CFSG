module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp2
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCentFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLayer
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SteinbergBRBlockParabolicDInf
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.ComponentInitial Polynomial Multiplicative

theorem QTwoSpFrame.no_fixed_coordinate {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} {E : Subgroup ↥(CFSG.Open.StatedSp m K)}
    {x : ↥(CFSG.Open.StatedSp m K)} {L D J : Subgroup ↥(CFSG.Open.StatedSp m K)}
    (hC : GGQTwoFRCfg E x L D J)
    {e₂ : ↥(CFSG.Open.StatedSp m K) ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K))}
    {E' : Subgroup ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K))}
    {F : SpNS.FrameData K (Fin m ⊕ Fin m → K)
      (CFSG.RankThree.Classical.spForm m K) E'}
    (hE' : E' = E.map e₂.toMonoidHom)
    (hτE : ∀ f, F.τ f ∈ E') {k : Fin F.s → ℕ}
    (hsp : ∀ t, ((e₂ t : ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K))) :
      LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) =
      CFSG.RankThree.Classical.spLin m K t)
    (hspx : ((e₂ x : ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K))) :
      LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) =
      CFSG.RankThree.Classical.spLin m K x)
    (hxk : ∀ d w, CFSG.RankThree.Classical.spEnd x (F.Φ (d, w)) =
      F.Φ (fun i => F.ζ ^ k i * d i, w)) :
    ∀ i, (fun i => F.ζ ^ k i) i ≠ 1 := by
  classical
  let V := Fin m ⊕ Fin m → K
  let B : LinearMap.BilinForm K V := CFSG.RankThree.Classical.spForm m K
  obtain ⟨hEel, hEcard, hsc, hxE, hx1, hxL, hLcomp, hEnorm, hCE, hDE, hDcard,
    hxD, hJcomp, hCJ⟩ := hC
  let M := AdjoinRoot F.g
  have hfact : Fact (Irreducible F.g) := ⟨F.hg⟩
  have : Fact (Irreducible F.g) := hfact
  have hMmod : Module.Finite K M := (AdjoinRoot.powerBasis F.hg.ne_zero).finite
  have : Module.Finite K M := hMmod
  have : Finite M := Module.finite_of_finite K
  have hM : Nat.card M = 4 := QTwoSpFrame.natCard_adjoinRoot_eq_four F.b hK
  have hcharM : CharP M 2 := charP_of_injective_algebraMap (algebraMap K M).injective 2
  have : CharP M 2 := hcharM
  let τ : M ≃+* M := frobeniusEquiv M 2
  have hτ2 : ∀ y, τ y = y ^ 2 := fun y => frobeniusEquiv_apply M 2 y
  have hτ : ∀ y, τ (τ y) = y := fun y => TraceFrame.frobeniusEquiv_two_involutive hM y
  have hx3 : x ^ 3 = 1 := hEel.2 x hxE
  let c : Fin F.s → M := fun i => F.ζ ^ k i
  have hc3 : ∀ i, c i ^ 3 = 1 := by
    intro i
    dsimp [c]
    rw [← pow_mul, mul_comm, pow_mul, F.hζp, one_pow]
  have hx_ne_one_coord : ∃ j, c j ≠ 1 := by
    by_contra h
    push Not at h
    dsimp [c] at h
    have hsp : CFSG.RankThree.Classical.spEnd x = 1 := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective v
      rw [hxk, Module.End.one_apply]
      congr 2
      funext i
      rw [h i, one_mul]
    have he2 : e₂ x = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa [hspx] using hsp
    exact hx1 (e₂.injective (by rw [he2, map_one]))
  have hm1 : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hcard : Nat.card ↥(CFSG.Open.StatedSp 0 K) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      simp
    have hle : Nat.card E ≤ Nat.card ↥(CFSG.Open.StatedSp 0 K) :=
      Subgroup.card_le_card_group (H := E)
    rw [hcard] at hle
    omega
  have hLcompO : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set _)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hLcomp
  have hL_or := CFSG.LocalAnalysis.GLTheoremA.T173O.eq_or_of_isComponentOf_centralizer
    hK hm1 hx3 hx1 hLcompO
  have hno_fix : ∀ i, c i ≠ 1 := by
    intro i hci
    rcases hL_or with hL1 | hL3
    · exfalso
      have hxL1 : x ∈ CFSG.RankThree.Classical.spSupported x
          ({(Polynomial.X : K[X]) - 1} : Set K[X]) := by
        rw [hL1] at hxL
        exact Subgroup.commutator_le_self _ hxL
      obtain ⟨j, hcj⟩ := hx_ne_one_coord
      have hcj_sq : c j ^ 2 + c j + 1 = 0 :=
        QTwoFrameTorus.frame_sq_add_add_one_eq_zero (hc3 j) hcj
      set v := F.Φ (Pi.single j (1 : AdjoinRoot F.g), 0) with hvdef
      have hxv : CFSG.RankThree.Classical.spEnd x v = F.Φ (Pi.single j (c j), 0) := by
        rw [hvdef, hxk]
        congr 1
        apply Prod.ext
        · funext l
          by_cases hl : l = j
          · subst hl; simp [c]
          · simp [Pi.single_eq_of_ne hl]
        · rfl
      have hx2v : CFSG.RankThree.Classical.spEnd x (CFSG.RankThree.Classical.spEnd x v) =
          F.Φ (Pi.single j (c j ^ 2), 0) := by
        rw [hxv, hxk]
        congr 1
        apply Prod.ext
        · funext l
          by_cases hl : l = j
          · subst hl; simp [c, pow_two]
          · simp [Pi.single_eq_of_ne hl]
        · rfl
      have hv : Polynomial.aeval (CFSG.RankThree.Classical.spEnd x)
          (CFSG.StandardType.ChoiceTwo.phi3 K) v = 0 := by
        rw [CFSG.StandardType.ChoiceTwo.aeval_phi3_apply, hx2v, hxv, hvdef]
        rw [← map_add, ← map_add]
        have hsum : ((Pi.single j (c j ^ 2) : Fin F.s → AdjoinRoot F.g) +
            (Pi.single j (c j) : Fin F.s → AdjoinRoot F.g) +
            (Pi.single j (1 : AdjoinRoot F.g) : Fin F.s → AdjoinRoot F.g)) =
            Pi.single j (c j ^ 2 + c j + 1) := by
          funext l
          by_cases hl : l = j <;> simp [hl]
        have hsum' : ((Pi.single j (c j ^ 2), (0 : F.κ → K)) +
            (Pi.single j (c j), 0) + (Pi.single j 1, 0) :
            (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) =
            (Pi.single j (c j ^ 2 + c j + 1), 0) := by
          apply Prod.ext
          · simpa using hsum
          · simp
        rw [hsum', hcj_sq]
        simp
      have hfix := CFSG.StandardType.ChoiceTwo.fix_of_mem_spSupported
        (x := x) (g := x) (O := ({(Polynomial.X : K[X]) - 1} : Set K[X])) hxL1
        (CFSG.StandardType.ChoiceTwo.phi3_irreducible hK)
        CFSG.StandardType.ChoiceTwo.monic_phi3
        (by intro h; exact CFSG.StandardType.ChoiceTwo.phi3_ne_X_sub_one h) hv
      have hpairs : ((Pi.single j (c j), (0 : F.κ → K)) :
          (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) = (Pi.single j 1, 0) :=
        F.Φ.injective (by rw [← hxv, hfix, hvdef])
      have hcj_eq : c j = 1 := by
        have h := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.1 j) hpairs
        simpa [Pi.single_eq_same] using h
      exact hcj hcj_eq
    · exfalso
      let f : Fin F.s → Multiplicative (ZMod 3) := Pi.mulSingle i (ofAdd (1 : ZMod 3))
      let t : ↥(CFSG.Open.StatedSp m K) := e₂.symm (F.τ f)
      have htE : t ∈ E := by
        have h : F.τ f ∈ E.map e₂.toMonoidHom := by
          rw [← hE']
          exact hτE f
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h
        have hty : t = y := by
          have h1 : e₂ y = F.τ f := hyeq
          have h2 : e₂.symm (e₂ y) = e₂.symm (F.τ f) := congrArg e₂.symm h1
          simpa [t] using h2.symm
        rw [hty]
        exact hy
      have htx : t * x = x * t := CFSG.Open.IsElemAbelian.comm hEel htE hxE
      have ht_act : ∀ d w, CFSG.RankThree.Classical.spEnd t (F.Φ (d, w)) =
          F.Φ (fun l => (if l = i then F.ζ else 1) * d l, w) := by
        intro d w
        have h := F.hτapp f (d, w)
        have heq : (e₂ t : ↥(sesqUnitaryGroup B)) = F.τ f := by
          dsimp [t]
          rw [e₂.apply_symm_apply]
        rw [← heq] at h
        have hsp_t : ((e₂ t : ↥(sesqUnitaryGroup B)) :
            LinearMap.GeneralLinearGroup K V) = CFSG.RankThree.Classical.spLin m K t := hsp t
        have h' : CFSG.RankThree.Classical.spEnd t (F.Φ (d, w)) =
            F.Φ (fun l => F.ζ ^ (toAdd (f l)).val * d l, w) := by
          simpa [CFSG.RankThree.Classical.spEnd, hsp_t] using h
        rw [h']
        congr 1
        apply Prod.ext
        · funext l
          by_cases hl : l = i
          · subst hl
            dsimp [f]
            rw [Pi.mulSingle_eq_same, toAdd_ofAdd, ZMod.val_one, pow_one, if_pos rfl]
          · dsimp [f]
            rw [Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod 3)) hl]
            simp [hl]
        · rfl
      have hxv_i : CFSG.RankThree.Classical.spEnd x (F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0))
          = F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0) := by
        have hx_i : CFSG.RankThree.Classical.spEnd x
            (F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0)) =
            F.Φ (Pi.single i (c i), 0) := by
          rw [hxk]
          congr 1
          apply Prod.ext
          · funext l
            by_cases hl : l = i
            · subst hl; simp [c]
            · simp [Pi.single_eq_of_ne hl]
          · rfl
        rw [hx_i, hci]
      have ht_fixed : t ∈ CFSG.RankThree.PartOne.spFixedFactor x := by
        refine CFSG.StandardType.ChoiceTwo.mem_spSupported_of hK hx3 htx ?_ ?_
        · intro h
          exact (h (Set.mem_singleton _)).elim
        · intro hphi v hv
          obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective v
          have hgen : CFSG.RankThree.Classical.spEnd x (F.Φ (d, w)) =
              F.Φ (fun l => c l * d l, w) := by
            rw [hxk]
          have hgen2 : CFSG.RankThree.Classical.spEnd x
              (CFSG.RankThree.Classical.spEnd x (F.Φ (d, w))) =
              F.Φ (fun l => c l ^ 2 * d l, w) := by
            rw [hgen, hxk]
            congr 1
            apply Prod.ext
            · funext l; simp [c, pow_two, mul_assoc]
            · rfl
          have hzero : F.Φ (fun l => (c l ^ 2 + c l + 1) * d l, w) = 0 := by
            have h := hv
            rw [hgen2, hgen] at h
            rw [← map_add, ← map_add] at h
            have hpair : ((fun l => c l ^ 2 * d l, w) + (fun l => c l * d l, w) +
                (d, w) : (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) =
                (fun l => (c l ^ 2 + c l + 1) * d l, w) := by
              apply Prod.ext
              · funext l
                simp only [Pi.add_apply, Prod.fst_add]
                ring
              · funext k
                simp only [Pi.add_apply, Prod.snd_add]
                rw [CharTwo.add_self_eq_zero, zero_add]
            rwa [hpair] at h
          have hdi : d i = 0 := by
            have h0pair : ((fun l => (c l ^ 2 + c l + 1) * d l, w) :
                (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) = 0 :=
              F.Φ.injective (by simpa using hzero)
            have h0 := congrFun (congrArg Prod.fst h0pair) i
            simp only at h0
            rw [hci] at h0
            have hone : ((1 : AdjoinRoot F.g) ^ 2 + 1 + 1) = 1 := by
              rw [one_pow, show (1 : AdjoinRoot F.g) + 1 = 0 from CharTwo.add_self_eq_zero 1,
                zero_add]
            rw [hone, one_mul] at h0
            exact h0
          rw [ht_act]
          congr 1
          apply Prod.ext
          · funext l
            by_cases hl : l = i
            · subst hl; simp [hdi]
            · simp [hl]
          · rfl
      have htC : t ∈ Subgroup.centralizer (L : Set ↥(CFSG.Open.StatedSp m K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hl3 : l ∈ CFSG.RankThree.Classical.spSupported x
            ({CFSG.StandardType.ChoiceTwo.phi3 K} : Set K[X]) := by
          rw [hL3] at hl
          exact Subgroup.commutator_le_self _ hl
        have hcomm := CFSG.StandardType.ChoiceTwo.commute_of_mem_spFixedFactor hK hx3
          (O := ({CFSG.StandardType.ChoiceTwo.phi3 K} : Set K[X]))
          (by
            intro h
            exact CFSG.StandardType.ChoiceTwo.phi3_ne_X_sub_one
              (Set.mem_singleton_iff.mp h).symm)
          ht_fixed hl3
        exact hcomm.symm
      have htCE : t ∈ E ⊓ Subgroup.centralizer (L : Set ↥(CFSG.Open.StatedSp m K)) :=
        ⟨htE, htC⟩
      rw [hCE] at htCE
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp htCE
      have hred : x ^ n = x ^ (n % (3 : ℤ)) := zpow_eq_zpow_emod' n hx3
      have htm : t = x ^ (n % (3 : ℤ)) := by rw [← hn, hred]
      have hr0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
      have hr3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
      have ht_cases : t = 1 ∨ t = x ∨ t = x ^ 2 := by
        interval_cases h : n % 3
        · left; simp [htm]
        · right; left; simp [htm]
        · right; right; simp [htm]
      set v := F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0) with hvdef
      have ht_v : CFSG.RankThree.Classical.spEnd t v = v := by
        rcases ht_cases with h | h | h
        · rw [h, CFSG.RankThree.PartOne.KCSpFull.spEnd_one, Module.End.one_apply]
        · rw [h]; exact hxv_i
        · rw [h, pow_two, CFSG.RankThree.PartOne.KCSpFull.spEnd_mul, Module.End.mul_apply,
            hxv_i, hxv_i]
      have ht_v' : CFSG.RankThree.Classical.spEnd t v = F.Φ (Pi.single i (F.ζ), 0) := by
        rw [hvdef, ht_act]
        congr 1
        apply Prod.ext
        · funext l
          by_cases hl : l = i
          · subst hl; simp
          · simp [Pi.single_eq_of_ne hl]
        · rfl
      have hpairs : ((Pi.single i (F.ζ), (0 : F.κ → K)) :
          (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) =
          (Pi.single i (1 : AdjoinRoot F.g), 0) :=
        F.Φ.injective (by rw [← ht_v', ht_v, hvdef])
      have hζ1' : F.ζ = 1 := by
        have h := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.1 i) hpairs
        simpa [Pi.single_eq_same] using h
      exact F.hζ1 hζ1'
  exact hno_fix

end CFSG.StandardType

end
