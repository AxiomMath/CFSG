module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoLower
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitFoldFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Class
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.StandardType.ExcFrames.E6QPlusThree CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp


private theorem e6c_top_eq_bot {K : Type*} [Group K] (hsol : Group.IsSolvable K)
    (htop : commutator K = ⊤) : (⊤ : Subgroup K) = ⊥ := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def K).mp hsol
  have hall : ∀ m, derivedSeries K m = ⊤ := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  rw [← hall n, hn]

theorem e6Two_classFacts {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (S : LangSetup .E6 (AlgebraicClosure K) 5) (hq : S.D.q = Nat.card K)
    (hρ : ∀ β, IsRoot .E6 β → S.ρ β = e6W0 • β)
    (ι : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K)
    (hι₀ : ∀ s, ι (ι₀ s) = e6ThreeDiag ζ hζ s) (hT : ∀ s, e6ThreeDiag ζ hζ s ∈ S.D.torus)
    (t : Fin Tag.F4.rank → ZMod 3) (ht : ι₀ (Multiplicative.ofAdd t) ≠ 1)
    {Y : Subgroup (adjointGroup .E6 K)}
    (hY : CFSG.Assembly.IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (adjointGroup .E6 K)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))),
      (∀ s : Fin Tag.F4.rank → ZMod 3,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))) i,
          ∑ j, (γ j : ZMod 3) * ExcFrames.frameCoord .F4 3 s j = 0) →
        ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (adjointGroup .E6 K))) ∧
      (∀ c ∈ componentRoots
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))) i,
        ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (rootReflection c) s))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set a₆ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t) with ha₆
  have hd : ι (ι₀ (Multiplicative.ofAdd t)) = rootDiagUnit .E6 a₆ := by
    rw [hι₀]
    rfl
  have hd1 : rootDiagUnit .E6 a₆ ≠ 1 := by
    intro h
    apply ht
    apply hι
    rw [hd, h, map_one]
  have hdT : rootDiagUnit .E6 a₆ ∈ S.D.torus := by
    have := hT (Multiplicative.ofAdd t)
    rwa [e6ThreeDiag_apply] at this
  have hap : ∀ i, a₆ i ^ 3 = 1 := by
    intro i
    change (ζ ^ (ExcFrames.twE6ThreeFrame t i).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    decide
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
    Nat.prime_three hpL (fun h => absurd h (by decide)) hdT hap hd1
  have hβ : ∀ c, ι (MulAut.conj (ι₀ (Multiplicative.ofAdd t)) c) =
      rootDiagUnit .E6 a₆ * ι c * (rootDiagUnit .E6 a₆)⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hd]
  have hfix : fixSubgroup (MulAut.conj (ι₀ (Multiplicative.ofAdd t))) =
      Subgroup.centralizer {ι₀ (Multiplicative.ofAdd t)} := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      calc x * ι₀ (Multiplicative.ofAdd t) =
          ι₀ (Multiplicative.ofAdd t) * x * (ι₀ (Multiplicative.ofAdd t))⁻¹ *
            ι₀ (Multiplicative.ofAdd t) := by rw [h]
        _ = ι₀ (Multiplicative.ofAdd t) * x := inv_mul_cancel_right _ _
    · intro h
      rw [← h, mul_inv_cancel_right]
  obtain ⟨i₆, hq6, hmap⟩ := components_of_langSetup S Nat.prime_three ι hι hrange
    (MulAut.conj (ι₀ (Multiplicative.ofAdd t))) hβ hdT hap hd1 hTame
    (hfix ▸ CFSG.Assembly.isComponentOf_iff_open.1 hY)
  have hρa : ∀ i, a₆ (TwistTag.E6.perm i) = a₆ i := fun i => twE6Split_zetaVec_perm hζ t i
  have hχ6 : ∀ x, rootCharHom a₆ (Multiplicative.ofAdd (permLattice TwistTag.E6.perm x)) =
      rootCharHom a₆ (Multiplicative.ofAdd x) := fun x => twE6Split_rootChar_perm hρa x
  have h2 : ∀ m : (AlgebraicClosure K)ˣ, m ^ 2 = 1 → m = 1 :=
    fun m hm => twE6Split_two_torsion m hm
  have hχ : ∀ γ, (MonoidHom.id (AlgebraicClosure K)ˣ)
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))
        (Multiplicative.ofAdd γ)) =
      rootCharHom a₆ (Multiplicative.ofAdd (TwistTag.E6.foldMap γ)) := by
    intro γ
    have h := twE6Split_char_fold (p := 3) (RingHom.id (AlgebraicClosure K)) hζ hζ t γ
    exact h
  obtain ⟨i₄, hA, hB⟩ := TwE6SplitFold.fold_class (rootCharHom a₆) hχ6 h2
    (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t)))
    (MonoidHom.id _) Function.injective_id hχ i₆
  refine ⟨i₄, fun s hs => ?_, ?_⟩
  ·
    set b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
      TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame s) with hb
    have hbperm : ∀ i, b (TwistTag.E6.perm i) = b i := fun i => twE6Split_zetaVec_perm hζ s i
    have hy : ∀ i, ExcFrames.twE6ThreeFrame s (TwistTag.E6.perm i) =
        ExcFrames.twE6ThreeFrame s i := fun i => twE6Split_frameCoord_perm s i
    have hδ : ∀ δ ∈ componentRoots (rootCharHom a₆) i₆, rootChar b δ = 1 := by
      intro δ hδmem
      obtain ⟨γ, hγ, hγδ⟩ := hA δ hδmem
      apply ggTBJTwE6_rootChar_zetaVec_eq_one hζ (ExcFrames.twE6ThreeFrame s) δ
      have h0 := hs γ hγ
      have hpf := twE6Split_pairing_foldMap (p := 3) γ (ExcFrames.twE6ThreeFrame s)
      have h1 : ∑ j : Fin Tag.E6.rank, ((TwE6SplitFold.twE6OrbSum δ j : ℤ) : ZMod 3) *
          ExcFrames.twE6ThreeFrame s j = 0 := by
        rw [← hγδ]
        refine hpf.trans ?_
        rw [← h0]
        refine Finset.sum_congr rfl fun b' _ => ?_
        exact congrArg (fun x => ((γ b' : ℤ) : ZMod 3) * x)
          (twE6Split_frameCoord_sum (p := 3) s b')
      exact twE6Split_pairing_orbSum_eq_zero (p := 3) (by norm_num) hy δ h1
    have hb' : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a₆) i₆, rootChar b γ = 1 := by
      rintro _ ⟨k, δ, hδmem, rfl⟩
      induction k with
      | zero => exact hδ δ hδmem
      | succ k ih =>
        have hroot : IsRoot .E6 ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ) :=
          LangRat.isRoot_of_mem_rationalRoots S i₆ ⟨k, δ, hδmem, rfl⟩
        have h2 : rootChar b (permLattice CFSG.RankThree.E6.e6Rho
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ)) =
            rootChar b ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ) :=
          twE6Split_rootChar_perm hbperm _
        rw [Function.iterate_succ_apply', hρ _ hroot, e6W0_smul,
          CFSG.RankThree.Chevalley.rootChar_neg_eq_inv, h2, ih, inv_one]
    have hcent := LangRat.rationalComponent_le_centralizer S i₆ hb'
    intro y hy'
    have hyR : ι y ∈ rationalComponent S.ρ S.Γ (rootCharHom a₆) i₆ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ι hy'
    have hxι : ι (ι₀ (Multiplicative.ofAdd s)) = rootDiagUnit .E6 b := by
      rw [hι₀]
      rfl
    have h1 : ι y * ι (ι₀ (Multiplicative.ofAdd s)) = ι (ι₀ (Multiplicative.ofAdd s)) * ι y := by
      rw [hxι]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hyR)
    apply hι
    rw [map_mul, map_mul]
    exact h1
  ·
    have hYns : ¬ Group.IsSolvable ↥Y := by
      intro hYs
      obtain ⟨-, -, hperf, hsimp⟩ := hY
      have htop := e6c_top_eq_bot hYs hperf
      haveI : Subsingleton ↥Y := by
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup ↥Y) := htop ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup ↥Y) := htop ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      haveI : Subsingleton (↥Y ⧸ Subgroup.center ↥Y) := inferInstance
      exact hsimp.toNontrivial.exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
    have ht0 : t ≠ 0 := by
      intro h
      apply ht
      rw [h, ofAdd_zero, map_one]
    exact e6Two_lowerClause hK S hq hρ ι hι hζo ι₀ hι₀ hT t ht0 i₆ hmap hYns i₄ hB

end CFSG.StandardType

end
