module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralChain
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.StandardType.E6Two

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.ClassicalInvolution.WeakCT

open Matrix
open scoped MatrixGroups commutatorElement


private theorem fixedA3_frameRoots_eq_a2Roots
    {τ : Tag} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    {α β : Fin τ.rank → ℤ} (hadd : ∀ i j k, σ i j + σ j k = σ i k)
    (hneg : ∀ i j, σ j i = -σ i j) (h01 : σ 0 1 = α) (h12 : σ 1 2 = β) :
    frameRoots σ = a2Roots α β := by
  have e02 : σ 0 2 = σ 0 1 + σ 1 2 := (hadd 0 1 2).symm
  have e10 : σ 1 0 = -σ 0 1 := hneg 0 1
  have e21 : σ 2 1 = -σ 1 2 := hneg 1 2
  have e20 : σ 2 0 = -σ 0 2 := hneg 0 2
  ext r
  simp only [frameRoots, a2Roots, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | simp [e02, e10, e21, e20, h01, h12]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, h01.symm⟩
    · exact ⟨1, 0, by decide, by rw [e10, h01]⟩
    · exact ⟨1, 2, by decide, h12.symm⟩
    · exact ⟨2, 1, by decide, by rw [e21, h12]⟩
    · exact ⟨0, 2, by decide, by rw [e02, h01, h12]⟩
    · exact ⟨2, 0, by decide, by rw [e20, e02, h01, h12]⟩

private theorem fixedA3_exists_a2Frame_E6
    {L : Type} [Field L] {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_weyl_a2Pair_E6 h
  have hfr := (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_frame (L := L)).transport v
  let σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ := fun i j =>
    v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j
  have h01 : σ 0 1 = α := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 0 1 = α
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_01, h0]
  have h12 : σ 1 2 = β := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 1 2 = β
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_12, h2]
  have hroots : frameRoots σ = a2Roots α β :=
    fixedA3_frameRoots_eq_a2Roots hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

theorem fixedWeyl_mem_rationalComponent_of_a3
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = 2)
    (hq : S.D.q = 2) {w : WeylGroup Tag.E6} (hρ : ∀ β, IsRoot Tag.E6 β → S.ρ β = w • β)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {γ δ γ' : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ) (hγ' : IsRoot Tag.E6 γ')
    (h1 : iform γ δ = -1) (h2 : iform δ γ' = -1) (h3 : iform γ γ' = 0)
    (hργ : S.ρ γ = -γ') (hρδ : S.ρ δ = -δ) (hργ' : S.ρ γ' = -γ)
    (hmem : ∀ r ∈ aChainRoots (![γ, δ, γ'] : Fin 3 → Fin Tag.E6.rank → ℤ),
      r ∈ rationalRoots S.ρ (rootCharHom a) i) :
    rootSL2 Tag.E6 L δ WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  let β : Fin 3 → Fin Tag.E6.rank → ℤ := ![γ, δ, γ']
  have hβ : ∀ c, IsRoot Tag.E6 (β c) := by
    intro c
    fin_cases c <;> simp [β, hγ, hδ, hγ']
  have hτ : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
    Or.inr (Or.inl rfl)
  have hG : ∀ c d, iform (β c) (β d) = chainGram c d := by
    intro c d
    fin_cases c <;> fin_cases d <;>
      simp [β, chainGram, h1, h2, h3,
        CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ,
        CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδ,
        CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ',
        iform_comm]
  have hγδ : IsRoot Tag.E6 (γ + δ) := by
    refine isRoot_add_of_iform_neg hγ hδ ?_ ?_
    · intro h
      rw [h, iform_neg_fst, CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδ] at h1
      omega
    · rw [h1]; omega
  have hδγ' : IsRoot Tag.E6 (δ + γ') := by
    refine isRoot_add_of_iform_neg hδ hγ' ?_ ?_
    · intro h
      rw [h, iform_neg_fst, CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ'] at h2
      omega
    · rw [h2]; omega
  have hformγδγ' : iform γ (δ + γ') = -1 := by
    rw [iform_add_right, h1, h3]
    norm_num
  have hγδγ' : IsRoot Tag.E6 (γ + (δ + γ')) := by
    refine isRoot_add_of_iform_neg hγ hδγ' ?_ ?_
    · intro h
      rw [h, iform_neg_fst,
        CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδγ'] at hformγδγ'
      omega
    · rw [hformγδγ']; norm_num
  have hA2_γδ : IsA2Pair γ δ := by
    refine ⟨hγ, hδ, hγδ, ?_, ?_⟩
    · rw [CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδ,
          CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ]
    · rw [h1, CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ]
      norm_num
  have hA2_δγ' : IsA2Pair δ γ' := by
    refine ⟨hδ, hγ', hδγ', ?_, ?_⟩
    · rw [CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ',
          CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδ]
    · rw [h2, CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδ]
      norm_num
  obtain ⟨ρ1, σ1, hfr1, h01, h12, hroots1⟩ := fixedA3_exists_a2Frame_E6 (L := L) hA2_γδ
  obtain ⟨ρ2, σ2, hfr2, h01', h12', hroots2⟩ := fixedA3_exists_a2Frame_E6 (L := L) hA2_δγ'
  have hθ : ∀ (c : Fin 3) (h : (c : ℕ) + 1 < 3), ∃ θ : SL(3, L) →* ModGL Tag.E6 L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 Tag.E6 L (β c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 Tag.E6 L (β ⟨c + 1, h⟩) := by
    intro c h
    fin_cases c
    · obtain ⟨θ, hθ0, hθ1⟩ := exists_normalized_a2Frame hfr1
      exact ⟨θ, by rw [hθ0, h01]; rfl, by rw [hθ1, h12]; rfl⟩
    · obtain ⟨θ, hθ0, hθ1⟩ := exists_normalized_a2Frame hfr2
      exact ⟨θ, by rw [hθ0, h01']; rfl, by rw [hθ1, h12']; rfl⟩
    · exact absurd h (by simp)
  obtain ⟨ψ, hψ⟩ := exists_chainHom hτ β hβ hG hθ
  have hframe := isSLFrame_chainHom hτ hβ hG hψ
  have hinj : Function.Injective ψ := by
    apply chainHom_injective hτ hβ hG hψ (by decide : 2 ≤ 3)
    intro (ζ : Lˣ) hζ _
    have hζL : ζ.val ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    have h2 : (ζ.val - 1) ^ (2 ^ 2) = 0 := by
      rw [sub_pow_char_pow, one_pow, show ζ.val ^ 2 ^ 2 = ζ.val ^ 4 by norm_num, hζL, sub_self]
    have h3 : ζ.val - 1 = 0 := (pow_eq_zero_iff (by norm_num)).1 h2
    exact Units.ext (sub_eq_zero.1 h3)
  let π : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  have hπ0 : π 0 = 3 := by decide
  have hπ1 : π 1 = 2 := by decide
  have hπ2 : π 2 = 1 := by decide
  have hπ3 : π 3 = 0 := by decide
  let Fr : L →+* L := iterateFrobenius L 2 1
  have hFr : ∀ c, Fr c = c ^ S.D.q := by
    intro c
    rw [hq]
    show iterateFrobenius L 2 1 c = c ^ 2
    rw [iterateFrobenius_def, pow_one]
  have hρ0 : S.ρ 0 = 0 := by
    have h0 := S.frob.neg_eq 0
    rw [neg_zero] at h0
    funext k
    have hk0 := congrFun h0 k
    simp only [Pi.neg_apply] at hk0
    simp only [Pi.zero_apply]
    omega
  have hρneg : ∀ x : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 x → S.ρ (-x) = -S.ρ x := by
    intro x hx
    rw [hρ (-x) (IsRoot.neg hx), smul_neg, ← hρ x hx]
  have hργδ : S.ρ (γ + δ) = -γ' - δ := by
    rw [hρ (γ + δ) hγδ, smul_add, ← hρ γ hγ, ← hρ δ hδ, hργ, hρδ]
    abel
  have hρδγ' : S.ρ (δ + γ') = -δ - γ := by
    rw [hρ (δ + γ') hδγ', smul_add, ← hρ δ hδ, ← hρ γ' hγ', hρδ, hργ']
    abel
  have hs3 : IsRoot Tag.E6 (γ + δ + γ') := by
    rw [add_assoc]
    exact hγδγ'
  have hργδγ' : S.ρ (γ + δ + γ') = -(γ + δ + γ') := by
    rw [hρ _ hs3, add_assoc, smul_add, ← hρ γ hγ, ← hρ (δ + γ') hδγ', hργ, hρδγ']
    abel
  have hω1 : chainω β 1 = γ := by
    have h := chainω_succ β (k := 0) (by norm_num)
    rw [chainω_zero] at h
    simpa [β] using h
  have hω2 : chainω β 2 = γ + δ := by
    have h := chainω_succ β (k := 1) (by norm_num)
    rw [hω1] at h
    simpa [β] using h
  have hω3 : chainω β 3 = γ + δ + γ' := by
    have h := chainω_succ β (k := 2) (by norm_num)
    rw [hω2] at h
    simpa [β] using h
  have s01 : chainσ β 0 1 = γ := by
    show chainω β 1 - chainω β 0 = γ
    rw [chainω_zero, hω1]; abel
  have s02 : chainσ β 0 2 = γ + δ := by
    show chainω β 2 - chainω β 0 = γ + δ
    rw [chainω_zero, hω2]; abel
  have s03 : chainσ β 0 3 = γ + δ + γ' := by
    show chainω β 3 - chainω β 0 = γ + δ + γ'
    rw [chainω_zero, hω3]; abel
  have s12 : chainσ β 1 2 = δ := by
    show chainω β 2 - chainω β 1 = δ
    rw [hω1, hω2]; abel
  have s13 : chainσ β 1 3 = δ + γ' := by
    show chainω β 3 - chainω β 1 = δ + γ'
    rw [hω1, hω3]; abel
  have s23 : chainσ β 2 3 = γ' := by
    show chainω β 3 - chainω β 2 = γ'
    rw [hω2, hω3]; abel
  have s10 : chainσ β 1 0 = -γ := by rw [chainσ_neg β 0 1, s01]
  have s20 : chainσ β 2 0 = -(γ + δ) := by rw [chainσ_neg β 0 2, s02]
  have s30 : chainσ β 3 0 = -(γ + δ + γ') := by rw [chainσ_neg β 0 3, s03]
  have s21 : chainσ β 2 1 = -δ := by rw [chainσ_neg β 1 2, s12]
  have s31 : chainσ β 3 1 = -(δ + γ') := by rw [chainσ_neg β 1 3, s13]
  have s32 : chainσ β 3 2 = -γ' := by rw [chainσ_neg β 2 3, s23]
  have hSρ_chainσ : ∀ i j : Fin 4, i ≠ j → S.ρ (chainσ β i j) = chainσ β (π i) (π j) := by
    have c01 : S.ρ (chainσ β 0 1) = chainσ β (π 0) (π 1) := by
      rw [s01, hπ0, hπ1, s32, hργ]
    have c02 : S.ρ (chainσ β 0 2) = chainσ β (π 0) (π 2) := by
      rw [s02, hπ0, hπ2, s31, hργδ]; abel
    have c03 : S.ρ (chainσ β 0 3) = chainσ β (π 0) (π 3) := by
      rw [s03, hπ0, hπ3, s30, hργδγ']
    have c10 : S.ρ (chainσ β 1 0) = chainσ β (π 1) (π 0) := by
      rw [s10, hπ1, hπ0, s23, hρneg γ hγ, hργ, neg_neg]
    have c12 : S.ρ (chainσ β 1 2) = chainσ β (π 1) (π 2) := by
      rw [s12, hπ1, hπ2, s21, hρδ]
    have c13 : S.ρ (chainσ β 1 3) = chainσ β (π 1) (π 3) := by
      rw [s13, hπ1, hπ3, s20, hρδγ']; abel
    have c20 : S.ρ (chainσ β 2 0) = chainσ β (π 2) (π 0) := by
      rw [s20, hπ2, hπ0, s13, hρneg (γ + δ) hγδ, hργδ]; abel
    have c21 : S.ρ (chainσ β 2 1) = chainσ β (π 2) (π 1) := by
      rw [s21, hπ2, hπ1, s12, hρneg δ hδ, hρδ, neg_neg]
    have c23 : S.ρ (chainσ β 2 3) = chainσ β (π 2) (π 3) := by
      rw [s23, hπ2, hπ3, s10, hργ']
    have c30 : S.ρ (chainσ β 3 0) = chainσ β (π 3) (π 0) := by
      rw [s30, hπ3, hπ0, s03, hρneg (γ + δ + γ') hs3, hργδγ', neg_neg]
    have c31 : S.ρ (chainσ β 3 1) = chainσ β (π 3) (π 1) := by
      rw [s31, hπ3, hπ1, s02, hρneg (δ + γ') hδγ', hρδγ']; abel
    have c32 : S.ρ (chainσ β 3 2) = chainσ β (π 3) (π 2) := by
      rw [s32, hπ3, hπ2, s01, hρneg γ' hγ', hργ', neg_neg]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact c01 | exact c02 | exact c03 | exact c10 | exact c12 | exact c13
        | exact c20 | exact c21 | exact c23 | exact c30 | exact c31 | exact c32
  have hΨ : ∀ i j : Fin 4, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      S.D.step (pinnedX Tag.E6 L (chainσ β i j) c) =
        pinnedX Tag.E6 L (chainσ β (π i) (π j)) ((b : L) * Fr c) := by
    intro i j hij
    refine ⟨1, fun c => ?_⟩
    rw [LangRat.step_pinnedX_of_charTwo S (isRoot_chainσ hβ hG hij), hSρ_chainσ i j hij]
    congr 1
    rw [hq]
    show c ^ 2 = (1 : Lˣ) * iterateFrobenius L 2 1 c
    rw [iterateFrobenius_def, pow_one]
    simp
  obtain ⟨-, hfin, hqs, hcard⟩ :=
    hframe.fix_split hinj Nat.prime_two (by norm_num : 1 ≤ 1) (k := k) (by simpa using hk)
      (by norm_num : 3 ≤ 4) Fr (fun c => (hFr c).trans (by rw [hq, pow_one])) S.D.step (splitLine_step_injective S) π hΨ
  let P : Subgroup (ModGL Tag.E6 L) := ψ.range ⊓ S.D.step.eqLocus (MonoidHom.id _)
  have hPperf : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥P := hqs.1
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hδ_frame : δ ∈ frameRoots (chainσ β) := by
    refine ⟨1, 2, by decide, ?_⟩
    rw [chainσ_of_val_eq β (a := 1) (b := 2) (by decide)]
    simp [β]
  have hnegδ_frame : -δ ∈ frameRoots (chainσ β) := by
    refine ⟨2, 1, by decide, ?_⟩
    rw [chainσ_neg β 1 2, chainσ_of_val_eq β (a := 1) (b := 2) (by decide)]
    simp [β]
  have hsub : ({δ, -δ} : Set (Fin Tag.E6.rank → ℤ)) ⊆ frameRoots (chainσ β) := by
    intro x hx
    rcases hx with rfl | hx
    · exact hδ_frame
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hnegδ_frame
  have hgS : rootSL2 Tag.E6 L δ WSL ∈ ψ.range := by
    rw [hframe.range]
    exact CFSG.LieType.Chevalley.rootSpan_mono hsub (rootSL2_mem_rootSpan_pair hδ WSL)
  have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_WSL]
    fin_cases i <;> fin_cases j <;> simp [Fr]
  have hgstep : S.D.step (rootSL2 Tag.E6 L δ WSL) = rootSL2 Tag.E6 L δ WSL := by
    rw [CFSG.StandardType.LangRat.step_rootSL2_of_rho_neg S hδ hρδ Fr hFr WSL, hWfix,
      CFSG.RankThree.Classical2.conjSLn_toGL]
    congr 1
    group
  have hgP : rootSL2 Tag.E6 L δ WSL ∈ P := by
    refine ⟨hgS, ?_⟩
    show S.D.step (rootSL2 Tag.E6 L δ WSL) = (MonoidHom.id _) (rootSL2 Tag.E6 L δ WSL)
    exact hgstep
  let X := ↥P
  let ψP : X →* ModGL Tag.E6 L := P.subtype
  have hψS : ∀ y : X, ψP y ∈ rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) := by
    intro y
    have hy : (y : ModGL Tag.E6 L) ∈ P := y.2
    have hy_range : (y : ModGL Tag.E6 L) ∈ ψ.range := hy.1
    rw [hframe.range] at hy_range
    have hsub_rat : frameRoots (chainσ β) ⊆ rationalRoots S.ρ (rootCharHom a) i := by
      intro r hr
      obtain ⟨i0, j0, hij0, rfl⟩ := hr
      exact hmem (chainσ β i0 j0)
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.chainσ_mem_aChainRoots β hij0)
    exact CFSG.LieType.Chevalley.rootSpan_mono hsub_rat hy_range
  have hψA : ∀ y : X, ψP y ∈ adjointGroup Tag.E6 L := by
    intro y
    exact hframe.range_le_adjointGroup y.2.1
  have hψF : ∀ y : X, S.D.step (ψP y) = ψP ((MonoidHom.id X) y) := by
    intro y
    exact y.2.2
  have hKperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := hPperf
  have hres := map_fix_le_rationalComponent S i ψP hψS hψA (MonoidHom.id X) hψF ⊤
    (fun _ _ => rfl) hKperf
  have hres' := hres ⟨rootSL2 Tag.E6 L δ WSL, hgP⟩ (Subgroup.mem_top _)
  change (rootSL2 Tag.E6 L δ WSL) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i at hres'
  exact hres'

end CFSG.StandardType.E6Two

end
