module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnComp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[local instance] private theorem charP_algebraicClosure_two {K : Type} [Field K] [CharP K 2] :
    CharP (AlgebraicClosure K) 2 :=
  (Algebra.charP_iff (K := K) (L := AlgebraicClosure K) 2).symm.mpr inferInstance

private theorem rationalRoots_eq_of_rho_pm
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = γ ∨ S.ρ γ = -γ) (i : KernelComponent (rootCharHom a)) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots i
  refine Set.Subset.antisymm ?_ fun γ hγ => ⟨0, γ, hγ, rfl⟩
  rintro _ ⟨k, δ, hδ, rfl⟩
  induction k with
  | zero => exact hδ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases hρ _ (hΨ.isRoot _ ih) with h | h
    · rw [h]
      exact ih
    · rw [h]
      exact hΨ.neg_mem _ ih

private theorem e7RootChar_frameDiag_eq_one {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) (s : Fin Tag.E7.rank → ZMod p) {γ : Fin Tag.E7.rank → ℤ}
    (hγ : ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord Tag.E7 p s j = 0) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E7 p s)) γ = 1 := by
  rw [NoOffE8Five.rootChar_zetaVec hζ, hγ, ofAdd_zero, map_one]

theorem e7Enn_class
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (ι : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hιι₀ : ∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s)
    (hT : ∀ s, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus)
    (hρ : ∀ γ, IsRoot .E7 γ → S.ρ γ = γ ∨ S.ρ γ = -γ)
    {t : Fin Tag.E7.rank → ZMod p} (ht : ι₀ (Multiplicative.ofAdd t) ≠ 1)
    {Y : Subgroup (adjointGroup .E7 K)}
    (hY : IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (adjointGroup .E7 K)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))),
      Y.map ι = rationalComponent S.ρ S.Γ
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))) i ∧
      ∀ s : Fin Tag.E7.rank → ZMod p,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t))) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E7 p s j = 0) →
        ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (adjointGroup .E7 K)) := by
  classical
  have hp : p.Prime := Fact.out
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := fun h0 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)).symm
  have hap : ∀ k, TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t) k ^ p = 1 :=
    fun k => by
      rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hιa : ι (ι₀ (Multiplicative.ofAdd t)) =
      rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p t)) := by
    rw [hιι₀ t]
    rfl
  obtain ⟨i, _, hmap⟩ := LangRat.langRatComp_of_component (p₀ := 5) S (Or.inl rfl) hp hpL ι hι
    hrange hιa (hT t) hap ht (CFSG.Assembly.isComponentOf_iff_open.1 hY)
  refine ⟨i, hmap, ?_⟩
  intro s hs
  have hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord .E7 p t))) i,
      rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 p s)) γ = 1 := by
    intro γ hγ
    rw [rationalRoots_eq_of_rho_pm S hρ i] at hγ
    exact e7RootChar_frameDiag_eq_one hζ s (hs γ hγ)
  have hle := LangRat.rationalComponent_le_centralizer S i hb
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hyR : ι y ∈ rationalComponent S.ρ S.Γ (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord .E7 p t))) i := by
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  have hcomm : rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord .E7 p s)) * ι y =
      ι y * rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord .E7 p s)) :=
    (Subgroup.mem_centralizer_iff.1 (hle hyR)) _ (by simp)
  apply hι
  rw [map_mul, map_mul, hιι₀ s]
  exact hcomm.symm

section Lower

open CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.LangRat CFSG.StandardType.QTwoCav
  CFSG.StandardType.MaxRankE8Action
open scoped MatrixGroups

private def e7PathList : Fin 5 → Fin 3 → Fin 7 :=
  ![![0, 2, 3], ![1, 3, 4], ![2, 3, 4], ![3, 4, 5], ![4, 5, 6]]

private def e7PathIdx (Sd : Finset (Fin 7)) (j : Fin 7) : Fin 5 :=
  if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 2
  else if j = 3 then (if 2 ∈ Sd then 1 else 2)
  else if j = 4 then (if 5 ∈ Sd then 2 else 3)
  else if j = 5 then 3 else 4

open scoped CFSG.Decide.Bounded in
private theorem e7Path_check :
    ∀ Sd ∈ e7LeviDel, ∀ j : Fin 7, j ∉ Sd →
      (∀ c : Fin 3, e7PathList (e7PathIdx Sd j) c ∉ Sd) ∧
        (∃ c : Fin 3, e7PathList (e7PathIdx Sd j) c = j) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7Path_inj (i : Fin 5) : Function.Injective (e7PathList i) := by
  revert i
  decide +kernel

private theorem e7Path_gram (i : Fin 5) (c d : Fin 3) :
    iform (kacE7.extRoot (some (e7PathList i c))) (kacE7.extRoot (some (e7PathList i d))) =
      chainGram c d := by
  rw [kacE7_extRoot]
  revert i c d
  decide +kernel

private theorem e7Path_edge (i : Fin 5) (c : Fin 2) :
    (nodeIdx (some (e7PathList i c.castSucc)), nodeIdx (some (e7PathList i c.succ))) ∈
      e7EdgeIdx := by
  revert i c
  decide +kernel

private def e7RealizedWeyl {G : Type} [Group G] (p : ℕ) [NeZero p]
    (ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* G) (Y : Subgroup G) :
    Subgroup (WeylGroup .E7) where
  carrier := {w | ∃ g ∈ Y, ∀ s, g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
    ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p w s))}
  one_mem' := by
    refine ⟨1, Y.one_mem, fun s => ?_⟩
    rw [TableBExc.torusAct_one]
    simp
  mul_mem' := by
    rintro a b ⟨g, hg, hg'⟩ ⟨h, hh, hh'⟩
    refine ⟨g * h, Y.mul_mem hg hh, fun s => ?_⟩
    rw [mul_inv_rev]
    calc g * h * ι₀ (Multiplicative.ofAdd s) * (h⁻¹ * g⁻¹)
        = g * (h * ι₀ (Multiplicative.ofAdd s) * h⁻¹) * g⁻¹ := by group
      _ = g * ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p b s)) * g⁻¹ := by rw [hh' s]
      _ = ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p a
            (TableBExc.torusAct .E7 p b s))) := hg' _
      _ = ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (a * b) s)) := by
            rw [TableBExc.torusAct_mul]
  inv_mem' := by
    rintro a ⟨g, hg, hg'⟩
    refine ⟨g⁻¹, Y.inv_mem hg, fun s => ?_⟩
    have hta : TableBExc.torusAct .E7 p a (TableBExc.torusAct .E7 p a⁻¹ s) = s := by
      rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
    have hs : ι₀ (Multiplicative.ofAdd s) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p a
          (TableBExc.torusAct .E7 p a⁻¹ s))) := by rw [hta]
    calc g⁻¹ * ι₀ (Multiplicative.ofAdd s) * (g⁻¹)⁻¹
        = g⁻¹ * ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p a
              (TableBExc.torusAct .E7 p a⁻¹ s))) * g := by rw [hs, inv_inv]
      _ = g⁻¹ * (g * ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p a⁻¹ s)) * g⁻¹) * g := by
            rw [← hg' (TableBExc.torusAct .E7 p a⁻¹ s)]
      _ = ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p a⁻¹ s)) := by group

private theorem e7Monomial_conj_frameDiag_gen
    {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) {m : ModGL .E7 L} (hm : m ∈ monomialSubgroup .E7 L)
    {w : WeylGroup .E7} (hmw : MapsRootLines m w) (s : Fin Tag.E7.rank → ZMod p) :
    m * ExcFrames.frameDiag ζ hζ s * m⁻¹ =
      ExcFrames.frameDiag ζ hζ (TableBExc.torusAct .E7 p w s) := by
  rw [ExcFrames.frameDiag, TableBExc.E6Three.monomial_conj_rootDiagUnit_weylTuple hm hmw,
    TableBExc.E6Three.weylTuple_zetaVec, ExcFrames.adAct_frameCoord, ExcFrames.frameDiag]

private theorem e7RootSL2_mem_rationalComponent_of_path
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E7 L p₀)
    (hρ : ∀ γ, IsRoot .E7 γ → S.ρ γ = -γ)
    {n : ℕ} (hn : 0 < n) (hq : S.D.q = 2 ^ n)
    {a : Fin Tag.E7.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {v : WeylGroup .E7} {Sd : Finset (Fin 7)} (hSd : Sd ∈ e7LeviDel)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E7 {j | j ∉ Sd})
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {j : Fin 7} (hj : j ∉ Sd) :
    rootSL2 .E7 L (v • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  let β : Fin Tag.E7.rank → ℤ := Pi.single j 1
  obtain ⟨hmem, hcont⟩ := e7Path_check Sd hSd j hj
  let l : Fin 3 → Option (Fin Tag.E7.rank) :=
    fun c => some (e7PathList (e7PathIdx Sd j) c)
  have hl : Function.Injective l := fun x y hxy => e7Path_inj (e7PathIdx Sd j) (Option.some.inj hxy)
  have hG : ∀ c d : Fin 3, iform (kacE7.extRoot (l c)) (kacE7.extRoot (l d)) = chainGram c d :=
    fun c d => e7Path_gram (e7PathIdx Sd j) c d
  have hA2 : ∀ (c : Fin 3) (hc : (c : ℕ) + 1 < 3), ∃ (ρ : SL(3, L) →* ModGL .E7 L)
      (σ : Fin 3 → Fin 3 → Fin Tag.E7.rank → ℤ), CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧
        σ 0 1 = kacE7.extRoot (l c) ∧ σ 1 2 = kacE7.extRoot (l ⟨(c : ℕ) + 1, hc⟩) := by
    intro c hc
    have hc2 : (⟨c, by omega⟩ : Fin 2).castSucc = c := Fin.ext rfl
    have hc2' : (⟨c, by omega⟩ : Fin 2).succ = ⟨(c : ℕ) + 1, hc⟩ := Fin.ext rfl
    have hE := e7Path_edge (e7PathIdx Sd j) ⟨c, by omega⟩
    rw [hc2, hc2'] at hE
    exact e7_frames _ _ hE
  obtain ⟨ψ, σ, hψ, hroots⟩ :=
    exists_frame_of_path (L := L) (Or.inr (Or.inr (Or.inl rfl))) kacE7 hl hG hA2 v
  have hnone : none ∉ Set.range l := by
    rintro ⟨c, hc⟩
    simp [l] at hc
  have hpar : kacE7.rootsOf (Set.range l) ⊆
      parabolicRoots .E7 {x : Fin Tag.E7.rank | x ∉ Sd} := by
    rw [KacData.rootsOf_eq_parabolicRoots (K := kacE7) hnone]
    refine parabolicRoots_mono ?_
    intro x hx
    obtain ⟨c, hc⟩ := hx
    have hci : e7PathList (e7PathIdx Sd j) c = x := by
      have h1 : (some (e7PathList (e7PathIdx Sd j) c) : Option (Fin Tag.E7.rank)) = some x := by
        simpa [l] using hc
      exact Option.some.inj h1
    rw [← hci]
    exact hmem c
  have hsub : frameRoots σ ⊆ componentRoots (rootCharHom a) i := by
    rw [hroots, hΨ]
    rintro γ ⟨δ, hδ, rfl⟩
    exact ⟨δ, hpar hδ, rfl⟩
  obtain ⟨c, hc⟩ := hcont
  have hγmem : v • β ∈ frameRoots σ := by
    rw [hroots]
    refine ⟨kacE7.extRoot (some j), ?_, ?_⟩
    · exact extRoot_mem_rootsOf (K := kacE7) ⟨c, by simp [l, hc]⟩
    · simp [kacE7_extRoot, e7ExtVec, β]
  have hν : 3 ≤ 4 := by omega
  have hker : ψ.ker ≠ ⊤ := frame_ker_ne_top_of_isSLFrame (ν := 3 + 1) (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(4, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_of_frame_of_isSLFrame (ν := 3 + 1) (by omega) hker
  have hΨc := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot .E7).subset fun γ hγ => hγ.1.1
  have hstable : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hρ γ hγ.1.1]
    exact hΨc.neg_mem γ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstable
  have hπ : ∀ x y : Fin 4, x ≠ y → (S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] (σ x y) = σ y x := by
    intro x y hxy
    rw [hs1, Function.iterate_one, hρ _ (hψ.isRoot x y hxy), hψ.neg x y]
  obtain ⟨F', hcomm, hperf⟩ := exists_unitary_source_perfect_of_frame (S := S)
    (a := a) (ν := 4) i hν hψ 1 hπ hs1 (k' := k') (r := 2) (e := n) Nat.prime_two hn hq
    (by intro hconj; exact absurd (congrArg Prod.fst hconj) (by norm_num))
  set g : ModGL .E7 L := rootSL2 .E7 L (v • β) WSL with hg
  have hβroot : IsRoot .E7 β := isRoot_single .E7 j
  have hγroot : IsRoot .E7 (v • β) := IsRoot.smul hβroot v
  have hnegmem : -(v • β) ∈ frameRoots σ := by
    obtain ⟨x, y, hxy, heq⟩ := hγmem
    refine ⟨y, x, hxy.symm, ?_⟩
    rw [heq]
    exact (hψ.neg x y).symm
  have hgframe : g ∈ rootSpan .E7 L (frameRoots σ) := by
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hγroot WSL)
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγmem
    · exact hnegmem
  have hmodel := rootSL2_WSL_mem_model_of_rho S hγroot (Or.inr (hρ _ hγroot))
  have hgfix : S.D.step g = g := (S.D.mem_model.mp hmodel).2
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self (v • β)
  exact map_eqLocus_le_rationalComponent_of_frame (S := S) (a := a) (g := g) i hψ hsub
    hkercenter hodd F' hcomm hperf hgframe hgfix hg2

theorem e7Enn_lower
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (ι : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)) (hι : Function.Injective ι)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K}
    (hιι₀ : ∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s)
    (hρ : ∀ γ, IsRoot .E7 γ → S.ρ γ = -γ) {n : ℕ} (hn : 0 < n) (hq : S.D.q = 2 ^ n)
    {a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ} (i : KernelComponent (rootCharHom a))
    {Y : Subgroup (adjointGroup .E7 K)}
    (hY : Y.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {v : WeylGroup .E7} {Sd : Finset (Fin 7)} (hSd : Sd ∈ e7LeviDel)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E7 {j | j ∉ Sd}) :
    ∀ c ∈ componentRoots (rootCharHom a) i, ∃ g ∈ Y, ∀ s,
      g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (rootReflection c) s)) := by
  classical
  let R := e7RealizedWeyl p ι₀ Y
  have hconj : ∀ j : Fin 7, j ∉ Sd → v * simple .E7 j * v⁻¹ ∈ R := by
    intro j hj
    let β : Fin Tag.E7.rank → ℤ := Pi.single j 1
    have hmem : rootSL2 .E7 (AlgebraicClosure K) (v • β) WSL ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      e7RootSL2_mem_rationalComponent_of_path (L := AlgebraicClosure K) (k' := K)
        S hρ hn hq (a := a) i hSd hΨ hj
    have hmap : rootSL2 .E7 (AlgebraicClosure K) (v • β) WSL ∈ Y.map ι := by
      rw [hY]
      exact hmem
    obtain ⟨g, hgY, hgι⟩ := Subgroup.mem_map.mp hmap
    have hβroot : IsRoot .E7 β := isRoot_single .E7 j
    have hγroot : IsRoot .E7 (v • β) := IsRoot.smul hβroot v
    have hact : ∀ s, g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (rootReflection (v • β)) s)) := by
      intro s
      apply hι
      calc ι (g * ι₀ (Multiplicative.ofAdd s) * g⁻¹)
          = ι g * ι (ι₀ (Multiplicative.ofAdd s)) * (ι g)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = rootSL2 .E7 (AlgebraicClosure K) (v • β) WSL * ExcFrames.frameDiag ζ hζ s *
              (rootSL2 .E7 (AlgebraicClosure K) (v • β) WSL)⁻¹ := by rw [hgι, hιι₀]
        _ = ExcFrames.frameDiag ζ hζ (TableBExc.torusAct .E7 p (rootReflection (v • β)) s) :=
              e7Monomial_conj_frameDiag_gen hζ
                (CFSG.ClassicalInvolution.ModelFacts.Levi.rootSL2_WSL_mem_monomialSubgroup
                  (τ := .E7) (K := AlgebraicClosure K) hγroot)
                (CFSG.ClassicalInvolution.ModelFacts.Levi.mapsRootLines_rootSL2_WSL
                  (τ := .E7) (K := AlgebraicClosure K) hγroot) s
        _ = ι (ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p
              (rootReflection (v • β)) s))) := (hιι₀ _).symm
    have hw : rootReflection (v • β) = v * simple .E7 j * v⁻¹ :=
      rootReflection_eq_conj (w := v) (j := j) (by simp [β])
    refine ⟨g, hgY, fun s => ?_⟩
    have h := hact s
    rwa [hw] at h
  have hclosure : Subgroup.closure ((fun j => v * simple .E7 j * v⁻¹) ''
      {j : Fin Tag.E7.rank | j ∉ Sd}) ≤ R := by
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨j, hj, rfl⟩
    exact hconj j hj
  rw [← closure_rootReflection_smul_parabolicRoots (τ := .E7) v
    {j : Fin Tag.E7.rank | j ∉ Sd}] at hclosure
  intro c hc
  rw [hΨ] at hc
  obtain ⟨α, hα, rfl⟩ := hc
  exact hclosure (Subgroup.subset_closure (show rootReflection (v • α) ∈
    {s : WeylGroup .E7 | ∃ γ ∈ (fun α => v • α) '' parabolicRoots .E7
      {j : Fin Tag.E7.rank | j ∉ Sd}, s = rootReflection γ}
    from ⟨v • α, ⟨α, hα, rfl⟩, rfl⟩))

end Lower

end CFSG.StandardType

end
