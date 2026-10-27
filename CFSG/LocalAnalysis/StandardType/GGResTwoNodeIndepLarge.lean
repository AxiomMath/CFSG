module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndep
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtLK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepDepTwin
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPm1
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtThree
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6a_rowAt_mono {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    {R R' : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hRR : ∀ labJ labX, R p labJ labX → R' p labJ labX) (h : GGResRowAt R p J X) :
    GGResRowAt R' p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hRR _ _ hr⟩

theorem l6a_xdatum_of_A {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatumA p Bs X n) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private theorem l6a_A_of_Ax {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {z : G} (h : GGResXDatumAx p Bs X z n) : GGResXDatumA p Bs X n := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

theorem l6a_reflGen_of_side {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G}
    (h : GGResSideDatum p Bs X J ∨ GGResTwoNodeSideDatum p Bs X J ∨
      GGResLeviSideDatumLE3 p Bs X J) :
    GGReflGenerated p (ggAutomizer X Bs) := by
  rcases h with h | h | h
  · obtain ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α, hW, hC, hWJ, hMJ, hlin, hrefl, hpair,
      hf, hcl, hfJ, hclJ, hconj⟩ := h
    exact ggIndep_reflGenerated_of_closure hrefl hcl
  · obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hW, hC, hWJ, hMJ, hlin, hrefl,
      hpair, hf, hcl, hfJ, hclJ, hconj⟩ := h
    exact ggIndep_reflGenerated_of_closure hrefl hcl
  · obtain ⟨Λ, i1, i2, S, M, C, MJ, V, i3, i4, ι, φ, h, α, hS2, hS3, hWM, hC, hWMJ, hMJ,
      hlin, hrefl, hpair, hf, hcl, hfJ, hclJ, hconj⟩ := h
    exact ggIndep_reflGenerated_of_closure hrefl hcl

private lemma l6a_row_facts {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X)
    (h9 : 8 ≤ X.rank) : (X.tag = .A ∨ X.tag = .twA) ∧ p ∣ X.rank + 1 := by
  rcases h with ⟨-, hp1, hp2, hX⟩ | ⟨-, hp1, hp2, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    refine ⟨Or.inl rfl, ?_⟩
    have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
    rw [he]; exact hp2
  · subst hX
    refine ⟨Or.inr rfl, ?_⟩
    have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
    rw [he]; exact hp2
  · subst hX
    have h0 : (⟨.E6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega
  · subst hX
    have h0 : (⟨.twE6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega

private lemma l6a_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hp3
  · subst h; exact absurd hp (by norm_num)
  · exact h

private theorem l6a_closeL (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 10 ≤ N)
    (hpN : p ∣ N) (hXd : GGResXDatumA p Bs L (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs L J)
    (hYr : GGReflGenerated p (ggAutomizer K Bs))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  ggTwoNodeIndepAtL_weyl hKG hOrb hFix hp5 hH hx hN hpN (ggIndep_moving_K hFixK hH hx) e hML hCL
    hφ hrefl hpair hAL hind
    (fun h5 => ggIndep_pm1_join hJr hPump hLB hSP h5 (by omega) hH hXd hXs hYr ι)

private theorem l6a_closeK (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {N : ℕ} (hN : 10 ≤ N) (hpN : p ∣ N) (hXd : GGResXDatumA p Bs K (N - 1))
    (hXs : GGResTwoNodeSideDatum p Bs K J)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  exact ggTwoNodeIndepAtK_weyl hKG hOrbK hp5 hH hy hstrong hLrefl hN hpN
    (ggIndep_moving_L hFix hH hy hLrefl) e hMK hCK hφ hrefl hpair hAK hind
    (fun h5 => ggIndep_pm1_join hJr hPump hLB hSP h5 (by omega) hH hXd hXs hLrefl ι)

theorem ggTwoNodeSide_automizer_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K J : Subgroup G}
    (h : GGResTwoNodeSideDatum p Bs K J) : ggAutomizer J Bs ≤ ggAutomizer K Bs := by
  obtain ⟨Λ', iF', iD', b₁, b₂, M', C', MJ, V', iV', iM', ι', φ', h', α', hb, hMw', hMC', hMJw,
    hMJeq, hφ', hrefl', hpair', hIsoK', hAK', hIsoJ', hAJ', hconj⟩ := h
  rw [hAJ', hAK']
  apply Subgroup.closure_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨j, rfl⟩

theorem ggResTwoNodeIndepL_large (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum)
    (hJ2 : GGTBJTwoNodeInput) (hCell : GGResTwoNodeNineDepInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeLargeLK p J L) (hxL : x ∈ L)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGResLeviSideDatumLE3 p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hrow2 : GGResRowAt ggRowTwoNode p J L := l6a_rowAt_mono (fun _ _ h => h.1) hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow⟩ := hrow
  obtain ⟨hRowN, h8⟩ := hRow
  have h8' : 8 ≤ labX.rank := by
    by_cases hp3 : p = 3
    · rw [if_pos hp3] at h8; exact h8
    · rw [if_neg hp3] at h8; omega
  obtain ⟨htag, hdvd⟩ := l6a_row_facts hRowN h8'
  rcases hD G p B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab hRowN
      hxL with ⟨-, hA⟩ | ⟨hE', -⟩
  · by_cases hp3 : p = 3
    ·
      have hN : 9 ≤ labX.rank + 1 := by omega
      rcases hA with hAx | ⟨hpg, hXA⟩
      · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
          hAL, hind⟩ := hAx
        letI := iF; letI := iD; letI := iAC; letI := iM
        exact ggTwoNodeIndepAtL_three hKG hOrb hFix hp3 hH hx hN hdvd (ggIndep_moving_K hFixK hH hx)
          e hMeq hC hφ hrefl hpair hAL (hind hxL)
      · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
          hAL⟩ := hXA
        letI := iF; letI := iD; letI := iAC; letI := iM
        by_cases hli : LinearIndependent (ZMod p) h
        · exact ggTwoNodeIndepAtL_three hKG hOrb hFix hp3 hH hx hN hdvd
            (ggIndep_moving_K hFixK hH hx) e hMeq hC hφ hrefl hpair hAL hli
        · by_cases h11 : 11 ≤ labX.rank + 1
          · exact (ggTwoNodeAtL_false_of_dep hKG hOrb hFix hFixK hp2 hH hx h11 hdvd e hMeq hC hφ hpair
              hAL hli hK).elim
          · have h9 : labX.rank = 8 := by
              have h1 : p ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
              rw [hp3] at h1
              obtain ⟨k, hk⟩ := h1
              omega
            have hnc := ggIndep_x_notComm_of_dep hFix hp2 hH hx (by omega) hdvd e hMeq hC hφ hpair hAL hli
            exact hCell G p B Bs x L D J y K hH hF hS hE
              (Or.inl ⟨⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, hp3, h9⟩⟩, hxL, hnc⟩)
    ·
      have hp5 : 5 ≤ p := l6a_five_le (Fact.out) hp2 hp3
      have hN : 10 ≤ labX.rank + 1 := by rw [if_neg hp3] at h8; omega
      rcases hA with hAx | ⟨hpg, hXA⟩
      · have hXA : GGResXDatumA p Bs L labX.rank := l6a_A_of_Ax hAx
        have hXs : GGResTwoNodeSideDatum p Bs L J :=
          (hJ2 G p B Bs x L D J y K hH).1 (l6a_xdatum_of_A hXA) hrow2
        obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
          hAL, hind⟩ := hAx
        letI := iF; letI := iD; letI := iAC; letI := iM
        exact l6a_closeL hKG hOrb hFix hFixK hJr hPump hLB hSP hp5 hH hx hN hdvd hXA hXs
          (l6a_reflGen_of_side hK) e hMeq hC hφ hrefl hpair hAL (hind hxL)
      · have hXs : GGResTwoNodeSideDatum p Bs L J :=
          (hJ2 G p B Bs x L D J y K hH).1 (l6a_xdatum_of_A hXA) hrow2
        have hXA0 := hXA
        obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
          hAL⟩ := hXA
        letI := iF; letI := iD; letI := iAC; letI := iM
        by_cases hli : LinearIndependent (ZMod p) h
        · exact l6a_closeL hKG hOrb hFix hFixK hJr hPump hLB hSP hp5 hH hx hN hdvd hXA0 hXs
            (l6a_reflGen_of_side hK) e hMeq hC hφ hrefl hpair hAL hli
        · exfalso
          have hN11 : 11 ≤ labX.rank + 1 := by
            have h1 : p ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
            have h2 : p ^ 2 ≤ labX.rank + 1 := Nat.le_of_dvd (by omega) h1
            have h3 : 25 ≤ p ^ 2 := by nlinarith
            omega
          exact ggTwoNodeAtL_false_of_dep hKG hOrb hFix hFixK hp2 hH hx hN11 hdvd e hMeq hC hφ hpair
            hAL hli hK
  · exfalso
    rcases hE' with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem ggResTwoNodeIndepK_large (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum)
    (hJ2 : GGTBJTwoNodeInput) (hCell : GGResTwoNodeNineDepInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeLargeLK p J K) (hyK : y ∈ K)
    (hL : GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGResLeviSideDatumLE3 p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hrow2 : GGResRowAt ggRowTwoNode p J K := l6a_rowAt_mono (fun _ _ h => h.1) hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow⟩ := hrow
  obtain ⟨hRowN, h8⟩ := hRow
  have h8' : 8 ≤ labX.rank := by
    by_cases hp3 : p = 3
    · rw [if_pos hp3] at h8; exact h8
    · rw [if_neg hp3] at h8; omega
  obtain ⟨htag, hdvd⟩ := l6a_row_facts hRowN h8'
  have hN9 : 9 ≤ labX.rank + 1 := by omega
  have hLrefl : GGReflGenerated p (ggAutomizer L Bs) := l6a_reflGen_of_side hL
  have hrowN : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = labX.rank + 1)
      p J K := ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, rfl⟩⟩
  rcases hD G p B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab hRowN
      hyK with ⟨-, hA⟩ | ⟨hE', -⟩
  ·
    have key : ∀ (hXA : GGResXDatumA p Bs K labX.rank),
        (∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
          (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
          (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin labX.rank ≃ Λ),
          M = (CoxeterMatrix.A labX.rank).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
            (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
            (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
            (∃ f : M.Group ≃* ↥(ggAutomizer K Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
            ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧ LinearIndependent (ZMod p) h) →
        GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
      intro hXA hInd
      have hXI : GGResXDatumAIndep p Bs K labX.rank := hInd
      have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y := by
        by_cases hN10 : labX.rank + 1 ≤ 10
        · exact fun b hb => ((hKFix G p B Bs x L D J y K (labX.rank + 1) hH hF hS hE hrowN hp2
            (by omega) hN10 hdvd hyK hXI b).mp hb)
        ·
          exact fun b hb => hFixK.2 G p B Bs x L D J y K hH
            ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, by omega⟩⟩ b hb
      have hXs : GGResTwoNodeSideDatum p Bs K J :=
        (hJ2 G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hXA) hrow2
      obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
        hAK, hind⟩ := hInd
      letI := iF; letI := iD; letI := iAC; letI := iM
      rw [sup_comm]
      by_cases hp3 : p = 3
      · exact ggTwoNodeIndepAtK_three hKG hOrbK hp3 hH hy hstrong hLrefl hN9 hdvd
          (ggIndep_moving_L hFix hH hy hLrefl) e hMeq hC hφ hrefl hpair hAK hind
      · exact l6a_closeK hKG hOrbK hFix hJr hPump hLB hSP (l6a_five_le (Fact.out) hp2 hp3) hH hy
          hstrong (by rw [if_neg hp3] at h8; omega) hdvd hXA hXs hLrefl e hMeq hC hφ hrefl hpair hAK
          hind
    rcases hA with hAx | ⟨hpg, hXA⟩
    · exact key (l6a_A_of_Ax hAx) (by
        obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, hf, hcl,
          hind⟩ := hAx
        exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, hf, hcl,
          hind hyK⟩)
    · have hXs : GGResTwoNodeSideDatum p Bs K J :=
        (hJ2 G p B Bs x L D J y K hH).2 (l6a_xdatum_of_A hXA) hrow2
      have hXA0 := hXA
      obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩,
        hAK⟩ := hXA
      letI := iF; letI := iD; letI := iAC; letI := iM
      by_cases hli : LinearIndependent (ZMod p) h
      · exact key hXA0 ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
          ⟨f, hf⟩, hAK, hli⟩
      · by_cases h11 : 11 ≤ labX.rank + 1
        · exfalso
          have hrowLarge : GGResRowAt ggRowTwoNodeLarge p J K :=
            ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, by omega⟩⟩
          exact ggTwoNodeAtK_false_of_dep hKG hOrbK hFix hFixK hp2 hH hrowLarge hy h11 hdvd e hMeq hC
            hφ hpair hAK (ggTwoNodeSide_automizer_le hXs) hli hL
        · have h9 : labX.rank = 8 ∧ p = 3 := by
            have h1 : p ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
            have hp3 : p = 3 := by
              by_contra hp3
              rw [if_neg hp3] at h8
              have h2 : p ^ 2 ≤ labX.rank + 1 := Nat.le_of_dvd (by omega) h1
              have h3 : 25 ≤ p ^ 2 := by
                have := l6a_five_le (Fact.out) hp2 hp3
                nlinarith
              omega
            rw [hp3] at h1
            obtain ⟨k, hk⟩ := h1
            exact ⟨by omega, hp3⟩
          have hnc := ggIndep_y_notComm_of_dep hp2 hH hy (by omega) hdvd e hMeq hC hφ hpair hAK hli
          have := hCell G p B Bs x L D J y K hH hF hS hE
            (Or.inr ⟨⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, h9.2, h9.1⟩⟩, hyK, hnc⟩)
          exact this
  · exfalso
    rcases hE' with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem ggResTwoNodeIndepLargeInput_of_inputs (hKG : GGReflClassLargeInput')
    (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum)
    (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeInput) (hCell : GGResTwoNodeNineDepInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeIndepLargeInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · rcases ggTwoNode_shape_K_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with hK1 | hK3 | hK2 | hW
    · exact ggResTwoNodeIndepL_large hKG hOrb hFix hFixK hJr hPump hLB hSP hD hJ2 hCell hH hF hS hE
        hrowL hxL (Or.inl hK1)
    · exact ggResTwoNodeIndepL_large hKG hOrb hFix hFixK hJr hPump hLB hSP hD hJ2 hCell hH hF hS hE
        hrowL hxL (Or.inr (Or.inr hK3))
    · exact ggResTwoNodeIndepL_large hKG hOrb hFix hFixK hJr hPump hLB hSP hD hJ2 hCell hH hF hS hE
        hrowL hxL (Or.inr (Or.inl hK2))
    · exact hW
  · rcases ggTwoNode_shape_L_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with hL1 | hL3 | hL2 | hW
    · exact ggResTwoNodeIndepK_large hKG hOrbK hFix hFixK hKFix hJr hPump hLB hSP hD hJ2 hCell hH hF
        hS hE hrowK hyK (Or.inl hL1)
    · exact ggResTwoNodeIndepK_large hKG hOrbK hFix hFixK hKFix hJr hPump hLB hSP hD hJ2 hCell hH hF
        hS hE hrowK hyK (Or.inr (Or.inr hL3))
    · exact ggResTwoNodeIndepK_large hKG hOrbK hFix hFixK hKFix hJr hPump hLB hSP hD hJ2 hCell hH hF
        hS hE hrowK hyK (Or.inr (Or.inl hL2))
    · exact hW

end CFSG.StandardType

end
