module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallAL
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallAK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6sm_rowAt_mono {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    {R R' : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hRR : ∀ labJ labX, R p labJ labX → R' p labJ labX) (h : GGResRowAt R p J X) :
    GGResRowAt R' p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hRR _ _ hr⟩

theorem GGResXDatumAIndep.toXDatum {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatumAIndep p Bs X n) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private theorem l6sm_reflGen_of_side {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G}
    (h : GGResSideDatum p Bs X J ∨ GGResTwoNodeSideDatum p Bs X J) :
    GGReflGenerated p (ggAutomizer X Bs) := by
  rcases h with h | h
  · obtain ⟨Λ, i1, i2, b, M, C, MJ, V, i3, i4, ι, φ, h, α, hW, hC, hWJ, hMJ, hlin, hrefl, hpair,
      hf, hcl, hfJ, hclJ, hconj⟩ := h
    exact ggIndep_reflGenerated_of_closure hrefl hcl
  · obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hW, hC, hWJ, hMJ, hlin, hrefl,
      hpair, hf, hcl, hfJ, hclJ, hconj⟩ := h
    exact ggIndep_reflGenerated_of_closure hrefl hcl

private lemma l6sm_row_facts_small {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X)
    (htag : X.tag = .A ∨ X.tag = .twA) :
    J.rank + 2 = X.rank ∧ p ∣ X.rank + 1 ∧ (J.tag = .A ∨ J.tag = .twA) := by
  rcases h with ⟨hJ, -, hd, hX⟩ | ⟨hJ, -, hd, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    exact ⟨rfl, by simpa using hd, Or.inl hJ⟩
  · subst hX
    exact ⟨rfl, by simpa using hd, Or.inr hJ⟩
  · exfalso
    have hE : X.tag = .E6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)
  · exfalso
    have hE : X.tag = .twE6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)

private lemma l6sm_lambda2_rank_lower {lab : LargeEvenLabel} (h : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A ∨ lab.tag = .twA) : 1 ≤ lab.rank := by
  rcases h with ⟨-, h⟩
  rcases htag with hA | hA
  · rw [hA] at h
    exact h.1
  · rw [hA] at h
    omega

private lemma l6sm_prime_dvd_four {p : ℕ} (hp : p.Prime) (h : p ∣ 4) (hp2 : p ≠ 2) : False := by
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
  have hp2le : 2 ≤ p := hp.two_le
  interval_cases p
  · exact hp2 rfl
  · norm_num at h
  · norm_num at hp

private lemma l6sm_cell {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ N)
    (h5 : 5 ≤ N) (hhi : N < (if p = 3 then 9 else 10)) : lr6SmallCellA p N := by
  have hp_le : p ≤ N := Nat.le_of_dvd (by omega) hdvd
  have hNlt10 : N < 10 := by
    by_cases hp3 : p = 3
    · rw [if_pos hp3] at hhi; omega
    · rw [if_neg hp3] at hhi; omega
  have hNlt9 : p = 3 → N < 9 := by
    intro hp3
    rw [if_pos hp3] at hhi; omega
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have h2 : 2 ≤ p := hp.two_le
    have h10 : p < 10 := by omega
    interval_cases p
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · norm_num at hp
    · exact Or.inr (Or.inr (Or.inl rfl))
    · norm_num at hp
    · exact Or.inr (Or.inr (Or.inr rfl))
    · norm_num at hp
    · norm_num at hp
  rcases hp_cases with h2 | h3 | h5' | h7
  · exact absurd h2 hp2
  · subst h3
    obtain ⟨k, hk⟩ := hdvd
    have hN9 : N < 9 := hNlt9 rfl
    have hN6 : N = 6 := by omega
    subst hN6
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · subst h5'
    obtain ⟨k, hk⟩ := hdvd
    have hN10 : N < 10 := hNlt10
    have hN5 : N = 5 := by omega
    subst hN5
    exact Or.inl ⟨rfl, rfl⟩
  · subst h7
    obtain ⟨k, hk⟩ := hdvd
    have hN10 : N < 10 := hNlt10
    have hN7 : N = 7 := by omega
    subst hN7
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private lemma l6sm_p2_not_le {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ N)
    (h5 : 5 ≤ N) (hhi : N < (if p = 3 then 9 else 10)) : ¬ (p ^ 2 ≤ N) := by
  intro h2
  have hcell := l6sm_cell hp hp2 hdvd h5 hhi
  obtain ⟨hp5, hq⟩ | ⟨hp3, hq⟩ | ⟨hp7, hq⟩ := hcell
  · subst hp5
    clear hhi h5 hdvd hp hp2
    omega
  · subst hp3
    clear hhi h5 hdvd hp hp2
    omega
  · subst hp7
    clear hhi h5 hdvd hp hp2
    omega

public theorem ggResTwoNodeSmallA_indep_datum_rank {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hD : GGTwoNodeIndepDatum) (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {z : G}
    (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y))
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J X) (hzX : z ∈ X) :
    ∃ N, lr6SmallCellA p N ∧ GGResXDatumAIndep p Bs X (N - 1) ∧
      GGResXDatum p Bs X ∧
      GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J X := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨⟨hRowN, hsmall⟩, htag⟩⟩ := hrow
  obtain ⟨hrank, hpN, hJtag⟩ := l6sm_row_facts_small hRowN htag
  have hJrank : 1 ≤ labJ.rank := l6sm_lambda2_rank_lower hJΛ hJtag
  have hN5 : 5 ≤ labX.rank + 1 := by
    by_contra hcon
    have hN4 : labX.rank + 1 = 4 := by omega
    have hp4 : p ∣ 4 := by rw [← hN4]; exact hpN
    exact l6sm_prime_dvd_four (Fact.out) hp4 hp2
  have hhi : labX.rank + 1 < (if p = 3 then 9 else 10) := by
    by_cases hp3 : p = 3
    · rw [if_pos hp3] at hsmall ⊢; omega
    · rw [if_neg hp3] at hsmall ⊢; omega
  have hcell : lr6SmallCellA p (labX.rank + 1) := l6sm_cell (Fact.out) hp2 hpN hN5 hhi
  have hXI : GGResXDatumAIndep p Bs X labX.rank := by
    rcases hD G p B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJlab hXlab
        hRowN hzX with ⟨-, hA⟩ | ⟨hE', -⟩
    · rcases hA with hAx | ⟨hpg, hXA⟩
      · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
          ⟨f, hf⟩, hAL, hind⟩ := hAx
        exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
          ⟨f, hf⟩, hAL, hind hzX⟩
      · exfalso
        have h1 : p ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
        have h2 : p ^ 2 ≤ labX.rank + 1 := Nat.le_of_dvd (by omega) h1
        exact absurd h2 (l6sm_p2_not_le (Fact.out) hp2 hpN hN5 hhi)
    · exfalso
      rcases hE' with h | h <;> rcases htag with h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)
  refine ⟨labX.rank + 1, hcell, ?_, GGResXDatumAIndep.toXDatum hXI,
    ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, rfl⟩⟩⟩
  simpa using hXI

theorem ggResTwoNodeSmallA_indep_datum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hD : GGTwoNodeIndepDatum) (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {z : G}
    (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y))
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J X) (hzX : z ∈ X) :
    ∃ N, lr6SmallCellA p N ∧ GGResXDatumAIndep p Bs X (N - 1) ∧
      GGResXDatum p Bs X ∧ GGResRowAt ggRowTwoNode p J X := by
  obtain ⟨N, hcell, hXI, hXD, hrowN⟩ :=
    ggResTwoNodeSmallA_indep_datum_rank hD hH hXz hrow hzX
  exact ⟨N, hcell, hXI, hXD, l6sm_rowAt_mono (fun _ _ h => h.1) hrowN⟩

theorem ggResTwoNodeIndepSmallL_A (hPos : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl)
    (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hJr : GGForkJr)
    (hPump : GGForkPumpOr) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallA p J L) (hxL : x ∈ L)
    (hK : GGResSideDatum p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨N, hcell, hXI, hXD, hrow2⟩ :=
    ggResTwoNodeSmallA_indep_datum hD hH (Or.inl ⟨rfl, rfl⟩) hrow hxL
  have hXs : GGResTwoNodeSideDatum p Bs L J :=
    (hJ2 G p B Bs x L D J y K hH).1 hXD hrow2
  exact ggTwoNodeIndepAtL_smallA hPos hExcl hOrb hFix hJr hPump hLB hSP hp2 hcell hH hx
    (ggIndep_moving_K hFixK hH hx) hXI hXs hK

theorem ggResTwoNodeIndepSmallK_A (hPos : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J K) (hyK : y ∈ K) (hL : GGResSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  obtain ⟨N, hcell, hXI, hXD, hrowN⟩ :=
    ggResTwoNodeSmallA_indep_datum_rank hD hH (Or.inr ⟨rfl, rfl⟩) hrow hyK
  have hrow2 : GGResRowAt ggRowTwoNode p J K :=
    l6sm_rowAt_mono (fun _ _ h => h.1) hrowN
  have hpN : p ∣ N := by
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hN5 : 5 ≤ N := by
    rcases hcell with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hN10 : N ≤ 10 := by
    rcases hcell with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y :=
    fun b hb => (hKFix G p B Bs x L D J y K N hH hF hS hE hrowN hp2 hN5 hN10 hpN hyK
      hXI b).mp hb
  have hXs : GGResTwoNodeSideDatum p Bs K J :=
    (hJ2 G p B Bs x L D J y K hH).2 hXD hrow2
  have hLrefl : GGReflGenerated p (ggAutomizer L Bs) := l6sm_reflGen_of_side (Or.inl hL)
  have hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩ :=
    ggIndep_moving_L hFix hH hy hLrefl
  rw [sup_comm]
  exact ggTwoNodeIndepAtK_smallA hPos hExcl hOrbK hJr hPump hLB hSP hp2 hcell hH hy hstrong hmove
    hXI hXs hL

theorem ggResTwoNodeIndepSmallInput_of_inputs (hRest : GGResTwoNodeIndepSmallRestInput)
    (hPos : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl) (hOrb : GGResCentBoundInput)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hKFix : GGTwoNodeKFixLineInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum)
    (hJ2 : GGTBJTwoNodeInput) : GGResTwoNodeIndepSmallInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · rcases hrowL.smallLK_split with hrowA | hrowE
    · by_cases hK' : GGResSideDatum p Bs K J
      · exact ggResTwoNodeIndepSmallL_A hPos hExcl hOrb hFix hFixK hJr hPump hLB hSP hD hJ2
          hH hrowA hxL hK'
      · exact hRest G p B Bs x L D J y K hH hF hS hE
          (Or.inr (Or.inr (Or.inl ⟨hrowA, hxL, hK'⟩)))
    · exact hRest G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowE, hxL⟩)
  · rcases hrowK.smallLK_split with hrowA | hrowE
    · by_cases hL' : GGResSideDatum p Bs L J
      · exact ggResTwoNodeIndepSmallK_A hPos hExcl hOrbK hFix hKFix hJr hPump hLB hSP hD hJ2
          hH hF hS hE hrowA hyK hL'
      · exact hRest G p B Bs x L D J y K hH hF hS hE
          (Or.inr (Or.inr (Or.inr ⟨hrowA, hyK, hL'⟩)))
    · exact hRest G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inl ⟨hrowE, hyK⟩))

end CFSG.StandardType

end
