module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallTwo
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndep_small_two_of_sides (hUse : ZS.UseInput) (hExcl : LR6SmallRankExcl)
    (hFix : GGTBFixInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    {z : G} (hH : GGResHyp p B Bs x L D J y K)
    (hXY : (X = L ∧ Y = K ∧ z = x) ∨ (X = K ∧ Y = L ∧ z = y))
    (hz : z ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer X Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers z)
    (hmove : ∃ t ∈ ggAutomizer Y Bs, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩)
    (hstab : Nat.card ↥((ggAutomizer X Bs ⊔ ggAutomizer Y Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer X Bs))
    (hXd : GGResXDatumAIndep p Bs X (N - 1))
    (hXs : GGResTwoNodeSideDatum p Bs X J) (hYs : GGResTwoNodeSideDatum p Bs Y J) :
    GGWeylReflectionGroup p (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) := by
  classical
  have hp5 : 5 ≤ p := by rcases hcell with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  have hN5 : 5 ≤ N := by rcases hcell with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hp2 : p ≠ 2 := by omega
  have hpN : p ∣ N := by rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact dvd_rfl
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hb, hcardΛa, hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK,
    ⟨fX, hfX⟩, ⟨fY, hfY⟩, hclosX, hclosY, hconn, hJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hXs hYs
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨Λ₁, j1, j2, M₁, C₁, V₁, k1, k2, ι₁, φ₁, h₁, α₁, e₁, hM₁, hWM₁, hC₁, hlin₁,
    hrefl₁, hpair₁, ⟨f₁, hf₁⟩, hclos₁, hind₁⟩ := hXd
  letI := j1; letI := j2; letI := k1; letI := k2
  obtain ⟨e, hML⟩ := ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega)
    hH.1.2.1.2.1 (ggAutomizer X Bs) e₁ hM₁ hWM₁ f₁ φ₁ hf₁ hrefl₁ hWML fX
      (fun i => φ (Sum.inl i)) hfX (fun i => hrefl (Sum.inl i))
  have hcard : Fintype.card Λ₁ = Fintype.card Λ :=
    (Fintype.card_congr e₁).symm.trans (Fintype.card_congr e)
  have hindX : LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggDatum_indep_transfer hlin₁ hrefl₁ (fun i w => hlin (Sum.inl i) w)
      (fun i => hrefl (Sum.inl i)) hclos₁ hclosX hcard hind₁
  have F : GGIndepAFrame p N (fun i => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) (ι (Additive.ofMul ⟨z, hz⟩)) := by
    rcases hXY with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ggXDatumA_indep_frame hFix hp2 hH hz hN5 hpN e hML hCL
        (fun i w => hlin (Sum.inl i) w) hpairL hclosX hindX
    · exact ggXDatumA_indep_frame_K hp2 hH hz hstrong hN5 hpN e hML hCL
        (fun i w => hlin (Sum.inl i) w) hpairL hclosX hindX
  have hJL : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs := by
    rcases hXY with ⟨rfl, _, _⟩ | ⟨_, rfl, _⟩
    · intro j
      rw [hclosX]
      exact Subgroup.subset_closure ⟨j.1, rfl⟩
    · intro j
      rw [hclosY]
      exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
  have hJM := ggJoint_coxeter_J_eq (Bs := Bs) (L := X) (K := Y) ⟨fX, hfX⟩ ⟨fY, hfY⟩
  have hXplain : GGResXDatumA p Bs X (N - 1) :=
    ⟨Λ₁, j1, j2, M₁, C₁, V₁, k1, k2, ι₁, φ₁, h₁, α₁, e₁,
      hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, ⟨f₁, hf₁⟩, hclos₁⟩
  have hYr : GGReflGenerated p (ggAutomizer Y Bs) := by
    obtain ⟨ΛY, y1, y2, c₁, c₂, MY, CY, MJ, VY, y3, y4, ιY, φY, hY, αY,
      hc, hWY, hCY, hWJ, hMJ, hlinY, hreflY, hpairY, hfY', hclosY', hfJ, hclJ, hconj⟩ := hYs
    exact ggIndep_reflGenerated_of_closure hreflY hclosY'
  have hpm := ggIndep_pm1_join_of_deleted_connected hJr hPump hLB hSP hp5 hN5 hH
    hXplain hXs hYr ι
  exact ggJoint_weyl_small_two hUse hExcl hJr hPump hLB hSP hcell hH hb hcardΛa
    e hML hWML hCL hWMK hCK hconn hJM hlin hrefl hpairL hpairK ⟨fY, hfY⟩
    hclosX hclosY hJL hJ hz F hmove hstab hpm

theorem ggResTwoNodeIndepSmallTwoL_A (hUse : ZS.UseInput) (hExcl : LR6SmallRankExcl)
    (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallA p J L)
    (hxL : x ∈ L) (hK : GGResTwoNodeSideDatum p Bs K J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨N, hcell, hXI, hXD, hrow2⟩ :=
    ggResTwoNodeSmallA_indep_datum hD hH (Or.inl ⟨rfl, rfl⟩) hrow hxL
  have hcell' : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) := by
    rcases hcell with h5 | ⟨h3, _⟩ | h7
    · exact Or.inl h5
    · exact (hp3 h3).elim
    · exact Or.inr h7
  have hL : GGResTwoNodeSideDatum p Bs L J := (hJ2 G p B Bs x L D J y K hH).1 hXD hrow2
  have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  exact ggTwoNodeIndep_small_two_of_sides hUse hExcl hFix hJr hPump hLB hSP hcell' hH
    (Or.inl ⟨rfl, rfl, rfl⟩) hx hstrong (ggIndep_moving_K hFixK hH hx)
    (hOrb G p B Bs x L D J y K hH hx) hXI hL hK

theorem ggResTwoNodeIndepSmallTwoK_A (hUse : ZS.UseInput) (hExcl : LR6SmallRankExcl)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J K) (hyK : y ∈ K)
    (hL : GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  obtain ⟨N, hcell, hXI, hXD, hrowN⟩ :=
    ggResTwoNodeSmallA_indep_datum_rank hD hH (Or.inr ⟨rfl, rfl⟩) hrow hyK
  have hcell' : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) := by
    rcases hcell with h5 | ⟨h3, _⟩ | h7
    · exact Or.inl h5
    · exact (hp3 h3).elim
    · exact Or.inr h7
  have hpN : p ∣ N := by rcases hcell' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact dvd_rfl
  have hN5 : 5 ≤ N := by rcases hcell' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hN10 : N ≤ 10 := by rcases hcell' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hrow2 : GGResRowAt ggRowTwoNode p J K := by
    obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow, _⟩ := hrowN
    exact ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hrow⟩
  have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y := fun b hb =>
    (hKFix G p B Bs x L D J y K N hH hF hS hE hrowN hp2 hN5 hN10 hpN hyK hXI b).mp hb
  have hK : GGResTwoNodeSideDatum p Bs K J := (hJ2 G p B Bs x L D J y K hH).2 hXD hrow2
  have hLrefl : GGReflGenerated p (ggAutomizer L Bs) := by
    obtain ⟨Λ, i1, i2, c₁, c₂, M, C, MJ, V, i3, i4, ι, φ, h, α,
      hc, hW, hC, hWJ, hMJ, hlin, hrefl, hpair, hf, hclos, hfJ, hJ, hconj⟩ := hL
    exact ggIndep_reflGenerated_of_closure hrefl hclos
  have hmove := ggIndep_moving_L hFix hH hy hLrefl
  rw [sup_comm]
  exact ggTwoNodeIndep_small_two_of_sides hUse hExcl hFix hJr hPump hLB hSP hcell' hH
    (Or.inr ⟨rfl, rfl, rfl⟩) hy hstrong hmove (by simpa [sup_comm] using
      (hOrbK G p B Bs x L D J y K hH hy)) hXI hK hL

end CFSG.StandardType

end
