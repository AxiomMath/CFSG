module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Cen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Two

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem edgeCirc_eq_of_verts {ℓ ℓ' : Line Γ} {i j : ℤ} (h0 : ℓ.vert i = ℓ'.vert j)
    (h1 : ℓ.vert (i + 1) = ℓ'.vert (j + 1)) :
    ℓ.edgeCirc (G := G) i = ℓ'.edgeCirc (G := G) j := by
  rw [Line.edgeCirc_eq_Ecirc, Line.edgeCirc_eq_Ecirc, h0, h1]

theorem contra {F : FanTree Γ G} (h40 : Fan40 F) (h51a : Fan51a F) (h51b : Fan51b F)
    (ℓ : Line Γ) {z z1 zL yR : G} {a tL tR : ℤ} (hz2 : z * z = 1) (hz12 : z1 * z1 = 1)
    (hfz : ∀ i, i ∈ ℓ.fixIdx z ↔ tL ≤ i ∧ i ≤ tR)
    (hfz1 : ∀ i, i ∈ ℓ.fixIdx z1 ↔ tL ≤ i ∧ i ≤ tR)
    (hcz : z ∈ Cen (ℓ.edgeStab (G := G) a : Set G))
    (hcz1 : z1 ∈ Cen (ℓ.edgeStab (G := G) (a - 1) : Set G)) (hne : z * z1 ≠ 1)
    (hL : zL ∈ Cen (ℓ.edgeStab (G := G) (tL - 1) : Set G))
    (hLfix : zL • ℓ.vert (a - 1) = ℓ.vert (a - 1)) (hLmov : zL • ℓ.vert a ≠ ℓ.vert a)
    (hR : yR ∈ Cen (ℓ.edgeStab (G := G) tR : Set G))
    (hRfix : yR • ℓ.vert (a + 1) = ℓ.vert (a + 1)) (hRmov : yR • ℓ.vert a ≠ ℓ.vert a)
    (htL : tL ≤ a - 1) (htR : a ≤ tR) : False := by
  obtain ⟨huL, huR⟩ := mul_mem_kernels F ℓ hz2 hz12 hfz hfz1 (by omega)
  have hcL : (z * z1) * zL = zL * (z * z1) := by
    refine hL.2 _ ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 huL _ (ℓ.adj_pred tL)), ?_⟩
    rw [sub_add_cancel]
    exact F.nbrStab_le_stabilizer _ huL
  have hcR : (z * z1) * yR = yR * (z * z1) :=
    hR.2 _ ⟨F.nbrStab_le_stabilizer _ huR, MulAction.mem_stabilizer_iff.2
      (mem_nbrStab.1 huR _ (ℓ.adj tR))⟩
  have hkc : ∀ s ∈ nbrStab Γ G (ℓ.vert a), s * (z * z1) = (z * z1) * s := fun s hs =>
    comm_kernel F ℓ hcz hcz1 hs
  have hS : ∀ s ∈ ((nbrStab Γ G (zL • ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert a) ∪
      nbrStab Γ G (yR • ℓ.vert a)), s * (z * z1) = (z * z1) * s := by
    rintro s ((hs | hs) | hs)
    · exact comm_kernel_conj F hcL hkc hs
    · exact hkc s hs
    · exact comm_kernel_conj F hcR hkc hs
  set M := Subgroup.closure ((nbrStab Γ G (zL • ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert a) ∪
    nbrStab Γ G (yR • ℓ.vert a)) with hM
  have hMu : ∀ h ∈ M, h * (z * z1) = (z * z1) * h := fun h hh =>
    ((Subgroup.mem_centralizer_iff.1 (closure_le_centralizer hS hh)) _ rfl).symm
  have hKM : ∀ {S : Set G}, S ⊆ ((nbrStab Γ G (zL • ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert a) ∪
      nbrStab Γ G (yR • ℓ.vert a)) → Subgroup.closure S ≤ M := fun hSub =>
    Subgroup.closure_mono hSub
  have hadj : Γ.Adj (ℓ.vert (a - 1)) (ℓ.vert a) := by
    have := ℓ.adj (a - 1)
    rwa [sub_add_cancel] at this
  have hp1 : Γ.Adj (zL • ℓ.vert a) (ℓ.vert (a - 1)) := by
    have := (F.adj_smul zL (ℓ.vert (a - 1)) (ℓ.vert a)).2 hadj
    rw [hLfix] at this
    exact this.symm
  have hq1 : Γ.Adj (ℓ.vert (a + 1)) (yR • ℓ.vert a) := by
    have := (F.adj_smul yR (ℓ.vert (a + 1)) (ℓ.vert a)).2 (ℓ.adj a).symm
    rw [hRfix] at this
    exact this
  obtain ⟨ℓA, hA0, hA1, hA2⟩ := exists_line_arc2 F hp1 hadj hLmov
  obtain ⟨ℓB, hB0, hB1, hB2⟩ := exists_line_arc2 F (ℓ.adj a) hq1 hRmov.symm
  have eA := two_edges h40 h51a h51b ℓA 0
  have eB := two_edges h40 h51a h51b ℓB 0
  have eC := two_edges h40 h51a h51b ℓ (a - 1)
  simp only [zero_add, hA0, hA1, hA2, hB0, hB1, hB2] at eA eB
  obtain ⟨hA, yA, hyA, hyAs, hyAo⟩ := eA
  obtain ⟨hB, -⟩ := eB
  obtain ⟨-, yC, hyC, hyCs, hyCo⟩ := eC
  have hA1' : ℓA.edgeCirc (G := G) 1 = ℓ.edgeCirc (G := G) (a - 1) :=
    edgeCirc_eq_of_verts (by rw [hA1])
      (by rw [show (1 : ℤ) + 1 = 2 from rfl, hA2, sub_add_cancel])
  have hB0' : ℓB.edgeCirc (G := G) 0 = ℓ.edgeCirc (G := G) a :=
    edgeCirc_eq_of_verts (by rw [hB0]) (by rw [zero_add, hB1])
  have hMA : Subgroup.closure (ℓA.edgeCirc (G := G) 0 ∪ ℓA.edgeCirc (G := G) 1) ≤ M :=
    hA.trans (hKM Set.subset_union_left)
  have hMB : Subgroup.closure (ℓB.edgeCirc (G := G) 0 ∪ ℓB.edgeCirc (G := G) 1) ≤ M :=
    hB.trans (hKM (Set.union_subset (fun g hg => Or.inl (Or.inr hg)) fun g hg => Or.inr hg))
  have hMC : Subgroup.closure (ℓ.edgeCirc (G := G) (a - 1) ∪
      ℓ.edgeCirc (G := G) (a - 1 + 1)) ≤ M := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · have : g ∈ ℓA.edgeCirc (G := G) 1 := by rw [hA1']; exact hg
      exact hMA (Subgroup.subset_closure (Or.inr this))
    · rw [sub_add_cancel] at hg
      have : g ∈ ℓB.edgeCirc (G := G) 0 := by rw [hB0']; exact hg
      exact hMB (Subgroup.subset_closure (Or.inl this))
  have hLocA : LocTr Γ M (ℓ.vert (a - 1)) := P58.locTr_of_pow F (hMA hyA) hyAs hyAo
  have hLocC : LocTr Γ M (ℓ.vert a) := by
    have := P58.locTr_of_pow F (hMC hyC) hyCs hyCo
    rwa [sub_add_cancel] at this
  have hfix : ∀ i, tL ≤ i → i ≤ tR → (z * z1) • ℓ.vert i = ℓ.vert i := fun i h1 h2 => by
    have f1 : z1 • ℓ.vert i = ℓ.vert i := (hfz1 i).2 ⟨h1, h2⟩
    have f : z • ℓ.vert i = ℓ.vert i := (hfz i).2 ⟨h1, h2⟩
    rw [mul_smul, f1, f]
  exact hne (P58.eq_one_of_locTr F hadj hMu (hfix _ htL (by omega)) (hfix _ (by omega) htR)
    hLocA hLocC)

end P59

end CFSG.Quasithin.Fan86
