
module

public import CFSG.Sporadic.Co2Rank3.GraphBase

public import CFSG.Sporadic.Co2Rank3.Facts
public import CFSG.Sporadic.Co2Rank3.Wales
public import CFSG.Certificates.NativeRefine

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3.Native MulAction

theorem co2P0_rec :
    (∀ x y : Fin 2300, y ∈ orbit co2P0 x ↔ p0Rec.1[(y : ℕ)]! = p0Rec.1[(x : ℕ)]!) ∧
    (∀ x : Fin 2300, ∃ r ∈ p0Roots, r.1 = p0Rec.1[(x : ℕ)]!) ∧
    (∀ r ∈ p0Roots, p0Rec.1[r.1]! = r.1) ∧
    (∀ r ∈ p0Roots, ∀ hr : r.1 < 2300, (orbit co2P0 (⟨r.1, hr⟩ : Fin 2300)).ncard = r.2) := by
  rw [co2P0_eq_closure]
  exact recOK_spec co2Rank3Facts.p0 fun _ hk => rep_lev1 hk

theorem mem_orbit_co2P0
    {x y : Fin 2300} :
    y ∈ orbit co2P0 x ↔ p0Rec.1[(y : ℕ)]! = p0Rec.1[(x : ℕ)]! :=
  co2P0_rec.1 x y

theorem p0Rec_three :

    p0Rec.1[3]! = 3 := co2P0_rec.2.2.1 (3, 891) (by simp [p0Roots])

theorem p0Rec_one :

    p0Rec.1[1]! = 1 := co2P0_rec.2.2.1 (1, 1408) (by simp [p0Roots])

theorem ncard_co2Delta :
    (orbit co2P0 (3 : Fin 2300)).ncard = 891 :=
  co2P0_rec.2.2.2 (3, 891) (by simp [p0Roots]) (by norm_num)

theorem ncard_co2Gamma :
    (orbit co2P0 (1 : Fin 2300)).ncard = 1408 :=
  co2P0_rec.2.2.2 (1, 1408) (by simp [p0Roots]) (by norm_num)

theorem co2P0_cover
    (x : Fin 2300) :
    x = 0 ∨ x ∈ orbit co2P0 (3 : Fin 2300) ∨ x ∈ orbit co2P0 (1 : Fin 2300) := by
  obtain ⟨r, hr, hrx⟩ := co2P0_rec.2.1 x
  simp only [p0Roots, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · left
    have hx : x ∈ orbit co2P0 (0 : Fin 2300) :=
      mem_orbit_co2P0.2 (by rw [← hrx]; exact (co2P0_rec.2.2.1 (0, 1) (by simp [p0Roots])).symm)
    rw [orbit_co2P0_zero] at hx
    exact hx
  · exact Or.inr (Or.inr (mem_orbit_co2P0.2 (by rw [← hrx]; exact p0Rec_one.symm)))
  · exact Or.inr (Or.inl (mem_orbit_co2P0.2 (by rw [← hrx]; exact p0Rec_three.symm)))

theorem mem_co2Delta_of_lab
    {x : Fin 2300} (h : p0Rec.1[(x : ℕ)]! = 3) :
    x ∈ orbit co2P0 (3 : Fin 2300) :=
  mem_orbit_co2P0.2 (by rw [h]; exact p0Rec_three.symm)

theorem mem_co2Gamma_of_lab
    {x : Fin 2300} (h : p0Rec.1[(x : ℕ)]! = 1) :
    x ∈ orbit co2P0 (1 : Fin 2300) :=
  mem_orbit_co2P0.2 (by rw [h]; exact p0Rec_one.symm)

theorem co2N_rec :
    (∀ x y : Fin 2300, y ∈ orbit co2N x ↔ stabRec.1[(y : ℕ)]! = stabRec.1[(x : ℕ)]!) ∧
    (∀ x : Fin 2300, ∃ r ∈ stabRoots, r.1 = stabRec.1[(x : ℕ)]!) ∧
    (∀ r ∈ stabRoots, stabRec.1[r.1]! = r.1) ∧
    (∀ r ∈ stabRoots, ∀ hr : r.1 < 2300, (orbit co2N (⟨r.1, hr⟩ : Fin 2300)).ncard = r.2) :=
  recOK_spec co2Rank3Facts.stab fun _ hk => rep_stab hk

theorem co2P01_rec :
    (∀ x y : Fin 2300, y ∈ orbit co2P01 x ↔ p01Rec.1[(y : ℕ)]! = p01Rec.1[(x : ℕ)]!) ∧
    (∀ x : Fin 2300, ∃ r ∈ p01Roots, r.1 = p01Rec.1[(x : ℕ)]!) ∧
    (∀ r ∈ p01Roots, p01Rec.1[r.1]! = r.1) ∧
    (∀ r ∈ p01Roots, ∀ hr : r.1 < 2300, (orbit co2P01 (⟨r.1, hr⟩ : Fin 2300)).ncard = r.2) := by
  rw [co2P01_eq_closure]
  exact recOK_spec co2Rank3Facts.p01 fun _ hk => rep_lev2 hk

theorem co2N_le_P0 :
    co2N ≤ co2P0 := le_trans co2N_le inf_le_left

theorem co2N_cover
    (x : Fin 2300) :
    x = 0 ∨ x = 3 ∨ x ∈ orbit co2N (36 : Fin 2300) ∨ x ∈ orbit co2N (4 : Fin 2300) ∨
      x ∈ orbit co2N (5 : Fin 2300) ∨ x ∈ orbit co2N (2 : Fin 2300) ∨
      x ∈ orbit co2N (1 : Fin 2300) := by
  obtain ⟨r, hr, hrx⟩ := co2N_rec.2.1 x
  have hroot := co2N_rec.2.2.1 r hr
  have hmem : ∀ z : Fin 2300, stabRec.1[(z : ℕ)]! = (z : ℕ) → stabRec.1[(x : ℕ)]! = (z : ℕ) →
      x ∈ orbit co2N z := fun z hz hxz => (co2N_rec.1 z x).2 (by rw [hxz, hz])
  simp only [stabRoots, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    have hx := hmem 0 hroot hrx.symm
    rwa [orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 (co2N_le hk).1.2] at hx
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hmem 1 hroot hrx.symm))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem 2 hroot hrx.symm))))))
  · right; left
    have hx := hmem 3 hroot hrx.symm
    rwa [orbit_subgroup_eq_singleton fun _ hk => mem_stabilizer_iff.1 (co2N_le hk).2] at hx
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hmem 4 hroot hrx.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem 5 hroot hrx.symm)))))
  · exact Or.inr (Or.inr (Or.inl (hmem 36 hroot hrx.symm)))

theorem ncard_co2N
    (r : ℕ × ℕ) (hr : r ∈ stabRoots) (hr' : r.1 < 2300) :
    (orbit co2N (⟨r.1, hr'⟩ : Fin 2300)).ncard = r.2 :=
  co2N_rec.2.2.2 r hr hr'

theorem co2P01_cover
    (x : Fin 2300) :
    x = 0 ∨ x = 1 ∨ x ∈ orbit co2P01 (4 : Fin 2300) ∨ x ∈ orbit co2P01 (3 : Fin 2300) ∨
      x ∈ orbit co2P01 (2 : Fin 2300) ∨ x ∈ orbit co2P01 (8 : Fin 2300) := by
  obtain ⟨r, hr, hrx⟩ := co2P01_rec.2.1 x
  have hroot := co2P01_rec.2.2.1 r hr
  have hmem : ∀ z : Fin 2300, p01Rec.1[(z : ℕ)]! = (z : ℕ) → p01Rec.1[(x : ℕ)]! = (z : ℕ) →
      x ∈ orbit co2P01 z := fun z hz hxz => (co2P01_rec.1 z x).2 (by rw [hxz, hz])
  simp only [p01Roots, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · left
    have hx := hmem 0 hroot hrx.symm
    rwa [orbit_subgroup_eq_singleton (K := co2P01) fun _ hk => mem_stabilizer_iff.1 hk.1.2]
      at hx
  · right; left
    have hx := hmem 1 hroot hrx.symm
    rwa [orbit_subgroup_eq_singleton (K := co2P01) fun _ hk => mem_stabilizer_iff.1 hk.2] at hx
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem 2 hroot hrx.symm)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hmem 3 hroot hrx.symm))))
  · exact Or.inr (Or.inr (Or.inl (hmem 4 hroot hrx.symm)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hmem 8 hroot hrx.symm)))))

theorem ncard_co2P01
    (r : ℕ × ℕ) (hr : r ∈ p01Roots) (hr' : r.1 < 2300) :
    (orbit co2P01 (⟨r.1, hr'⟩ : Fin 2300)).ncard = r.2 :=
  co2P01_rec.2.2.2 r hr hr'

theorem co2P_swap :
    orbitalRel co2P (0 : Fin 2300) 3 3 0 :=
  orbitalRel_swap_of_suborbits co2P_htr co2P0_cover ncard_co2Delta ncard_co2Gamma

@[expose] def co2Graph :
    SimpleGraph (Fin 2300) where
  Adj := orbitalRel co2P 0 3
  symm := ⟨fun _ _ h => orbitalRel_symm co2P_swap h⟩
  loopless := ⟨fun x h => not_orbitalRel_self (by decide : (0 : Fin 2300) ≠ 3) x h⟩

theorem co2Graph_adj
    {x y : Fin 2300} : co2Graph.Adj x y ↔ orbitalRel co2P 0 3 x y := Iff.rfl

theorem co2Graph_adj_smul
    {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) {x y : Fin 2300} :
    co2Graph.Adj (g x) (g y) ↔ co2Graph.Adj x y :=
  orbitalRel_smul_iff hg

theorem co2Graph_adj_zero
    (y : Fin 2300) : co2Graph.Adj 0 y ↔ y ∈ orbit co2P0 (3 : Fin 2300) :=
  mem_orbitalNbr_self

theorem co2Nbr_facts :
    AdjFacts 2300 co2OrigArrs co2Nbr co2DeltaList :=
  adjFacts_of_adjOK co2Rank3Facts.adj

theorem co2Nbr_inv
    {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2P) : NbrInv co2Nbr σ :=
  co2Nbr_facts.inv_of_mem_closure (fun _ hk => rep_co2Gen (by rwa [co2OrigArrs_size] at hk))
    (co2P_eq_closure_gens ▸ hσ)

theorem mem_co2DeltaList
    {x : Fin 2300} :
    (x : ℕ) ∈ co2DeltaList ↔ x ∈ orbit co2P0 (3 : Fin 2300) := by
  rw [listLabelOK_spec co2Rank3Facts.delta x.2, List.mem_singleton, mem_orbit_co2P0]
  exact ⟨fun h => h.trans p0Rec_three.symm, fun h => h.trans p0Rec_three⟩

theorem co2Nbr_zero
    (y : Fin 2300) :
    (y : ℕ) ∈ co2Nbr[((0 : Fin 2300) : ℕ)]! ↔ y ∈ orbit co2P0 (3 : Fin 2300) := by
  rw [Fin.val_zero, co2Nbr_facts.root, mem_co2DeltaList]

theorem co2Nbr_adj
    (x y : Fin 2300) : (y : ℕ) ∈ co2Nbr[(x : ℕ)]! ↔ co2Graph.Adj x y := by
  rw [co2Graph_adj]
  constructor
  · intro h
    obtain ⟨g, hg, hgx⟩ := co2P_htr x
    have h1 := (co2Nbr_inv (co2P.inv_mem hg) x y).1 h
    have hx0 : g⁻¹ x = 0 := by rw [← hgx, Equiv.Perm.smul_def, perm_inv_apply_self]
    rw [hx0, co2Nbr_zero] at h1
    obtain ⟨k, hk, hky⟩ := mem_orbit_subgroup_iff.1 h1
    refine ⟨g * k, co2P.mul_mem hg hk.1, ?_, ?_⟩
    · rw [mul_smul, mem_stabilizer_iff.1 hk.2, hgx]
    · rw [mul_smul, hky, Equiv.Perm.smul_def, perm_apply_inv_self]
  · rintro ⟨g, hg, rfl, rfl⟩
    have h3 : ((3 : Fin 2300) : ℕ) ∈ co2Nbr[((0 : Fin 2300) : ℕ)]! :=
      (co2Nbr_zero 3).2 (mem_orbit_self _)
    exact (co2Nbr_inv hg 0 3).1 h3

end CFSG.Sporadic.Co2Rank3
