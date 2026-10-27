module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338ME

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch3Sec3

variable {V : Type} [CommGroup V]

theorem fixV_anti {A B : Subgroup (MulAut V)} (h : A ≤ B) : fixV B ≤ fixV A :=
  fun _ hv x hx => hv x (h hx)

theorem commV_le_modComm {G : Subgroup (MulAut V)} {W W' C : Subgroup V} (hcG : commV G ≤ W)
    (hW'inv : ∀ g ∈ G, ∀ w ∈ W', g w ∈ W') (hWW : W ⊔ W' = ⊤) (hWiW : W ⊓ W' = C) :
    commV G ≤ modComm G W ⊔ C := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  have hv : v ∈ W ⊔ W' := hWW ▸ Subgroup.mem_top v
  obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.mp hv
  have e : g (w * w') * (w * w')⁻¹ = (g w * w⁻¹) * (g w' * w'⁻¹) := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  rw [SetLike.mem_coe, e]
  refine Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨⟨g, hg⟩, w, hw, rfl⟩) ?_
  rw [← hWiW]
  exact ⟨hcG (gen_mem_commV hg w'), W'.mul_mem (hW'inv g hg w' hw') (W'.inv_mem hw')⟩

theorem case3_core [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {J K₁ K₂ G G' : Subgroup (MulAut V)}
    {W W' : Subgroup V} (hq₁ : CFSG.IsQuasisimple ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂)
    (hA₁ : A38Types ↥K₁) (hA₂ : A38Types ↥K₂) (hSL3 : A38TypesSLThree)
    (hKJ : K₁ ⊔ K₂ ≤ J) (hGJ : G ≤ J) (hG'J : G' ≤ J)
    (hinv : ∀ j ∈ J, ∀ w ∈ W, j w ∈ W) (hinv' : ∀ j ∈ J, ∀ w ∈ W', j w ∈ W')
    (hCW : fixV J ≤ W) (hCW' : fixV J ≤ W') (hWW : W ⊔ W' = ⊤) (hWiW : W ⊓ W' = fixV J)
    (hp : B56Piece G W (fixV J)) (hp' : B56Piece G' W' (fixV J)) (h₁ : InCore K₁ G)
    (h₂ : InCore K₂ G') :
    (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) ⊓ (commV K₂ ⊔ fixV (K₁ ⊔ K₂)) = fixV (K₁ ⊔ K₂) ∧
      ModType K₁ (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) (fixV (K₁ ⊔ K₂)) := by
  set C := fixV J with hC
  have hWiW' : W' ⊓ W = C := by rw [inf_comm]; exact hWiW
  have hWW' : W' ⊔ W = ⊤ := by rw [sup_comm]; exact hWW
  have hcomm := commV_le_modComm (commV_le_of_piece hp) (fun g hg => hinv' g (hGJ hg)) hWW hWiW
  have hcomm' := commV_le_modComm (commV_le_of_piece hp') (fun g hg => hinv g (hG'J hg)) hWW'
    hWiW'
  obtain ⟨hP1, hP2, hP3⟩ := piece_out h₁.1 h₁.2 hq₁ hV2 hA₁ hSL3 (fun g hg => hinv g (hGJ hg))
    hcomm hCW hp
  obtain ⟨hP1', hP2', -⟩ := piece_out h₂.1 h₂.2 hq₂ hV2 hA₂ hSL3 (fun g hg => hinv' g (hG'J hg))
    hcomm' hCW' hp'
  have hZ : fixV (K₁ ⊔ K₂) = C := by
    refine le_antisymm (fun z hz => ?_) (fixV_anti hKJ)
    have hv : z ∈ W ⊔ W' := hWW ▸ Subgroup.mem_top z
    obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.mp hv
    have key : ∀ k ∈ K₁ ⊔ K₂, k w * w⁻¹ ∈ C ∧ k w' * w'⁻¹ ∈ C := by
      intro k hk
      have h1 : k (w * w') = w * w' := hz k hk
      have hkw : k w * w⁻¹ ∈ W := W.mul_mem (hinv k (hKJ hk) w hw) (W.inv_mem hw)
      have hkw' : k w' * w'⁻¹ ∈ W' := W'.mul_mem (hinv' k (hKJ hk) w' hw') (W'.inv_mem hw')
      have e : k w * w⁻¹ = (k w' * w'⁻¹)⁻¹ := by
        rw [map_mul] at h1
        rw [eq_inv_iff_mul_eq_one, mul_mul_mul_comm, h1, ← mul_inv, mul_inv_cancel]
      have hin : k w * w⁻¹ ∈ W ⊓ W' := ⟨hkw, e ▸ W'.inv_mem hkw'⟩
      rw [hWiW] at hin
      refine ⟨hin, ?_⟩
      have : k w' * w'⁻¹ = (k w * w⁻¹)⁻¹ := by rw [e, inv_inv]
      rw [this]
      exact C.inv_mem hin
    have hw1 : w ∈ C := hP1 w hw fun k hk => (key k (Subgroup.mem_sup_left hk)).1
    have hw2 : w' ∈ C := hP1' w' hw' fun k hk => (key k (Subgroup.mem_sup_right hk)).2
    exact C.mul_mem hw1 hw2
  rw [hZ]
  refine ⟨le_antisymm ?_ (le_inf le_sup_right le_sup_right), hP3⟩
  exact (inf_le_inf hP2 hP2').trans hWiW.le

theorem commV_conjSub (y : MulAut V) (K : Subgroup (MulAut V)) :
    commV (conjSub y K) = (commV K).map y.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq K y

theorem fixV_conjSub (y : MulAut V) (K : Subgroup (MulAut V)) :
    fixV (conjSub y K) = (fixV K).map y.toMonoidHom :=
  CFSG.Quasithin.B6.fixV_conjSub y K

theorem mem_fixV_sup {A B : Subgroup (MulAut V)} {v : V} (hA : v ∈ fixV A) (hB : v ∈ fixV B) :
    v ∈ fixV (A ⊔ B) :=
  CFSG.Quasithin.FixVLat.mem_fixV_sup hA hB

end CFSG.Quasithin.H13.M338
