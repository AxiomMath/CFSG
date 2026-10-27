module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139C3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.concl_of_shapeCover (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K)
    (h : ShapeCover K X n) : Concl139 W G X n := by
  obtain ⟨hn3, hHat, hXcenter, hWcard⟩ := h
  have hXK : X ≤ K := by
    rw [← hXcenter]
    exact Subgroup.map_subtype_le (Subgroup.center ↥K)
  have hKG : K ≤ G := hK.comp.1
  let N : Subgroup (MulAut W) := Subgroup.normalizer (K : Set (MulAut W))
  have hGN : G ≤ N := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hK.normal g hg)
  have hirr : IsIrrOn K ⊤ ⊥ := by
    refine ⟨lt_of_le_of_ne le_top (Ne.symm hK.irr.1), hK.irr.2.1, ?_, ?_⟩
    · intro x _ y hy
      rw [Subgroup.mem_bot] at hy ⊢
      rw [hy, map_one]
    · intro J hKJ _ _
      exact hK.irr.2.2.2 J hKJ (fun x hx j hj => hKJ x (hXK hx) j hj) le_top
  obtain ⟨φ, hφsurj, hφker⟩ := gapThreeA6Normalizer_holds W hw2 K hHat hirr hWcard
  have hφker' : φ.ker = X.subgroupOf N := by
    rw [hφker, hXcenter]
  have hKcard : Nat.card ↥K = 1080 := by
    obtain ⟨e⟩ := hHat.2.2
    have h1 : Nat.card ↥K =
        Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card (Subgroup.center ↥K) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [h1, Nat.card_congr e.toEquiv, hHat.2.1, hA6]
  have hXN : X ≤ N := hXK.trans (hKG.trans hGN)
  have hPerm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hNcard : Nat.card ↥N = 2160 := by
    have h1 : Nat.card ↥N = Nat.card (↥N ⧸ φ.ker) * Nat.card φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker : Subgroup ↥N)
    have h2 : Nat.card (↥N ⧸ φ.ker) = Nat.card (Equiv.Perm (Fin 6)) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := φ) hφsurj).toEquiv
    have h3 : Nat.card φ.ker = 3 := by
      rw [hφker', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv, S.Xcard]
    rw [h1, h2, h3, hPerm]
  have hs_notK : s ∉ K := by
    intro hsK
    obtain ⟨x, hXgen, hx3, hx_ne, _hfixX, hsx⟩ := Std139.exists_gen hw2 S
    have hxX : x ∈ X := by rw [hXgen]; exact Subgroup.mem_zpowers x
    have hxcenter : x ∈ (Subgroup.center ↥K).map K.subtype := by
      rw [hXcenter]
      exact hxX
    obtain ⟨z, hz, hzx⟩ := hxcenter
    have hzx' : (z : MulAut W) = x := hzx
    have hcomm : (⟨s, hsK⟩ : ↥K) * z = z * ⟨s, hsK⟩ :=
      (Subgroup.mem_center_iff.mp hz) ⟨s, hsK⟩
    have hsx_eq : s * x = x * s := by
      have hh := congrArg (fun g : ↥K => (g : MulAut W)) hcomm
      simpa [hzx'] using hh
    have hconj : s * x * s⁻¹ = x := by
      rw [hsx_eq, mul_assoc, mul_inv_cancel, mul_one]
    have hxinv : x⁻¹ = x := by rw [← hsx, hconj]
    have hx2 : x ^ 2 ≠ 1 := by
      intro h2
      have h3 := hx3
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at h3
      exact hx_ne h3
    have hxinv_ne : x⁻¹ ≠ x := by
      intro hinv
      have hxx : x * x = 1 := by
        have h : x * x⁻¹ = 1 := mul_inv_cancel x
        rwa [hinv] at h
      exact hx2 (by simpa [pow_two] using hxx)
    exact hxinv_ne hxinv
  have hsG_notin : (⟨s, S.sG⟩ : ↥G) ∉ K.subgroupOf G := fun hmem =>
    hs_notK (by simpa [Subgroup.mem_subgroupOf] using hmem)
  have hKsub_ne_top : K.subgroupOf G ≠ ⊤ := fun htop =>
    hsG_notin (htop.symm ▸ Subgroup.mem_top (⟨s, S.sG⟩ : ↥G))
  have hIndex_gt1 : 1 < (K.subgroupOf G).index :=
    Subgroup.one_lt_index_of_ne_top hKsub_ne_top
  have hGcard : Nat.card ↥G = 2160 := by
    have h1 : Nat.card ↥(K.subgroupOf G) * (K.subgroupOf G).index = Nat.card ↥G :=
      Subgroup.card_mul_index (K.subgroupOf G)
    have h2 : Nat.card ↥(K.subgroupOf G) = 1080 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv]
      exact hKcard
    rw [h2] at h1
    have hle : Nat.card ↥G ≤ 2160 := by
      calc Nat.card ↥G ≤ Nat.card ↥N := Subgroup.card_le_of_le hGN
        _ = 2160 := hNcard
    omega
  have hGN_eq : G = N :=
    Subgroup.eq_of_le_of_card_ge hGN (by rw [hNcard, hGcard])
  have hS6G : IsS6Cover W G X := hGN_eq.symm ▸ ⟨φ, hφsurj, hφker'⟩
  exact Or.inl (Or.inr (Or.inr ⟨hS6G, hn3⟩))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
