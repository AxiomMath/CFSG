module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.LongRootClosure
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRootTransport
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
import CFSG.Quasithin.Vol2.KGNatComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem lam_range_le_of_single_mem_centres {H : Subgroup (StatedSp 2 K)} {i : Fin 2}
    (he : Pi.single (Sum.inl i) 1 ∈ centres H) (hf : Pi.single (Sum.inr i) 1 ∈ centres H) :
    (lam i : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H := by
  have hU : ∀ c : K, (lam i) (sl2Up K c) ∈ H := by
    intro c
    rw [← pairRootElt_long i c]
    exact (single_mem_centres_iff (Sum.inl i)).1 he c
  have hL : ∀ c : K, (lam i) (sl2Low K c) ∈ H := by
    intro c
    rw [← pairRootElt_long' i c]
    exact (single_mem_centres_iff (Sum.inr i)).1 hf c
  rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
    (K := K), Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro x (hx | hx)
  · obtain ⟨c, rfl⟩ := hx
    exact hU c
  · obtain ⟨c, rfl⟩ := hx
    exact hL c

theorem span_centres_eq_top {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hred : ¬ IsTorusReducible H) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ centres H) (hv0 : v ≠ 0) :
    Submodule.span K (centres H) = ⊤ := by
  have hne_bot : Submodule.span K (centres H) ≠ ⊥ := by
    intro h
    have hvW : v ∈ Submodule.span K (centres H) := Submodule.subset_span hv
    rw [h] at hvW
    exact hv0 (by simpa using hvW)
  by_contra hne_top
  refine hred ⟨Submodule.span K (centres H), hne_bot, hne_top, ?_, ?_⟩
  · intro d hd w hw
    have hle : Submodule.span K (centres H) ≤
        Submodule.comap (Matrix.mulVecLin
          (((d : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
          (Submodule.span K (centres H)) := by
      rw [Submodule.span_le]
      intro u hu
      exact Submodule.subset_span (torus_mulVec_mem_centres hT hu hd)
    simpa only [Matrix.mulVecLin_apply, Submodule.mem_comap] using hle hw
  · intro h hh w hw
    have hle : Submodule.span K (centres H) ≤
        Submodule.comap (Matrix.mulVecLin
          (((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
          (Submodule.span K (centres H)) := by
      rw [Submodule.span_le]
      intro u hu
      exact Submodule.subset_span (mulVec_mem_centres hu hh)
    simpa only [Matrix.mulVecLin_apply, Submodule.mem_comap] using hle hw

variable [Finite K] [CharP K 2]

theorem single_swap_mem_centres (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hspan : Submodule.span K (centres H) = ⊤) {c : Fin 2 ⊕ Fin 2}
    (hc : Pi.single c 1 ∈ centres H) : Pi.single c.swap 1 ∈ centres H := by
  have hex : ∃ v : Fin 2 ⊕ Fin 2 → K, v ∈ centres H ∧ v c.swap ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Submodule.span K (centres H) ≤ LinearMap.ker (LinearMap.proj c.swap) := by
      rw [Submodule.span_le]
      exact fun v hv => LinearMap.mem_ker.mpr (h v hv)
    have hone : (Pi.single c.swap 1 : Fin 2 ⊕ Fin 2 → K) ∈ Submodule.span K (centres H) := by
      rw [hspan]
      exact Submodule.mem_top
    have h0 : (Pi.single c.swap 1 : Fin 2 ⊕ Fin 2 → K) c.swap = 0 := by
      simpa [LinearMap.proj_apply] using hle hone
    rw [Pi.single_eq_same] at h0
    exact one_ne_zero h0
  obtain ⟨v, hv, hv0⟩ := hex
  rcases c with i | i
  · have hvw : Matrix.toBilin' (CFSG.Quasithin.Vol2.KGNat.spJ K) v
        (Pi.single (Sum.inl i) 1) ≠ 0 := by
      rw [CFSG.Quasithin.Vol2.KGNat.spB_single_inl]
      exact neg_ne_zero.mpr hv0
    let u : Fin 2 ⊕ Fin 2 → K :=
      (1 : K) • v + (1 - v (Sum.inl i)) • Pi.single (Sum.inl i) 1
    have hu : u ∈ centres H :=
      add_smul_mem_centres (H := H) (v := v) (w := Pi.single (Sum.inl i) 1) hv hc hvw
        1 (1 - v (Sum.inl i))
    have hu1 : u (Sum.inl i) ≠ 0 := by
      have h1 : u (Sum.inl i) = 1 := by
        simp [u]
      rw [h1]
      exact one_ne_zero
    have hu2 : u (Sum.inr i) ≠ 0 := by
      have h1 : u (Sum.inr i) = v (Sum.inr i) := by simp [u]
      rw [h1]
      exact hv0
    exact (single_mem_centres_of_apply_ne_zero hK hT hu hu1 hu2).2
  · have hvw : Matrix.toBilin' (CFSG.Quasithin.Vol2.KGNat.spJ K) v
        (Pi.single (Sum.inr i) 1) ≠ 0 := by
      rw [CFSG.Quasithin.Vol2.KGNat.spB_single_inr]
      exact hv0
    let u : Fin 2 ⊕ Fin 2 → K :=
      (1 : K) • v + (1 - v (Sum.inr i)) • Pi.single (Sum.inr i) 1
    have hu : u ∈ centres H :=
      add_smul_mem_centres (H := H) (v := v) (w := Pi.single (Sum.inr i) 1) hv hc hvw
        1 (1 - v (Sum.inr i))
    have hu1 : u (Sum.inr i) ≠ 0 := by
      have h1 : u (Sum.inr i) = 1 := by
        simp [u]
      rw [h1]
      exact one_ne_zero
    have hu2 : u (Sum.inl i) ≠ 0 := by
      have h1 : u (Sum.inl i) = v (Sum.inl i) := by simp [u]
      rw [h1]
      exact hv0
    exact (single_mem_centres_of_apply_ne_zero hK hT hu hu2 hu1).1

theorem single_inl_mem_centres_of_ne (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hspan : Submodule.span K (centres H) = ⊤) {i j : Fin 2} (hij : i ≠ j)
    (he : Pi.single (Sum.inl i) 1 ∈ centres H) (hf : Pi.single (Sum.inr i) 1 ∈ centres H) :
    Pi.single (Sum.inl j) 1 ∈ centres H := by
  have hex : ∃ v : Fin 2 ⊕ Fin 2 → K, v ∈ centres H ∧ v (Sum.inl j) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Submodule.span K (centres H) ≤ LinearMap.ker (LinearMap.proj (Sum.inl j)) := by
      rw [Submodule.span_le]
      exact fun v hv => LinearMap.mem_ker.mpr (h v hv)
    have hone : (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → K) ∈
        Submodule.span K (centres H) := by
      rw [hspan]
      exact Submodule.mem_top
    have h0 : (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → K) (Sum.inl j) = 0 := by
      simpa [LinearMap.proj_apply] using hle hone
    rw [Pi.single_eq_same] at h0
    exact one_ne_zero h0
  obtain ⟨v, hv, hv0⟩ := hex
  let w : Fin 2 ⊕ Fin 2 → K :=
    fun k => if k = Sum.inl i ∨ k = Sum.inr i then 0 else v k
  have hw : w ∈ centres H := proj_mem_centres hK hT he hf hv
  have hwi : w (Sum.inl i) = 0 := by simp [w]
  have hwir : w (Sum.inr i) = 0 := by simp [w]
  have hwj : w (Sum.inl j) ≠ 0 := by
    have h1 : (Sum.inl j : Fin 2 ⊕ Fin 2) ≠ Sum.inl i :=
      fun h => hij (Sum.inl_injective h).symm
    have h2 : (Sum.inl j : Fin 2 ⊕ Fin 2) ≠ Sum.inr i := Sum.inl_ne_inr
    simpa [w, h1, h2] using hv0
  by_cases h2 : w (Sum.inr j) ≠ 0
  · exact (single_mem_centres_of_apply_ne_zero hK hT hw hwj h2).1
  · push Not at h2
    have hfin : ∀ a : Fin 2, a ≠ i → a = j := by
      intro a hai
      have h1 : a.val ≠ i.val := fun h => hai (Fin.ext h)
      have h3 : i.val ≠ j.val := fun h => hij (Fin.ext h)
      exact Fin.ext (by omega)
    have hsupp : ∀ k : Fin 2 ⊕ Fin 2, k ≠ Sum.inl j → w k = 0 := by
      intro k hk
      rcases k with a | a
      · by_cases hai : a = i
        · rw [hai]; exact hwi
        · rw [hfin a hai] at hk ⊢
          exact absurd rfl hk
      · by_cases hai : a = i
        · rw [hai]; exact hwir
        · rw [hfin a hai]; exact h2
    have hmul : (w (Sum.inl j))⁻¹ • w = Pi.single (Sum.inl j) 1 := by
      funext k
      by_cases hk : k = Sum.inl j
      · subst hk
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
        exact inv_mul_cancel₀ hwj
      · rw [Pi.smul_apply, hsupp k hk, smul_zero]
        simp [hk]
    rw [← hmul]
    exact smul_mem_centres hw _

theorem lam_range_le_of_long_root (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) {a : Fin 2 ⊕ Fin 2}
    (ha : ∀ s : K, pairRootElt (swap_ne_self a).symm s ∈ H) (hred : ¬ IsTorusReducible H) :
    (lam 0 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H ∧
      (lam 1 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H := by
  have hae : Pi.single a 1 ∈ centres H := (single_mem_centres_iff a).2 ha
  have hne : (Pi.single a 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa using congrFun h a
    exact one_ne_zero h1
  have hspan : Submodule.span K (centres H) = ⊤ := span_centres_eq_top hT hred hae hne
  have haswap : Pi.single a.swap 1 ∈ centres H := single_swap_mem_centres hK hT hspan hae
  have key : ∀ (i : Fin 2), Pi.single (Sum.inl i) 1 ∈ centres H →
      Pi.single (Sum.inr i) 1 ∈ centres H →
      (lam 0 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H ∧
        (lam 1 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H := by
    intro i hei hfi
    by_cases h0 : i = 0
    · subst h0
      have he1 : Pi.single (Sum.inl 1) 1 ∈ centres H :=
        single_inl_mem_centres_of_ne (H := H) hK hT hspan (i := 0) (j := 1) (by decide) hei hfi
      have hf1 : Pi.single (Sum.inr 1) 1 ∈ centres H :=
        single_swap_mem_centres (H := H) (c := Sum.inl 1) hK hT hspan he1
      exact ⟨lam_range_le_of_single_mem_centres (H := H) hei hfi,
        lam_range_le_of_single_mem_centres (H := H) he1 hf1⟩
    · have hi1 : i = 1 := by
        have hne : i.val ≠ 0 := fun h' => h0 (Fin.ext (by simpa using h'))
        have hlt : i.val < 2 := i.isLt
        exact Fin.ext (by omega)
      subst hi1
      have he0 : Pi.single (Sum.inl 0) 1 ∈ centres H :=
        single_inl_mem_centres_of_ne (H := H) hK hT hspan (i := 1) (j := 0) (by decide) hei hfi
      have hf0 : Pi.single (Sum.inr 0) 1 ∈ centres H :=
        single_swap_mem_centres (H := H) (c := Sum.inl 0) hK hT hspan he0
      exact ⟨lam_range_le_of_single_mem_centres (H := H) he0 hf0,
        lam_range_le_of_single_mem_centres (H := H) hei hfi⟩
  rcases a with i | i
  · exact key i hae haswap
  · exact key i haswap hae

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
