module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

@[expose] def e6TwoT31Exp (j : Fin (Tag.rank .E6)) : ℤ :=
  (![30, 24, 29, 27, 23, 16] : Fin 6 → ℤ) j

@[expose] def e6TwoT31Char {K : Type} [Field K] (ζ : Kˣ) : Fin (Tag.rank .E6) → Kˣ :=
  fun j => ζ ^ e6TwoT31Exp j

private theorem e6TwoT31_rootChar {K : Type} [Field K] (ζ : Kˣ)
    (v : Fin (Tag.rank .E6) → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (e6TwoT31Char ζ) v =
      ζ ^ (∑ j, v j * e6TwoT31Exp j) := by
  simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, e6TwoT31Char,
    ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem e6TwoT31_rootChar_eq_one {K : Type} [Field K] {ζ : Kˣ}
    (hζ : orderOf ζ = 31) {v : Fin (Tag.rank .E6) → ℤ}
    (h : (31 : ℤ) ∣ ∑ j, v j * e6TwoT31Exp j) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (e6TwoT31Char ζ) v = 1 := by
  rw [e6TwoT31_rootChar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  exact h

private theorem e6TwoT31_dvd_of_rootChar_eq_one {K : Type} [Field K] {ζ : Kˣ}
    (hζ : orderOf ζ = 31) {v : Fin (Tag.rank .E6) → ℤ}
    (h : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (e6TwoT31Char ζ) v = 1) :
    (31 : ℤ) ∣ ∑ j, v j * e6TwoT31Exp j := by
  rw [e6TwoT31_rootChar] at h
  rw [← orderOf_dvd_iff_zpow_eq_one, hζ] at h
  exact h

private theorem e6TwoT31_kernel_check : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) →
      v = highRoot .E6 ∨ v = -highRoot .E6 := by
  decide +kernel

private def e6TwoT31_s (i : Fin 6) : Fin (Tag.rank .E6) → ℤ :=
  Pi.single (Fin.cast (by decide) i) 1

private def e6TwoT31_c0 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) = 0 then -1 else if (j : ℕ) = 1 then 0 else -1

private def e6TwoT31_c2 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) < 2 then 0 else -1

private def e6TwoT31_c3 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) < 3 then 0 else -1

private def e6TwoT31_c4 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) < 4 then 0 else -1

private def e6TwoT31_c5 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) = 1 then 0 else if (j : ℕ) = 5 then 0 else 1

private def e6TwoT31_c1a : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) = 1 then 0 else if (j : ℕ) = 4 then 0 else if (j : ℕ) = 5 then 0 else 1

private def e6TwoT31_c1 : Fin (Tag.rank .E6) → ℤ :=
  fun j => if (j : ℕ) = 2 then -2 else if (j : ℕ) = 3 then -3 else if (j : ℕ) = 4 then -2 else -1

private theorem e6TwoT31_beta0 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 30 →
      v = e6TwoT31_s 0 ∨ v = e6TwoT31_c0 := by
  decide +kernel

private theorem e6TwoT31_beta1 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 24 →
      v = e6TwoT31_s 1 ∨ v = e6TwoT31_c1a ∨ v = e6TwoT31_c1 := by
  decide +kernel

private theorem e6TwoT31_beta2 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 29 →
      v = e6TwoT31_s 2 ∨ v = e6TwoT31_c2 := by
  decide +kernel

private theorem e6TwoT31_beta3 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 27 →
      v = e6TwoT31_s 3 ∨ v = e6TwoT31_c3 := by
  decide +kernel

private theorem e6TwoT31_beta4 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 23 →
      v = e6TwoT31_s 4 ∨ v = e6TwoT31_c4 := by
  decide +kernel

private theorem e6TwoT31_beta5 : ∀ v ∈ rootFinset .E6,
    (31 : ℤ) ∣ (∑ j, v j * e6TwoT31Exp j) - 16 →
      v = e6TwoT31_s 5 ∨ v = e6TwoT31_c5 := by
  decide +kernel

private theorem e6TwoT31_force02 {x y : Fin (Tag.rank .E6) → ℤ}
    (hx : x = e6TwoT31_s 0 ∨ x = e6TwoT31_c0)
    (hy : y = e6TwoT31_s 2 ∨ y = e6TwoT31_c2)
    (h : CFSG.LieType.Steinberg.Adjoint.iform x y =
      CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 0) (e6TwoT31_s 2)) :
    x = e6TwoT31_s 0 ∧ y = e6TwoT31_s 2 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso; exact absurd h (by decide +kernel)
  · exfalso; exact absurd h (by decide +kernel)
  · exfalso; exact absurd h (by decide +kernel)

private theorem e6TwoT31_force23 {y : Fin (Tag.rank .E6) → ℤ}
    (hy : y = e6TwoT31_s 3 ∨ y = e6TwoT31_c3)
    (h : CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 2) y =
      CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 2) (e6TwoT31_s 3)) :
    y = e6TwoT31_s 3 := by
  rcases hy with rfl | rfl
  · rfl
  · exfalso; exact absurd h (by decide +kernel)

private theorem e6TwoT31_force34 {y : Fin (Tag.rank .E6) → ℤ}
    (hy : y = e6TwoT31_s 4 ∨ y = e6TwoT31_c4)
    (h : CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 3) y =
      CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 3) (e6TwoT31_s 4)) :
    y = e6TwoT31_s 4 := by
  rcases hy with rfl | rfl
  · rfl
  · exfalso; exact absurd h (by decide +kernel)

private theorem e6TwoT31_force45 {y : Fin (Tag.rank .E6) → ℤ}
    (hy : y = e6TwoT31_s 5 ∨ y = e6TwoT31_c5)
    (h : CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 4) y =
      CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 4) (e6TwoT31_s 5)) :
    y = e6TwoT31_s 5 := by
  rcases hy with rfl | rfl
  · rfl
  · exfalso; exact absurd h (by decide +kernel)

private theorem e6TwoT31_force13 {x : Fin (Tag.rank .E6) → ℤ}
    (hx : x = e6TwoT31_s 1 ∨ x = e6TwoT31_c1a ∨ x = e6TwoT31_c1)
    (h : CFSG.LieType.Steinberg.Adjoint.iform x (e6TwoT31_s 3) =
      CFSG.LieType.Steinberg.Adjoint.iform (e6TwoT31_s 1) (e6TwoT31_s 3)) :
    x = e6TwoT31_s 1 ∨ x = e6TwoT31_c1 := by
  rcases hx with rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso; exact absurd h (by decide +kernel)
  · exact Or.inr rfl

theorem rootCharKernel_e6TwoT31Char {K : Type} [Field K] {ζ : Kˣ}
    (hζ : orderOf ζ = 31) :
    rootCharKernel (e6TwoT31Char ζ) = {highRoot .E6, -highRoot .E6} := by
  ext α
  rw [rootCharKernel]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, h1⟩
    exact e6TwoT31_kernel_check α (mem_rootFinset.2 hα)
      (e6TwoT31_dvd_of_rootChar_eq_one hζ h1)
  · rintro (rfl | rfl)
    · exact ⟨isRoot_highRoot .E6, e6TwoT31_rootChar_eq_one hζ (by decide)⟩
    · exact ⟨IsRoot.neg (isRoot_highRoot .E6), e6TwoT31_rootChar_eq_one hζ (by decide)⟩

theorem rootCharStabilizerSubgroup_e6TwoT31Char_le
    {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 31) :
    rootCharStabilizerSubgroup (e6TwoT31Char ζ) ≤ kernelReflectionGroup (e6TwoT31Char ζ) := by
  intro w hw
  let i0 : Fin (Tag.rank .E6) := ⟨0, by decide⟩
  let i1 : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  let i2 : Fin (Tag.rank .E6) := ⟨2, by decide⟩
  let i3 : Fin (Tag.rank .E6) := ⟨3, by decide⟩
  let i4 : Fin (Tag.rank .E6) := ⟨4, by decide⟩
  let i5 : Fin (Tag.rank .E6) := ⟨5, by decide⟩
  have hw' : ∀ v : Fin (Tag.rank .E6) → ℤ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (e6TwoT31Char ζ) (w • v) =
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (e6TwoT31Char ζ) v := hw
  have hβdvd : ∀ i : Fin (Tag.rank .E6),
      (31 : ℤ) ∣ (∑ j, (w • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)) j * e6TwoT31Exp j) -
        e6TwoT31Exp i := by
    intro i
    have h := hw' (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)
    rw [e6TwoT31_rootChar, e6TwoT31_rootChar] at h
    have he : ∑ j, (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) j * e6TwoT31Exp j =
        e6TwoT31Exp i := by
      rw [Finset.sum_eq_single i
        (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [Pi.single_eq_same, one_mul]
    have hsub : ζ ^ ((∑ j, (w • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)) j *
        e6TwoT31Exp j) - e6TwoT31Exp i) = 1 := by
      rw [zpow_sub, h, he, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hζ] at hsub
    exact hsub
  have hβ0 := e6TwoT31_beta0 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i0) w))
    (hβdvd i0)
  have hβ1 := e6TwoT31_beta1 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i1) w))
    (hβdvd i1)
  have hβ2 := e6TwoT31_beta2 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i2) w))
    (hβdvd i2)
  have hβ3 := e6TwoT31_beta3 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i3) w))
    (hβdvd i3)
  have hβ4 := e6TwoT31_beta4 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i4) w))
    (hβdvd i4)
  have hβ5 := e6TwoT31_beta5 _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 i5) w))
    (hβdvd i5)
  have h02 := e6TwoT31_force02 hβ0 hβ2
    (iform_smul w (Pi.single i0 1) (Pi.single i2 1))
  have h23 := e6TwoT31_force23 hβ3 (by
    have h := iform_smul w (Pi.single i2 1) (Pi.single i3 1)
    rw [h02.2] at h
    exact h)
  have h34 := e6TwoT31_force34 hβ4 (by
    have h := iform_smul w (Pi.single i3 1) (Pi.single i4 1)
    rw [h23] at h
    exact h)
  have h45 := e6TwoT31_force45 hβ5 (by
    have h := iform_smul w (Pi.single i4 1) (Pi.single i5 1)
    rw [h34] at h
    exact h)
  have h13 := e6TwoT31_force13 hβ1 (by
    have h := iform_smul w (Pi.single i1 1) (Pi.single i3 1)
    rw [h23] at h
    exact h)
  rcases h13 with h13s | h13c
  · have hw1 : w = 1 := by
      refine ext_single fun i => ?_
      fin_cases i
      · rw [h02.1, one_smul]; rfl
      · rw [h13s, one_smul]; rfl
      · rw [h02.2, one_smul]; rfl
      · rw [h23, one_smul]; rfl
      · rw [h34, one_smul]; rfl
      · rw [h45, one_smul]; rfl
    rw [hw1]
    exact one_mem _
  · have hwR : w = rootReflection (highRoot .E6) := by
      refine ext_single fun i => ?_
      rw [rootReflection_smul (isRoot_highRoot .E6) (Pi.single i 1)]
      fin_cases i
      · rw [h02.1]; decide +kernel
      · rw [h13c]; decide +kernel
      · rw [h02.2]; decide +kernel
      · rw [h23]; decide +kernel
      · rw [h34]; decide +kernel
      · rw [h45]; decide +kernel
    rw [hwR]
    have hθker : highRoot .E6 ∈ rootCharKernel (e6TwoT31Char ζ) := by
      rw [rootCharKernel_e6TwoT31Char hζ]
      exact Set.mem_insert_iff.2 (Or.inl rfl)
    obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 (isRoot_highRoot .E6)
    rw [rootReflection_eq_conj huj]
    exact Subgroup.subset_closure ⟨u, j, huj ▸ hθker, rfl⟩

end CFSG.StandardType.GGSixE6Two
