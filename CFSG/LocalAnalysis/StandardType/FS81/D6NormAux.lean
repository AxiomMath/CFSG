module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem rot_swap (a b : V) : rot Q b a = (rot Q a b)⁻¹ := by
  rw [rot, rot, mul_inv_rev, reflect_inv, reflect_inv]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

namespace CFSG.StandardType.SevOm

open Module QuadraticMap
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem Frame.iSup_pieces_eq_top (F : Frame Q 3 A r) (hdim : finrank K V = 2 * r)
    (hU : ∀ i, finrank K (F.U i) = 2) : (⨆ i, F.U i) = ⊤ := by
  have hind := F.iSupIndep_pieces
  have hsum : (⨆ i ∈ (Finset.univ : Finset (Fin r)), F.U i) = ⨆ i, F.U i := by simp
  have h1 : finrank K ↥(⨆ i, F.U i) = 2 * r := by
    rw [← hsum, CFSG.RankThree.Classical.finrank_biSup_of_iSupIndep hind Finset.univ]
    rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  exact Submodule.eq_top_of_finrank_eq (by rw [h1, hdim])

end CFSG.StandardType.SevOm

namespace CFSG.StandardType.SevOm

open Module QuadraticMap
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {r : ℕ} {A : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem Frame.exists_rot_pair (F : Frame Q 3 A r)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (htop : (⨆ i, F.U i) = ⊤)
    (j : Fin r) (hUj : finrank (ZMod 2) (F.U j) = 2) {x : V} (hx : x ∈ F.U j) (hx0 : x ≠ 0) :
    MinusPair Q x (F.ι (Multiplicative.ofAdd (Pi.single j 1)) x) ∧
      F.ι (Multiplicative.ofAdd (Pi.single j 1)) x ∈ F.U j ∧
      rot Q x (F.ι (Multiplicative.ofAdd (Pi.single j 1)) x) =
        F.ι (Multiplicative.ofAdd (Pi.single j 1)) := by
  classical
  set τ : V ≃ₗ[ZMod 2] V := F.ι (Multiplicative.ofAdd (Pi.single j 1)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have h3 : (Multiplicative.ofAdd (Pi.single j 1) : Multiplicative (Fin r → ZMod 3)) ^ 3 = 1 := by
      rw [← ofAdd_nsmul]
      have h0 : (3 : ℕ) • (Pi.single j 1 : Fin r → ZMod 3) = 0 := by
        have h : ∀ y : ZMod 3, (3 : ℕ) • y = 0 := by decide
        ext i
        simpa using h ((Pi.single j 1 : Fin r → ZMod 3) i)
      rw [h0, ofAdd_zero]
    rw [h3, map_one]
  have hτO : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine hAO ?_
    rw [← F.range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hτQ : ∀ v, Q (τ v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hτO v
  have hmapU : ∀ v ∈ F.U j, τ v ∈ F.U j := fun v hv => F.mapsTo _ j v hv
  have hfpf : ∀ v ∈ F.U j, τ v = v → v = 0 := fun v hv => F.fpf _ j (by simp) v hv
  set y : V := τ x with hy
  set z : V := τ y with hz
  have hτx : τ x = y := hy.symm
  have hτy : τ y = z := hz.symm
  have hyU : y ∈ F.U j := hmapU x hx
  have hzU : z ∈ F.U j := hmapU y hyU
  have hQy : Q y = Q x := hτQ x
  have hQz : Q z = Q y := hτQ y
  have hy0 : y ≠ 0 := by
    intro h
    exact hx0 (τ.injective (by rw [hτx, h, map_zero]))
  have hz0 : z ≠ 0 := by
    intro h
    exact hy0 (τ.injective (by rw [hτy, h, map_zero]))
  have h3x : τ (τ (τ x)) = x := by
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) hτ3
    simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using h
  have hτz : τ z = x := by
    rw [hz, ← hτx]
    exact h3x
  have hxy : x ≠ y := by
    intro h
    exact hx0 (hfpf x hx ((h.trans hy).symm))
  have hxz : x ≠ z := by
    intro h
    have h1 : τ x = τ z := by rw [h]
    rw [hτz] at h1
    exact hxy (by rw [hy]; exact h1.symm)
  have hli : LinearIndependent (ZMod 2) ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [zero_smul, zero_add, one_smul] at hcd
      exact absurd hcd hy0
    · simp only [zero_smul, add_zero, one_smul] at hcd
      exact absurd hcd hx0
    · simp only [one_smul] at hcd
      have h1 : x = y := by
        have h2 : x = -y := add_eq_zero_iff_eq_neg.mp hcd
        rwa [vec_neg] at h2
      exact absurd h1 hxy
  have hrange : Set.range ![x, y] = ({x, y} : Set V) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hv
      rcases hv with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : Submodule.span (ZMod 2) ({x, y} : Set V) = F.U j := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro v (rfl | rfl)
      · exact hx
      · exact hyU
    · rw [hUj, ← hrange, finrank_span_eq_card hli, Fintype.card_fin]
  have hzU' : z ∈ Submodule.span (ZMod 2) ({x, y} : Set V) := by
    rw [hspan]
    exact hzU
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hzU'
  have hzy : z = x + y := by
    rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
    · exact absurd (by rw [← hcd]; simp) hz0
    · have hzy' : z = y := by rw [← hcd]; simp
      exact absurd (by rw [← hτz, hzy', hτy, hzy']) hxy
    · exact absurd (by rw [← hcd]; simp) hxz
    · rw [← hcd]; simp
  have hB : polar Q x y = Q x := by
    have h1 : Q z = Q x := hQz.trans hQy
    rw [hzy] at h1
    rw [QuadraticMap.map_add Q x y] at h1
    rw [hQy] at h1
    have h2 : Q x + Q x = 0 := by
      have h2' : ∀ y : ZMod 2, y + y = 0 := by decide
      exact h2' (Q x)
    rw [h2, zero_add] at h1
    exact h1
  have hB1 : polar Q x y = 1 := by
    by_contra hne
    have hq0 : Q x = 0 := by
      rw [← hB]
      rcases zmod_two_cases (polar Q x y) with h | h
      · exact h
      · exact absurd h hne
    refine hx0 (F.nondeg j x hx (fun v hv => ?_))
    rw [← hspan] at hv
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, polar_self_zero]
    rw [QuadraticMap.polar_comm Q y x, hB, hq0]
    simp
  have hQx : Q x = 1 := by
    rw [← hB]
    exact hB1
  have hmp : MinusPair Q x y := ⟨hQx, hQy.trans hQx, hB1⟩
  have hrot : rot Q x y = τ := by
    refine LinearEquiv.ext fun v => ?_
    refine Submodule.iSup_induction (p := F.U) (motive := fun v => rot Q x y v = τ v)
      (by rw [htop]; exact Submodule.mem_top) ?_ ?_ ?_
    · intro k v hv
      by_cases hk : k = j
      · subst hk
        rw [← hspan] at hv
        obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
        simp only [map_add, map_smul, rot_apply_left hmp, rot_apply_right hmp, hτx, hτy, hzy]
      · have hτv : τ v = F.ι (Multiplicative.ofAdd (Pi.single j 1)) v := by rw [hτ]
        rw [hτv, F.triv _ k (by
            rw [toAdd_ofAdd]
            exact Pi.single_eq_of_ne hk 1) v hv,
          rot_apply_of_perp hmp (F.orth k j hk v hv x hx) (F.orth k j hk v hv y hyU)]
    · rw [map_zero, map_zero]
    · intro a b ha hb
      rw [map_add, map_add, ha, hb]
  exact ⟨hmp, hyU, hrot⟩

end CFSG.StandardType.SevOm
