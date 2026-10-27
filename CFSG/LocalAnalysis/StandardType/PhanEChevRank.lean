module

public import CFSG.LocalAnalysis.StandardType.PhanEChevConj
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] (M : ChevModel2 D n H Fld)

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

private theorem q2nPE_ht_zsmul {ι : Type*} [Fintype ι] (c : ℤ) (v : ι → ℤ) :
    ht (c • v) = c * ht v := by
  simp only [ht, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

theorem weylAction_inv_single_eq {v : W} {i j : Fin D.rank}
    (hv : (cs).simple i * v = v * (cs).simple j) (hi : ¬ (cs).IsLeftDescent v i) :
    weylAction D.isFiniteType v⁻¹ (Pi.single i 1) = Pi.single j 1 := by
  set g := weylAction D.isFiniteType v⁻¹ (Pi.single i 1) with hg
  have hsj : (cs).simple j = v⁻¹ * (cs).simple i * v := by
    calc (cs).simple j = (v⁻¹ * v) * (cs).simple j := by rw [inv_mul_cancel, one_mul]
      _ = v⁻¹ * (v * (cs).simple j) := by rw [mul_assoc]
      _ = v⁻¹ * ((cs).simple i * v) := by rw [← hv]
      _ = v⁻¹ * (cs).simple i * v := by rw [mul_assoc]
  have hvg : weylAction D.isFiniteType v g = Pi.single i 1 := by
    rw [hg, weylAction_apply_inv_apply]
  have hrefl : weylAction D.isFiniteType ((cs).simple j) g = -g := by
    calc weylAction D.isFiniteType ((cs).simple j) g
        = weylAction D.isFiniteType (v⁻¹ * (cs).simple i * v) g := by rw [hsj]
      _ = weylAction D.isFiniteType v⁻¹
            (weylAction D.isFiniteType ((cs).simple i) (weylAction D.isFiniteType v g)) := by
          rw [weylAction_mul_apply, weylAction_mul_apply]
      _ = weylAction D.isFiniteType v⁻¹
            (weylAction D.isFiniteType ((cs).simple i) (Pi.single i 1)) := by rw [hvg]
      _ = weylAction D.isFiniteType v⁻¹ (-Pi.single i 1) := by rw [weylAction_simple_single]
      _ = -weylAction D.isFiniteType v⁻¹ (Pi.single i 1) := by rw [map_neg]
      _ = -g := by rw [hg]
  have hfix : ∀ k : Fin D.rank, k ≠ j → g k = 0 := by
    intro k hk
    have h1 : weylAction D.isFiniteType ((cs).simple j) g k = g k :=
      weylAction_simple_apply_of_ne (hA := D.isFiniteType) j g hk
    have h2 : g k = -g k := by
      have h3 := congrFun hrefl k
      rw [h1, Pi.neg_apply] at h3
      exact h3
    omega
  have hg_eq : g = g j • Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [hfix k hk, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]
  have hc : g j = 1 ∨ g j = -1 :=
    CFSG.LieType.Steinberg.OfCartan.eq_one_or_eq_neg_one_of_weylAction_eq_smul
      (hA := D.isFiniteType) (v := v⁻¹) (i := j) (j := i) (c := g j)
      (by rw [← hg]; exact hg_eq)
  have hht : ht g = g j := by
    conv_lhs => rw [hg_eq]
    rw [q2nPE_ht_zsmul, ht_single, mul_one]
  have hpos : 0 < ht g := by
    rw [hg]; exact ht_weylAction_inv_single_pos hi
  have hgj : g j = 1 := by rcases hc with hc | hc <;> omega
  rw [hg_eq, hgj, one_smul]

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀)

@[expose] noncomputable def ChevModel2.rankOneField (θ : Fld →+* Fld) (hθ : ∃ c, θ c ≠ c)
    (hφ : ∀ i c, F.φ (M.x (Pi.single i 1) c) = M.x (Pi.single (F.op i) 1) (θ c)) :
    RankOneField hct F where
  Fld := Fld
  θ := θ
  θ_ne := hθ
  X i := M.x (Pi.single i 1)
  X_add i c d := M.x_add _ ((Φ).single_mem i) c d
  X_inj i := M.x_inj _ ((Φ).single_mem i)
  X_range i := by
    ext g
    simp only [Set.mem_range, SetLike.mem_coe]
    exact (M.x_mem _ ((Φ).single_mem i) g).symm
  φ_X := hφ
  torus_X i h hh := M.torus_conj ((Φ).single_mem i) hh
  nrep_X v i j hv hi := by
    refine ⟨1, one_ne_zero, fun c => ?_⟩
    rw [one_mul, M.nrep_inv_conj hct v ((Φ).single_mem i) c, weylAction_inv_single_eq hv hi]

end CFSG.ClassicalInvolution.Phan.PhanE
