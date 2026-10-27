module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open Module

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

structure IsQuadSpace (B : LinearMap.BilinForm K E) (Qf : E → K) : Prop where
  alt : ∀ e, B e e = 0
  nondeg : ∀ e, (∀ f, B e f = 0) → e = 0
  Qf_add : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f

namespace IsQuadSpace

variable {B : LinearMap.BilinForm K E} {Qf : E → K} (hQ : IsQuadSpace B Qf)
include hQ

theorem B_neg (e f : E) : B f e = - B e f := by
  have h := hQ.alt (e + f)
  simp only [map_add, LinearMap.add_apply, hQ.alt] at h
  linear_combination h

theorem nondegenerate : B.Nondegenerate :=
  ⟨hQ.nondeg, fun y hy => hQ.nondeg y fun x => by rw [hQ.B_neg]; simp [hy x]⟩

theorem B_iso (g : E ≃ₗ[K] E) (hg : ∀ e, Qf (g e) = Qf e) (u v : E) :
    B (g u) (g v) = B u v := by
  have h1 := hQ.Qf_add u v
  have h2 := hQ.Qf_add (g u) (g v)
  rw [← map_add, hg, hg u, hg v] at h2
  linear_combination h1 - h2

end IsQuadSpace

structure OrthFlag (B : LinearMap.BilinForm K E) (Qf : E → K) (Vm N Wm : Submodule K E) : Prop where
  VN : Vm ≤ N
  NW : N ≤ Wm
  Wperp : ∀ w, w ∈ Wm ↔ ∀ v ∈ Vm, B v w = 0
  Nsing : ∀ n ∈ N, Qf n = 0
  Ndim : finrank K E = 2 * finrank K N
  Wdim : finrank K Wm = finrank K N + 2

namespace OrthFlag

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {Vm N Wm : Submodule K E}
  (hQ : IsQuadSpace B Qf) (hF : OrthFlag B Qf Vm N Wm)
include hQ hF

theorem B_N (n n' : E) (hn : n ∈ N) (hn' : n' ∈ N) : B n n' = 0 := by
  have h := hQ.Qf_add n n'
  rw [hF.Nsing _ (N.add_mem hn hn'), hF.Nsing n hn, hF.Nsing n' hn'] at h
  linear_combination -h

theorem perp_N : B.orthogonal N = N := by
  have hle : N ≤ B.orthogonal N := fun n hn m hm => hF.B_N hQ m n hm hn
  have hdim : finrank K (B.orthogonal N) = finrank K N := by
    have h2 := hF.Ndim
    rw [LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate]
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

theorem perp_W : B.orthogonal Wm = Vm := by
  have : Wm = B.orthogonal Vm := by
    ext w
    rw [hF.Wperp, LinearMap.BilinForm.mem_orthogonal_iff]
  rw [this, LinearMap.BilinForm.orthogonal_orthogonal hQ.nondegenerate
    (LinearMap.BilinForm.IsAlt.isRefl hQ.alt)]

end OrthFlag

section Basis

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {Vm N Wm : Submodule K E}
  (hF : OrthFlag B Qf Vm N Wm)
include hF

theorem OrthFlag.exists_basis_mod :
    ∃ u₁ ∈ Wm, ∃ u₂ ∈ Wm, ∀ w ∈ Wm, ∃ a b : K, w - a • u₁ - b • u₂ ∈ N := by
  classical
  let N' : Submodule K Wm := N.comap Wm.subtype
  have hN'dim : finrank K N' = finrank K N :=
    (Submodule.comapSubtypeEquivOfLe hF.NW).finrank_eq
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl N'
  have hPdim : finrank K P = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hP
    have h2 := hF.Wdim
    omega
  let bs := Module.finBasisOfFinrankEq K P hPdim
  refine ⟨((bs 0 : P) : Wm), ((bs 0 : P) : Wm).2, ((bs 1 : P) : Wm), ((bs 1 : P) : Wm).2, ?_⟩
  intro w hw
  have hw' : (⟨w, hw⟩ : Wm) ∈ N' ⊔ P := by
    rw [hP.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨n', hn', p, hp, hsum⟩ := Submodule.mem_sup.mp hw'
  refine ⟨bs.repr ⟨p, hp⟩ 0, bs.repr ⟨p, hp⟩ 1, ?_⟩
  have hrep : (⟨p, hp⟩ : P) = bs.repr ⟨p, hp⟩ 0 • bs 0 + bs.repr ⟨p, hp⟩ 1 • bs 1 := by
    have := bs.sum_repr ⟨p, hp⟩
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have h1 : ((n' : Wm) : E) + ((p : Wm) : E) = w := congrArg (fun x : Wm => (x : E)) hsum
  have h2 : ((p : Wm) : E) = bs.repr ⟨p, hp⟩ 0 • ((bs 0 : P) : Wm) +
      bs.repr ⟨p, hp⟩ 1 • ((bs 1 : P) : Wm) := by
    have := congrArg (fun x : P => ((x : Wm) : E)) hrep
    simpa using this
  have h3 : ((n' : Wm) : E) ∈ N := hn'
  have : w - bs.repr ⟨p, hp⟩ 0 • ((bs 0 : P) : Wm) - bs.repr ⟨p, hp⟩ 1 • ((bs 1 : P) : Wm) =
      ((n' : Wm) : E) := by
    rw [← h1, h2]
    abel
  rw [this]
  exact h3

end Basis

section Action

variable {B : LinearMap.BilinForm K E} {Qf : E → K} {Vm N Wm : Submodule K E}
  {Γ : Type*} [Group Γ] (hQ : IsQuadSpace B Qf) (hF : OrthFlag B Qf Vm N Wm)
  (α : Γ →* (E ≃ₗ[K] E)) (hiso : ∀ g e, Qf (α g e) = Qf e)
  (hW : ∀ g, ∀ w ∈ Wm, α g w ∈ Wm) (hNV : ∀ g, ∀ n ∈ N, α g n - n ∈ Vm)

include hQ hF hiso hW hNV

theorem D_mem_N (g : Γ) {w : E} (hw : w ∈ Wm) : α g w - w ∈ N := by
  rw [← hF.perp_N hQ, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have h1 : B n (α g w) = B (α g⁻¹ n) w := by
    have := hQ.B_iso (α g) (hiso g) (α g⁻¹ n) w
    have e : α g (α g⁻¹ n) = n := by
      have := congrArg (fun f : E ≃ₗ[K] E => f n)
        (show α g * α g⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
      simpa using this
    rw [e] at this
    exact this
  have h2 : B (α g⁻¹ n - n) w = 0 := (hF.Wperp w).mp hw _ (hNV g⁻¹ n hn)
  rw [map_sub, h1]
  rw [map_sub, LinearMap.sub_apply] at h2
  linear_combination h2

theorem B_act (g : Γ) (u x : E) : B u (α g x) = B (α g⁻¹ u) x := by
  have := hQ.B_iso (α g) (hiso g) (α g⁻¹ u) x
  have e : α g (α g⁻¹ u) = u := by
    have := congrArg (fun f : E ≃ₗ[K] E => f u)
      (show α g * α g⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
    simpa using this
  rw [e] at this
  exact this

theorem b_symm (g : Γ) {u v : E} (hu : u ∈ Wm) (hv : v ∈ Wm) :
    B u (α g v - v) = B v (α g u - u) := by
  have h := hQ.B_iso (α g) (hiso g) u v
  have h0 := hF.B_N hQ _ _ (D_mem_N hQ hF α hiso hW hNV g hu) (D_mem_N hQ hF α hiso hW hNV g hv)
  generalize hDu : α g u - u = Du at h0 ⊢
  generalize hDv : α g v - v = Dv at h0 ⊢
  have eu : α g u = u + Du := by rw [← hDu]; abel
  have ev : α g v = v + Dv := by rw [← hDv]; abel
  rw [eu, ev] at h
  simp only [map_add, LinearMap.add_apply] at h
  have hn : B Du v = - B v Du := hQ.B_neg _ _
  linear_combination h - h0 - hn

theorem b_alt (g : Γ) {u : E} (hu : u ∈ Wm) : B u (α g u - u) = 0 := by
  have h := hQ.Qf_add u (α g u - u)
  rw [add_sub_cancel, hiso g u, hF.Nsing _ (D_mem_N hQ hF α hiso hW hNV g hu)] at h
  linear_combination -h

theorem b_N_left (g : Γ) {n v : E} (hn : n ∈ N) (hv : v ∈ Wm) : B n (α g v - v) = 0 :=
  hF.B_N hQ n _ hn (D_mem_N hQ hF α hiso hW hNV g hv)

theorem b_N_right (g : Γ) {u n : E} (hu : u ∈ Wm) (hn : n ∈ N) : B u (α g n - n) = 0 := by
  have h := (hF.Wperp u).mp hu _ (hNV g n hn)
  rw [hQ.B_neg, h, neg_zero]

theorem b_mul (g g' : Γ) {u v : E} (hu : u ∈ Wm) (hv : v ∈ Wm) :
    B u (α (g * g') v - v) = B u (α g v - v) + B u (α g' v - v) := by
  have e : α (g * g') v - v = α g (α g' v - v) + (α g v - v) := by
    rw [map_mul]
    simp only [LinearEquiv.mul_apply, map_sub]
    abel
  rw [e, map_add, B_act hQ hF α hiso hW hNV g u (α g' v - v)]
  have h1 : B (α g⁻¹ u - u) (α g' v - v) = 0 :=
    hF.B_N hQ _ _ (D_mem_N hQ hF α hiso hW hNV g⁻¹ hu) (D_mem_N hQ hF α hiso hW hNV g' hv)
  generalize hDg : α g⁻¹ u - u = Dg at h1
  have e2 : α g⁻¹ u = u + Dg := by rw [← hDg]; abel
  rw [e2, map_add, LinearMap.add_apply]
  linear_combination h1

theorem exists_orth_subgroup [Finite K] :
    ∃ C : Subgroup Γ, (∀ g, g ∈ C ↔ ∀ w ∈ Wm, α g w - w ∈ Vm) ∧ C.index ≤ Nat.card K := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hdec⟩ := hF.exists_basis_mod
  let c : Γ → K := fun g => B u₁ (α g u₂ - u₂)
  have hc : ∀ g g', c (g * g') = c g + c g' := fun g g' =>
    b_mul hQ hF α hiso hW hNV g g' hu₁ hu₂
  have hc1 : c 1 = 0 := by simp [c]
  let f : Γ →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd (c g)
      map_one' := by simp [hc1]
      map_mul' := fun g g' => by simp [hc] }
  refine ⟨f.ker, ?_, ?_⟩
  · intro g
    rw [MonoidHom.mem_ker]
    have hf : f g = 1 ↔ c g = 0 := by
      show Multiplicative.ofAdd (c g) = 1 ↔ _
      exact ofAdd_eq_one
    rw [hf]
    constructor
    · intro hcg w hw
      rw [← hF.perp_W hQ, LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      obtain ⟨a, b, hxN⟩ := hdec x hx
      obtain ⟨a', b', hwN⟩ := hdec w hw
      let Φ : E →ₗ[K] E →ₗ[K] K := B.compl₂ ((α g).toLinearMap - LinearMap.id)
      have hΦ : ∀ x y, Φ x y = B x (α g y - y) := fun x y => by simp [Φ]
      have hx' : x = a • u₁ + b • u₂ + (x - a • u₁ - b • u₂) := by abel
      have hw' : w = a' • u₁ + b' • u₂ + (w - a' • u₁ - b' • u₂) := by abel
      have h11 : Φ u₁ u₁ = 0 := by rw [hΦ]; exact b_alt hQ hF α hiso hW hNV g hu₁
      have h22 : Φ u₂ u₂ = 0 := by rw [hΦ]; exact b_alt hQ hF α hiso hW hNV g hu₂
      have h12 : Φ u₁ u₂ = 0 := by rw [hΦ]; exact hcg
      have h21 : Φ u₂ u₁ = 0 := by
        rw [hΦ, ← b_symm hQ hF α hiso hW hNV g hu₁ hu₂]
        exact hcg
      have hNl : ∀ y ∈ Wm, Φ (x - a • u₁ - b • u₂) y = 0 := fun y hy => by
        rw [hΦ]; exact b_N_left hQ hF α hiso hW hNV g hxN hy
      have hNr : ∀ y ∈ Wm, ∀ n ∈ N, Φ y n = 0 := fun y hy n hn => by
        rw [hΦ]; exact b_N_right hQ hF α hiso hW hNV g hy hn
      have key : Φ x w = 0 := by
        rw [hx', hw']
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h11, h22, h12,
          h21, smul_zero, add_zero, zero_add]
        rw [hNl u₁ hu₁, hNl u₂ hu₂, hNl _ (hF.NW hwN), hNr u₁ hu₁ _ hwN, hNr u₂ hu₂ _ hwN]
        simp
      rw [← hΦ]
      exact key
    · intro h
      have hv := (hF.Wperp u₁).mp hu₁ _ (h u₂ hu₂)
      show B u₁ (α g u₂ - u₂) = 0
      rw [hQ.B_neg, hv, neg_zero]
  · rw [Subgroup.index_ker f]
    haveI : Finite (Multiplicative K) := inferInstanceAs (Finite K)
    calc Nat.card f.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group _
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end Action

end CFSG.RankThree.GF2n.Stroth80.HS9
