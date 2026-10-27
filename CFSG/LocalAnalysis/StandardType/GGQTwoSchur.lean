module

public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoConnectivity
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xS_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2xS_zmod3_cases : ∀ ν : ZMod 3, ν = 0 ∨ ν = 1 ∨ ν = -1 := by decide

private def ggQ2xS_lam (D : GGQ2Lin 3) (z : D.V ≃ₗ[ZMod 3] D.V) (k : D.ι) : ZMod 3 :=
  (2 : ZMod 3)⁻¹ * D.root k (z (D.coroot k))

private def ggQ2xS_mu (D : GGQ2Lin 3) (z : D.V ≃ₗ[ZMod 3] D.V)
    (γ : ↥D.rootPairs) : ZMod 3 :=
  (2 : ZMod 3)⁻¹ * γ.1.1 (z γ.1.2)

private def ggQ2xS_simplePair (D : GGQ2Lin 3) (k : D.ι) : ↥D.rootPairs :=
  ⟨(D.root k, D.coroot k), k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2xS_pair_self (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    γ.1.1 γ.1.2 = 2 := by
  obtain ⟨k, w, _, hq2, hq1⟩ := γ.2
  rw [hq2, hq1]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply, D.root_coroot_self]

private lemma ggQ2xS_mu_simplePair (D : GGQ2Lin 3) (z : D.V ≃ₗ[ZMod 3] D.V)
    (k : D.ι) : ggQ2xS_mu D z (ggQ2xS_simplePair D k) = ggQ2xS_lam D z k := rfl

private lemma ggQ2xS_eigen (D : GGQ2Lin 3) (z : D.V ≃ₗ[ZMod 3] D.V)
    (hz : ∀ w ∈ D.weyl, z * w = w * z) (k : D.ι) (v : D.V) :
    D.root k v • z (D.coroot k) = D.root k (z v) • D.coroot k := by
  have hmem : D.simpleRefl k ∈ D.weyl := Subgroup.subset_closure ⟨k, trivial, rfl⟩
  have hcomm : z * D.simpleRefl k = D.simpleRefl k * z := hz _ hmem
  have h1 : z (D.simpleRefl k v) = D.simpleRefl k (z v) := by
    rw [← LinearEquiv.mul_apply, hcomm, LinearEquiv.mul_apply]
  rw [show D.simpleRefl k v = v - D.root k v • D.coroot k from
        Module.reflection_apply v (D.root_coroot_self k),
      show D.simpleRefl k (z v) = z v - D.root k (z v) • D.coroot k from
        Module.reflection_apply (z v) (D.root_coroot_self k)] at h1
  rw [map_sub, map_smul] at h1
  exact (sub_right_inj).mp h1

private lemma ggQ2xS_lam_coroot (D : GGQ2Lin 3) (z : D.V ≃ₗ[ZMod 3] D.V)
    (hz : ∀ w ∈ D.weyl, z * w = w * z) (k : D.ι) :
    z (D.coroot k) = ggQ2xS_lam D z k • D.coroot k := by
  have h2 : (2 : ZMod 3) • z (D.coroot k) =
      D.root k (z (D.coroot k)) • D.coroot k := by
    simpa [D.root_coroot_self k] using ggQ2xS_eigen D z hz k (D.coroot k)
  have h3 := congrArg (fun w : D.V => (2 : ZMod 3)⁻¹ • w) h2
  simp only [smul_smul, inv_mul_cancel₀ ggQ2xS_two_ne_zero, one_smul] at h3
  simpa [ggQ2xS_lam] using h3

private lemma ggQ2xS_lam_root (D : GGQ2Lin 3) (hbas : D.Basis)
    (z : D.V ≃ₗ[ZMod 3] D.V) (hz : ∀ w ∈ D.weyl, z * w = w * z) (k : D.ι) (v : D.V) :
    D.root k (z v) = ggQ2xS_lam D z k * D.root k v := by
  have heig := ggQ2xS_eigen D z hz k v
  rw [ggQ2xS_lam_coroot D z hz k, smul_smul] at heig
  have hk : D.coroot k ≠ 0 := LinearIndependent.ne_zero k hbas.1
  have hzero : (D.root k v * ggQ2xS_lam D z k - D.root k (z v)) • D.coroot k = 0 := by
    rw [sub_smul, heig, sub_self]
  have hsub := (smul_eq_zero.mp hzero).resolve_right hk
  rw [mul_comm] at hsub
  exact (sub_eq_zero.mp hsub).symm

private lemma ggQ2xS_mu_spec (D : GGQ2Lin 3) (hbas : D.Basis)
    (z : D.V ≃ₗ[ZMod 3] D.V) (hz : ∀ w ∈ D.weyl, z * w = w * z)
    (γ : ↥D.rootPairs) :
    z γ.1.2 = ggQ2xS_mu D z γ • γ.1.2 ∧
      ∀ v : D.V, γ.1.1 (z v) = ggQ2xS_mu D z γ * γ.1.1 v := by
  obtain ⟨k, w, hw, h2, h1⟩ := γ.2
  have hzw : z * w = w * z := hz w hw
  have hzc : z γ.1.2 = ggQ2xS_lam D z k • γ.1.2 := by
    rw [h2]
    have hmul : z (w (D.coroot k)) = w (z (D.coroot k)) := by
      rw [← LinearEquiv.mul_apply, hzw, LinearEquiv.mul_apply]
    rw [hmul, ggQ2xS_lam_coroot D z hz k, map_smul]
  have hmueq : ggQ2xS_mu D z γ = ggQ2xS_lam D z k := by
    show (2 : ZMod 3)⁻¹ * γ.1.1 (z γ.1.2) = ggQ2xS_lam D z k
    rw [hzc, map_smul, smul_eq_mul, ggQ2xS_pair_self D γ,
      mul_comm (ggQ2xS_lam D z k) 2, ← mul_assoc,
      inv_mul_cancel₀ ggQ2xS_two_ne_zero, one_mul]
  refine ⟨?_, ?_⟩
  · rw [hmueq]; exact hzc
  · intro v
    rw [h1]
    change D.root k (w.symm (z v)) = ggQ2xS_mu D z γ * D.root k (w.symm v)
    have hzw' : z * w.symm = w.symm * z := (show Commute z w from hzw).inv_right
    have happ : z (w.symm v) = w.symm (z v) := by
      rw [← LinearEquiv.mul_apply, hzw', LinearEquiv.mul_apply]
    rw [← happ, ggQ2xS_lam_root D hbas z hz k (w.symm v), hmueq]

private lemma ggQ2xS_mu_adj (D : GGQ2Lin 3) (hbas : D.Basis)
    (z : D.V ≃ₗ[ZMod 3] D.V) (hz : ∀ w ∈ D.weyl, z * w = w * z)
    (γ δ : ↥D.rootPairs) (h : γ.1.1 δ.1.2 ≠ 0) :
    ggQ2xS_mu D z γ = ggQ2xS_mu D z δ := by
  have hγ := (ggQ2xS_mu_spec D hbas z hz γ).2
  have hδ := (ggQ2xS_mu_spec D hbas z hz δ).1
  have h1 : γ.1.1 (z δ.1.2) = ggQ2xS_mu D z γ * γ.1.1 δ.1.2 := hγ δ.1.2
  have h2 : γ.1.1 (z δ.1.2) = ggQ2xS_mu D z δ * γ.1.1 δ.1.2 := by
    rw [hδ, map_smul, smul_eq_mul]
  have h3 : (ggQ2xS_mu D z γ - ggQ2xS_mu D z δ) * γ.1.1 δ.1.2 = 0 := by
    rw [sub_mul, ← h1, h2, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h)

private lemma ggQ2xS_mu_eq_of_chain (D : GGQ2Lin 3) (hbas : D.Basis)
    (z : D.V ≃ₗ[ZMod 3] D.V) (hz : ∀ w ∈ D.weyl, z * w = w * z) (cv : D.V)
    {γ δ : ↥D.rootPairs}
    (h : Relation.ReflTransGen
      (fun γ' δ' : ↥D.rootPairs => γ'.1.1 cv ≠ 0 ∧ δ'.1.1 cv ≠ 0 ∧
        γ'.1.1 δ'.1.2 ≠ 0) γ δ) :
    γ.1.1 cv ≠ 0 → δ.1.1 cv ≠ 0 → ggQ2xS_mu D z γ = ggQ2xS_mu D z δ := by
  induction h with
  | refl => intro _ _; rfl
  | tail hab hbc ih =>
      intro hγ hδ
      exact (ih hγ hbc.1).trans (ggQ2xS_mu_adj D hbas z hz _ _ hbc.2.2)

private lemma ggQ2xS_exists_ne_zero_pair (D : GGQ2Lin 3) (i j : D.ι) :
    ∃ cv : D.V, D.root i cv ≠ 0 ∧ D.root j cv ≠ 0 := by
  have hφ : D.root i ≠ 0 := by
    intro h
    have h' := DFunLike.congr_fun h (D.coroot i)
    rw [D.root_coroot_self i] at h'
    exact ggQ2xS_two_ne_zero (by simpa using h')
  have hψ : D.root j ≠ 0 := by
    intro h
    have h' := DFunLike.congr_fun h (D.coroot j)
    rw [D.root_coroot_self j] at h'
    exact ggQ2xS_two_ne_zero (by simpa using h')
  obtain ⟨u, hu⟩ : ∃ u, D.root i u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext (fun u => by
      by_contra hu
      exact h ⟨u, hu⟩))
  obtain ⟨w, hw⟩ : ∃ w, D.root j w ≠ 0 := by
    by_contra h
    exact hψ (LinearMap.ext (fun w => by
      by_contra hw
      exact h ⟨w, hw⟩))
  by_cases huw : D.root j u ≠ 0
  · exact ⟨u, hu, huw⟩
  · simp only [ne_eq, not_not] at huw
    by_cases h1 : D.root i (u + w) ≠ 0
    · refine ⟨u + w, h1, ?_⟩
      rw [map_add, huw, zero_add]
      exact hw
    · simp only [ne_eq, not_not] at h1
      have hφw : D.root i w ≠ 0 := by
        intro h0
        have h1' := h1
        rw [map_add, h0, add_zero] at h1'
        exact hu h1'
      exact ⟨w, hφw, hw⟩

theorem ggQ2_weyl_centralizer_scalar {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p)
    (hbas : D.Basis) (h4 : 4 ≤ Fintype.card D.ι) (z : D.V ≃ₗ[ZMod p] D.V)
    (hz : ∀ w ∈ D.weyl, z * w = w * z) : ∃ μ : ZMod p, ∀ v, z v = μ • v := by
  subst hp
  haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
  have hlameq : ∀ k l : D.ι, ggQ2xS_lam D z k = ggQ2xS_lam D z l := by
    intro k l
    obtain ⟨cv, hcvk, hcvl⟩ := ggQ2xS_exists_ne_zero_pair D k l
    have hconn := ggQ2_connectivity (p := 3) rfl D hbas h4 cv
      (ggQ2xS_simplePair D k) (ggQ2xS_simplePair D l) hcvk hcvl
    have h := ggQ2xS_mu_eq_of_chain D hbas z hz cv hconn hcvk hcvl
    rw [ggQ2xS_mu_simplePair] at h
    exact h
  let μ : ZMod 3 := ggQ2xS_lam D z (Classical.choice ‹Nonempty D.ι›)
  refine ⟨μ, fun v => ?_⟩
  let b : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hb : ⇑b = D.coroot := coe_basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hmap : (z : D.V →ₗ[ZMod 3] D.V) = μ • (LinearMap.id : D.V →ₗ[ZMod 3] D.V) := by
    apply b.ext
    intro k
    rw [LinearMap.smul_apply, LinearMap.id_apply, congrFun hb k]
    have hμk : μ = ggQ2xS_lam D z k := hlameq _ k
    rw [hμk]
    exact ggQ2xS_lam_coroot D z hz k
  have := congrArg (fun (f : D.V →ₗ[ZMod 3] D.V) => f v) hmap
  simpa [LinearMap.smul_apply] using this

theorem ggQ2_lemmaN {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (a g : D.V ≃ₗ[ZMod p] D.V)
    (hconj : ∀ k, a * D.simpleRefl k * a⁻¹ = g * D.simpleRefl k * g⁻¹) :
    (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  subst hp
  obtain ⟨c, hcdef⟩ : ∃ c : D.V ≃ₗ[ZMod 3] D.V, c = g⁻¹ * a := ⟨g⁻¹ * a, rfl⟩
  have hc : ∀ k, c * D.simpleRefl k = D.simpleRefl k * c := by
    intro k
    have h := hconj k
    have e1 : c * D.simpleRefl k = g⁻¹ * (a * D.simpleRefl k * a⁻¹) * a := by
      rw [hcdef]; group
    have e2 : g⁻¹ * (g * D.simpleRefl k * g⁻¹) * a = D.simpleRefl k * c := by
      rw [hcdef]; group
    rw [e1, h, e2]
  have hz : ∀ w ∈ D.weyl, c * w = w * c := by
    intro w hw
    change w ∈ Subgroup.closure (D.simpleRefl '' Set.univ) at hw
    refine Subgroup.closure_induction (p := fun w _ => c * w = w * c) ?_ ?_ ?_ ?_ hw
    · rintro x ⟨k, -, rfl⟩
      exact hc k
    · simp
    · intro x y hx hy ihx ihy
      calc c * (x * y) = c * x * y := by rw [mul_assoc]
        _ = x * c * y := by rw [ihx]
        _ = x * (c * y) := by rw [mul_assoc]
        _ = x * (y * c) := by rw [ihy]
        _ = (x * y) * c := by rw [mul_assoc]
    · intro x hx ihx
      exact (show Commute c x from ihx).inv_right.eq
  obtain ⟨μ, hμ⟩ := ggQ2_weyl_centralizer_scalar (p := 3) rfl D hbas h4 c hz
  have hμ0 : μ ≠ 0 := by
    intro h0
    haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
    let k0 := Classical.choice ‹Nonempty D.ι›
    have hk : D.coroot k0 ≠ 0 := LinearIndependent.ne_zero k0 hbas.1
    have hc0 : c (D.coroot k0) = 0 := by rw [hμ (D.coroot k0), h0, zero_smul]
    have hcontra : D.coroot k0 = 0 := by
      have := congrArg (fun x => c.symm x) hc0
      simpa using this
    exact hk hcontra
  have hcases : μ = 1 ∨ μ = -1 := by
    rcases ggQ2xS_zmod3_cases μ with h0 | h1 | h1
    · exact absurd h0 hμ0
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hcases with h1 | h1
  · left
    intro v
    have hcv : c v = v := by
      have := hμ v
      rw [h1] at this
      simpa using this
    have := congrArg (fun x => g x) hcv
    simpa [hcdef, LinearEquiv.mul_apply] using this
  · right
    intro v
    have hcv : c v = -v := by
      have := hμ v
      rw [h1] at this
      rw [show (-1 : ZMod 3) • v = -v from neg_one_smul (ZMod 3) v] at this
      exact this
    have := congrArg (fun x => g x) hcv
    simpa [hcdef, LinearEquiv.mul_apply] using this

end CFSG.StandardType

end
