module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2g_transport {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e₀ : D.ι) {n : ℕ}
    (σ : Fin n ≃ {i // i ≠ e₀})
    (hσ : ∀ i j, D.cartan (σ i) (σ j) = CartanMatrix.D n i j)
    {π : {k // k ≠ e₀} ≃ {k // k ≠ e₀}} {μ : {k // k ≠ e₀} → ZMod p}
    (h : D.ScaledAut e₀ π μ) :
    ∃ (π' : Equiv.Perm (Fin n)) (μ' : Fin n → ZMod p), (∀ i, μ' i ≠ 0) ∧
      (∀ i j, μ' i * (CartanMatrix.D n i j : ZMod p) =
        μ' j * (CartanMatrix.D n (π' i) (π' j) : ZMod p)) ∧
      (∀ i, π (σ i) = σ (π' i)) ∧ (∀ i, μ (σ i) = μ' i) := by
  refine ⟨(σ.trans π).trans σ.symm, fun i => μ (σ i), fun i => h.1 _, fun i j => ?_,
    fun i => by simp, fun i => rfl⟩
  have hh := h.2 (σ i) (σ j)
  rw [hσ i j] at hh
  have e1 : π (σ i) = σ (((σ.trans π).trans σ.symm) i) := by simp
  have e2 : π (σ j) = σ (((σ.trans π).trans σ.symm) j) := by simp
  rw [e1, e2, hσ] at hh
  exact hh

theorem ggQ2g_basis {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e₀ : D.ι) (x : D.V)
    (hdet : ((D.cartan.det : ℤ) : ZMod p) ≠ 0)
    (hV : Submodule.span (ZMod p)
      (insert x (Set.range fun i : {k // k ≠ e₀} => D.coroot i)) = ⊤) : D.Basis := by
  classical
  have hLI : LinearIndependent (ZMod p) D.coroot := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hC : ∀ j, ∑ i, (D.cartan j i : ZMod p) * g i = 0 := by
      intro j
      have h := congrArg (D.root j) hg
      simp only [map_sum, map_smul, smul_eq_mul, D.pairing, map_zero] at h
      calc ∑ i, (D.cartan j i : ZMod p) * g i = ∑ i, g i * (D.cartan j i : ZMod p) :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = 0 := h
    have hmul : ((Int.castRingHom (ZMod p)).mapMatrix D.cartan).mulVec g = 0 := by
      funext j
      simpa [Matrix.mulVec, dotProduct] using hC j
    have hdet' : ((Int.castRingHom (ZMod p)).mapMatrix D.cartan).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact hdet
    have hg0 := Matrix.eq_zero_of_mulVec_eq_zero hdet' hmul
    intro i
    exact congrFun hg0 i
  have hrange : Set.range (fun o : Option {k // k ≠ e₀} =>
      Option.elim o x (fun i => D.coroot i))
      = insert x (Set.range fun i : {k // k ≠ e₀} => D.coroot i) := by
    ext v
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
    · intro hv
      rw [Set.mem_insert_iff] at hv
      rcases hv with rfl | ⟨i, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
  have hfg : (⊤ : Submodule (ZMod p) D.V).FG := by
    rw [← hV, ← hrange]
    exact Submodule.fg_span (Set.finite_range _)
  haveI : Module.Finite (ZMod p) D.V := Module.finite_def.mpr hfg
  refine ⟨hLI, le_antisymm hLI.fintype_card_le_finrank ?_⟩
  have htop : Module.finrank (ZMod p) D.V ≤ Fintype.card (Option {k // k ≠ e₀}) :=
    finrank_le_of_span_eq_top (R := ZMod p)
      (v := fun o : Option {k // k ≠ e₀} => Option.elim o x (fun i => D.coroot i))
      (by rw [hrange]; exact hV)
  rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_subtype_eq] at htop
  have hpos : 0 < Fintype.card D.ι := Fintype.card_pos_iff.mpr ⟨e₀⟩
  omega

theorem ggQ2g_alpha_fixed {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (e : D.ι)
    (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ e}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) :
    ∀ j : {k // k ≠ e}, D.root j xV = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    haveI : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro j
  have hxV : xV ∈ Submodule.span (ZMod p) {xV} := Submodule.mem_span_singleton_self xV
  have hmem : D.simpleRefl j ∈ D.parab {k | k ≠ e} :=
    Subgroup.subset_closure ⟨j.1, j.2, rfl⟩
  have hfixj : D.simpleRefl j xV = xV := (hfix xV).mpr hxV _ hmem
  have happ : D.simpleRefl j xV = xV - D.root j xV • D.coroot j :=
    Module.reflection_apply (h := D.root_coroot_self j) xV
  have hsmul : D.root j xV • D.coroot j = 0 := by
    rw [happ] at hfixj
    exact sub_eq_self.mp hfixj
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exfalso
    exact h2ne (by
      calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
        _ = D.root j 0 := by rw [h]
        _ = 0 := map_zero (D.root j))

end CFSG.StandardType

end
