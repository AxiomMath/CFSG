module

public import CFSG.RankThree.GF2n.Stroth80.DictModel
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

namespace QuadModel

@[expose] noncomputable def toQuadraticForm (M₀ : QuadModel QF V K γ) :
    QuadraticForm K M₀.E where
  toFun := M₀.Qf
  toFun_smul := fun a x => by
    simp only [smul_eq_mul]
    rw [M₀.Qf_smul]
    ring
  exists_companion' := ⟨M₀.B, fun x y => M₀.Qf_add x y⟩

theorem toQuadraticForm_apply (M₀ : QuadModel QF V K γ) (e : M₀.E) :
    M₀.toQuadraticForm e = M₀.Qf e := rfl

theorem polar_toQuadraticForm (M₀ : QuadModel QF V K γ) (x y : M₀.E) :
    QuadraticMap.polar M₀.toQuadraticForm x y = M₀.B x y := by
  rw [QuadraticMap.polar]
  show M₀.Qf (x + y) - M₀.Qf x - M₀.Qf y = M₀.B x y
  rw [M₀.Qf_add]
  ring

theorem B_eq_zero_of_singular (M₀ : QuadModel QF V K γ) {U : AddSubgroup M₀.E}
    (hU : ∀ e ∈ U, M₀.Qf e = 0) {u v : M₀.E} (hu : u ∈ U) (hv : v ∈ U) : M₀.B u v = 0 := by
  have h := M₀.Qf_add u v
  rw [hU _ (U.add_mem hu hv), hU u hu, hU v hv] at h
  simpa using h.symm

theorem two_mul_finrank_le_of_totallySingular (M₀ : QuadModel QF V K γ)
    (S : Submodule K M₀.E) (hS : ∀ x ∈ S, M₀.Qf x = 0) :
    2 * Module.finrank K S ≤ Module.finrank K M₀.E := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [B_comm, hy f, neg_zero]
  have hle : S ≤ M₀.B.orthogonal S := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact B_eq_zero_of_singular M₀ (U := S.toAddSubgroup) hS hy hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
  have h2 := Submodule.finrank_le S
  omega

theorem card_le_of_totallySingular [Finite K] (M₀ : QuadModel QF V K γ) {U : AddSubgroup M₀.E}
    (hU : ∀ e ∈ U, M₀.Qf e = 0) {w : ℕ} (hdim : Module.finrank K M₀.E = 2 * w) :
    Nat.card U ≤ Nat.card K ^ w := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  set Qf' := M₀.toQuadraticForm with hQf'
  have hspan : ∀ x ∈ Submodule.span K (U : Set M₀.E), M₀.Qf x = 0 := by
    intro x hx
    exact CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span (Q := Qf') (S := (U : Set M₀.E))
      (fun u hu => hU u hu)
      (fun u hu v hv => by rw [polar_toQuadraticForm]; exact B_eq_zero_of_singular M₀ hU hu hv) hx
  have h1 := two_mul_finrank_le_of_totallySingular M₀ _ hspan
  have h2 : Nat.card U ≤ Nat.card (Submodule.span K (U : Set M₀.E)) :=
    Nat.card_le_card_of_injective (fun u => ⟨u.1, Submodule.subset_span u.2⟩)
      (fun a b h => Subtype.ext (congrArg (fun z : Submodule.span K (U : Set M₀.E) =>
        (z : M₀.E)) h))
  have h3 : Nat.card (Submodule.span K (U : Set M₀.E)) =
      Nat.card K ^ Module.finrank K (Submodule.span K (U : Set M₀.E)) :=
    Module.natCard_eq_pow_finrank
  refine h2.trans (h3 ▸ Nat.pow_le_pow_right Nat.card_pos ?_)
  omega

end QuadModel

end CFSG.RankThree.GF2n.Tim79
