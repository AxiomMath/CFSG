module

public import CFSG.Quasithin.Vol2.Ch6SL2Fix
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_autOn_iff {L V : Subgroup G} {φ : MulAut ↥V} :
    φ ∈ autOn L V ↔ ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ L ∧ conjAct V g = φ :=
  CFSG.Quasithin.AutOn.mem_autOn_iff

theorem conjAct_apply_coe {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

section Transitive

variable {K : Type} [Field K]

@[expose] noncomputable def slToStated (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ↥(Assembly.LowTwoRank.StatedSL 2 K) :=
  ⟨Matrix.SpecialLinearGroup.toGL A, Subgroup.subset_closure (by simp)⟩

theorem slToStated_coe (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((slToStated A : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) := rfl

end Transitive

section Natural

variable {L V : Subgroup G} {n : ℕ}

theorem IsNatModCh5.exists_equiv (h : IsNatModCh5 L V n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(Assembly.LowTwoRank.StatedSL 2 K) →* ↥(autOn L V))
      (E : ↥V ≃* Multiplicative (Fin 2 → K)),
      Nat.card K = 2 ^ n ∧ Function.Surjective π ∧
      ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) (v : ↥V),
        Multiplicative.toAdd (E (((π γ : ↥(autOn L V)) : MulAut ↥V) v)) =
          ((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (E v)) := by
  obtain ⟨-, hc, K, hK, hKf, hcard, π, hπ⟩ := h
  obtain ⟨E, hE⟩ :=
    G64.RealizesVia.exists_secEquiv (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)) rfl hπ
  exact ⟨hc, K, hK, hKf, π, E.trans Subgroup.topEquiv, hcard, hπ.1,
    fun γ v => congrArg Multiplicative.toAdd (hE γ v)⟩

theorem IsNatModCh5.exists_conj_eq (h : IsNatModCh5 L V n) {v w : G} (hv : v ∈ V)
    (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ g ∈ L, g * v * g⁻¹ = w := by
  obtain ⟨_, K, _, _, π, E, -, -, hE⟩ := h.exists_equiv
  have hx : Multiplicative.toAdd (E ⟨v, hv⟩) ≠ 0 := by
    intro h0
    apply hv1
    have : E ⟨v, hv⟩ = 1 := h0
    have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff E).mp this)
    simpa using this
  have hy : Multiplicative.toAdd (E ⟨w, hw⟩) ≠ 0 := by
    intro h0
    apply hw1
    have : E ⟨w, hw⟩ = 1 := h0
    have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff E).mp this)
    simpa using this
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq _ _ hx hy
  have hγ := hE (slToStated A) ⟨v, hv⟩
  rw [slToStated_coe, hA] at hγ
  have hEq : (((π (slToStated A) : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv⟩) = ⟨w, hw⟩ :=
    E.injective (Multiplicative.toAdd.injective hγ)
  obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp (π (slToStated A)).2
  refine ⟨g, hgL, ?_⟩
  have := congrArg Subtype.val hEq
  rw [← hg, conjAct_apply_coe] at this
  exact this

theorem IsNatModCh5.irreducible (h : IsNatModCh5 L V n) (W : Subgroup G) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
    refine le_antisymm hWV fun v hv => ?_
    by_cases hv1 : v = 1
    · rw [hv1]; exact W.one_mem
    · obtain ⟨g, hgL, hg⟩ :=
        h.exists_conj_eq (hWV w.2) hv (fun h1 => hw1 (Subtype.ext h1)) hv1
      rw [← hg]
      exact (Subgroup.mem_normalizer_iff.mp (hLW hgL) w).mp w.2

end Natural

end CFSG.Quasithin.H13
