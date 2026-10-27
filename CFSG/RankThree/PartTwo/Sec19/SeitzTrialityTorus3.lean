module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus1
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusFibreA
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusFibreB
public import CFSG.RankThree.PartOne.D4RC.Lines
import CFSG.RankThree.PartOne.D4RC.RxFrame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartOne.D4RC

namespace CFSG.RankThree.PartTwo.Sec19

section Fibre


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem fibre_exists (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : (p : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1)
    (h3 : (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε) {x : C0 σ} (hx : IsClassX σ x) :
    ∃ y : C0 σ, orderOf y = p ∧
      Subgroup.centralizer ({y} : Set (C0 σ)) = Subgroup.centralizer ({x} : Set (C0 σ)) := by
  classical
  have hP : D4Par n X σ := ⟨by omega, hX, hσ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP X 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := n * 3) (by omega) (by rw [hX, pow_mul])
  haveI : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  obtain ⟨F⟩ := rcl_exists_frame (ℓ := 2) (f := n) (K := X) (σ := σ) (ε := ε) (p := p)
    (L := AlgebraicClosure X) rfl (by omega) hX hσ hε hp (by omega) hpd
  obtain S : Sylow p (C0 σ) := (inferInstance : Nonempty (Sylow p (C0 σ))).some
  obtain ⟨E, hES, hEp, hEc⟩ := exists_plane_in_sylow σ n hn hX hσ hε hp hp5 hpd S
  obtain ⟨c, hc⟩ := F.hconj (S : Subgroup (C0 σ)) S.isPGroup'
  obtain ⟨Ln⟩ := rce_exists_lines F S hc hES hEp hEc
  obtain ⟨ζ, hζP, hζc, hζ3, hζ1, hCζ⟩ := rce_center_fibre σ Ln 0 (h3 := h3)
  have hcl : IsClassX σ ζ := special_center_classX σ hP hn Ln 0 hζP hζc hζ3 hζ1
  obtain ⟨g, hg⟩ := classX_conj σ hP hx hcl
  refine ⟨g⁻¹ * Ln.x 0 * g, ?_, ?_⟩
  · have h1 : ((MulAut.conj g⁻¹).toMonoidHom : C0 σ →* C0 σ) (Ln.x 0) = g⁻¹ * Ln.x 0 * g := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← h1, orderOf_injective _ (MulAut.conj g⁻¹).injective]
    exact (Ln.sp 0).hx
  · ext k
    have e1 : g⁻¹ * Ln.x 0 * g = g⁻¹ * Ln.x 0 * g⁻¹⁻¹ := by rw [inv_inv]
    rw [e1, mem_centralizer_conj_iff g⁻¹ (Ln.x 0) k, inv_inv, hCζ, ← hg,
      mem_centralizer_conj_iff g x (g * k * g⁻¹)]
    have e2 : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [e2]

end Fibre

end CFSG.RankThree.PartTwo.Sec19
