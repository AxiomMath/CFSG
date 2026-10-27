module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_a2_linear_of_IsA2
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀) [CharP K 2]
    (hKZ : Nat.card K = Nat.card Z)
    {a : G} (haLB : a ∈ LB M Q B) (hA : IsA2 Q Z a) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) ∧
      T * T = 1 ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧
      (∀ e f, M₀.B (T e) (T f) = M₀.B e f) ∧
      Module.finrank K (LinearMap.range (T.toLinearMap - 1)) = 2 ∧
      (∀ e, M₀.Qf ((T.toLinearMap - 1) e) = 0) ∧
      (∀ e, M₀.B e (T e) = 0) := by
  classical
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have haH : a ∈ H0 M Z := Gl37.LB_le_H0 hc haLB
  have haM : a ∈ M := hc.LB_le_M haLB
  obtain ⟨ha, ha'⟩ := Gl37.conj_mem_Q hc haM
  set T : M₀.E ≃ₗ[K] M₀.E := φ ⟨a, haH⟩ with hT
  have hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x) := fun x hx => hφπ ⟨a, haH⟩ x hx
  have hQf : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => hφQ ⟨a, haH⟩ e
  have hK : 1 < Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hA2 := (isA2_iff M₀ hD.reg hKZ hK T ha ha' hTπ).mp hA
  refine ⟨T, hTπ, ?_, hQf, ?_, hA2.2.2.1, fun e => hA2.2.2.2 _ (LinearMap.mem_range_self _ e), ?_⟩
  ·
    have hmem : a * a ∈ Q := by simpa [pow_two] using hA.2.2.1
    show φ ⟨a, haH⟩ * φ ⟨a, haH⟩ = 1
    rw [← map_mul]
    exact (hφker _).mpr (by simpa using hmem)
  ·
    exact Tim79.QuadModel.B_iso (T := T.toLinearMap) hQf
  ·
    intro e
    have hsub : (T.toLinearMap - 1) e = T e - e := rfl
    have h0 : M₀.Qf ((T.toLinearMap - 1) e) = 0 := hA2.2.2.2 _ (LinearMap.mem_range_self _ e)
    have hTe : T e = e + (T.toLinearMap - 1) e := by
      rw [hsub]
      abel
    have horth : M₀.B e ((T.toLinearMap - 1) e) = 0 := by
      have h1 : M₀.Qf e + M₀.B e ((T.toLinearMap - 1) e) = M₀.Qf e + 0 := by
        calc M₀.Qf e + M₀.B e ((T.toLinearMap - 1) e)
            = M₀.Qf e + M₀.Qf ((T.toLinearMap - 1) e) +
                M₀.B e ((T.toLinearMap - 1) e) := by rw [h0, add_zero]
          _ = M₀.Qf (e + (T.toLinearMap - 1) e) := (M₀.Qf_add e _).symm
          _ = M₀.Qf (T e) := by rw [hTe]
          _ = M₀.Qf e := hQf e
          _ = M₀.Qf e + 0 := (add_zero _).symm
      exact add_left_cancel h1
    calc M₀.B e (T e) = M₀.B e (e + (T.toLinearMap - 1) e) := by rw [hTe]
      _ = M₀.B e e + M₀.B e ((T.toLinearMap - 1) e) := map_add (M₀.B e) e _
      _ = 0 := by rw [M₀.alt e, horth, add_zero]

end CFSG.RankThree.GF2n.Stroth80
