module

public import CFSG.Quasithin.Background.E1SolvProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

theorem fourFive_abelian_subset {Q : Type} [Group Q] [Finite Q] {j : ℕ} (hj : 1 ≤ j)
    {T R : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl ⊤ Ω) [R.Normal]
    (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ R → M = ⊥ ∨ M = R)
    (hab : IsMulCommutative R) :
    (R : Set Q) ⊆ (E1.eGen j ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) := by
  have hRsolv : Group.IsSolvable R :=
    Group.isSolvable_of_comm fun a b => hab.is_comm.comm a b
  haveI : CFSG.IsMinimalNormal R := ⟨fun K _ hKR => hmin K inferInstance hKR⟩
  obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian R
  have hRp : IsPGroup r R := CFSG.IsElementaryAbelian.isPGroup r R
  have hRn : R.Normal := inferInstance
  have hTN : T ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set Q) :=
    E1.le_normalizer_weakClosure hΩ
  have h1 : (R : Set Q) ⊆ (E1.eGen 1 ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) := by
    intro ρ hρ
    by_cases hr2 : r = 2
    · have hR2 : IsPGroup 2 R := hr2 ▸ hRp
      have hRT : R ≤ T := hT.le_of_normal le_top inferInstance hR2
      exact ⟨1, (E1.eGen 1 ⊤ T Ω).one_mem, ρ, hTN (hRT hρ), one_mul ρ⟩
    · haveI : Fact r.Prime := ⟨hr⟩
      have hRodd : Nat.Coprime 2 (Nat.card R) := by
        obtain ⟨k, hk⟩ := hRp.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hr).mpr (by omega))
      have hWR : E1.weakClosure T Ω ≤ Subgroup.normalizer (R : Set Q) := fun w _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top w
      have hW2 : IsPGroup 2 (E1.weakClosure T Ω) :=
        hT.isPGroup.to_le E1.weakClosure_le
      have hcomm : ⁅R, E1.weakClosure T Ω⁆ ≤ E1.eGen 1 ⊤ T Ω :=
        E1.commutator_le_eGen hr (by omega) hT hΩ hRp
      have hRfac := E1.comm_sup_inf_centralizer_eq hWR hW2 hRodd hRsolv
      have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
        congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have hcommRW_le_R : ⁅R, E1.weakClosure T Ω⁆ ≤ R := by
        refine Subgroup.commutator_le.mpr fun r hr w _ => ?_
        have e : ⁅r, w⁆ = r * (w * r⁻¹ * w⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R.mul_mem hr (hRn.conj_mem r⁻¹ (R.inv_mem hr) w)
      have hRc : R ≤ Subgroup.centralizer (R : Set Q) := fun x hx =>
        Subgroup.mem_centralizer_iff.2 (fun y hy => (hcommR x hx y hy).symm)
      have hnorm : R ⊓ Subgroup.centralizer (E1.weakClosure T Ω : Set Q) ≤
          Subgroup.normalizer ((⁅R, E1.weakClosure T Ω⁆ : Subgroup Q) : Set Q) :=
        ((inf_le_left.trans hRc).trans (Subgroup.centralizer_le hcommRW_le_R)).trans
          (Subgroup.centralizer_le_normalizer ((⁅R, E1.weakClosure T Ω⁆ : Subgroup Q) : Set Q))
      have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left ⁅R, E1.weakClosure T Ω⁆
        (R ⊓ Subgroup.centralizer (E1.weakClosure T Ω : Set Q)) hnorm
      rw [hRfac] at hcoe
      have hmem : ρ ∈ (⁅R, E1.weakClosure T Ω⁆ : Subgroup Q) *
          ((R ⊓ Subgroup.centralizer (E1.weakClosure T Ω : Set Q)) : Set Q) := hcoe ▸ hρ
      rw [Set.mem_mul] at hmem
      obtain ⟨h, hh, k, hk, hkρ⟩ := hmem
      exact ⟨h, hcomm hh, k,
        Subgroup.centralizer_le_normalizer (E1.weakClosure T Ω : Set Q) hk.2, hkρ⟩
  exact h1.trans
    (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr (E1.eGen_mono hj ⊤ T Ω)))

end CFSG.LocalAnalysis.WeakClosure81
