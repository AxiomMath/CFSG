module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.GLS2.GroupTheory.PComponentOrbitClosure
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.StandardType.QTwo

open CFSG

private theorem qtwoDB7_b1_isComponent_of_isPComponent {X : Type} [Group X] [Finite X]
    (hX : CFSG.pPrimeCore 3 X = ⊥) {A : Subgroup X} (hA : CFSG.IsPComponent 3 A) :
    CFSG.IsComponent A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsub, -, hq⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple
      3 A).1 hA
  have hcore : CFSG.pPrimeCore 3 A = ⊥ := by
    rw [CFSG.ComponentClassification.CatalogueBHeldSmallCore.primeCore_subnormal_intersection
      3 A hsub, hX, Subgroup.bot_subgroupOf]
  refine ⟨?_, hsub⟩
  have e : (↥A ⧸ CFSG.pPrimeCore 3 ↥A) ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq

theorem qtwoDB7_single_or_diag {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.pPrimeCore 3 Y = ⊥) {τ : Y} (hτ : τ ^ 3 = 1) {Jb : Subgroup Y}
    (hJ : CFSG.GH74.GLS.IsPCompIn 3 (Subgroup.centralizer ({τ} : Set Y)) Jb)
    (hlay : Jb ≤ CFSG.pLayer Y 3) :
    (∃ Q : Subgroup Y, CFSG.IsComponent Q ∧ Jb ≤ Q) ∨
      ∃ A : Subgroup Y, CFSG.IsComponent A ∧
        A ≠ A.map (MulAut.conj τ).toMonoidHom ∧
        A ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom ∧
        A.map (MulAut.conj τ).toMonoidHom ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom ∧
        Jb ≤ A ⊔ A.map (MulAut.conj τ).toMonoidHom ⊔ A.map (MulAut.conj (τ ^ 2)).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hτ1 : τ = 1
  · have hcent : Subgroup.centralizer ({τ} : Set Y) = ⊤ := by
      rw [hτ1]
      ext g
      simp [Subgroup.mem_centralizer_iff]
    have hJ2 : CFSG.IsPComponent 3 (Jb.subgroupOf (⊤ : Subgroup Y)) := by
      rw [hcent] at hJ
      exact hJ.2
    have hJp : CFSG.IsPComponent 3 Jb := by
      have h := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_extend_subnormal
        3 (⊤ : Subgroup Y) Subgroup.IsSubnormal.top (Jb.subgroupOf ⊤) hJ2
      rwa [Subgroup.map_subgroupOf_eq_of_le le_top] at h
    exact Or.inl ⟨Jb, qtwoDB7_b1_isComponent_of_isPComponent hY hJp, le_rfl⟩
  · have hx : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
    obtain ⟨A, hA, hJeq, -, -, hdich⟩ :=
      CFSG.SecondGeneration.exists_pComponent_normalClosure_eq_orbit_join
        (p := 3) (x := τ) hx hJ hlay
    have hAcomp : CFSG.IsComponent A := qtwoDB7_b1_isComponent_of_isPComponent hY hA
    let f : Fin 3 → Subgroup Y :=
      fun i => A.map (MulAut.conj (τ ^ (i : ℕ))).toMonoidHom
    have hJle : Jb ≤ (Subgroup.normalClosure
        (Jb.subgroupOf (CFSG.pLayer Y 3) : Set (CFSG.pLayer Y 3))).map
          (CFSG.pLayer Y 3).subtype := by
      have h := Subgroup.map_mono (f := (CFSG.pLayer Y 3).subtype)
        (Subgroup.le_normalClosure (H := Jb.subgroupOf (CFSG.pLayer Y 3)))
      rwa [Subgroup.map_subgroupOf_eq_of_le hlay] at h
    rcases hdich with ⟨-, hJA⟩ | ⟨-, hinj⟩
    · exact Or.inl ⟨A, hAcomp, hJle.trans hJA.le⟩
    · have h0 : f 0 = A := by
        simp only [f, Fin.val_zero, pow_zero]
        rw [map_one MulAut.conj]
        exact Subgroup.map_id A
      have h1 : f 1 = A.map (MulAut.conj τ).toMonoidHom := by simp [f]
      have h2 : f 2 = A.map (MulAut.conj (τ ^ 2)).toMonoidHom := by simp [f]
      have hne01 : A ≠ A.map (MulAut.conj τ).toMonoidHom := by
        intro h
        have hh : f 0 = f 1 := by rw [h0, h1]; exact h
        exact absurd (hinj hh) (by decide)
      have hne02 : A ≠ A.map (MulAut.conj (τ ^ 2)).toMonoidHom := by
        intro h
        have hh : f 0 = f 2 := by rw [h0, h2]; exact h
        exact absurd (hinj hh) (by decide)
      have hne12 : A.map (MulAut.conj τ).toMonoidHom ≠
          A.map (MulAut.conj (τ ^ 2)).toMonoidHom := by
        intro h
        have hh : f 1 = f 2 := by rw [h1, h2]; exact h
        exact absurd (hinj hh) (by decide)
      have hiSup : (⨆ i : Fin 3, f i) = f 0 ⊔ f 1 ⊔ f 2 := by
        apply le_antisymm
        · refine iSup_le (fun i => ?_)
          fin_cases i
          · exact le_sup_left.trans le_sup_left
          · exact le_sup_right.trans le_sup_left
          · exact le_sup_right
        · exact sup_le (sup_le (le_iSup f 0) (le_iSup f 1)) (le_iSup f 2)
      refine Or.inr ⟨A, hAcomp, hne01, hne02, hne12, ?_⟩
      calc Jb ≤ (Subgroup.normalClosure
            (Jb.subgroupOf (CFSG.pLayer Y 3) : Set (CFSG.pLayer Y 3))).map
              (CFSG.pLayer Y 3).subtype := hJle
        _ = ⨆ i : Fin 3, f i := hJeq
        _ = f 0 ⊔ f 1 ⊔ f 2 := hiSup
        _ = A ⊔ A.map (MulAut.conj τ).toMonoidHom ⊔
              A.map (MulAut.conj (τ ^ 2)).toMonoidHom := by rw [h0, h1, h2]

end CFSG.StandardType.QTwo

end
