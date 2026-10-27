module

public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.RootGroupCard
public import CFSG.LieType.Universal.Unitary.RootGroupCardRankTwo
import CFSG.LieType.Universal.Unitary.Extras.Basic

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.LieType.Universal.Unitary CFSG.LieType.RootSystem CFSG.LieType.BorelTits

@[expose] def excU7Beta : Fin (6 / 2) → ℤ := Pi.single 0 1

section Datum

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem excU7Beta_mem_roots (hF : Nat.card F = (p ^ f) ^ 2) :
    excU7Beta ∈ (rootDatum hF 6).roots := by
  show (Pi.single 0 1 : Fin (6 / 2) → ℤ) ∈ roots (isFiniteType_cartan 6) (divisible 6)
  exact (isCTRootSystem (isFiniteType_cartan 6) (divisible 6)).single_mem 0

theorem two_smul_excU7Beta_notMem_roots (hF : Nat.card F = (p ^ f) ^ 2) :
    2 • excU7Beta ∉ (rootDatum hF 6).roots := by
  have h1 : ∀ i j : Fin 6, toStd 6 (2 • excU7Beta) ≠ weight 6 i - weight 6 j := by decide
  have h2 : ∀ i : Fin 6, toStd 6 (2 • excU7Beta) ≠ 2 • weight 6 i := by decide
  show (2 • excU7Beta) ∉ roots (isFiniteType_cartan 6) (divisible 6)
  rw [roots_eq 6]
  rintro (⟨i, j, -, -, -, -, h⟩ | ⟨i, -, h⟩ | ⟨h6, -⟩)
  · exact h1 i j h
  · exact h2 i h
  · exact h6 (by decide)

theorem rootGroup_excU7Beta (hF : Nat.card F = (p ^ f) ^ 2) :
    (rootDatum hF 6).rootGroup excU7Beta =
      (rootHom (unitaryInvolution F p f) (unitaryInvolution_involutive hF)
        (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) (by decide) (by decide)).range := by
  have hto : toStd 6 excU7Beta = weight 6 0 - weight 6 1 := by decide
  show rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6 excU7Beta = _
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rw [hto] at hw
      rcases SUExtras.eq_of_weight_sub_eq_sub (i := 0) (j := 1) (by decide) (by decide)
        (by decide) (by decide) hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact le_rfl
      · exact rootHom_range_rev_le (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rw [hto] at hw
      exfalso
      obtain ⟨h0, h1⟩ := SUExtras.eq_of_weight_sub_eq_two_smul (i := i) hi hw.symm
      have hi0 : i = 0 := h0.symm
      subst hi0
      exact absurd h1 (by decide)
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact SUExtras.rootHom_mem (unitaryInvolution_involutive hF) (by decide) (by decide)
      (by decide) (by decide) hto.symm c

theorem card_rootGroup_excU7Beta (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card ↥((rootDatum hF 6).rootGroup excU7Beta) = (p ^ f) ^ 2 := by
  rw [rootGroup_excU7Beta hF]
  rw [card_rootHom_range (unitaryInvolution_involutive hF) (by decide) (by decide) (by decide)
    (by decide)]
  exact hF

end Datum

end CFSG.StandardType.LieKnownR2.ExcPos
