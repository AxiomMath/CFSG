module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Hyp

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

theorem Hyp18.p_prime (h : Hyp18 D V₀ V p L) : p.Prime := (D.sig_prime p h.hp).1

theorem Hyp18.p_ne_two (h : Hyp18 D V₀ V p L) : p ≠ 2 := (D.sig_prime p h.hp).2

theorem Hyp18.L_mem_calC (h : Hyp18 D V₀ V p L) : L ∈ calC D.M := h.hL.1

theorem Hyp18.L_le_M (h : Hyp18 D V₀ V p L) : L ≤ D.M := h.L_mem_calC.1.le

theorem Hyp18.p_dvd_card_L (h : Hyp18 D V₀ V p L) : p ∣ Nat.card L := h.hL.2.2

theorem Hyp18.L_le_X (h : Hyp18 D V₀ V p L) : L ≤ conjClosure D.M L := by
  have hmem : L ∈ conjSetOf D.M L := ⟨1, D.M.one_mem, by
    show L = L.map (MulAut.conj (1 : G)).toMonoidHom
    rw [show MulAut.conj (1 : G) = 1 from map_one _]
    exact (Subgroup.map_id L).symm⟩
  exact le_iSup₂ (f := fun K (_ : K ∈ conjSetOf D.M L) => K) L hmem

theorem Hyp18.X_le_M (h : Hyp18 D V₀ V p L) : conjClosure D.M L ≤ D.M := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨g, hg, rfl⟩ := hK
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  show g * y * g⁻¹ ∈ D.M
  exact D.M.mul_mem (D.M.mul_mem hg (h.L_mem_calC.1.le hy)) (D.M.inv_mem hg)

theorem Hyp18.not_solvable (h : Hyp18 D V₀ V p L) : ¬ Group.IsSolvable ↥D.M :=
  UC6S846.not_solvable_of_mem_calC h.L_mem_calC

theorem Hyp18.stronglyPEmbedded (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
  UC6S846.sp_of_mem_sig hSg h.not_solvable h.hp

theorem Hyp18.p_not_dvd_card_inf (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) {g : G}
    (hg : g ∉ D.M) :
    ¬ p ∣ Nat.card (D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g : Subgroup G) := by
  have hsp := h.stronglyPEmbedded hSg
  have hg' : g⁻¹ ∉ D.M := fun hmem => hg (by simpa using D.M.inv_mem hmem)
  exact hsp.2.2 g⁻¹ hg'

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
