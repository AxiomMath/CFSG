module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43ExtA
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_extraspecial_of_hyp {M V : Subgroup G} {g : G} (h : Hyp612Sym 1 M V g)
    (hU : Nat.card ↥(UOf M V g) = 32) (hB : Nat.card ↥(BOf M V g) = 32)
    (hN : Nat.card ↥(NOf M V g) = 2) : IsExtraspecialPlus2 ↥(KOf M V g) 4 := by
  have hKL : KOf M V g ≤ LOf V g := by
    unfold KOf LOf UOf BOf
    exact sup_le_sup inf_le_left inf_le_left
  refine s16c1G43_extraspecial (K := KOf M V g) (U := UOf M V g) (B := BOf M V g)
    (N := NOf M V g) le_sup_left le_sup_right ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ hU hB hN
  · intro k hk
    obtain ⟨u, hu, b, hb, rfl⟩ := (h.mem_KOf_iff).1 hk
    exact ⟨u, hu, b, hb, rfl⟩
  · intro x hx y hy
    exact h.elemAbelian.comm hx.1 hy.1
  · intro x hx
    simpa [pow_two] using h.elemAbelian.2 x hx.1
  · intro x hx y hy
    exact h.elemAbelian_conj.comm hx.1 hy.1
  · intro x hx
    simpa [pow_two] using h.elemAbelian_conj.2 x hx.1
  · intro k hk k' hk'
    exact h.commutator_KOf_KOf_mem_N hk hk'
  · intro n hn k hk
    exact (h.mul_comm_of_mem_NOf hn (hKL hk)).symm
  · intro u hu hcomm
    refine Subgroup.mem_inf.2 ⟨?_, h.le_M hu.1⟩
    exact h.centralizer_le
      (Subgroup.mem_inf.2 ⟨hu.1, Subgroup.mem_centralizer_iff.2 hcomm⟩)
  · intro b hb hcomm
    refine Subgroup.mem_inf.2
      ⟨h.centralizer_le' (Subgroup.mem_inf.2 ⟨hb.1, ?_⟩), h.conjV_le_conjM hb.1⟩
    exact Subgroup.mem_centralizer_iff.2 hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
