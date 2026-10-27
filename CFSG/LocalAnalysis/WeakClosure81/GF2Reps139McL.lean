module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLaughlin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrime
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem mcLaughlin1969_holds : McLaughlin1969 := by
  intro M _ _ hM2 J L hLJ _ hidx hq hirr hgen
  have hfaith : ∀ j ∈ J, (∀ r ∈ (⊤ : Subgroup M), j r = r) → j = 1 := fun j _ hj =>
    MulEquiv.ext fun m => hj m (Subgroup.mem_top m)
  have hJ : J ≠ ⊥ := by
    intro hJ
    have := hq.2.1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    have h1 : ∀ x : ↥L, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hJ ▸ hLJ x.2))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [h1 x, h1 y])
  obtain ⟨-, hK⟩ := rJPrime153_holds M hM2 J ⊤
    (rMcLaughlin_holds M hM2 J ⊤ hJ hirr hfaith hgen) hfaith
  have hLL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hq.1.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hL : L = ⁅J, J⁆ := le_antisymm (hLL.symm.le.trans (Subgroup.commutator_mono hLJ hLJ))
    (H13.Ch4.E443.commutator_le_of_index_le_two hidx Subgroup.index_ne_zero_of_finite)
  subst hL
  rcases hK with hP | ⟨⟨hcyc, hcard⟩, -⟩
  · rcases hP with ⟨n, -, -, hnat⟩ | ⟨n, -, hX, hnat⟩ | ⟨n, -, hX, hnat⟩ | ⟨n, -, hX, hnat⟩ |
      ⟨n, -, hX, hnat⟩
    · obtain ⟨K, hF, hfin, hcardK, ⟨e⟩⟩ := hnat.exists_equiv
      exact Or.inl ⟨n, ⟨K, hF, hfin, hcardK, ⟨e.symm⟩⟩, hnat⟩
    · exact Or.inr (Or.inl ⟨n, hX, hnat⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, hX, hnat⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hX, hnat⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hX, hnat⟩)))
  · exfalso
    have := hcyc.isMulCommutative
    have h := congrArg (fun H : Subgroup ↥⁅J, J⁆ => Nat.card H)
      ((_root_.commutator_eq_bot ↥⁅J, J⁆).symm.trans hq.1.commutator_eq_top)
    simp only [Subgroup.card_bot, Subgroup.card_top] at h
    omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

end
