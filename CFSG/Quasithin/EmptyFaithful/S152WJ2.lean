module

public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Quasithin.S152W

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.J2Cover

theorem j2_class_card : ∀ t ∈ P, orderOf t = 2 →
    Nat.card (centralizerIn P t) = 240 ∨ Nat.card (centralizerIn P t) = 1920 := by
  intro t ht ho
  obtain ⟨hcov, -, h1, -, h2⟩ := inner_classes
  obtain ⟨-, hc1, -⟩ := cent2B_facts
  obtain ⟨-, hc2, -⟩ := cent2A_facts
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov t ht ho
  rw [centralizerIn_conj P hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [h1]
    exact hc1
  · right
    rw [h2]
    exact hc2

theorem atlasClauses_J2 :
    AtlasClauses NativeSporadic.J2 := by
  have : Finite NativeSporadic.J2 := Finite.of_equiv _ nativeEquivP.symm.toEquiv
  refine atlasClauses_of_data AT_J2_Schreier.1 [240, 1920] ?_ (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_equiv nativeEquivP t, card_centralizer_subtype]
  have := j2_class_card (nativeEquivP t : Equiv.Perm (Fin 315)) (nativeEquivP t).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact this

end CFSG.Quasithin.S152W
