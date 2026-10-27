module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Hypotheses
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Model
public import CFSG.RankThree.GF2n.Tim79a34GriessSpException
import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap spMap_injective spMap_surjective)

private theorem c8_nonempty_mulEquiv_gf_of_isSpn {X : Type} [Group X] (hX : IsSpn X 6 1) :
    Nonempty (X ≃* ↥(StatedSp 3 (GaloisField 2 1))) := by
  obtain ⟨e⟩ := c8_nonempty_mulEquiv_of_isSpn hX
  let σ : ZMod 2 ≃+* GaloisField 2 1 := (GaloisField.equivZmodP 2).toRingEquiv.symm
  exact ⟨e.trans (MulEquiv.ofBijective (spMap (n := 3) σ.toRingHom)
    ⟨spMap_injective (n := 3) σ.toRingHom, spMap_surjective (n := 3) σ⟩)⟩

theorem c8SchurSp6_holds :
    C8SchurSp6 := by
  unfold C8SchurSp6
  intro X Q _ _ _ hX hQ q hq hker
  obtain ⟨e⟩ := c8_nonempty_mulEquiv_gf_of_isSpn hX
  have hk : (e.toMonoidHom.comp q).ker = q.ker :=
    MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective
  have hle := CFSG.RankThree.GF2n.Tim79a.card_ker_le_two_statedSp_three_two_one
    (e.toMonoidHom.comp q) (e.surjective.comp hq)
    (by rw [hk]; exact hker)
    (by rw [Group.isPerfect_def.1 hQ]; exact le_top)
  rw [hk] at hle
  have hpos : 0 < Nat.card q.ker := Nat.card_pos
  exact (Nat.dvd_prime Nat.prime_two).2 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
