module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveF4WeylInf
import CFSG.LocalAnalysis.StandardType.GGSecFiveF4ReflMax
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGF4H1Exceptional
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageDefs
import Certificates.Certificate709551

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem guardedLargeEvenLabel_or_unitDvd63_of_coordB_four {p : ℕ} {lab : LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel 4 p lab ∨ GGSecFiveBCoordBResLabel p lab) :
    GuardedLargeEvenLabel lab ∨ GGUnitDvd63Label p lab := by
  unfold GGSecFiveBCoordBLabel GGSecFiveBCoordBResLabel at h
  unfold GuardedLargeEvenLabel GGUnitDvd63Label GGUnitDvdLabel
  rcases h with (⟨hBC, hr, -⟩ | ⟨ht, hr, -⟩ | ⟨-, -, hodd, -⟩ | ⟨ht, hr, hn, -⟩) |
      ⟨hp, ⟨ht, hr, hn⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, hr, hd⟩⟩
  · exact Or.inl (Or.inl ⟨hBC, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨Or.inr ht, by omega⟩))
  · exact absurd hodd (by decide)
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨ht, by omega, hn⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨ht, by omega, hn⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ht))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ht)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ht)))))
  · subst hp
    exact Or.inr ⟨⟨ht, by omega, hd, by rw [hr]; norm_num⟩, hr, rfl⟩

theorem ggF4JoinB3GuardedInput_of_inputs
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGF4JoinB3GuardedInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ ι M e hP hF4 hB3
  obtain ⟨hp, -, hxBs, -, h4⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hWB : GGIsWeylMatrix (CoxeterMatrix.B 3) :=
    Or.inl ⟨3, Equiv.refl _, by decide, Or.inr (Or.inl ⟨by decide, rfl⟩)⟩
  obtain ⟨eta, -, hle⟩ := hR.exists_eta_bCoordinateBlock_of_F4 hTBF hWI
    ⟨Fin 3, CoxeterMatrix.B 3, hWB, hB3⟩ hP hF4 hxBs
  have hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p 3 := by
    refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨a, ha, rfl⟩; exact hle a ha) ?_
    obtain ⟨f, -⟩ := hB3
    have hB48 : Nat.card ↥(ggAutomizer L Bs) = 48 :=
      (Nat.card_congr f.toEquiv).symm.trans
        ((ggCoxeterB_card 3 (by norm_num)).trans (by norm_num [Nat.factorial]))
    have hC48 : Nat.card ↥(bCoordinateBlock 4 p 3) = 48 :=
      (card_bCoordinateBlock hp hp2 3).trans (by norm_num [Nat.factorial])
    rw [Subgroup.card_map_of_injective (MulAut.congr eta).injective, hB48, hC48]
  have hcard : Nat.card Bs = p ^ 4 := le_antisymm (hR.card_eq_of_typeF4 hTBF hWI e hP hF4).2 h4
  have hlab : GGInnerDiagOnLabel (fun p lab => GuardedLargeEvenLabel lab ∨ GGUnitDvd63Label p lab)
      p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h =>
        ⟨guardedLargeEvenLabel_or_unitDvd63_of_coordB_four h.1, h.2⟩)
      (ggSecFiveBCoordBLabel_core (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds hR
        le_rfl eta 3 hAut)
  rcases hlab.elim_or with hG | hU
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hG
  · exact (no_original_unitSix_at_card_four hR.1.1 hU hcard).elim

end CFSG.StandardType

end
