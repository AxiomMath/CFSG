module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Cfg


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι}

theorem qtwoNode_card_iso {R : ℕ → Prop} (hRk1 : GGSecFiveRk1PhanInput)
    (hL1 : GGQTwoL1InputOn R) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hm : R m) (i : Fin m) :
    Nat.card ↥(qtwoNode Bs (qtwoRefl e e') i) = 6 ∧
      Nonempty (Su (GaloisField 2 2) 2 1 2 ≃* ↥(qtwoNode Bs (qtwoRefl e e') i)) := by
  obtain ⟨hcfg0, ht, hns, hpres, r₀, hr₀A, hr₀C, hr₀6⟩ := hcfg
  have h3 := qtwo_label_le_three e' hM
  obtain ⟨-, F, hF, hfin, θ, hFcard, hθinj, hθrange⟩ :=
    qtwo_rankOne_six_of_rk1 hRk1 hcfg0 hns hpres h3 hr₀A hr₀C hr₀6
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 h3
  obtain ⟨a, haA, hai⟩ := ggSimple_eq_conj_of_mem_ggCoxRefl e hconn hr₀C (e' i)
  obtain ⟨g, -, -, hg1, -⟩ := ggRankOne_conj_of_mem_ggAutomizerJoin (𝒦 := 𝒦) haA r₀
  have hL1r : ggRankOne Bs r₀ = ggRankOneIn L Bs r₀ :=
    (hL1 G p B Bs x L D J 𝒦 ι M e ⟨hcfg0, ht, hns, hpres, r₀, hr₀A, hr₀C, hr₀6⟩ m e' hm hM
      L (Or.inl rfl) r₀ hr₀A hr₀C).1
  have hnode : qtwoNode Bs (qtwoRefl e e') i =
      (θ.range).map (MulAut.conj g).toMonoidHom := by
    rw [hθrange, ← hL1r, hg1, ← hai]
    rfl
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨?_, ?_⟩
  · rw [hnode, Subgroup.card_map_of_injective hinj, hθrange, hr₀6]
  · obtain ⟨e1⟩ := qtwo_su_two_equiv_sl2 hFcard
    exact ⟨e1.trans ((MonoidHom.ofInjective hθinj).trans
      ((Subgroup.equivMapOfInjective θ.range _ hinj).trans
        (MulEquiv.subgroupCongr hnode.symm)))⟩

end Cfg

end CFSG.StandardType.QTwo

end
