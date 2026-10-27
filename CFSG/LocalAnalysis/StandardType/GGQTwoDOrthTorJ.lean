module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorStruct
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorRed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Assembly

theorem qtwoOrth_jlabel_of_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (Φ : OrthFrameCore p Bs L)
    (hF : Nat.card Φ.F = 2) (_h4 : 4 ≤ Φ.r) (hZ : Subgroup.center ↥L = ⊥) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2) := by
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hStd : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  have hBstar : GGBstar p B Bs := hcfg.1.1.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  obtain ⟨t, htA, htC⟩ := Φ.exists_torC_eq_inf_centralizer (D := D) (x := x)
    (hStd.1.trans hBstar.1) hStd.2.1 hStd.2.2.1 hStd.2.2.2.1 hS.2.2.1 hS.2.2.2.1.1 hZ
  have hJc : IsComponentOf J (Φ.img (Φ.torC t)) := by
    rw [← htC]
    exact hStd.2.2.2.2.2.1
  have ht : Φ.TorStruct t := qtwoOrth_torStruct Φ hF htA
  exact (Φ.torStruct_component ht hJc).1

theorem qtwoOrth_jAnchor_of_frame {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X J : Subgroup G} {x : G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2)
    (_h4 : 4 ≤ Φ.r) (hx : x ∈ Bs)
    (hJc : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∃ x' y' : OmPlusIdx Φ.r,
      omPlusRefl p x' * omPlusRefl p y' ≠ omPlusRefl p y' * omPlusRefl p x' ∧
        Φ.img (Φ.rank2 x' y') ≤ J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := Φ.inf_centralizer_eq_img ⟨x, hx⟩
  have hJc' : IsComponentOf J (Φ.img (Φ.torC (Φ.toral ⟨x, hx⟩))) := by
    rw [← h]
    exact hJc
  have ht : Φ.toral ⟨x, hx⟩ ∈ Φ.A := Φ.toral_mem ⟨x, hx⟩
  have hts : Φ.TorStruct (Φ.toral ⟨x, hx⟩) := qtwoOrth_torStruct Φ hF ht
  exact (Φ.torStruct_component hts hJc').2

end CFSG.StandardType.QTwo

end
