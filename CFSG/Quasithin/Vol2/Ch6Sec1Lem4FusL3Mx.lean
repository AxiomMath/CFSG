module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3CoreB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxL1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxL2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxL4
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxU1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxU2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxU3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxU4
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxU5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

theorem l3FusFacts_of_statedSL {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hF : Nat.card F = p) {G : Type} [Group G] (ψ : ↥(StatedSL 3 F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
    (hN : ψ.range.Normal) (hC : ∀ v : G, (∀ n ∈ ψ.range, v * n = n * v) → v = 1) :
    L3FusFacts ψ.range p := by
  have hS : L3Shape F (StatedSL 3 F) ⊤ p :=
    { l3ShapeBase_statedSL hp hp5 hF with
      exists_inverter := fun h5 => exists_inverter_statedSL hp h5 hF }
  exact
    { rank := rank_statedSL hp hp5 hF ψ hker
      invConj := hS.invConj hker
      levi := hS.levi hker
      uniq := fun h5 => hS.uniq hker h5
      invert := fun h5 => hS.invert hker h5
      factB := hS.factB hker (factB_std_statedSL hp hp5 hF ψ hker hN hC) }

theorem l3FusFacts_of_statedSU {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hF : Nat.card F = (p ^ 1) ^ 2) {G : Type} [Group G]
    (ψ : ↥(StatedSU 3 (p ^ 1) F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ 1) F))
    (hN : ψ.range.Normal) (hC : ∀ v : G, (∀ n ∈ ψ.range, v * n = n * v) → v = 1) :
    L3FusFacts ψ.range p := by
  obtain ⟨hcharP, hdet, hneg, hconj, hcent, hblk⟩ := l3ShapeU_basic hp hp5 hF
  obtain ⟨hder, hperf, hctr, hpsl, hscal⟩ := l3ShapeU_sl2 hp hp5 hF
  have hS : L3Shape F (StatedSU 3 (p ^ 1) F) (GU2Stated (p ^ 1) F) p :=
    { charP := hcharP
      det_one := hdet
      neg_mem := hneg
      conj := hconj
      cent := hcent
      blk_mem := hblk
      derived_eq := hder
      sl2_perfect := hperf
      sl2_center := hctr
      sl2_psl := hpsl
      scalar_of_commute := hscal
      exists_inverter := fun h5 => exists_inverter_statedSU hp h5 hF }
  exact
    { rank := rank_statedSU hp hp5 hF ψ hker
      invConj := hS.invConj hker
      levi := hS.levi hker
      uniq := fun h5 => hS.uniq hker h5
      invert := fun h5 => hS.invert hker h5
      factB := hS.factB hker (factB_std_statedSU hp hp5 hF ψ hker hN hC) }

end CFSG.Quasithin.H13
