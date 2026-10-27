module

public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlCl
public import CFSG.LocalAnalysis.StandardType.GGK1CBlSu
public import CFSG.LocalAnalysis.StandardType.GGK1CBlPre
public import CFSG.LocalAnalysis.StandardType.GGK1CBlSolv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

theorem ggK1CBl_witness_facts {nf : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {kind : ggK1CCo_Kind}
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hw : ggK1CBl_KindWitness nf K kind A) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ ↔ (ggK1CCo_kindOrbit nf kind).qs = true) ∧
      (CFSG.IsQuasisimple ↥⁅A, A⁆ → ggK1CBl_Model nf K kind ↥⁅A, A⁆) := by
  cases kind with
  | sl m =>
      obtain ⟨hm, ⟨e⟩⟩ := hw
      exact ggK1CBl_classical_sl hK hnf hm e
  | su m =>
      obtain ⟨hm, E, _hEfield, _hEfin, hE, V, _hVadd, _hVmod, _hVfin, Hf, hsym, hsep,
        hb, he⟩ := hw
      obtain ⟨b, hb⟩ := hb
      obtain ⟨e⟩ := he
      exact ggK1CBl_classical_su hK hnf hm hE hsym hsep b hb e
  | sp s =>
      obtain ⟨hs, W, _hWadd, _hWmod, _hWfin, B, hB, hn, hdim, he⟩ := hw
      obtain ⟨e⟩ := he
      exact ggK1CBl_classical_sp hK hnf hs hB hn hdim e

theorem ggK1CCo_blocks_exists {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) : Nonempty (ggK1CCo_Blocks p nf d r K x m) := by
  obtain ⟨P⟩ := ggK1CBl_preblocks_exists hnf hp hp2 hdvd hK hm hx
  letI : Fintype P.ι := P.fintype
  refine ⟨⟨P.ι, P.A, P.kind, P.hcomm, P.hjoin, P.hindep, ?_, P.kind_multiset, ?_, ?_, ?_⟩⟩
  · exact fun i => (ggK1CBl_witness_facts hnf hK (P.witness i)).1
  · exact fun i => (ggK1CBl_witness_facts hnf hK (P.witness i)).2.1
  · intro i hq
    exact ggK1CBl_model_subgroup ⁅P.A i, P.A i⁆
      ((ggK1CBl_witness_facts hnf hK (P.witness i)).2.2 hq)
  · intro i hh hqs
    exact ggK1CBl_solvable_witness hnf hK hp hp2 hdvd (P.witness i) hh hqs

end CFSG.StandardType

end
