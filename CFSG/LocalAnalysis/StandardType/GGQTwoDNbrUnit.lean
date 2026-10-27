module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
public import CFSG.LocalAnalysis.StandardType.GGNSJoinToralA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G] [Finite G]

@[expose] def QTwoDFixBound (Bs X : Subgroup G) (m : ℕ) : Prop :=
  ∀ (n : ℕ) (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs)), 5 ≤ n →
    (∀ a b : Fin n, a ≠ b →
      GGIsReflection 3 ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) →
    n ≤ m ∧ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ (m - n + 1)

theorem qtwoDNbr_unit_of_cover (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) {m : ℕ} (hcard : Nat.card ↥Bs = 3 ^ m)
    (hFix : QTwoDFixBound Bs X m) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {ψ : Su K 2 1 n →* G} (hKcard : Nat.card K = (2 ^ 1) ^ 2) (hn5 : 5 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n)) (hrange : ψ.range = X)
    (hdvd : 3 ∣ 2 ^ 1 + 1) (hacts : GGActsUnitarily (p := 2) (f := 1) ψ Bs) :
    QTwoDL1Chart 3 B Bs X := by
  classical
  have hX : X = L ∨ ∃ y : G, GGNbr 3 B x D J y X := Or.inr ⟨y, hnbr⟩
  have hloc : GGNSLocalHyp 3 B Bs K 1 n ψ :=
    ggNSLocalHyp_of_nbr hcfg hX hKcard (by omega) hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag hC hloc
  have hloc' := hloc.comp_conj c
  have hrange' : (ψ.comp (MulAut.conj c).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, hrange]
  have hpos := ggNSDiag_position hloc' hc
  rw [hrange'] at hpos
  obtain ⟨ε, hεrefl, -⟩ := hpos
  have hbound := hFix n ε hn5 hεrefl
  have htor := ggNSDiag_toral_bound hloc' hc
  rw [hrange'] at htor
  have hKcard4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  refine Or.inl ⟨K, inferInstance, inferInstance, inferInstance, n,
    ψ.comp (MulAut.conj c).toMonoidHom, hKcard4, hloc', hrange', hc, le_antisymm htor ?_⟩
  calc 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))
      ≤ 3 ^ (n - 1) * 3 ^ (m - n + 1) := Nat.mul_le_mul_left _ hbound.2
    _ = 3 ^ m := by
        rw [← pow_add]
        congr 1
        omega
    _ = Nat.card ↥Bs := hcard.symm

theorem qtwoDNbr_unit
    (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) {m : ℕ} (hcard : Nat.card ↥Bs = 3 ^ m)
    (hFix : QTwoDFixBound Bs X m)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank ≠ 3 ∧
      lab.rank ≠ 5) 3 Bs X) :
    QTwoDL1Chart 3 B Bs X := by
  classical
  obtain ⟨lab, K, hKf, hKfin, hKchar, f, n, ψ, ⟨hrow, hn1, h3, h5⟩, hnrank, hf, hKcard, h4,
      hker, hrange, hdvd, hacts, -⟩ :=
    ggNSLie_cover_of_esu_pred (P := fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank ≠ 3 ∧
      lab.rank ≠ 5) (fun p lab hl => ⟨hl.1, fun h => by
        rcases h.2 with h' | h'
        · exact hl.2.2.1 h'
        · exact hl.2.2.2 h'⟩) hmark
  obtain rfl : f = 1 := hf.trans hn1
  have hrank4 : 4 ≤ lab.rank := by
    rcases hrow.1 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  exact qtwoDNbr_unit_of_cover hC hcfg hnbr hcard hFix hKcard (by omega) hker hrange hdvd hacts

end CFSG.StandardType.QTwo

end
