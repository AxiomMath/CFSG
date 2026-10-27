module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAssemble
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggUnitaryCover_position_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    (hrange : ψ.range = X) (hdvd : p ∣ 2 ^ f + 1)
    (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs) :
    ∃ ψ' : Su K 2 f n →* G, ψ'.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ'.range = X ∧
      GGTableBPosSU p Bs X K f n ψ' := by
  have h : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_nbr hcfg hX hcard hn hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_position ggSecFiveNSCornerInput_holds h
  have hr : (ψ.comp (MulAut.conj c).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, hrange]
  refine ⟨ψ.comp (MulAut.conj c).toMonoidHom, (h.comp_conj c).ker, hr, ?_⟩
  rw [← hrange] at hr
  have hc' := hc
  rwa [hrange] at hc'

theorem ggMemberUnitary_position_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hU : GGMemberUnitary p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGTableBPosSU p Bs X K f n ψ ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) := by
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hcard, hn, hker, hrange, hdvd, hacts, hlabel⟩ :=
    ggNSLie_cover_of_esu hU
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ψ', hker', hrange', hpos'⟩ :=
    ggUnitaryCover_position_nbr hcfg hX hcard hn hker hrange hdvd hacts
  exact ⟨K, hKf, hKfin, hKchar, f, n, ψ', hcard, hn, hker', hrange', hdvd, hpos', hlabel⟩


theorem ggMemberUnitary_position
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    (hU : GGMemberUnitary p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGTableBPosSU p Bs X K f n ψ ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) :=
  ggMemberUnitary_position_nbr hcfg (hX.imp_right (hcfg.2.2.2.1.2 X)) hU

end CFSG.StandardType

end
