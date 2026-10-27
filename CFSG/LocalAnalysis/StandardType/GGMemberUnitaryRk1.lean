module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open CFSG.LieType.Steinberg

open scoped MatrixGroups

section Nbr


theorem ggExists_sl2_of_tableBPosSU {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hpos : GGTableBPosSU p Bs X K f n ψ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrefl : GGIsReflection p r) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G,
      Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r := by
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  obtain ⟨a, b, hab, hr_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hεrefl hrA hrefl
  have hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a b).map ψ := by
    rw [hr_eq]; exact hεlevi a b hab
  let a0 : Fin n := ⟨0, by omega⟩
  let b0 : Fin n := ⟨1, by omega⟩
  have ha0b0 : a0 ≠ b0 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, b0] at this
  obtain ⟨σ, hσ0, hσ1⟩ :=
    ggPhanNSAPairAux_exists_perm_two (n := n) (a := a0) (b := b0) (i := a) (j := b) ha0b0 hab
  let g : Su K 2 f n := ggPhanNSAPairAux_permElt (f := f) σ
  have hconj : (ggSuPairBlock K 2 f n a0 b0).map ((MulAut.conj g).toMonoidHom) =
      ggSuPairBlock K 2 f n a b := by
    have h := ggPhanNSAPairAux_suPairBlock_conj (K := K) (f := f) σ a0 b0
    rw [hσ0, hσ1] at h
    simpa only [g] using h
  have hrS' : ggRankOneIn X Bs r =
      (ggSuPairBlock K 2 f n a0 b0).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
    rw [hrS, ← hconj, Subgroup.map_map]
  let blockMap : Su K 2 f 2 →* Su K 2 f n := blockEmb K 2 f n 2 0 (by omega)
  have hblockrange : blockMap.range = ggSuPairBlock K 2 f n a0 b0 := by
    change (blockEmb K 2 f n 2 0 (by omega)).range = ggSuPairBlock K 2 f n a0 b0
    simpa [a0, b0] using
      ggPhanNSAPairAux_range_blockEmb2 (K := K) (p := 2) (f := f) (n := n) (i := 0) (by omega)
  obtain ⟨eSL⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
      (p := 2) (f := f) hcard
  have hblockMap_inj : Function.Injective blockMap := blockEmb_injective (by omega)
  have hφinj : Function.Injective (blockMap.comp eSL.toMonoidHom) :=
    hblockMap_inj.comp eSL.injective
  haveI : CharP (fixedSubfield K 2 f) 2 := inferInstance
  let θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G :=
    ψ.comp ((MulAut.conj g).toMonoidHom.comp (blockMap.comp eSL.toMonoidHom))
  have hθinj : Function.Injective θ := by
    change Function.Injective
      (ψ.comp ((MulAut.conj g).toMonoidHom.comp (blockMap.comp eSL.toMonoidHom)))
    exact PsiDiag.injective_comp_of_ker_le_center
      ((MulAut.conj g).toMonoidHom.comp (blockMap.comp eSL.toMonoidHom))
      ((MulAut.conj g).injective.comp hφinj) ψ hker
  refine ⟨θ, hθinj, ?_⟩
  change (ψ.comp ((MulAut.conj g).toMonoidHom.comp (blockMap.comp eSL.toMonoidHom))).range =
    ggRankOneIn X Bs r
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr eSL.surjective, Subgroup.map_top, hblockrange,
    Subgroup.map_map, ← hrS']

theorem ggRk1ConclEx_of_sl2 {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n)
    {r : MulAut ↥Bs} (θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G)
    (hθinj : Function.Injective θ) (hrangeθ : θ.range = ggRankOneIn X Bs r)
    (hrA : r ∈ ggAutomizer X Bs) (hr2 : r * r = 1) (hXns : ¬ GGSplitLie p X)
    (hpf : p ∣ 2 ^ f + 1)
    (hlab : ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGRk1ConclEx p Bs X r := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hcard, h0] at h1
      norm_num at h1
    · exact h0
  obtain ⟨b, hnb, hlabX⟩ := hlab
  have hb3 : 3 ≤ b := by omega
  obtain ⟨n', hn'in, hn'N, hn'act⟩ := ggExists_weylElt_of_mem_ggAutomizer hrA hr2
  haveI : CharP (fixedSubfield K 2 f) 2 := inferInstance
  refine ⟨fixedSubfield K 2 f, inferInstance, inferInstance, θ, inferInstance, hθinj, hrangeθ,
    ⟨n', hn'in, hn'N, hn'act⟩, ?_, ?_, ?_, ?_⟩
  · intro hs
    exact absurd hs hXns
  · intro _
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard]
    exact hpf
  · intro lab' hlam' hl'
    have hnn : lab'.n = f :=
      ggLabel_n_eq_of_twA ggLabelRigidInput_holds hb3 hf1 hlabX hlam' hl'
    exact le_of_eq (by rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard, hnn])
  · exact ⟨⟨.twA, b, f⟩,
      ⟨hf1, show 2 ≤ b by omega, fun h => absurd (show b = 2 from h) (by omega)⟩, hlabX,
      CFSG.LieType.Steinberg.card_fixedSubfield hcard⟩

theorem ggRk1ConclEx_of_unitaryCover_nbr {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXns : ¬ GGSplitLie p X)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    (hrange : ψ.range = X) (hdvd : p ∣ 2 ^ f + 1)
    (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs)
    (hlab : ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨ψ', hker', hrange', hpos'⟩ :=
    ggUnitaryCover_position_nbr hcfg hX hcard hn hker hrange hdvd hacts
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
  have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  obtain ⟨θ, hθinj, hrangeθ⟩ :=
    ggExists_sl2_of_tableBPosSU hcard hn hker' hpos' hp hp2 hBs hrA hrefl
  have hr2 : r * r = 1 := by
    simpa [pow_two] using hrefl.1
  exact ggRk1ConclEx_of_sl2 hcard hn θ hθinj hrangeθ hrA hr2 hXns hdvd hlab

theorem ggRk1Concl_unitary_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXns : ¬ GGSplitLie p X)
    (hU : GGMemberUnitary p Bs X) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hrC : r ∈ ggCoxRefl M e) : GGRk1Concl p Bs X r := by
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpf, hacts, hlab⟩ :=
    ggNSLie_cover_of_esu hU
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  exact (ggRk1ConclEx_of_unitaryCover_nbr hcfg hpres hX hXns hKcard hn4 hker hrange hpf hacts hlab
    hrA hrC).toConcl

end Nbr

theorem ggRk1UnitaryMemberInput_holds :
    GGRk1UnitaryMemberInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXns hU r hrA hrC
  exact ggRk1Concl_unitary_nbr hcfg hpres (hX.imp_right (hcfg.2.2.2.1.2 X)) hXns hU hrA hrC

end CFSG.StandardType

end
