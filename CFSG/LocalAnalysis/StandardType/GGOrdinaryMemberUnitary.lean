module

public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
public import CFSG.LocalAnalysis.StandardType.GGSelectedPSU
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
public import CFSG.LocalAnalysis.StandardType.GGPhanOneNodePosition
import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan Matrix

variable {G : Type} [Group G] [Finite G]

theorem exists_selected_member_of_unitary (hL1 : GGSecFiveL1PhanInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hU : GGMemberUnitary p Bs L) :
    ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
      ∃ (d f : ℕ) (lambda : (ggU .PSU d f).K →* G),
        StatedLieAdmissible .PSU d 2 f ∧ 2 ≤ (ggU .PSU d f).D.rank ∧
        lambda.ker ≤ Subgroup.center (ggU .PSU d f).K ∧ lambda.range = L ∧
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
          (delta : Fin (ggU .PSU d f).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .PSU d f).D k delta),
          (lambda.comp model.phi).range = ggRankOnePerf Bs r₀ := by
  obtain ⟨K, hKf, hKfin, hKchar, f, d, ψL, hKcard, hd4, hkerL, hrangeL, hpL, hpos, -⟩ :=
    ggMemberUnitary_position hcfg (Or.inl rfl) hU
  let : Field K := hKf
  have : Finite K := hKfin
  have : CharP K 2 := hKchar
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst f
      have : Nat.card K = 1 := by simpa using hKcard
      have h := Finite.one_lt_card (α := K)
      omega
    · exact hf
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  let a0 : Fin d := ⟨0, by omega⟩
  let b0 : Fin d := ⟨1, by omega⟩
  have hab : a0 ≠ b0 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, b0] at this
  let r₀ : MulAut ↥Bs := ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer L Bs := (ε (Equiv.swap a0 b0)).2
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) (hεrefl a0 b0 hab)
  have hperf₀ : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) r₀ hr₀A hr₀C
  have hlevi : ggRankOneIn L Bs r₀ = (ggSuPairBlock K 2 f d a0 b0).map ψL :=
    hεlevi a0 b0 hab
  let F := GaloisField 2 (2 * f)
  have hF : Nat.card F = (2 ^ f) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf1
  obtain ⟨β, delta, model, hblock⟩ := SelectedRoot.exists_selectedModel_PSU_block hF hd4
  let : Fintype K := Fintype.ofFinite K
  let : Fintype F := Fintype.ofFinite F
  let E : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard, hF])
  have hE : ∀ c, E (unitaryInvolution K 2 f c) = unitaryInvolution F 2 f (E c) := by
    intro c
    simp only [unitaryInvolution_apply, map_pow]
  let T : Su K 2 f d ≃* Su F 2 f d := suidCongr E hE d
  have hTblock : (ggSuPairBlock K 2 f d a0 b0).map T.toMonoidHom =
      ggSuPairBlock F 2 f d a0 b0 :=
    SetLike.coe_injective (by
      simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using
        ggPhanNSAPairAux_suidCongr_pairBlock E hE a0 b0)
  let lambda : SU (unitaryInvolution F 2 f) d →* G :=
    ψL.comp (T.symm.toMonoidHom.comp β.toMonoidHom)
  have hker : lambda.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) d) := by
    refine (Subgroup.comap_mono hkerL).trans ?_
    exact Subgroup.comap_center_le_center (f := T.symm.toMonoidHom.comp β.toMonoidHom)
      (T.symm.injective.comp β.injective)
  have hrange : lambda.range = L := by
    dsimp only [lambda]
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr β.surjective, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr T.symm.surjective, Subgroup.map_top, hrangeL]
  have himage : (lambda.comp model.phi).range = ggRankOnePerf Bs r₀ := by
    calc (lambda.comp model.phi).range
        = ((model.phi.range.map β.toMonoidHom).map T.symm.toMonoidHom).map ψL := by
          rw [MonoidHom.range_comp, Subgroup.map_map, Subgroup.map_map]
          rfl
      _ = ((ggSuPairBlock F 2 f d a0 b0).map T.symm.toMonoidHom).map ψL := by rw [hblock]
      _ = (ggSuPairBlock K 2 f d a0 b0).map ψL := by
          have hc : ((ggSuPairBlock K 2 f d a0 b0).map T.toMonoidHom).map
              T.symm.toMonoidHom = ggSuPairBlock K 2 f d a0 b0 := by
            rw [Subgroup.map_map]
            have hid : T.symm.toMonoidHom.comp T.toMonoidHom = MonoidHom.id _ := by
              ext y
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
                T.symm_apply_apply, MonoidHom.id_apply]
            rw [hid, Subgroup.map_id]
          rw [← hTblock, hc]
      _ = ggRankOneIn L Bs r₀ := hlevi.symm
      _ = ggRankOnePerf Bs r₀ := hperf₀.symm
  have hadm : StatedLieAdmissible .PSU d 2 f :=
    ⟨Nat.prime_two, hf1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  have hD : ggU .PSU d f =
      ⟨Unitary.SU (unitaryInvolution F 2 f) d, Unitary.rootDatum hF d⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
    rfl
  refine ⟨r₀, hr₀A, hr₀C, d, f, ?_⟩
  rw [hD]
  refine ⟨lambda, hadm, ?_, hker, hrange, CFSG.LieType.Steinberg.fixedSubfield F 2 f,
    inferInstance, inferInstance, inferInstance, delta, model, himage⟩
  show 2 ≤ d / 2
  omega

theorem exists_selected_unitary_member_of_join (hL1 : GGSecFiveL1PhanInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hDE : GGIsWeylMatrixD M ∨ GGIsWeylMatrixE M)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hU : GGMemberUnitary p Bs L) :
    ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
      ∃ (d f : ℕ) (lambda : (ggU .PSU d f).K →* G),
        StatedLieAdmissible .PSU d 2 f ∧ 2 ≤ (ggU .PSU d f).D.rank ∧
        lambda.ker ≤ Subgroup.center (ggU .PSU d f).K ∧ lambda.range = L ∧
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
          (delta : Fin (ggU .PSU d f).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .PSU d f).D k delta),
          (lambda.comp model.phi).range = ggRankOnePerf Bs r₀ := by
  have htype : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M := hDE.imp_left (fun hD => Or.inr hD)
  have hns : ¬ GGSplitLie p L := fun hs => hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, htype⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    rcases htype with hAD | hE
    · exact hAD.le_three
    · exact hE.le_three
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 := by
    intro r hr hrC h6
    apply hSix
    rcases hDE with hD | hE
    · exact ⟨hpres, Or.inr (Or.inl hD), r, hr, hrC, h6⟩
    · exact ⟨hpres, Or.inr (Or.inr hE), r, hr, hrC, h6⟩
  exact exists_selected_member_of_unitary hL1 hcfg hns hpres hle3 hbig hU

end CFSG.StandardType
