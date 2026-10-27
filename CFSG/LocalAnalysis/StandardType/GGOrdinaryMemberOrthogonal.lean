module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
public import CFSG.LocalAnalysis.StandardType.GGNsq2U62
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCoxRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRowDefs
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinDCell
import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberUnitary
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameSpinCover
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoRankOne
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoInternal
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixPZ
import CFSG.LocalAnalysis.StandardType.GGResIBasic
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
import CFSG.GroupTheory.CenterlessInnerCentralizer

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open CFSG.RankThree.Classical2 (orthDerived)

variable {G : Type} [Group G] [Finite G]

theorem bstar_le_ggG0_of_original_E7 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    Bs ≤ ggG0 p B x L D J := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hBs : IsElemAbelian p Bs := hcfg.1.1.tableB_facts.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    bstar_le_normalizer_ggG0_of_join hcfg hJoin
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs := by
    rw [hJoin]
    exact ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  have hW : GGWeylOfType p CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
    obtain ⟨σ, rfl⟩ := hE7
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 :=
    fun b hb => hcfg.eq_one_of_forall_join_fix hTBF hWI b hb
  have hstep : ∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ∀ b : ↥Bs,
      ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ ggG0 p B x L D J := by
    intro ψ hψ b
    simpa only [sup_idem] using
      mul_inv_mem_sup_of_mem_sup_ggAutomizer hN hN (Subgroup.mem_sup_left (hA hψ)) b
  have hdet : IsUnit (CartanMatrix.E₇.det : ZMod p) := by
    rw [CartanMatrix.E₇_det]
    exact isUnit_iff_ne_zero.mpr (by rw [Int.cast_ofNat]; exact h2)
  apply le_of_cartan_pairing (M := CoxeterMatrix.E₇) (C := CartanMatrix.E₇)
    hp2 hBs hstep
  · intro V _ _ ιV
    exact SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (p := p)
      hp2 hNT ggIntCartan_E₇
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      ![0, 3, 0, 2, 3, 4, 5] 0 ![0, 3, 1, 2, 3, 4, 5]
      (by intro i j hij; fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide)
      (by decide) hW
      (fun ψ hψ => mem_ggAutomizer_iff.mp ((ggAutomizer_mono Bs le_top) (hA hψ))) ιV
  · exact card_le_pow_rank_of_isUnit_det hdet hW hfix

section NativeToralSource

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional
  CFSG.SeitzReduction.E8Pilot

theorem lambda_actor_eq_of_center_eq_bot {H U : Type*} [Group H] [Group U]
    (lambda : U →* H) (hinj : Function.Injective lambda)
    (hZ : Subgroup.center U = ⊥) (Bs : Subgroup H) (x : H)
    (hx : x ∈ Bs) (hxr : x ∈ lambda.range) (Γ : Bs →* MulAut U)
    (hΓ : ∀ b z, lambda (Γ b z) = (b : H) * lambda z * (b : H)⁻¹)
    (y : U) (hinner : Γ ⟨x, hx⟩ = MulAut.conj y) : lambda y = x := by
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hxr
  have hzΓ : MulAut.conj z = Γ ⟨x, hx⟩ := by
    ext u
    apply hinj
    change lambda (z * u * z⁻¹) = lambda (Γ ⟨x, hx⟩ u)
    rw [map_mul, map_mul, map_inv, hz]
    exact (hΓ ⟨x, hx⟩ u).symm
  have hzy : z = y := CFSG.mulAutConj_injective_of_center_eq_bot hZ (hzΓ.trans hinner)
  simpa only [hzy] using hz

theorem GGSecFiveRouteCfg.lambda_native_actor_eq_of_original_E7
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 p B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (Γ : Bs →* MulAut (e7Data_valid.minGroup K))
    (hΓ : ∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹)
    (y : e7Data_valid.minGroup K)
    (hinner : Γ ⟨x, hcfg.1.1.tableB_facts.2.2.1⟩ = MulAut.conj y) :
    lambda y = x := by
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := center_minGroup_e7_eq_bot
  have hinj : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp (le_antisymm (by simpa only [hZ] using hker) bot_le)
  have hx : x ∈ Bs := hcfg.1.1.tableB_facts.2.2.1
  have hxrange : x ∈ lambda.range := by
    rw [hrange]
    exact bstar_le_ggG0_of_original_E7 hTBF hWI hcfg hpres hE7 hJoin hx
  exact lambda_actor_eq_of_center_eq_bot lambda hinj hZ Bs x hx hxrange Γ hΓ y hinner

theorem exists_conj_torus_of_original_E7_bstar (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 3 B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K)) :
    ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K),
      ∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (e7MinEquivAdjoint K u : ModGL .E7 K) * g ∈ torusGroup .E7 (AlgebraicClosure K) := by
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := center_minGroup_e7_eq_bot
  have hinj : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp (le_antisymm (by simpa only [hZ] using hker) bot_le)
  have hBsG0 := bstar_le_ggG0_of_original_E7 hTBF hWI hcfg hpres hE7 hJoin
  have hBsrange : Bs ≤ lambda.range := by simpa only [hrange] using hBsG0
  let E := Bs.comap lambda
  have : Finite (e7Data_valid.minGroup K) := Finite.of_injective lambda hinj
  have hEmap : E.map lambda = Bs := by
    apply le_antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact hu
    · intro z hz
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (hBsrange hz)
      exact ⟨u, by change lambda u ∈ Bs; rw [hu]; exact hz, hu⟩
  let θ := e7MinEquivAdjoint K
  let rho : e7Data_valid.minGroup K →* ModGL .E7 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup .E7 K).subtype.comp θ.toMonoidHom)
  have hrhoinj : Function.Injective rho :=
    (baseChangeGL_injective _).comp (Subtype.val_injective.comp θ.injective)
  let A := E.map rho
  have hAadj : A ≤ adjointGroup .E7 (AlgebraicClosure K) := by
    rintro z ⟨u, -, rfl⟩
    exact TableBExcTwo.baseChangeGL_mem_adjointGroup _ (θ u).2
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.tableB_facts.2.1
  have hcomm : ∀ z ∈ A, ∀ w ∈ A, z * w = w * z := by
    rintro z ⟨u, hu, rfl⟩ w ⟨v, hv, rfl⟩
    have huv : u * v = v * u := hinj (by
      rw [map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm hBs hu hv)
    rw [← map_mul, ← map_mul, huv]
  have hexp : ∀ z ∈ A, z ^ 3 = 1 := by
    rintro z ⟨u, hu, rfl⟩
    have hu3 : u ^ 3 = 1 := hinj (by
      rw [map_pow, map_one]
      exact hBs.2 (lambda u) hu)
    rw [← map_pow, hu3, map_one]
  have hcardE : Nat.card E = Nat.card Bs := by
    rw [← hEmap, Subgroup.card_map_of_injective hinj]
  have hcardA : Nat.card A = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hrhoinj, hcardE]
  have hW : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
    obtain ⟨σ, rfl⟩ := hE7
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hlow : 3 ^ 7 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
    Nat.prime_three (by norm_num) hBs hW FrameRoute.exists_elemAbelian_two_coxeterE7
  have hAcard : 3 ^ (Tag.E7.rank - 1) ≤ Nat.card A := by
    rw [hcardA]
    exact (show 3 ^ (Tag.E7.rank - 1) ≤ 3 ^ 7 by norm_num [Tag.rank]).trans hlow
  have hKnot3 : ¬ 3 ∣ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    intro h
    exact (by norm_num : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  obtain ⟨g, hg, hgt⟩ := ExcFramesHalf.bigElemAbelianToralBar_E7_three
    K hKnot3 A hAadj hcomm hexp hAcard
  refine ⟨g, hg, ?_⟩
  intro u hu
  exact hgt (rho u) ⟨u, hu, rfl⟩

end NativeToralSource

theorem exists_original_D_base_frame (hTB : GGTBFixInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hD : GGIsWeylMatrixD M) (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hU : ¬ GGMemberUnitary p Bs L) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized := by
  have hns : ¬ GGSplitLie p L := fun hs =>
    hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inl (Or.inr hD)⟩
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      Nat.card (ggRankOneIn L Bs r) ≠ 6 := by
    intro r hr hrC h6
    exact hSix ⟨hpres, Or.inr (Or.inl hD), r, hr, hrC, h6⟩
  exact NSJoin.exists_orthWeakFrame_L_typeD_of_guard hTB ggU62OuterDiagInput_holds
    hcfg hpres hD hns hU hbig

theorem exists_original_D_base_rankOne_pair (hTB : GGTBFixInput)
    (hL1 : GGSecFiveL1PhanInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hD : GGIsWeylMatrixD M) (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hU : ¬ GGMemberUnitary p Bs L) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized ∧
      ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
        GGIsReflection p r₀ ∧ ggRankOnePerf Bs r₀ =
          ((Φ.Δ.rankOne ⟨0, by have := Φ.hr; omega⟩ ⟨1, by have := Φ.hr; omega⟩).subgroupOf
            (orthDerived Φ.Q)).map Φ.ψ := by
  obtain ⟨Φ, hΦ⟩ := exists_original_D_base_frame hTB hcfg hReg hpres hD hSix hU
  have hns : ¬ GGSplitLie p L := fun hs =>
    hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inl (Or.inr hD)⟩
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      Nat.card (ggRankOneIn L Bs r) ≠ 6 := by
    intro r hr hrC h6
    exact hSix ⟨hpres, Or.inr (Or.inl hD), r, hr, hrC, h6⟩
  exact ⟨Φ, hΦ, Φ.exists_coxRefl_perf_eq_pair hL1 hcfg hns hpres
    (GGIsWeylMatrixAD.le_three (Or.inr hD)) hbig⟩

theorem exists_original_base_frame_of_orthogonal_marking
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs L) :
    ∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  exact OrthTorus.exists_orthWeakFrame_of_marking ggLabelRigidInput_holds hp2 hBs
    hconf.2.1.2.2.2 hmark (ggGamma_L_exists_ne_one hconf)

theorem original_E_base_marking (hTB : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE : GGIsWeylMatrixE M) (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hU : ¬ GGMemberUnitary p Bs L) :
    GGInnerDiagOnLabel
        (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs L ∨
      GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L := by
  have hns : ¬ GGSplitLie p L := fun hs =>
    hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inr hE⟩
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      Nat.card (ggRankOneIn L Bs r) ≠ 6 := by
    intro r hr hrC h6
    exact hSix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrC, h6⟩
  have hsmall := NSJoin.not_innerDiagOnLabel_resGenRestTwo_L_typeE hTB
    ggU62OuterDiagInput_holds hcfg hpres hE hbig
  have hcases : GGInnerDiagOnLabel (fun p lab =>
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) ∨
      ggRowP_ETwE6 p lab ∨
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
      ggRowP_ResGenRestTwo p lab ∨
      (ggRowP_EE7 p lab ∧ lab.n = 1) ∨ ggRowP_EE8 p lab ∨ GGF4ThreeLabel p lab) p Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_
      (ggL_baseLabel_of_nonSplit hcfg hpres hE.le_three hns)
    intro lab hΛ _ hrow
    rcases hrow with hu | hm | ht | ⟨hn, hp3, ho | h7 | h8 | h4⟩
    · by_cases hs : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs.1, Or.inl ⟨hu, hs.2⟩⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hu, hs⟩))
    · by_cases hn : lab.n = 1
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, Or.inr (Or.inr hm)⟩)))
      · exact Or.inl ⟨Or.inr hm, by have := hΛ.1; omega⟩
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, Or.inr (Or.inl ho)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h7, hn⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4.1, hp3, ?_⟩)))))
      rw [hn]
      norm_num
  rcases GGInnerDiagOnLabel.elim_or hcases with h | h
  · exact Or.inl h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact Or.inr h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (hU h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (hsmall h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (not_e7Two_base_marking_of_rankOne_guard hcfg hpres hE.le_three hbig h).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (ggRow_absurd_EE8 ggLabelRigidInput_holds hTB hWA hcfg e hE (Or.inl rfl)
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)) h).elim
  · exact (NSJoin.not_f4Three_of_cfg hcfg hpres hE.le_three h).elim

theorem exists_original_E_base_rankOne_pair_or_twistedE6 (hTB : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hL1 : GGSecFiveL1PhanInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE : GGIsWeylMatrixE M) (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (hU : ¬ GGMemberUnitary p Bs L) :
    (∃ Φ : OrthTorus.OrthWeakFrame p Bs L, Φ.Recognized ∧
      ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
        GGIsReflection p r₀ ∧ ggRankOnePerf Bs r₀ =
          ((Φ.Δ.rankOne ⟨0, by have := Φ.hr; omega⟩ ⟨1, by have := Φ.hr; omega⟩).subgroupOf
            (orthDerived Φ.Q)).map Φ.ψ) ∨
    (∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ ∧
      GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) := by
  rcases original_E_base_marking hTB hWA hcfg hReg hpres hE hSix hU with horth | htw
  · obtain ⟨Φ, hΦ⟩ := exists_original_base_frame_of_orthogonal_marking hcfg horth
    have hns : ¬ GGSplitLie p L := fun hs =>
      hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inr hE⟩
    have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
        Nat.card (ggRankOneIn L Bs r) ≠ 6 := by
      intro r hr hrC h6
      exact hSix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrC, h6⟩
    exact Or.inl ⟨Φ, hΦ, Φ.exists_coxRefl_perf_eq_pair hL1 hcfg hns hpres hE.le_three hbig⟩
  · rcases hE with h6 | h7 | h8
    · exact (ggRow_absurd_TwE6_L_of_E6 ggLabelRigidInput_holds hTB hWA hcfg e h6 htw).elim
    · obtain ⟨σ, hM⟩ := h7
      exact Or.inr ⟨σ, hM, htw⟩
    · exact (ggRow_absurd_TwE6_L_of_E8 hcfg hpres h8 htw).elim

theorem exists_selected_E_member_or_E7_source (hTB : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hARow : ¬ GGSecFivePhanARow p B Bs x L D J)
    (hQTwo : ¬ GGSecFiveQTwoCell p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE : GGIsWeylMatrixE M) (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hψ : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    (∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
      ∃ (t' : StatedLieTag) (n' f' : ℕ) (lambda : (ggU t' n' f').K →* G),
        StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
        lambda.ker ≤ Subgroup.center (ggU t' n' f').K ∧ lambda.range = L ∧
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
          (delta : Fin (ggU t' n' f').D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k delta),
          (lambda.comp model.phi).range = ggRankOnePerf Bs r₀) ∨
    (GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L ∧
      ∃ (q : ℕ), 4 ≤ 2 ^ q ∧ p ∣ 2 ^ q + 1 ∧
        ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ ∧
          ∃ ψ₀ : (ggU .E7 0 q).K →* G,
            GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 0 q).D .E7 0 q ψ₀ ∧
            ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
              GGIsReflection p r₀ ∧
              ∃ (i : Fin (ggU .E7 0 q).D.rank) (u : (ggU .E7 0 q).K),
                (rankOne (ggU .E7 0 q).D.rootGroup i).map
                  (ψ₀.comp (MulAut.conj u).toMonoidHom) = ggRankOnePerf Bs r₀ ∧
                (rankOne (ggU .E7 0 q).D.rootGroup i).map (MulAut.conj u).toMonoidHom ≤
                  (Subgroup.centralizer {x}).comap ψ₀) := by
  classical
  by_cases hU : GGMemberUnitary p Bs L
  · obtain ⟨r₀, hr₀A, hr₀C, d, f', lambda, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩ :=
      exists_selected_unitary_member_of_join hL1 hcfg hReg hpres (Or.inr hE) hSix hU
    exact Or.inl ⟨r₀, hr₀A, hr₀C, .PSU, d, f', lambda, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩
  · rcases exists_original_E_base_rankOne_pair_or_twistedE6 hTB hWA hL1
      hcfg hReg hpres hE hSix hU with ⟨Φ, _hΦ, r₀, hr₀A, hr₀C, _hr₀, hpair⟩ |
      ⟨σ, hM, htw⟩
    · have : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
      obtain ⟨t', lambda, _ht, hadm, hrk, hker, hrange,
        k, hk, hfin, hchar, delta, model, himage⟩ :=
        Φ.exists_nativeSpin_selected_pair (ggRouteCfg_prime hcfg).2
      exact Or.inl ⟨r₀, hr₀A, hr₀C, t', Φ.r, Φ.f, lambda, hadm, hrk, hker, hrange,
        k, hk, hfin, hchar, delta, model, himage.trans hpair.symm⟩
    · exact Or.inr ⟨htw, exists_E7_source_rankOne_at_twistedE6_join_of_marking
        hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hReg hARow hQTwo hpres
        ⟨σ, hM⟩ hSix t n f ψ hψ hJoin htw⟩

theorem ggSecFiveJoinMemberAt_D (hTB : GGTBFixInput) (hL1 : GGSecFiveL1PhanInput) :
    GGSecFiveJoinMemberAt GGIsWeylMatrixD := by
  classical
  intro H _ _ p B Bs x L D J 𝒦 hcfg hReg _hARow _hQTwo ι M e hpres hD hSix
    _t _n _f _ψ _hψ _hJoin
  by_cases hU : GGMemberUnitary p Bs L
  · obtain ⟨r₀, hr₀A, hr₀C, d, f, lambda, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩ :=
      exists_selected_unitary_member_of_join hL1 hcfg hReg hpres (Or.inl hD) hSix hU
    exact ⟨r₀, hr₀A, hr₀C, L, Or.inl rfl, .PSU, d, f, lambda, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩
  · obtain ⟨Φ, _hΦ, r₀, hr₀A, hr₀C, _hr₀, hpair⟩ :=
      exists_original_D_base_rankOne_pair hTB hL1 hcfg hReg hpres hD hSix hU
    have : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
    obtain ⟨t, lambda, _ht, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩ :=
      Φ.exists_nativeSpin_selected_pair (ggRouteCfg_prime hcfg).2
    exact ⟨r₀, hr₀A, hr₀C, L, Or.inl rfl, t, Φ.r, Φ.f, lambda, hadm, hrk, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage.trans hpair.symm⟩

end CFSG.StandardType
