module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinEMarked
public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Core
public import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.E8Pilot

variable {G : Type} [Group G] [Finite G]

theorem exists_rankOne_position_of_marked_E7
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {f : ℕ} (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : Fin 7 ≃ ι)
    (ψ : (ggU .E7 0 f).K →* G)
    (hψ : GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 0 f).D .E7 0 f ψ)
    (hnode : ∀ i, ((e7StdConfig F f hF hf).S.ι i).range.map ψ =
      ggRankOnePerf Bs ((e (M.simple (σ i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M e) :
    ∃ (i : Fin (ggU .E7 0 f).D.rank) (u : (ggU .E7 0 f).K),
      (rankOne (ggU .E7 0 f).D.rootGroup i).map
        (ψ.comp (MulAut.conj u).toMonoidHom) = ggRankOnePerf Bs r := by
  dsimp only [ggU] at *
  obtain ⟨w, j, rfl⟩ := hr
  let i : Fin (CFSG.Blueprint.Chevalley.Tag.rank .E7) := σ.symm j
  let k : Fin (ggU .E7 0 f).D.rank := i
  obtain ⟨v, hv⟩ := exists_e7_stdConfig_rankOne_node (n := 0) hF hf i
  change (rankOne (ggU .E7 0 f).D.rootGroup k).map
    (MulAut.conj v).toMonoidHom = ((e7StdConfig F f hF hf).S.ι i).range at hv
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs := by
    rw [hJoin]
    exact ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  obtain ⟨g, hgG0, -, hg⟩ := mem_ggAutomizer_iff.mp (hA (e w).2)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hψ.2.1.1.symm ▸ hgG0)
  have hcomp : ((MulAut.conj g).toMonoidHom.comp ψ).comp
      (MulAut.conj v).toMonoidHom =
        ψ.comp (MulAut.conj (z * v)).toMonoidHom := by
    ext a
    change g * ψ (v * a * v⁻¹) * g⁻¹ = ψ ((z * v) * a * (z * v)⁻¹)
    simp only [map_mul, map_inv, mul_inv_rev, hz]
    group
  have heq : ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ =
      ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨k, z * v, ?_⟩
  calc (rankOne (ggU .E7 0 f).D.rootGroup k).map
        (ψ.comp (MulAut.conj (z * v)).toMonoidHom)
      = (((rankOne (ggU .E7 0 f).D.rootGroup k).map
          (MulAut.conj v).toMonoidHom).map ψ).map (MulAut.conj g).toMonoidHom := by
            rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    _ = (((e7StdConfig F f hF hf).S.ι i).range.map ψ).map
        (MulAut.conj g).toMonoidHom := by rw [hv]
    _ = (ggRankOnePerf Bs
        ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)).map
        (MulAut.conj g).toMonoidHom := by rw [hnode]; simp only [σ.apply_symm_apply]
    _ = ggRankOnePerf Bs
        ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
          rw [ggRankOnePerf_map_conj hg, heq]

theorem exists_E7_source_rankOne_at_twistedE6_join_of_marking
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (_hARow : ¬ GGSecFivePhanARow p B Bs x L D J)
    (_hQTwo : ¬ GGSecFiveQTwoCell p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (_hψ : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) :
    ∃ (q : ℕ), 4 ≤ 2 ^ q ∧ p ∣ 2 ^ q + 1 ∧
      ∃ (σ : Fin 7 ≃ ι), M = CoxeterMatrix.E₇.reindex σ ∧
        ∃ (ψ₀ : (ggU .E7 0 q).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 0 q).D .E7 0 q ψ₀ ∧
          ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
            GGIsReflection p r₀ ∧
            ∃ (i : Fin (ggU .E7 0 q).D.rank) (u : (ggU .E7 0 q).K),
              (rankOne (ggU .E7 0 q).D.rootGroup i).map
                (ψ₀.comp (MulAut.conj u).toMonoidHom) = ggRankOnePerf Bs r₀ ∧
              (rankOne (ggU .E7 0 q).D.rootGroup i).map (MulAut.conj u).toMonoidHom ≤
                (Subgroup.centralizer {x}).comap ψ₀ := by
  dsimp only [ggU] at *
  have hE : GGIsWeylMatrixE M := Or.inr (Or.inl hE7)
  have hns : ¬ GGSplitLie p L := fun hs =>
    hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inr hE⟩
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hE.le_three
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      Nat.card (ggRankOneIn L Bs r) ≠ 6 := fun r hr hrC h6 =>
    hSix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrC, h6⟩
  have hW : GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs) := by
    by_cases hp3 : p = 3
    · exact ggTwE6Bad_weylOfType hcfg.1
        (hmark.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, hp3, hp3 ▸ h.2⟩)
    · exact ggTwE6Row_weylOfType hcfg.1
        (hmark.mono_label_of_hasLabel fun _ _ _ h => ⟨h.1, h.2, hp3⟩)
  obtain ⟨w, hw⟩ := hW
  let r₀ : MulAut ↥Bs := ((w (CoxeterMatrix.E₆.simple 0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer L Bs := (w (CoxeterMatrix.E₆.simple 0)).2
  have hr₀R : GGIsReflection p r₀ := hw 0
  have hr₀C : r₀ ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg
    (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) hr₀R
  obtain ⟨q, hq4, hpq, hall⟩ := ggSecFiveJoinE_markedTop hL1 hRk1 hGen hOrb hL2 hPair hNbr
    hcfg hReg hpres hE hSix hJoin
  have hq1 : 1 ≤ q := one_le_of_four_le_two_pow hq4
  let F := GaloisField 2 (2 * q)
  have hF : Nat.card F = (2 ^ q) ^ 2 := card_galoisField_two_mul 2 q hq1
  obtain ⟨σ₇, -⟩ := hE7
  have hc7 : Nat.card ι = 7 := by simpa using (Nat.card_congr σ₇).symm
  rcases hall F hF with ⟨σ, -, ψ₀, hψ₀, hnode⟩ | ⟨σ, hM, ψ₀, hψ₀, hnode⟩ |
      ⟨σ, -, ψ₀, hψ₀, hnode⟩
  · have hc6 : Nat.card ι = 6 := by simpa using (Nat.card_congr σ).symm
    omega
  · obtain ⟨i, u, hpos⟩ := exists_rankOne_position_of_marked_E7 hJoin hq1 F hF σ ψ₀ hψ₀
      hnode hr₀C
    have hperfL : ggRankOnePerf Bs r₀ ≤ L := by
      rw [hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl)
        r₀ hr₀A hr₀C]
      exact ggRankOneIn_le L Bs r₀
    have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
      hcfg.1.1.isComponentOf_ggG0_inf.1.trans inf_le_right
    refine ⟨q, hq4, hpq, σ, hM, ψ₀, hψ₀, r₀, hr₀A, hr₀C, hr₀R, i, u, hpos, ?_⟩
    apply Subgroup.map_le_iff_le_comap.mp
    rw [Subgroup.map_map, hpos]
    exact hperfL.trans hLx
  · have hc8 : Nat.card ι = 8 := by simpa using (Nat.card_congr σ).symm
    omega

theorem bstar_le_normalizer_ggG0_of_join
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  have hNK : ∀ K ∈ 𝒦, Bs ≤ Subgroup.normalizer (K : Set G) := by
    intro K hK
    obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
    exact GGDichotomy.le_normalizer_of_innerDiagOn (hcfg.1.2.2.1.2 y K hy)
  intro b hb
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [hJoin]
  simp only [Subgroup.map_sup, Subgroup.map_iSup]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNL hb)]
  congr 1
  apply iSup_congr
  intro K
  apply iSup_congr
  intro hK
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNK K hK hb)

theorem exists_inner_E7_action_of_root_image
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 p B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (i : Fin (Tag.rank .E7))
    (hroot : (rankOne (e7Datum K).rootGroup i).map lambda ≤ L) :
    ∃ Γ : Bs →* MulAut (e7Data_valid.minGroup K),
      (∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹) ∧
      ∃ y : e7Data_valid.minGroup K, y ^ p = 1 ∧
        Γ ⟨x, hcfg.1.1.x_facts.1⟩ = MulAut.conj y := by
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ :=
    center_minGroup_e7_eq_bot
  have hlambdaker : lambda.ker = ⊥ := le_antisymm (by simpa only [hZ] using hker) bot_le
  have hlambdainj : Function.Injective lambda := (MonoidHom.ker_eq_bot_iff lambda).mp hlambdaker
  let G₀ := ggG0 p B x L D J
  let P : e7Data_valid.minGroup K →* G₀ := lambda.codRestrict G₀ (fun z => by
    change lambda z ∈ ggG0 p B x L D J
    rw [← hrange]
    exact ⟨z, rfl⟩)
  have hPinj : Function.Injective P := by
    intro a b h
    exact hlambdainj (congrArg Subtype.val h)
  have hPsurj : Function.Surjective P := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ lambda.range := by
      change z ∈ ggG0 p B x L D J at hz
      simpa only [hrange] using hz
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hz'
    exact ⟨a, Subtype.ext ha⟩
  let E : e7Data_valid.minGroup K ≃* G₀ := MulEquiv.ofBijective P ⟨hPinj, hPsurj⟩
  have hE : ∀ z, ((E z : G₀) : G) = lambda z := fun _ => rfl
  have hN : Bs ≤ Subgroup.normalizer (G₀ : Set G) :=
    bstar_le_normalizer_ggG0_of_join hcfg hJoin
  let Γ : Bs →* MulAut (e7Data_valid.minGroup K) :=
    (MulAut.congr E.symm).toMonoidHom.comp (ggGamma G₀ hN)
  have hΓ : ∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹ := by
    intro b z
    change lambda (E.symm (ggGamma G₀ hN b (E z))) = _
    rw [← hE (E.symm (ggGamma G₀ hN b (E z))), E.apply_symm_apply,
      ggGamma_coe, hE z]
  let xb : Bs := ⟨x, hC.x_facts.1⟩
  have hxb : xb ^ p = 1 := by
    apply Subtype.ext
    change x ^ p = 1
    rw [← hC.orderOf_x]
    exact pow_orderOf_eq_one x
  have hΓp : (Γ xb) ^ p = 1 := by rw [← map_pow, hxb, map_one]
  let θ : e7Data_valid.minGroup K ≃* adjointGroup .E7 K := e7MinEquivAdjoint K
  let β : MulAut (adjointGroup .E7 K) := (MulAut.congr θ) (Γ xb)
  have hβp : β ^ p = 1 := by
    change ((MulAut.congr θ) (Γ xb)) ^ p = 1
    rw [← map_pow, hΓp, map_one]
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hβodd : Odd (orderOf β) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hβp)
  have hmap : (rankOne (e7Datum K).rootGroup i).map θ.toMonoidHom =
      rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i := by
    dsimp only [θ]
    rw [map_e7_rankOne_rootPair]
    change rootPairSL2 .E7 K (Pi.single i 1) =
      rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single i 1)
    rw [rankOneGroup_adjDatum _ (isRoot_single .E7 i)]
    rfl
  have hfix : ∀ z ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i,
      β z = z := by
    intro z hz
    rw [← hmap] at hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have haL : lambda a ∈ L := hroot (Subgroup.mem_map_of_mem lambda ha)
    have haC : lambda a ∈ Subgroup.centralizer ({x} : Set G) :=
      (hC.isComponentOf_ggG0_inf.1.trans inf_le_right) haL
    have hfixa : Γ xb a = a := by
      apply hlambdainj
      rw [hΓ]
      change x * lambda a * x⁻¹ = lambda a
      rw [← Subgroup.mem_centralizer_singleton_iff.mp haC]
      group
    change θ (Γ xb (θ.symm (θ a))) = θ a
    rw [θ.symm_apply_apply, hfixa]
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (CFSG.ComponentClassification.Burgoyne.E2.mem_inner_of_odd_fix_rankOne i hβodd hfix)
  let y := θ.symm z
  have hy : Γ xb = MulAut.conj y := by
    apply (MulAut.congr θ).injective
    change β = (MulAut.congr θ) (MulAut.conj y)
    rw [← hz]
    ext a
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv]
    simp only [y, θ.apply_symm_apply]
  have hyp : y ^ p = 1 := by
    have hconj : MulAut.conj (y ^ p) = 1 := by rw [map_pow, ← hy, hΓp]
    have hc : y ^ p ∈ Subgroup.center (e7Data_valid.minGroup K) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have he := congrArg (fun f : MulAut (e7Data_valid.minGroup K) => f a) hconj
      change y ^ p * a * (y ^ p)⁻¹ = a at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    simpa only [hZ, Subgroup.mem_bot] using hc
  exact ⟨Γ, hΓ, y, hyp, hy⟩

theorem exists_native_E7_centralizer_of_twistedE6_join_of_marking
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hARow : ¬ GGSecFivePhanARow p B Bs x L D J)
    (hQTwo : ¬ GGSecFiveQTwoCell p B Bs x L D J)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 N e)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hψ : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) :
    ∃ q : ℕ, 4 ≤ 2 ^ q ∧ p ∣ 2 ^ q + 1 ∧
      ∃ (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G),
        GGPresentsG0 (ggG0 p B x L D J) (e7Datum (GaloisField 2 q)) .E7 0 q lambda ∧
        ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl N e ∧
          GGIsReflection p r₀ ∧
          ∃ (i : Fin (Tag.rank .E7))
            (Γ : Bs →* MulAut (e7Data_valid.minGroup (GaloisField 2 q)))
            (y : e7Data_valid.minGroup (GaloisField 2 q))
            (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))),
            (rankOne (e7Datum (GaloisField 2 q)).rootGroup i).map lambda =
                ggRankOnePerf Bs r₀ ∧
            (∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹) ∧
            y ^ p = 1 ∧ Γ ⟨x, hcfg.1.1.x_facts.1⟩ = MulAut.conj y ∧
            IsComponentOf M (Subgroup.centralizer {y}) ∧ M.map lambda = L ∧
            rankOne (e7Datum (GaloisField 2 q)).rootGroup i ≤ M ∧
            ∀ b z, z ∈ M → Γ b z ∈ M := by
  obtain ⟨q, hq4, hpq, σ, -, ψ₀, hψ₀, r₀, hr₀A, hr₀C, hr₀R, i₀, u, hpos, -⟩ :=
    exists_E7_source_rankOne_at_twistedE6_join_of_marking hL1 hRk1 hGen hOrb hL2 hPair hNbr
      hcfg hReg hARow hQTwo hpres hE7 hSix t n f ψ hψ hJoin hmark
  let K := GaloisField 2 q
  let U := e7Data_valid.minGroup K
  let j : Fin (Tag.rank .E7) := i₀
  let u₀ : U := u
  let psi : U →* G := ψ₀
  let lambda : U →* G := psi.comp (MulAut.conj u₀).toMonoidHom
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hZ : Subgroup.center U = ⊥ := center_minGroup_e7_eq_bot
  have hpsiKer : psi.ker ≤ Subgroup.center U := hψ₀.2.1.2
  have hpsiKer0 : psi.ker = ⊥ := le_antisymm (by simpa only [hZ] using hpsiKer) bot_le
  have hpsiInj : Function.Injective psi := (MonoidHom.ker_eq_bot_iff psi).mp hpsiKer0
  have hlambdaInj : Function.Injective lambda :=
    hpsiInj.comp (MulAut.conj u₀).injective
  have hlambdaKer : lambda.ker ≤ Subgroup.center U := by
    rw [MonoidHom.ker_eq_bot lambda hlambdaInj]
    exact bot_le
  have hrange : lambda.range = ggG0 p B x L D J := by
    change (psi.comp (MulAut.conj u₀).toMonoidHom).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj u₀).surjective,
      Subgroup.map_top]
    exact hψ₀.2.1.1
  have hPP : GGPresentsG0 (ggG0 p B x L D J) (e7Datum K) .E7 0 q lambda :=
    ⟨hψ₀.1, ⟨hrange, hlambdaKer⟩, hψ₀.2.2⟩
  have hrootEq : (rankOne (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r₀ := by
    change (rankOne (ggU .E7 0 q).D.rootGroup i₀).map
      (ψ₀.comp (MulAut.conj u).toMonoidHom) = _
    exact hpos
  have hE : GGIsWeylMatrixE N := Or.inr (Or.inl hE7)
  have hns : ¬ GGSplitLie p L := fun hs => hReg ⟨𝒦, hcfg, hs, ι, N, e, hpres, Or.inr hE⟩
  have h3 : ∀ i j : ι, i ≠ j → N.M i j ≤ 3 := hE.le_three
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl N e →
      Nat.card (ggRankOneIn L Bs r) ≠ 6 := fun r hr hrC h6 =>
    hSix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrC, h6⟩
  have hrootL : (rankOne (e7Datum K).rootGroup j).map lambda ≤ L := by
    rw [hrootEq, hL1 G p B Bs x L D J 𝒦 hcfg hns ι N e hpres h3 hbig L (Or.inl rfl)
      r₀ hr₀A hr₀C]
    exact ggRankOneIn_le L Bs r₀
  obtain ⟨Γ, hΓ, y, hyp, hΓx⟩ :=
    exists_inner_E7_action_of_root_image hcfg hJoin K lambda hrange hlambdaKer j hrootL
  have hinner : ∀ z : U, x * lambda z * x⁻¹ = lambda (y * z * y⁻¹) := by
    intro z
    have h := hΓ ⟨x, hC.x_facts.1⟩ z
    rw [hΓx] at h
    exact h.symm
  have hCent : ggG0 p B x L D J ⊓ Subgroup.centralizer ({x} : Set G) =
      (Subgroup.centralizer ({y} : Set U)).map lambda := by
    rw [← hrange]
    simpa only [Set.image_singleton] using
      StarFour.inf_centralizer_eq_map_centralizer lambda hlambdaInj ({x} : Set G)
        (fun _ => y) (fun b hb z => by
          have hb' : b = x := Set.mem_singleton_iff.mp hb
          subst b
          exact hinner z)
  have hLcomp : IsComponentOf L ((Subgroup.centralizer ({y} : Set U)).map lambda) := by
    rw [← hCent]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨M, hM₀, hmap⟩ := CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift lambda
    (fun z hz => hlambdaKer (MonoidHom.mem_ker.mpr hz))
    (CFSG.Assembly.isComponentOf_iff_open.mp hLcomp)
  have hM : IsComponentOf M (Subgroup.centralizer ({y} : Set U)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hM₀
  have hMback : ∀ z : U, lambda z ∈ L → z ∈ M := by
    intro z hz
    rw [← hmap] at hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
    exact hlambdaInj haz ▸ ha
  have hRM : rankOne (e7Datum K).rootGroup j ≤ M := by
    intro z hz
    exact hMback z (hrootL (Subgroup.mem_map_of_mem lambda hz))
  have hstable : ∀ b z, z ∈ M → Γ b z ∈ M := by
    intro b z hz
    apply hMback
    rw [hΓ]
    have hzL : lambda z ∈ L := by rw [← hmap]; exact Subgroup.mem_map_of_mem lambda hz
    exact (Subgroup.mem_normalizer_iff.mp
      ((GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1) b.2) _).mp hzL
  exact ⟨q, hq4, hpq, lambda, hPP, r₀, hr₀A, hr₀C, hr₀R, j, Γ, y, M,
    hrootEq, hΓ, hyp, hΓx, hM, hmap, hRM, hstable⟩

end CFSG.StandardType
