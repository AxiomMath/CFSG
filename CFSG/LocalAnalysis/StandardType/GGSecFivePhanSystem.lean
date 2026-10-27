module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.RankThree.PartOne.CTP.PhanBridge
import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
import CFSG.ClassicalInvolution.Models.LinearPairs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

open scoped MatrixGroups

private theorem ggPhan_conj_presentation_simple {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (w s : M.Group) :
    ((e w⁻¹ : ↥A) : MulAut ↥Bs) * ((e (w * s * w⁻¹) : ↥A) : MulAut ↥Bs) *
      ((e w⁻¹ : ↥A) : MulAut ↥Bs)⁻¹ = ((e s : ↥A) : MulAut ↥Bs) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

theorem ggSecFivePhanSystem_of_prim
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) :
    ∃ f : ℕ, 4 ≤ 2 ^ f ∧ p ∣ 2 ^ f + 1 ∧
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ f) ^ 2 →
        (∀ i : ι, Nonempty (Su K 2 f 2 ≃*
          ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))) ∧
        (∀ i j : ι, i ≠ j → M.M i j = 2 →
          ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
          ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            a * b = b * a) ∧
        (∀ i j : ι, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
          (ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
          (ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))) ∧
        ⨆ i, ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
          L ⊔ ⨆ K ∈ 𝒦, K := by
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hsl : GGSimplyLaced M := hconn.1
  have hnsX : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X := by
    intro X hX
    rcases hX with hXL | hK
    · rw [hXL]
      exact hns
    · exact hNbr G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hK
  have hgenX : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
      X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
        ggRankOneIn X Bs r :=
    fun X hX => hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX (hnsX X hX)
  have hL1X : ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
      ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
    fun X hX => hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX
  obtain ⟨r₀, hr₀A, hr₀C⟩ : ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e := by
    by_contra hne
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r := hgenX L (Or.inl rfl)
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd ⟨r, hr.1, hr.2⟩ hne
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, ⟨n₀, hn₀L, hn₀N, hn₀r⟩, -, hpF, -⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C
  letI : Field F := hF
  letI : Finite F := hFfin
  haveI : CharP F 2 := hchar
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hFcard : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hL1r₀ : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ := hL1X L (Or.inl rfl) r₀ hr₀A hr₀C
  have hn₀S : n₀ ∈ ggRankOnePerf Bs r₀ := hL1r₀ ▸ hn₀L
  have hcard₀ : Nat.card (ggRankOnePerf Bs r₀) = Nat.card SL(2, F) := by
    rw [hL1r₀, ← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hsimple : ∀ i : ι, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = a * r₀ * a⁻¹ :=
    fun i => ggSimple_eq_conj_of_mem_ggCoxRefl e hconn hr₀C i
  have hN : ∀ i : ι, ∃ n ∈ ggRankOnePerf Bs
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : ↥Bs) : G) =
        n * b * n⁻¹ := by
    intro i
    obtain ⟨a, haA, hai⟩ := hsimple i
    obtain ⟨g, -, -, -, hnS, hnN, hnr⟩ := ggWeylElt_conj (hAH haA) hn₀S hn₀N hn₀r
    exact ⟨g * n₀ * g⁻¹, by rw [hai]; exact hnS, hnN, by rw [hai]; exact hnr⟩
  have hcardC : ∀ r ∈ ggCoxRefl M e, Nat.card (ggRankOnePerf Bs r) = Nat.card SL(2, F) := by
    intro r hr
    obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hr
    rw [hra, (ggRankOnePerf_conj_card_le (hAH haA) r₀).1, hcard₀]
  have hiso : ∀ i : ι, Nonempty (SL(2, F) ≃*
      ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
    intro i
    obtain ⟨a, haA, hai⟩ := hsimple i
    obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (hAH haA)
    have hmap : (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom =
        ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
      rw [hai]
      exact ggRankOnePerf_map_conj hg r₀
    have e1 : SL(2, F) ≃* ggRankOnePerf Bs r₀ :=
      (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr (hθrange.trans hL1r₀.symm))
    have e2 : ggRankOnePerf Bs r₀ ≃* (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom :=
      (ggRankOnePerf Bs r₀).equivMapOfInjective _ (MulAut.conj g).injective
    exact ⟨(e1.trans e2).trans (MulEquiv.subgroupCongr hmap)⟩
  have hm4 : 4 ≤ 2 ^ (m : ℕ) := by
    have h6 : Nat.card (ggRankOneIn L Bs r₀) ≠ 6 := hbig r₀ hr₀A hr₀C
    rw [← hL1r₀, hcard₀, ggSL2_card F, hFcard] at h6
    by_contra hlt
    have hm1 : (m : ℕ) = 1 := by
      have hpos : 1 ≤ (m : ℕ) := m.pos
      by_contra hne
      have h2 : 2 ≤ (m : ℕ) := by omega
      have : 2 ^ 2 ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
      omega
    rw [hm1] at h6
    norm_num at h6
  refine ⟨m, hm4, hFcard ▸ hpF hns, fun K _ _ _ hK => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i
    obtain ⟨φ⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK hFcard
    obtain ⟨ψ⟩ := hiso i
    exact ⟨φ.trans ψ⟩
  · intro i j hij hM2
    by_cases hO : GGOrbPair L Bs 𝒦 M e i j
    · obtain ⟨w, X, hX, hrX, hr'X⟩ := hO
      have hrC : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
          ggCoxRefl M e := ⟨w, i, rfl⟩
      have hr'C : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
          ggCoxRefl M e := ⟨w, j, rfl⟩
      have hne := ggCoxConj_ne e (ggSimplyLaced_simple_injective hsl) w hij
      have hcomm := ggCoxConj_comm e w (ggSimplyLaced_simple_comm hM2)
      have h1 := (hPair G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX (hnsX X hX) _ hrX
        hrC _ hr'X hr'C hne).1 hcomm
      refine ggRankOnePerf_comm_of_conj_pair hAH e w i j ?_
      intro a ha b hb
      rw [hL1X X hX _ hrX hrC] at ha
      rw [hL1X X hX _ hr'X hr'C] at hb
      exact h1 a ha b hb
    · exact hL2 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig i j hij hM2 hO
  · intro i j hM3
    have hij : i ≠ j := by
      rintro rfl
      have h1 := M.diagonal i
      omega
    obtain ⟨w, X, hX, hrX, hr'X⟩ :=
      hOrb G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig i j hM3
    have hrC : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggCoxRefl M e := ⟨w, i, rfl⟩
    have hr'C : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggCoxRefl M e := ⟨w, j, rfl⟩
    have hne := ggCoxConj_ne e (ggSimplyLaced_simple_injective hsl) w hij
    have hnc := ggCoxConj_ne_comm e w (ggSimplyLaced_simple_noncomm hsl hM3)
    have hcardX : Nat.card (ggRankOneIn X Bs
        ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) =
        2 ^ (m : ℕ) * ((2 ^ (m : ℕ)) ^ 2 - 1) := by
      rw [← hL1X X hX _ hrX hrC, hcardC _ hrC, ggSL2_card F, hFcard]
    obtain ⟨W, hW⟩ := (hPair G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX (hnsX X hX) _
      hrX hrC _ hr'X hr'C hne).2 hnc K m hK hcardX
    rw [← hL1X X hX _ hrX hrC, ← hL1X X hX _ hr'X hr'C] at hW
    obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp
      (hAH ((e w⁻¹ : ↥(ggAutomizerJoin L Bs 𝒦))).2)
    have hthis := CFSG.ClassicalInvolution.Models.unitaryBlockStandardPair_map hW
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rw [ggRankOnePerf_map_conj hg, ggRankOnePerf_map_conj hg,
      ggPhan_conj_presentation_simple e w (M.simple i),
      ggPhan_conj_presentation_simple e w (M.simple j)] at hthis
    exact ⟨_, hthis⟩
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨a, haA, hai⟩ := hsimple i
      rw [hai]
      refine (ggRankOnePerf_conj_card_le (hAH haA) r₀).2 ?_
      rw [hL1r₀]
      exact (ggRankOneIn_le L Bs r₀).trans le_sup_left
    · refine sup_le ?_ (iSup₂_le fun K hK => ?_)
      · exact ggLe_iSup_ggRankOnePerf_of_gen e hN (hgenX L (Or.inl rfl)) (hL1X L (Or.inl rfl))
      · exact ggLe_iSup_ggRankOnePerf_of_gen e hN (hgenX K (Or.inr hK)) (hL1X K (Or.inr hK))

end CFSG.StandardType

end
