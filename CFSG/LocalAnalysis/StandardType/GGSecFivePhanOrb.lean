module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGA2Conj
import CFSG.ClassicalInvolution.Asc77.WP3SCVConn

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

private theorem ggPhanOrbAux_quasisimple_normal_le_center_or_eq_top {G : Type} [Group G]
    (h : CFSG.Assembly.IsQuasisimple G) (N : Subgroup G) [N.Normal] :
    N ≤ Subgroup.center G ∨ N = ⊤ :=
  CFSG.ClassicalInvolution.Asc77.SCV.isQuasisimple_normal_le_center_or_eq_top h N

private theorem ggPhanOrb_exists_le_of_comm {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple ↥L) {ι : Type} (S : ι → Subgroup G) (hSL : ∀ i, S i ≤ L)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a) (hgen : L = ⨆ i, S i) :
    ∃ i, L ≤ S i := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  let T : ι → Subgroup ↥L := fun i => (S i).subgroupOf L
  have hnorm' : ∀ i j, j ≠ i → S j ≤ Subgroup.normalizer (S i : Set G) := by
    intro i j hji
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (S i : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm j i hji x hx y hy).symm
  have hLnorm : ∀ i, L ≤ Subgroup.normalizer (S i : Set G) := by
    intro i
    rw [hgen]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · rw [hji]; exact Subgroup.le_normalizer
    · exact hnorm' i j hji
  have hTi_normal : ∀ i, (T i).Normal := fun i =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSL i)).2 (hLnorm i)
  have hnormal : ∀ i, T i ≤ Subgroup.center ↥L ∨ T i = ⊤ := fun i => by
    haveI := hTi_normal i
    exact ggPhanOrbAux_quasisimple_normal_le_center_or_eq_top hL (T i)
  have hnot : ∀ i, T i ≠ ⊤ := by
    intro i hi
    exact hcon i (Subgroup.subgroupOf_eq_top.mp hi)
  have hle : (⨆ i, T i) ≤ Subgroup.center ↥L :=
    iSup_le fun i => (hnormal i).resolve_right (hnot i)
  have hunion : (⊤ : Subgroup ↥L) = ⨆ i, T i := by
    apply Subgroup.map_injective (Subgroup.subtype_injective L)
    rw [Subgroup.map_iSup]
    have hmap : ∀ i, Subgroup.map L.subtype (T i) = S i := by
      intro i
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hSL i)]
    simp only [hmap]
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hgen
  have hcenter : Subgroup.center ↥L = ⊤ := top_le_iff.mp (hunion.symm ▸ hle)
  haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.subsingleton_iff.mpr hcenter
  haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hL.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  exact hab (Subsingleton.elim a b)

private theorem ggPhanOrb_false_of_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {r : MulAut ↥Bs}
    (hr : GGIsReflection p r) (hLS : L ≤ ggRankOneIn L Bs r) : False := by
  have hLc : L ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    refine le_trans hLS ?_
    rw [ggRankOneIn]
    exact le_trans (ggOTwoPrime_le _) inf_le_right
  have hHc : ggHyperplane Bs r ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.le_centralizer_iff.mp hLc
  have hHle : ggHyperplane Bs r ≤ Bs := by
    rw [ggHyperplane]
    exact Subgroup.map_subtype_le _
  have hHinf : ggHyperplane Bs r ≤ Bs ⊓ Subgroup.centralizer (L : Set G) := le_inf hHle hHc
  have hHcard : Nat.card ↥(ggHyperplane Bs r) ≤ p :=
    le_trans (Subgroup.card_le_of_le hHinf) (GGConfig.card_bstar_centralizer_le hcfg)
  have hrel : (ggHyperplane Bs r).relIndex Bs = p := GGDichotomy.relIndex_ggFixG hr
  have hcardBs : Nat.card Bs ≤ p * p := by
    have h := Subgroup.relIndex_mul_card (ggHyperplane Bs r) Bs
    rw [inf_eq_left.mpr hHle, hrel] at h
    rw [← h]
    exact Nat.mul_le_mul_left p hHcard
  have hcontra : p ^ 4 ≤ p ^ 2 :=
    le_trans (ggConfig_bstar_facts hcfg).2.2.2 (by simpa [pow_two] using hcardBs)
  have hp2 : 2 ≤ p := (ggConfig_bstar_facts hcfg).1.two_le
  have hlt : p ^ 2 < p ^ 4 := by
    calc p ^ 2 = p ^ 2 * 1 := (mul_one _).symm
      _ < p ^ 2 * p ^ 2 :=
          Nat.mul_lt_mul_of_pos_left (by nlinarith [hp2]) (by positivity)
      _ = p ^ 4 := by ring
  exact (not_le.mpr hlt) hcontra

private theorem ggPhanOrbAux_quasisimple_of_cfg {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) : CFSG.Assembly.IsQuasisimple ↥L := by
  obtain ⟨⟨⟨⟨_, _, _, _, _, _, hS, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨_, _, _, hC, _⟩ := hS
  exact hC.2.2

theorem ggPhan_noncomm_reflections_of_gen_pair
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) :
    ∃ r ∈ ggAutomizer L Bs, ∃ r' ∈ ggAutomizer L Bs,
      r ∈ ggCoxRefl M e ∧ r' ∈ ggCoxRefl M e ∧ r * r' ≠ r' * r := by
  classical
  by_contra hcon
  let R : Set (MulAut ↥Bs) := {r | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e}
  have hcomm_all : ∀ r ∈ ggAutomizer L Bs, ∀ r' ∈ ggAutomizer L Bs,
      r ∈ ggCoxRefl M e → r' ∈ ggCoxRefl M e → r * r' = r' * r := by
    intro r hrA r' hr'A hrC hr'C
    by_contra hne
    exact hcon ⟨r, hrA, r', hr'A, hrC, hr'C, hne⟩
  have hgenL :=
    hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns
  have hgenR : L = ⨆ r : R, ggRankOneIn L Bs (r : MulAut ↥Bs) :=
    hgenL.trans (iSup_subtype' (p := fun r => r ∈ R)
      (f := fun r (_ : r ∈ R) => ggRankOneIn L Bs r))
  let S : R → Subgroup G := fun r => ggRankOneIn L Bs (r : MulAut ↥Bs)
  have hSL : ∀ i, S i ≤ L := fun i => ggRankOneIn_le L Bs _
  have hcommR : ∀ i j : R, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a := by
    intro i j hij a ha b hb
    exact ((hPair G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns
        (i : MulAut ↥Bs) i.2.1 i.2.2 (j : MulAut ↥Bs) j.2.1 j.2.2
        (fun h => hij (Subtype.ext h))).1
      (hcomm_all (i : MulAut ↥Bs) i.2.1 (j : MulAut ↥Bs) j.2.1 i.2.2 j.2.2)) a ha b hb
  obtain ⟨r, hLr⟩ := ggPhanOrb_exists_le_of_comm (ggPhanOrbAux_quasisimple_of_cfg hcfg)
    S hSL hcommR hgenR
  exact ggPhanOrb_false_of_le hcfg.1.1
    (ggCoxRefl_isReflection (fun i => hpres.2 i) r.2.2) hLr

theorem ggSecFiveOrbPhanInput_of_gen_pair
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) : GGSecFiveOrbPhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig i j hij
  classical
  obtain ⟨ra, hra, rb, hrb, hraC, hrbC, hnc⟩ :=
    ggPhan_noncomm_reflections_of_gen_pair hGen hPair hcfg hns hpres hle3 hbig
  obtain ⟨w₁, i₁, hw₁⟩ := hraC
  obtain ⟨w₂, i₂, hw₂⟩ := hrbC
  have hraC : ra ∈ ggCoxRefl M e := ⟨w₁, i₁, hw₁⟩
  have hrbC : rb ∈ ggCoxRefl M e := ⟨w₂, i₂, hw₂⟩
  let t₁ : M.Group := w₁ * M.simple i₁ * w₁⁻¹
  let t₂ : M.Group := w₂ * M.simple i₂ * w₂⁻¹
  have hra_e : ra = ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₁
  have hrb_e : rb = ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₂
  have hra_sq : ra * ra = 1 :=
    (by simpa [pow_two] using (ggCoxRefl_isReflection (fun i => hpres.2 i) hraC).1)
  have hrb_sq : rb * rb = 1 :=
    (by simpa [pow_two] using (ggCoxRefl_isReflection (fun i => hpres.2 i) hrbC).1)
  have hne : t₁ ≠ t₂ := by
    intro ht12
    apply hnc
    rw [hra_e, hrb_e, ht12]
  have hord : (t₁ * t₂) ^ 3 = 1 := by
    rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hraC hrbC with h2 | h3
    · exfalso
      apply hnc
      have h2' : (ra * rb) * (ra * rb) = 1 := by simpa [pow_two] using h2
      have h1 : ra * rb = (ra * rb)⁻¹ := (inv_eq_of_mul_eq_one_right h2').symm
      rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hra_sq,
        inv_eq_of_mul_eq_one_right hrb_sq]
    · have hra_rb_e : ra * rb =
          ((e (t₁ * t₂) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        rw [hra_e, hrb_e]
        exact (congrArg Subtype.val (map_mul e t₁ t₂)).symm
      have h1 : ((e ((t₁ * t₂) ^ 3) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = 1 := by
        have h2 : (ra * rb) ^ 3 =
            ((e ((t₁ * t₂) ^ 3) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
          rw [hra_rb_e]
          exact (congrArg Subtype.val (map_pow e (t₁ * t₂) 3)).symm
        rw [← h2]
        exact h3
      have h3' : e ((t₁ * t₂) ^ 3) = 1 := Subtype.coe_injective (by simpa using h1)
      exact e.injective (by rw [h3', map_one])
  obtain ⟨w, hw1, hw2⟩ :=
    ggA2_conj hpres.1 hle3 ⟨w₁, i₁, rfl⟩ ⟨w₂, i₂, rfl⟩ hne hord hij
  refine ⟨w, L, Or.inl rfl, ?_, ?_⟩
  · have h : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw1]
    rw [h, ← hra_e]
    exact hra
  · have h : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw2]
    rw [h, ← hrb_e]
    exact hrb

end CFSG.StandardType

end
