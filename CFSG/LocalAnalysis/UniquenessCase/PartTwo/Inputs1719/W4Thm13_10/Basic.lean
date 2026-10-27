module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Quot
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D4
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem component_eq_or_of_le_sup {W : Type} [CommGroup W] [Finite W]
    {Y L K M : Subgroup (MulAut W)} (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (hM : IsComponentOf M Y) (hMX : M ≤ L ⊔ K) : M = L ∨ M = K := by
  rcases eq_or_commute_of_isComponentOf hM hcL with h1 | h1
  · exact Or.inl h1
  rcases eq_or_commute_of_isComponentOf hM hcK with h2 | h2
  · exact Or.inr h2
  exfalso
  have hMcomm : ∀ m ∈ M, ∀ x ∈ (L ⊔ K : Subgroup (MulAut W)), m * x = x * m := by
    intro m hm x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · exact h1 m hm x hx
        · exact h2 m hm x hx
    | one => simp
    | mul x y _ _ ihx ihy =>
        calc m * (x * y) = m * x * y := (mul_assoc _ _ _).symm
          _ = x * m * y := by rw [ihx]
          _ = x * (m * y) := mul_assoc _ _ _
          _ = x * (y * m) := by rw [ihy]
          _ = x * y * m := (mul_assoc _ _ _).symm
    | inv x _ ih =>
        have h' : x⁻¹ * m = m * x⁻¹ := by
          calc x⁻¹ * m = x⁻¹ * (m * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * m) * x⁻¹ := by rw [ih]
            _ = m * x⁻¹ := by group
        exact h'.symm
  have hMabel : IsMulCommutative ↥M := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : MulAut W) ∈ L ⊔ K := hMX b.2
    exact hMcomm a.1 a.2 b.1 hb
  have hq : CFSG.Open.IsQuasisimple ↥M := hM.2.2
  have hbot : commutator ↥M = ⊥ := (commutator_eq_bot_iff (G := ↥M)).mpr hMabel
  haveI : _root_.IsSimpleGroup (↥M ⧸ Subgroup.center ↥M) := hq.2
  haveI : Nontrivial ↥M :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥M)).nontrivial
  have htopbot : (⊤ : Subgroup ↥M) = ⊥ := by rw [← hq.1, hbot]
  exact top_ne_bot htopbot

theorem w4Thm13_10_dichotomy {W : Type} [CommGroup W] [Finite W]
    {Y L K : Subgroup (MulAut W)} (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (hne : L ≠ K) (hXn : ((L ⊔ K).subgroupOf Y).Normal) :
    (∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) ∨
      ((L.subgroupOf Y).Normal ∧ (K.subgroupOf Y).Normal) := by
  have hXle : L ⊔ K ≤ Y := sup_le hcL.1 hcK.1
  have hnormX : Y ≤ Subgroup.normalizer ((L ⊔ K : Subgroup (MulAut W)) : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp hXn
  have hXmap : ∀ g ∈ Y, (L ⊔ K).map (MulAut.conj g).toMonoidHom = L ⊔ K := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX hg)
  have hLX : L ≤ L ⊔ K := le_sup_left
  have hKX : K ≤ L ⊔ K := le_sup_right
  by_cases hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom
  · exact Or.inl hsw
  · right
    have hconjL : ∀ g ∈ Y, IsComponentOf (L.map (MulAut.conj g).toMonoidHom) Y :=
      fun g hg => isComponentOf_map_conj_of_mem hcL hg
    have hconjK : ∀ g ∈ Y, IsComponentOf (K.map (MulAut.conj g).toMonoidHom) Y :=
      fun g hg => isComponentOf_map_conj_of_mem hcK hg
    have hLX' : ∀ g ∈ Y, L.map (MulAut.conj g).toMonoidHom ≤ L ⊔ K := by
      intro g hg
      have hle : L.map (MulAut.conj g).toMonoidHom ≤
          (L ⊔ K).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hLX
      rwa [hXmap g hg] at hle
    have hKX' : ∀ g ∈ Y, K.map (MulAut.conj g).toMonoidHom ≤ L ⊔ K := by
      intro g hg
      have hle : K.map (MulAut.conj g).toMonoidHom ≤
          (L ⊔ K).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKX
      rwa [hXmap g hg] at hle
    have hLnorm : ∀ g ∈ Y, L.map (MulAut.conj g).toMonoidHom = L := by
      intro g hg
      rcases component_eq_or_of_le_sup hcL hcK (hconjL g hg) (hLX' g hg) with h | h
      · exact h
      · exact absurd ⟨g, hg, h.symm⟩ hsw
    have hKnorm : ∀ g ∈ Y, K.map (MulAut.conj g).toMonoidHom = K := by
      intro g hg
      rcases component_eq_or_of_le_sup hcL hcK (hconjK g hg) (hKX' g hg) with h | h
      · exfalso
        have h2 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
        have hcomp : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
            MonoidHom.id (MulAut W) := by
          ext x
          simp [MulAut.conj_apply]
        rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h2
        rw [hLnorm g⁻¹ (Y.inv_mem hg)] at h2
        exact hne h2.symm
      · exact h
    constructor
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcL.1]
      intro y hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hLnorm y hy
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcK.1]
      intro y hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hKnorm y hy

theorem map_conj_cases {W : Type} [CommGroup W] [Finite W]
    {Y L K : Subgroup (MulAut W)} (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (hne : L ≠ K) (hXn : ((L ⊔ K).subgroupOf Y).Normal) {y : MulAut W} (hy : y ∈ Y) :
    (L.map (MulAut.conj y).toMonoidHom = L ∧ K.map (MulAut.conj y).toMonoidHom = K) ∨
      (L.map (MulAut.conj y).toMonoidHom = K ∧ K.map (MulAut.conj y).toMonoidHom = L) := by
  have hXle : L ⊔ K ≤ Y := sup_le hcL.1 hcK.1
  have hnormX : Y ≤ Subgroup.normalizer ((L ⊔ K : Subgroup (MulAut W)) : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp hXn
  have hXmap : (L ⊔ K).map (MulAut.conj y).toMonoidHom = L ⊔ K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX hy)
  have hLcomp : IsComponentOf (L.map (MulAut.conj y).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hcL hy
  have hLle : L.map (MulAut.conj y).toMonoidHom ≤ L ⊔ K := by
    have hle : L.map (MulAut.conj y).toMonoidHom ≤
        (L ⊔ K).map (MulAut.conj y).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) le_sup_left
    rwa [hXmap] at hle
  have hKcomp : IsComponentOf (K.map (MulAut.conj y).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hcK hy
  have hKle : K.map (MulAut.conj y).toMonoidHom ≤ L ⊔ K := by
    have hle : K.map (MulAut.conj y).toMonoidHom ≤
        (L ⊔ K).map (MulAut.conj y).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) le_sup_right
    rwa [hXmap] at hle
  rcases component_eq_or_of_le_sup hcL hcK hLcomp hLle with h1 | h1
  · rcases component_eq_or_of_le_sup hcL hcK hKcomp hKle with h2 | h2
    · exfalso
      apply hne
      exact Subgroup.map_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective (h1.trans h2.symm)
    · exact Or.inl ⟨h1, h2⟩
  · rcases component_eq_or_of_le_sup hcL hcK hKcomp hKle with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      apply hne
      exact Subgroup.map_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective (h1.trans h2.symm)

theorem dMinDeg_eq_four_of_isAlt_five {X : Type} [Group X] (hX : IsAlt X 5) :
    dMinDeg X = 4 := by
  obtain ⟨e⟩ := hX
  obtain ⟨e'⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel
    (CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e)
  have := CFSG.LocalAnalysis.WeakClosure81.dMinDeg_eq_of_mulEquiv_sl2 (n := 2) (by norm_num)
    (e'.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 2)))
  simpa using this

theorem commSub_le_fixV_zpowers_of_commute {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {N : Subgroup (MulAut W)} {t : MulAut W}
    (hc : ∀ x ∈ N, t * x = x * t) (htd : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥N) :
    commSub (⊤ : Subgroup W) N ≤ fixV (Subgroup.zpowers t) := by
  have hstab : StableUnder N (fixV (Subgroup.zpowers t)) := by
    refine stableUnder_fixV ?_
    intro y hy h hh
    have hyt : MulAut.conj y t = t := by
      rw [MulAut.conj_apply]
      calc y * t * y⁻¹ = t * y * y⁻¹ := by rw [(hc y hy).symm]
        _ = t := by group
    have hmap : (Subgroup.zpowers t).map (MulAut.conj y).toMonoidHom =
        Subgroup.zpowers t := by
      rw [MonoidHom.map_zpowers]
      rw [show (MulAut.conj y).toMonoidHom t = t from hyt]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hh
  have hrk : rk ↥(⊤ : Subgroup W) <
      rk ↥(fixV (Subgroup.zpowers t)) + dMinDeg ↥N := by
    rw [CFSG.Quasithin.rk_top]
    have h := CFSG.Quasithin.rk_add_rkIdx (fixV (Subgroup.zpowers t))
    omega
  exact commSub_le_of_rk_lt_dMinDeg hW (U := fixV (Subgroup.zpowers t)) (S := ⊤) le_top
    (fun _ _ _ _ => Subgroup.mem_top _) hstab hrk

theorem commSub_top_eq_top_of_normal {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hnL : (L.subgroupOf Y).Normal) :
    commSub (⊤ : Subgroup W) L = ⊤ := by
  have hnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcL.1).mp hnL
  have hLmap : ∀ g ∈ Y, L.map (MulAut.conj g).toMonoidHom = L := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm hg)
  have hH : L = ⨆ X ∈ conjSet L Y, X := by
    rw [iSup_conjSet_eq_biSup_conj]
    refine le_antisymm ?_ ?_
    · have h1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
        rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
          ext x
          simp]
        exact Subgroup.map_id L
      calc L = L.map (MulAut.conj (1 : MulAut W)).toMonoidHom := h1.symm
        _ ≤ ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom :=
          le_iSup₂_of_le 1 Y.one_mem le_rfl
    · exact iSup₂_le fun g hg => (hLmap g hg).le
  have htop := commV_eq_top hW hO2 hB hcL hH
  rwa [commV_eq_commSub] at htop

theorem commSub_le_of_isSimpleGroup {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    (hK : IsSimpleGroup ↥K) {C : Subgroup W} (hKC : K ≤ stabSub C) {c : MulAut W}
    (hcK : c ∈ K) (hc1 : c ≠ 1) (hc : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤ C) :
    commSub (⊤ : Subgroup W) K ≤ C := by
  haveI : IsSimpleGroup ↥K := hK
  let φ : ↥K →* MulAut (W ⧸ C) := (quotHom C).comp (Subgroup.inclusion hKC)
  have hc_mem_cent : c ∈ centQuot C := by
    rw [mem_centQuot]
    intro v
    exact hc (Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, v, Subgroup.mem_top v, rfl⟩)
  have hc_ker : (⟨c, hcK⟩ : ↥K) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have hgker : (⟨c, hKC hcK⟩ : ↥(stabSub C)) ∈ (quotHom C).ker := by
      rw [ker_quotHom, Subgroup.mem_subgroupOf]
      exact hc_mem_cent
    exact MonoidHom.mem_ker.mp hgker
  have hker_ne : φ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot] at hc_ker
    exact hc1 (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hc_ker))
  have htop : φ.ker = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top φ.ker).resolve_left hker_ne
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, v, -, rfl⟩
  have hk_ker : (⟨k, hk⟩ : ↥K) ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top _
  have hquot : quotHom C ⟨k, hKC hk⟩ = 1 := MonoidHom.mem_ker.mp hk_ker
  have hk_cent : k ∈ centQuot C := by
    have hmem : (⟨k, hKC hk⟩ : ↥(stabSub C)) ∈ (quotHom C).ker :=
      MonoidHom.mem_ker.mpr hquot
    rw [ker_quotHom, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  exact (mem_centQuot.mp hk_cent) v

theorem eq_one_of_commSub_le_fixV {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (hX : commSub (⊤ : Subgroup W) X = ⊤) {c : MulAut W}
    (hcX : ∀ x ∈ X, c * x = x * c)
    (hc : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤ fixV X) : c = 1 := by
  have hcomm : ⁅Subgroup.zpowers c, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
      Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcX x hx).symm
  have h2 : commSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers c)) X =
      commSub (⊤ : Subgroup W) (Subgroup.zpowers c) := by
    have h := s13_commSub_comm (Subgroup.zpowers c) X hcomm (⊤ : Subgroup W)
    rwa [hX] at h
  have h3 : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) = ⊥ := by
    rw [← h2]
    exact commSub_eq_bot_iff.mpr hc
  have htop : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers c) := commSub_eq_bot_iff.mp h3
  have hfix : fixV (Subgroup.zpowers c) = ⊤ := top_le_iff.mp htop
  ext v
  have hv : v ∈ fixV (Subgroup.zpowers c) := by rw [hfix]; exact Subgroup.mem_top v
  simpa using mem_fixV.mp hv c (Subgroup.mem_zpowers c)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
