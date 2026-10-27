module

public import CFSG.Quasithin.EmptyFaithful.S151XB
public import CFSG.Quasithin.Background.FLc2ML
public import CFSG.Quasithin.Background.FLc2Cases
public import CFSG.Quasithin.Background.FLc2Simple
public import CFSG.Quasithin.Background.FLc2UD
public import CFSG.Quasithin.Background.FLc2NZ
public import CFSG.Quasithin.Background.FLcSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15128ML_holds : Input15128ML := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hns
  have hq := hc.ctx.qtfe
  have hM := hc.ctx.mf
  have hS := hc.ctx.setting
  have h18 := hc.h18
  have hsmall := ce15Small_of_four_or_six hc.h24.one
  have h7 := not_seven_of_four_or_six hc.h24.one
  have hdiag := hS.diagonal hsmall h7
  have hL1520 : IsL1520 T Mc Z₁ L := hc.hL.isL1520 h18.four (hS.pCore_g1_ne_bot hq hM)
  have hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hL1520
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hCZ2 : ∀ x : G, x ∈ L → (x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ↔
      x ∈ Subgroup.centralizer (Z₂ : Set G)) := by
    intro x hx
    have h := congrArg (fun K : Subgroup G => x ∈ K) hdiag.1
    simp only [Subgroup.mem_inf, eq_iff_iff] at h
    constructor
    · intro hxc
      exact (h.1 ⟨hLG hx, hxc⟩).2
    · intro hxc
      exact (h.2 ⟨hLG hx, hxc⟩).2
  have hCZ : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ mZ1516 Mc Z₁ ⊓ L := by
    intro x ⟨hxL, hxZ⟩
    refine ⟨⟨hLG hxL, ?_⟩, hxL⟩
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hq.omegaOneCenter_ne_bot
    have hzmem : (z : G) ∈ quasithinOmegaOneCenter T := z.2
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hHyp := h18.six (z : G) hzmem hz1'
    apply hHyp.centralizer_z_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hxZ (z : G) hzmem).symm
  have hMlne : mZ1516 Mc Z₁ ⊓ L ≠ L := fun h => hc.hL.not_le (by
    calc L = mZ1516 Mc Z₁ ⊓ L := h.symm
      _ ≤ mZ1516 Mc Z₁ := inf_le_left)
  obtain ⟨hU, halt⟩ := hc.h27
  have hLU : L ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) := le_normalizer_conjClosure Z₂ L
  have hZ₂U : Z₂ ≤ uOf1527 Z₂ L := le_conjClosure Z₂ L
  have hULU : uLOf1527 Z₂ L ≤ uOf1527 Z₂ L := by
    unfold uLOf1527
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : l * u⁻¹ * l⁻¹ ∈ uOf1527 Z₂ L := (Subgroup.mem_normalizer_iff.1 (hLU hl) u⁻¹).1
      ((uOf1527 Z₂ L).inv_mem hu)
    have : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (uOf1527 Z₂ L).mul_mem hu h1
  have := hU.1
  have hUc : ∀ a ∈ uOf1527 Z₂ L, ∀ b ∈ uOf1527 Z₂ L, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm ha hb
  have hU2 : ∀ a ∈ uOf1527 Z₂ L, a ^ 2 = 1 := hU.2
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hU
  have hV2 : ∀ w : ↥(uOf1527 Z₂ L), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hU2 w w.2)
  have hSLZ : ∀ s ∈ s1516 T Z₁ ⊓ L, ∀ z ∈ Z₂, s * z * s⁻¹ = z := by
    intro s hs z hz
    have hsC : s ∈ Subgroup.centralizer (Z₂ : Set G) := by
      have : s ∈ T ⊓ Subgroup.centralizer (Z₂ : Set G) := by rw [← hdiag.2]; exact hs.1
      exact this.2
    have := Subgroup.mem_centralizer_iff.1 hsC z hz
    calc s * z * s⁻¹ = (s * z) * s⁻¹ := rfl
      _ = (z * s) * s⁻¹ := by rw [← this]
      _ = z := by group
  have hcommS : ∀ s : G, s ∈ s1516 T Z₁ ⊓ L → ∀ z ∈ Z₂, z * s = s * z := by
    intro s hs z hz
    have := hSLZ s hs z hz
    calc z * s = (s * z * s⁻¹) * s := by rw [this]
      _ = s * z := by group
  have hodd : Odd ((s1516 T Z₁ ⊓ L).relIndex L) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSylL.2.2)
  have hd := FLc.ud_decomp hLU hUc hU2 hodd hZ₂U hSLZ
  have hcz := FLc.centralizer_zU_eq hd hZ₂U hULU
  have hncZ : uLOf1527 Z₂ L ≠ ⊥ →
      ¬ L ≤ Subgroup.centralizer (FLc.projZU Z₂ L (uOf1527 Z₂ L) : Set G) := by
    intro hne hLle
    apply hne
    have hLZ₂ : ∀ l ∈ L, l ∈ Subgroup.centralizer (Z₂ : Set G) := fun l hl =>
      (hcz l hl).2 (hLle hl)
    have hUZ₂ : uOf1527 Z₂ L ≤ Z₂ := by
      refine conjClosure_le fun h hh z hz => ?_
      have := Subgroup.mem_centralizer_iff.1 (hLZ₂ h hh) z hz
      have e : h * z * h⁻¹ = z := by
        calc h * z * h⁻¹ = (h * z) * h⁻¹ := rfl
          _ = (z * h) * h⁻¹ := by rw [← this]
          _ = z := by group
      rw [e]
      exact hz
    unfold uLOf1527
    rw [eq_bot_iff]
    calc ⁅uOf1527 Z₂ L, L⁆ ≤ ⁅Z₂, L⁆ := Subgroup.commutator_mono hUZ₂ le_rfl
      _ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.1 (hLZ₂ l hl) z hz).symm
      _ ≤ ⊥ := le_rfl
  have hML : FLc.MLConcl (autOn L (uOf1527 Z₂ L)) ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)) := by
    rcases halt with ⟨Z, hZ1, -, h⟩ | h | h | ⟨n, hn, k, hk1, -, h⟩
    · exact FLc.ml_case_ext4 hV2 (fun z hz => (hZ1 hz).1) h
    · exact FLc.ml_case_ext5 hV2 h
    · exact absurd ⟨hU, h⟩ hns
    · exact FLc.ml_case_nat hV2 (by omega) hk1 h
  obtain ⟨n, c, ρ, hn3, hcn, hρL, hρR, hULne, hfix⟩ := hML
  have hULne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hULne (by rw [h, Subgroup.bot_subgroupOf])
  let θ : ↥L →* MulAut ↥(uOf1527 Z₂ L) :=
    (conjAct (uOf1527 Z₂ L)).comp (Subgroup.inclusion hLU)
  have hθ : ∀ (l : ↥L) (v : ↥(uOf1527 Z₂ L)),
      (uOf1527 Z₂ L).subtype (θ l v) = (l : G) * (uOf1527 Z₂ L).subtype v * (l : G)⁻¹ := fun l v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (uOf1527 Z₂ L)
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hLU l)) v
  have hθmem : ∀ l : ↥L, θ l ∈ autOn L (uOf1527 Z₂ L) := fun l =>
    Subgroup.mem_map.2 ⟨⟨(l : G), hLU l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hρθ : ∀ l : ↥L, ∃ g, ρ g = θ l := fun l => hρR _ (hθmem l)
  have hθρ : ∀ g, ∃ l : ↥L, θ l = ρ g := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (hρL g)
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, hxg⟩
  have := FLc.isSimpleGroup_SLt hn3
  have hρinj : Function.Injective ρ := by
    refine FLc.injective_of_ne_one ρ ?_
    by_contra hall
    push Not at hall
    apply hULne'
    unfold uLOf1527
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨g, hg⟩ := hρθ ⟨l, hl⟩
    have h1 : θ ⟨l, hl⟩ = 1 := by rw [← hg, hall g]
    have h2 := hθ ⟨l, hl⟩ ⟨u, hu⟩
    rw [h1] at h2
    have h3 : u = l * u * l⁻¹ := h2
    calc l * u = (l * u * l⁻¹) * l := by group
      _ = u * l := by rw [← h3]
  have hZUle : FLc.projZU Z₂ L (uOf1527 Z₂ L) ≤ uLOf1527 Z₂ L := inf_le_right
  have hmap : ((FLc.projZU Z₂ L (uOf1527 Z₂ L)).subgroupOf (uOf1527 Z₂ L)).map
      (uOf1527 Z₂ L).subtype = FLc.projZU Z₂ L (uOf1527 Z₂ L) :=
    Subgroup.map_subgroupOf_eq_of_le (hZUle.trans hULU)
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hc.h26.2 with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 h).2
  have hcentZU : ∀ l ∈ L, l ∈ Subgroup.centralizer (Z₂ : Set G) ↔
      l ∈ Subgroup.centralizer (FLc.projZU Z₂ L (uOf1527 Z₂ L) : Set G) :=
    fun l hl => hcz l hl
  have key := FLc.ml_abstract (uOf1527 Z₂ L).subtype Subtype.val_injective (L := L)
    (SL := s1516 T Z₁ ⊓ L) (Ml := mZ1516 Mc Z₁ ⊓ L) hn3 hcn hSylL θ hθ hsimple ρ hρinj hρθ hθρ
    ((FLc.projZU Z₂ L (uOf1527 Z₂ L)).subgroupOf (uOf1527 Z₂ L))
    (fun g v hv hvf i hi hic => hfix g v
      (Subgroup.mem_subgroupOf.2 (hZUle (Subgroup.mem_subgroupOf.1 hv))) hvf i hi hic)
    (fun s hs v hv => by
      apply Subtype.val_injective
      have hsc : (s : G) ∈ Subgroup.centralizer (FLc.projZU Z₂ L (uOf1527 Z₂ L) : Set G) := by
        refine (hcentZU s s.2).1 ?_
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact hcommS s hs z hz
      have := Subgroup.mem_centralizer_iff.1 hsc (v : G) (Subgroup.mem_subgroupOf.1 hv)
      refine (hθ s v).trans ?_
      show (s : G) * (v : G) * (s : G)⁻¹ = (v : G)
      calc (s : G) * (v : G) * (s : G)⁻¹ = ((v : G) * s) * (s : G)⁻¹ := by rw [this]
        _ = v := by group)
    inf_le_right
    (by
      rw [hmap]
      intro x ⟨hxL, hxC⟩
      exact hCZ ⟨hxL, (hCZ2 x hxL).2 ((hcentZU x hxL).2 hxC)⟩)
    hMlne
    (by
      rw [hmap]
      exact hncZ hULne')
  rw [hmap] at key
  refine ⟨?_, ?_⟩
  · rw [key]
    ext x
    constructor
    · rintro ⟨hxL, hxC⟩
      exact ⟨hxL, (hCZ2 x hxL).2 ((hcentZU x hxL).2 hxC)⟩
    · rintro ⟨hxL, hxC⟩
      exact ⟨hxL, (hcentZU x hxL).1 ((hCZ2 x hxL).1 hxC)⟩
  · apply le_antisymm
    · rw [key]
      exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
    · rw [key]
      refine FLc.normalizer_le_centralizer_of_sylow hSylL ?_ ?_
      · rcases hc.h26.2 with h | h
        · exact FLc.normalizer_inf_le_of_isPSL (by norm_num) h hSylL
        · exact FLc.normalizer_inf_le_of_isPSL (by norm_num) h hSylL
      · intro s hs z hz
        have hsc : s ∈ Subgroup.centralizer (FLc.projZU Z₂ L (uOf1527 Z₂ L) : Set G) :=
          (hcentZU s (hs.2)).1 (by
            rw [Subgroup.mem_centralizer_iff]
            intro z' hz'
            exact hcommS s hs z' hz')
        have := Subgroup.mem_centralizer_iff.1 hsc z hz
        calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [← this]
          _ = z := by group

end CFSG.Quasithin
