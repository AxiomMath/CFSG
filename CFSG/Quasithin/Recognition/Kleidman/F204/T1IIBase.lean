module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CritB2
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalLemmaT
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalLemmaN
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDichZ
public import CFSG.Quasithin.Recognition.Kleidman.F204.CritCases

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

namespace Amal

variable {H M B S : Subgroup G} (hA : Amal H M B S)
include hA

theorem Zv_le_Vn {δ μ : Geo H M} (h : μ ∈ nbrs δ) : Zv μ ≤ Vn δ :=
  le_iSup₂_of_le (f := fun μ (_ : μ ∈ nbrs δ) => Zv μ) μ h le_rfl

theorem isElemAbelian_Vn (hb : 3 ≤ bMin H M) (δ : Geo H M) : IsElemAbelian 2 (Vn δ) := by
  have e : Vn δ = ⨆ μ : {μ : Geo H M // μ ∈ nbrs δ}, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun μ => hA.isElemAbelian_Zv μ.1) (fun μ μ' x hx y hy => ?_)
  have h1 : dist δ μ.1 = 1 := dist_eq_one_iff_adj.mpr μ.2
  have h2 : dist δ μ'.1 = 1 := dist_eq_one_iff_adj.mpr μ'.2
  have h3 := dist_triangle hA.amalgam.gen μ.1 δ μ'.1
  rw [CosetGeom.dist_comm μ.1 δ] at h3
  have h4 := bMin_le_bAt (H := H) (M := M) μ.1
  have hd : dist μ.1 μ'.1 < bAt μ.1 := by omega
  have hxQ : x ∈ Qv μ'.1 := Zv_le_Qv_of_dist_lt hd hx
  exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ'.1 hy).2 x hxQ)

theorem Vn_le_stab {δ δ' : Geo H M} (h : dist δ δ' + 1 = bMin H M) : Vn δ ≤ stab δ' := by
  refine iSup₂_le fun l hl => ?_
  apply hA.Zv_le_stab_of_dist_le
  have h1 : dist δ l = 1 := dist_eq_one_iff_adj.mpr hl
  have h3 := dist_triangle hA.amalgam.gen l δ δ'
  rw [CosetGeom.dist_comm l δ] at h3
  have h4 := bMin_le_bAt (H := H) (M := M) l
  omega

omit hA in
omit [Finite G] in
theorem stab_le_normalizer_Vn' (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Vn δ : Set G) :=
  stab_le_normalizer_Vn δ

end Amal

variable {L1 L2 S D X : Subgroup G}

theorem no_five_Vn (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {e : G} (he : e ∈ stab δ)
    (heC : e ∈ Subgroup.centralizer (Vn δ : Set G)) (he5 : e ^ 5 ∈ Qv δ) : e ∈ Qv δ := by
  by_contra heQ
  have hA := Amal.of_frame F
  obtain ⟨u, hu, -⟩ := exists_nbr_not_fixed F hδ he heQ he5
  have hall : ∀ u' ∈ nbrs δ, Zv u' = Zv u := by
    intro u' hu'
    obtain ⟨g, hg, hgu⟩ := exists_zpow_smul_nbr F hδ he heQ he5 hu hu'
    have hgC : (g : G) ∈ Subgroup.centralizer (Vn δ : Set G) :=
      (Subgroup.zpowers_le.mpr heC) hg
    have hgc : ∀ y ∈ Zv u, y * (g : G) = (g : G) * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hgC y (hA.Zv_le_Vn hu hy)
    have hconj : conjSub (g : G) (Zv u) = Zv u := by
      ext x
      rw [mem_conjSub]
      constructor
      · intro h
        have e1 := hgc _ h
        have : x = (g : G)⁻¹ * x * (g : G) := by
          calc x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
            _ = ((g : G)⁻¹ * x * (g : G)) * (g : G) * (g : G)⁻¹ := by rw [← e1]
            _ = (g : G)⁻¹ * x * (g : G) := by group
        rw [this]; exact h
      · intro h
        have e1 := hgc x h
        have : (g : G)⁻¹ * x * (g : G) = x := by
          calc (g : G)⁻¹ * x * (g : G) = (g : G)⁻¹ * (x * (g : G)) := by group
            _ = (g : G)⁻¹ * ((g : G) * x) := by rw [e1]
            _ = x := by group
        rw [this]; exact h
    rw [← hgu, Zv_smul, hconj]
  have hU : Zv u ≤ stab δ ⊓ stab u :=
    le_inf ((hA.Zv_le_Qv u).trans (hA.Qv_le_stab_of_mem_nbrs
      (show δ ∈ nbrs u from (show (graph _ _ _).Adj δ u from hu).symm)))
      ((hA.Zv_le_Qv u).trans (pCoreOf_le 2 _))
  have hnδ : stab δ ≤ Subgroup.normalizer (Zv u : Set G) := by
    intro h hh
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hh
    have hhu : (⟨h, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • u ∈ nbrs δ := by
      have := (smul_adj (⟨h, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr
        (show (graph _ _ _).Adj δ u from hu)
      rwa [hfix] at this
    have e := Zv_smul (⟨h, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) u
    rw [hall _ hhu] at e
    exact mem_normalizer_of_conjSub_eq e.symm
  have hb := hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj δ u from hu) hU hnδ
    (hA.stab_le_normalizer_Zv u)
  exact hA.Zv_ne_bot u hb

theorem lemmaT_Vn (F : Frame L1 L2 S D X) (hb : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
    {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) {x : G} (hx : x ∈ stab δ)
    (hxQ : x ∉ Qv δ) {k : ℕ} (hxk : x ^ 2 ^ k ∈ Qv δ) :
    4 ≤ (Vn δ ⊓ Subgroup.centralizer {x}).relIndex (Vn δ) :=
  four_le_relIndex_of_no_five F hδ ((Amal.of_frame F).isElemAbelian_Vn hb δ)
    (stab_le_normalizer_Vn δ) (fun _ he heC he5 => no_five_Vn F hδ he heC he5) hx hxQ hxk

abbrev ConfigT1 (L1 L2 S : Subgroup G) : Prop :=
  ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false

theorem t1II_setup (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α) :
    vtype α = true ∧ vtype β = false ∧ vtype α' = false ∧
      Odd (bMin (P1 L1 L2 S) (P2 L1 L2 S)) ∧ 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S) := by
  have hA := Amal.of_frame F
  obtain ⟨hcen, -, hnα, hodd, hvt⟩ := hA.caseII (frame_dichotomy F) hc hII
  have hα : vtype α = true := by
    cases h : vtype α
    · exact absurd ((hT1 α).mpr h) hnα
    · rfl
  have hα' : vtype α' = false := (hT1 α').mp hcen
  have hβ : vtype β = false := by rw [← hvt, hα']
  have h2 := two_le_bMin F
  refine ⟨hα, hβ, hα', hodd, ?_⟩
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem relIndex_le_two_of_le (F : Frame L1 L2 S D X)
    {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) {E C : Subgroup G}
    (hE : E ≤ stab δ) (hE2 : IsElemAbelian 2 E) (hle : E ⊓ Qv δ ≤ C) :
    (E ⊓ C).relIndex E ≤ 2 := by
  have h2 := relIndex_inf_Qv_le_two F hδ hE hE2
  have hle' : E ⊓ Qv δ ≤ E ⊓ C := le_inf inf_le_left hle
  exact (Subgroup.relIndex_le_of_le_left hle' Subgroup.index_ne_zero_of_finite).trans h2

omit [Finite G] in
private theorem sq_mem_of_elem {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E)
    (Q : Subgroup G) : x ^ 2 ^ 1 ∈ Q := by
  rw [pow_one, hE.2 x hx]; exact one_mem Q

section T1II

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem t1II_Vn_le_stab :
    Vn β ≤ stab α' ∧ Vn α' ≤ stab β := by
  have hA := Amal.of_frame F
  refine ⟨hA.Vn_le_stab hc.dist_eq', hA.Vn_le_stab ?_⟩
  rw [CosetGeom.dist_comm]; exact hc.dist_eq'

theorem t1II_exists_z : ∃ z ∈ Zv α, z ∉ Qv α' := by
  by_contra h
  push Not at h
  exact hc.not_le fun z hz => h z hz

theorem t1II_W_inf_not_le : ¬ Vn α' ⊓ Qv β ≤ Qv α := by
  intro hle
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  obtain ⟨z, hz, hzQ⟩ := t1II_exists_z F hT1 hc hII
  have hzα' : z ∈ stab α' := hVβ (hA.Zv_le_Vn (show α ∈ nbrs β from
    (show (graph _ _ _).Adj α β from hc.adj).symm) hz)
  have hT := lemmaT_Vn F hb3 hα' hzα' hzQ (sq_mem_of_elem (hA.isElemAbelian_Zv α) hz _)
  have hW2 : IsElemAbelian 2 (Vn α') := hA.isElemAbelian_Vn hb3 α'
  have hidx : (Vn α' ⊓ Subgroup.centralizer {z}).relIndex (Vn α') ≤ 2 := by
    apply relIndex_le_two_of_le F hβ hWβ hW2
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α hz).2 w (hle hw)
    exact this
  omega

theorem t1II_no_transv {w : G} (hwα : w ∈ stab α) (hw2 : w * w = 1) (hwQ : w ∉ Qv α)
    (hwc : Zv α ⊓ Qv α' ≤ Subgroup.centralizer {w}) : False := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, -⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hαβ : α ∈ nbrs β := (show (graph _ _ _).Adj α β from hc.adj).symm
  have hwsq : ∀ y ∈ Subgroup.zpowers w, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : w ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two]; exact hw2
    rw [this, one_zpow]
  have hfaith : ¬ stab α ≤ Subgroup.centralizer (Zv α : Set G) := by
    intro hle
    apply hwQ
    have hU := hA.le_Qv_of_ZFaithful (hA.ZFaithful_of_bAt (frame_dichotomy F) hc.bAt_eq)
      (Subgroup.zpowers_le.mpr hwα) (isPGroup_two_of_sq hwsq)
      (Subgroup.zpowers_le.mpr (hle hwα))
    exact hU (Subgroup.mem_zpowers w)
  have hQC : Qv α ≤ Subgroup.centralizer (Zv α : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α hy).2 q hq).symm
  have hw2' : w ^ 2 ^ 1 ∈ Qv α := by rw [pow_one, pow_two, hw2]; exact one_mem _
  have hN := four_le_relIndex_A F hα (hA.isElemAbelian_Zv α) (hA.stab_le_normalizer_Zv α)
    hQC hfaith hwα hwQ hw2'
  have hidx : (Zv α ⊓ Subgroup.centralizer {w}).relIndex (Zv α) ≤ 2 :=
    relIndex_le_two_of_le F hα' (fun y hy => hVβ (hA.Zv_le_Vn hαβ hy)) (hA.isElemAbelian_Zv α)
      hwc
  omega

theorem t1II_comm_ne :
    ∃ k ∈ Vn β ⊓ Qv α', ∃ w ∈ Vn α', k * w ≠ w * k := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hαβ : α ∈ nbrs β := (show (graph _ _ _).Adj α β from hc.adj).symm
  by_contra hcomm
  push Not at hcomm
  have hW2 : IsElemAbelian 2 (Vn α') := hA.isElemAbelian_Vn hb3 α'
  have hV2 : IsElemAbelian 2 (Vn β) := hA.isElemAbelian_Vn hb3 β
  by_cases hWQ : Vn α' ≤ Qv β
  ·
    have hWα : Vn α' ≤ stab α := hWQ.trans (hA.Qv_le_stab_of_mem_nbrs hαβ)
    obtain ⟨z, hz, hzQ⟩ := t1II_exists_z F hT1 hc hII
    have hnot : ¬ Vn α' ≤ Qv α := by
      intro hle
      have hzα' : z ∈ stab α' := hVβ (hA.Zv_le_Vn hαβ hz)
      have hT := lemmaT_Vn F hb3 hα' hzα' hzQ (sq_mem_of_elem (hA.isElemAbelian_Zv α) hz _)
      have : Vn α' ⊓ Subgroup.centralizer {z} = Vn α' := by
        apply inf_eq_left.mpr
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α hz).2 w (hle hw)
      rw [this, Subgroup.relIndex_self] at hT
      omega
    obtain ⟨w, hw, hwQ⟩ : ∃ w ∈ Vn α', w ∉ Qv α := by
      by_contra h; push Not at h; exact hnot fun w hw => h w hw
    refine t1II_no_transv F hT1 hc hII (hWα hw) ?_ hwQ ?_
    · rw [← pow_two]; exact hW2.2 w hw
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm y ⟨hA.Zv_le_Vn hαβ hy.1, hy.2⟩ w hw
  ·
    obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ Vn α', x ∉ Qv β := by
      by_contra h; push Not at h; exact hWQ fun w hw => h w hw
    have hT := lemmaT_Vn F hb3 hβ (hWβ hx) hxQ (sq_mem_of_elem hW2 hx _)
    have hidx : (Vn β ⊓ Subgroup.centralizer {x}).relIndex (Vn β) ≤ 2 := by
      apply relIndex_le_two_of_le F hα' hVβ hV2
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm k ⟨hk.1, hk.2⟩ x hx
    omega

theorem t1II_exists_nbr : ∃ μ ∈ nbrs α', ¬ Zv α ⊓ Qv α' ≤ Qv μ := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  have hαβ : α ∈ nbrs β := (show (graph _ _ _).Adj α β from hc.adj).symm
  by_contra h
  push Not at h
  obtain ⟨w, ⟨hwW, hwQβ⟩, hwQα⟩ : ∃ w ∈ Vn α' ⊓ Qv β, w ∉ Qv α := by
    by_contra h'; push Not at h'
    exact t1II_W_inf_not_le F hT1 hc hII fun w hw => h' w hw
  have hW2 : IsElemAbelian 2 (Vn α') := hA.isElemAbelian_Vn hb3 α'
  refine t1II_no_transv F hT1 hc hII (hA.Qv_le_stab_of_mem_nbrs hαβ hwQβ) ?_ hwQα ?_
  · rw [← pow_two]; exact hW2.2 w hwW
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyW : Vn α' ≤ Subgroup.centralizer {y} := by
      refine iSup₂_le fun μ hμ => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hx).2 y (h μ hμ hy)).symm
    exact ((Subgroup.mem_centralizer_singleton_iff.mp (hyW hwW))).symm

end T1II

end CFSG.Quasithin.Kleidman.F204
