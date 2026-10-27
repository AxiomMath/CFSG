module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A2Set
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameDef
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6fl_ofFn_smul (k : ℤ) (α : Fin Tag.E6.rank → ℤ) :
    List.ofFn (k • α) = smulL k (List.ofFn α) := by
  apply List.ext_getElem
  · simp [smulL]
  · intro i h1 h2
    simp [smulL]

theorem e6fl_addL_len {a b : List ℤ} (ha : a.length = 6) (hb : b.length = 6) :
    (tcAddL a b).length = 6 := by
  simp [tcAddL, ha, hb]

theorem e6fl_smulL_len (k : ℤ) {a : List ℤ} (ha : a.length = 6) :
    (smulL k a).length = 6 := by
  simp [smulL, ha]

theorem e6fl_ofL_addL {a b : List ℤ} (ha : a.length = 6) (hb : b.length = 6) :
    tcOfL (tcAddL a b) = tcOfL a + tcOfL b := by
  have h : tcAddL a b = List.ofFn (tcOfL a + tcOfL b) := by
    rw [ofFn_add, ofFn_ofL ha, ofFn_ofL hb]
  rw [h, tcOfL_ofFn]

theorem e6fl_ofL_smulL (k : ℤ) {a : List ℤ} (ha : a.length = 6) :
    tcOfL (smulL k a) = k • tcOfL a := by
  have h : smulL k a = List.ofFn (k • tcOfL a) := by
    rw [e6fl_ofFn_smul, ofFn_ofL ha]
  rw [h, tcOfL_ofFn]

theorem e6fl_list5 (c : List ℤ) (hc : c.length = 5) :
    ∃ c0 c1 c2 c3 c4 : ℤ, c = [c0, c1, c2, c3, c4] := by
  rcases c with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨c0, c1, c2, c3, c4, rfl⟩
    | (simp at hc; done)
    | (simp at hc; omega)

theorem e6fl_comb5_len {c : List ℤ} (hc : c.length = 5) {d₀ d₁ d₂ d₃ d₄ : List ℤ}
    (h₀ : d₀.length = 6) (h₁ : d₁.length = 6) (h₂ : d₂.length = 6) (h₃ : d₃.length = 6)
    (h₄ : d₄.length = 6) : (tcComb5 c d₀ d₁ d₂ d₃ d₄).length = 6 := by
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := e6fl_list5 c hc
  simp only [tcComb5]
  exact e6fl_addL_len (e6fl_addL_len (e6fl_addL_len (e6fl_addL_len (e6fl_smulL_len c0 h₀)
    (e6fl_smulL_len c1 h₁)) (e6fl_smulL_len c2 h₂)) (e6fl_smulL_len c3 h₃)) (e6fl_smulL_len c4 h₄)

theorem e6fl_ofL_comb5 (c0 c1 c2 c3 c4 : ℤ) {d₀ d₁ d₂ d₃ d₄ : List ℤ} (h₀ : d₀.length = 6)
    (h₁ : d₁.length = 6) (h₂ : d₂.length = 6) (h₃ : d₃.length = 6) (h₄ : d₄.length = 6) :
    tcOfL (tcComb5 [c0, c1, c2, c3, c4] d₀ d₁ d₂ d₃ d₄) =
      c0 • tcOfL d₀ + c1 • tcOfL d₁ + c2 • tcOfL d₂ + c3 • tcOfL d₃ + c4 • tcOfL d₄ := by
  have e0 : (smulL c0 d₀).length = 6 := e6fl_smulL_len c0 h₀
  have e1 : (smulL c1 d₁).length = 6 := e6fl_smulL_len c1 h₁
  have e2 : (smulL c2 d₂).length = 6 := e6fl_smulL_len c2 h₂
  have e3 : (smulL c3 d₃).length = 6 := e6fl_smulL_len c3 h₃
  have e4 : (smulL c4 d₄).length = 6 := e6fl_smulL_len c4 h₄
  have f1 : (tcAddL (smulL c0 d₀) (smulL c1 d₁)).length = 6 := e6fl_addL_len e0 e1
  have f2 : (tcAddL (tcAddL (smulL c0 d₀) (smulL c1 d₁)) (smulL c2 d₂)).length = 6 :=
    e6fl_addL_len f1 e2
  have f3 : (tcAddL (tcAddL (tcAddL (smulL c0 d₀) (smulL c1 d₁)) (smulL c2 d₂))
      (smulL c3 d₃)).length = 6 := e6fl_addL_len f2 e3
  simp only [tcComb5]
  rw [e6fl_ofL_addL f3 e4, e6fl_ofL_addL f2 e3, e6fl_ofL_addL f1 e2, e6fl_ofL_addL e0 e1,
    e6fl_ofL_smulL c0 h₀, e6fl_ofL_smulL c1 h₁, e6fl_ofL_smulL c2 h₂, e6fl_ofL_smulL c3 h₃,
    e6fl_ofL_smulL c4 h₄]

theorem e6fl_chainVec_eq (c0 c1 c2 c3 c4 : ℤ) {δ₀ δ₁ δ₂ δ₃ δ₄ : List ℤ} (h₀ : δ₀.length = 6)
    (h₁ : δ₁.length = 6) (h₂ : δ₂.length = 6) (h₃ : δ₃.length = 6) (h₄ : δ₄.length = 6) :
    tcChainVec [c0, c1, c2, c3, c4] (fun k => tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] k)) =
      tcOfL (tcComb5 [c0, c1, c2, c3, c4] δ₀ δ₁ δ₂ δ₃ δ₄) := by
  rw [e6fl_ofL_comb5 c0 c1 c2 c3 c4 h₀ h₁ h₂ h₃ h₄]
  simp [tcChainVec, Fin.sum_univ_five]

theorem e6fl_chainVec_eq' {c : List ℤ} (hc : c.length = 5) {δ₀ δ₁ δ₂ δ₃ δ₄ : List ℤ}
    (h₀ : δ₀.length = 6) (h₁ : δ₁.length = 6) (h₂ : δ₂.length = 6) (h₃ : δ₃.length = 6)
    (h₄ : δ₄.length = 6) :
    tcChainVec c (fun k => tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] k)) = tcOfL (tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄) := by
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := e6fl_list5 c hc
  exact e6fl_chainVec_eq c0 c1 c2 c3 c4 h₀ h₁ h₂ h₃ h₄

theorem e6fl_std30_len : ∀ c ∈ std30, c.length = 5 := by
  decide +kernel

theorem e6fl_a2_root : ∀ p ∈ e6CanonBases, ∀ m ∈ tcA2L p.1 p.2, m ∈ e6RootList := by
  decide +kernel

theorem e6fl_diag : ∀ m ∈ e6RootList, e6ip m m = 2 := by
  decide +kernel

theorem e6fl_e6ip_iform {l m : List ℤ} (hl : l.length = 6) (hm : m.length = 6) :
    e6ip l m = iform (tcOfL l) (tcOfL m) := by
  rw [iform_eq_e6ip, ofFn_ofL hl, ofFn_ofL hm]

theorem e6fl_e6ip_comm {l m : List ℤ} (hl : l.length = 6) (hm : m.length = 6) :
    e6ip l m = e6ip m l := by
  rw [e6fl_e6ip_iform hl hm, e6fl_e6ip_iform hm hl]
  exact iform_comm_E6 _ _

theorem e6fl_lineL_mem (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (g : List ℤ) :
    g ∈ tcLineL c₁ d₁ c₂ d₂ c₃ d₃ u₀ ↔ g ∈ e6RootList ∧ g ∉ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ ∧
      ((e6ip g c₃, e6ip g d₃) = u₀ ∨ (e6ip g c₃, e6ip g d₃) = (-u₀.1, -u₀.2)) := by
  simp only [tcLineL, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.or_eq_true]

theorem e6_frame_lang
    {α₁ β₁ α₂ β₂ : Fin Tag.E6.rank → ℤ}
    (r1 : IsRoot .E6 α₁) (r2 : IsRoot .E6 β₁) (r3 : IsRoot .E6 α₂) (r4 : IsRoot .E6 β₂)
    (a1 : iform α₁ β₁ = -1) (a2 : iform α₂ β₂ = -1)
    (o1 : iform α₁ α₂ = 0) (o2 : iform α₁ β₂ = 0) (o3 : iform β₁ α₂ = 0) (o4 : iform β₁ β₂ = 0) :
    ∃ α₃ β₃ : Fin Tag.E6.rank → ℤ, E6Frame α₁ β₁ α₂ β₂ α₃ β₃ := by
  have hadd_l : ∀ x x' y : Fin Tag.E6.rank → ℤ, iform (x + x') y = iform x y + iform x' y := by
    intro x x' y
    simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hadd_r : ∀ x y y' : Fin Tag.E6.rank → ℤ, iform x (y + y') = iform x y + iform x y' := by
    intro x y y'
    simp only [iform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hneg_l : ∀ x y : Fin Tag.E6.rank → ℤ, iform (-x) y = -iform x y := by
    intro x y
    simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hneg_r : ∀ x y : Fin Tag.E6.rank → ℤ, iform x (-y) = -iform x y := by
    intro x y
    simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  obtain ⟨p₁, hp₁, hX1⟩ := tcE6_canon_exists r1 r2 a1
  obtain ⟨p₂, hp₂, hX2⟩ := tcE6_canon_exists r3 r4 a2
  have hl1 := e6_canon_length p₁ hp₁
  have hl2 := e6_canon_length p₂ hp₂
  have hlen6 : ∀ l ∈ e6RootList, l.length = 6 := by decide +kernel
  have hO : ∀ x ∈ tcA2Set α₁ β₁, ∀ y ∈ tcA2Set α₂ β₂, iform x y = 0 := by
    intro x hx y hy
    simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with h | h | h | h | h | h <;> rcases hy with h' | h' | h' | h' | h' | h' <;>
      simp [h, h', hadd_l, hadd_r, hneg_l, hneg_r, o1, o2, o3, o4]
  have hO' : ∀ l l' : List ℤ, l.length = 6 → l'.length = 6 → tcOfL l ∈ tcA2Set α₁ β₁ →
      tcOfL l' ∈ tcA2Set α₂ β₂ → e6ip l l' = 0 := by
    intro l l' hl hl' h h'
    have h0 := hO _ h _ h'
    rwa [iform_eq_e6ip, ofFn_ofL hl, ofFn_ofL hl'] at h0
  have m1a : tcOfL p₁.1 ∈ tcA2Set α₁ β₁ := by rw [← hX1]; simp [tcA2Set]
  have m1b : tcOfL p₁.2 ∈ tcA2Set α₁ β₁ := by rw [← hX1]; simp [tcA2Set]
  have m2a : tcOfL p₂.1 ∈ tcA2Set α₂ β₂ := by rw [← hX2]; simp [tcA2Set]
  have m2b : tcOfL p₂.2 ∈ tcA2Set α₂ β₂ := by rw [← hX2]; simp [tcA2Set]
  have hpo : e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧
      e6ip p₁.2 p₂.2 = 0 :=
    ⟨hO' _ _ hl1.1 hl2.1 m1a m2a, hO' _ _ hl1.1 hl2.2 m1a m2b,
      hO' _ _ hl1.2 hl2.1 m1b m2a, hO' _ _ hl1.2 hl2.2 m1b m2b⟩
  obtain ⟨c3, hc3, d3, hd3, hF⟩ := e6_canon_frames p₁ hp₁ p₂ hp₂ hpo
  obtain ⟨hcd, hmem, htab, hrootT, hwtT, hA5⟩ := hF
  have hc3r : c3 ∈ e6RootList := List.mem_of_mem_filter hc3
  have hd3r : d3 ∈ e6RootList := List.mem_of_mem_filter hd3
  have hc3l : c3.length = 6 := hlen6 c3 hc3r
  have hd3l : d3.length = 6 := hlen6 d3 hd3r
  have hroot : ∀ l ∈ e6RootList, IsRoot .E6 (tcOfL l) := by
    intro l hl
    have h1 : l ∈ (rootFinset .E6).image List.ofFn := by
      rw [rootFinset_E6_image_eq]
      exact List.mem_toFinset.2 hl
    obtain ⟨γ, hγ, hγl⟩ := Finset.mem_image.1 h1
    rw [← hγl, tcOfL_ofFn]
    exact mem_rootFinset.1 hγ
  have hT1 : ∀ (γ : Fin Tag.E6.rank → ℤ) (l : List ℤ), l.length = 6 →
      iform γ (tcOfL l) = e6ip (List.ofFn γ) l := by
    intro γ l hl
    rw [iform_eq_e6ip, ofFn_ofL hl]
  have hA1 : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ tcA2Set α₁ β₁ ↔ List.ofFn γ ∈ tcA2L p₁.1 p₁.2 := by
    intro γ
    rw [← hX1, mem_tcA2Set_iff, ofFn_ofL hl1.1, ofFn_ofL hl1.2]
  have hA2 : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ tcA2Set α₂ β₂ ↔ List.ofFn γ ∈ tcA2L p₂.1 p₂.2 := by
    intro γ
    rw [← hX2, mem_tcA2Set_iff, ofFn_ofL hl2.1, ofFn_ofL hl2.2]
  have hXU : ∀ γ : Fin Tag.E6.rank → ℤ,
      γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ↔ List.ofFn γ ∈ tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2 := by
    intro γ
    rw [Set.mem_union, hA1, hA2, List.mem_append]
  have hlenA : ∀ a b : List ℤ, a.length = 6 → b.length = 6 → ∀ m ∈ tcA2L a b, m.length = 6 := by
    intro a b ha hb m hm
    simp [tcA2L] at hm
    rcases hm with h | h | h | h | h | h <;> simp [h, tcAddL, tcNegL, ha, hb]
  have m_α₁ : α₁ ∈ tcA2Set α₁ β₁ := by simp [tcA2Set]
  have m_β₁ : β₁ ∈ tcA2Set α₁ β₁ := by simp [tcA2Set]
  have m_α₂ : α₂ ∈ tcA2Set α₂ β₂ := by simp [tcA2Set]
  have m_β₂ : β₂ ∈ tcA2Set α₂ β₂ := by simp [tcA2Set]
  have C1 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      (γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ↔ (iform γ (tcOfL c3) = 0 ∧ iform γ (tcOfL d3) = 0)) := by
    intro γ hγ
    rw [hXU, hT1 γ c3 hc3l, hT1 γ d3 hd3l]
    exact hmem _ (mem_e6RootList_of_isRoot hγ)
  have C2 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ → (iform γ (tcOfL c3), iform γ (tcOfL d3)) ∈ tab12 := by
    intro γ hγ hn
    rw [hT1 γ c3 hc3l, hT1 γ d3 hd3l]
    exact htab _ (mem_e6RootList_of_isRoot hγ) (fun h => hn ((hXU γ).2 h))
  have C3 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ → (iform γ (tcOfL c3), iform γ (tcOfL d3)) ∈ tcRootTab →
        ∀ m ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, iform γ m = 0 := by
    intro γ hγ hn hr m hm
    rw [hT1 γ c3 hc3l, hT1 γ d3 hd3l] at hr
    rw [iform_eq_e6ip]
    exact hrootT _ (mem_e6RootList_of_isRoot hγ) (fun h => hn ((hXU γ).2 h)) hr _ ((hXU m).1 hm)
  have C4 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ → (iform γ (tcOfL c3), iform γ (tcOfL d3)) ∈ wtTab →
        (∃ m ∈ tcA2Set α₁ β₁, iform γ m ≠ 0) ∧ (∃ m ∈ tcA2Set α₂ β₂, iform γ m ≠ 0) := by
    intro γ hγ hn hw
    rw [hT1 γ c3 hc3l, hT1 γ d3 hd3l] at hw
    obtain ⟨⟨m1, hm1, hne1⟩, ⟨m2, hm2, hne2⟩⟩ :=
      hwtT _ (mem_e6RootList_of_isRoot hγ) (fun h => hn ((hXU γ).2 h)) hw
    have hl_m1 : m1.length = 6 := hlenA _ _ hl1.1 hl1.2 m1 hm1
    have hl_m2 : m2.length = 6 := hlenA _ _ hl2.1 hl2.2 m2 hm2
    refine ⟨⟨tcOfL m1, ?_, ?_⟩, ⟨tcOfL m2, ?_, ?_⟩⟩
    · rw [hA1, ofFn_ofL hl_m1]
      exact hm1
    · rw [hT1 γ m1 hl_m1]
      exact hne1
    · rw [hA2, ofFn_ofL hl_m2]
      exact hm2
    · rw [hT1 γ m2 hl_m2]
      exact hne2
  obtain ⟨a1c, a1d⟩ := (C1 α₁ r1).1 (Set.mem_union_left _ m_α₁)
  obtain ⟨b1c, b1d⟩ := (C1 β₁ r2).1 (Set.mem_union_left _ m_β₁)
  obtain ⟨a2c, a2d⟩ := (C1 α₂ r3).1 (Set.mem_union_right _ m_α₂)
  obtain ⟨b2c, b2d⟩ := (C1 β₂ r4).1 (Set.mem_union_right _ m_β₂)
  have hiff : iform (tcOfL c3) (tcOfL d3) = -1 := by
    rw [iform_eq_e6ip, ofFn_ofL hc3l, ofFn_ofL hd3l]
    exact hcd
  have hchain : ∀ u₀ ∈ wtRep, ∃ δ : Fin 5 → (Fin Tag.E6.rank → ℤ), (∀ k, IsRoot .E6 (δ k)) ∧
    (∀ j k, iform (δ j) (δ k) = a5gram j k) ∧
    δ 0 ∈ tcA2Set α₁ β₁ ∧ δ 1 ∈ tcA2Set α₁ β₁ ∧ δ 3 ∈ tcA2Set α₂ β₂ ∧ δ 4 ∈ tcA2Set α₂ β₂ ∧
    δ 2 ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
    ((iform (δ 2) (tcOfL c3), iform (δ 2) (tcOfL d3)) = u₀ ∨
      (iform (δ 2) (tcOfL c3), iform (δ 2) (tcOfL d3)) = (-u₀.1, -u₀.2)) ∧
    ∀ γ, IsRoot .E6 γ →
      ((γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∨
          (γ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂ ∧
            ((iform γ (tcOfL c3), iform γ (tcOfL d3)) = u₀ ∨
              (iform γ (tcOfL c3), iform γ (tcOfL d3)) = (-u₀.1, -u₀.2)))) ↔
        ∃ c ∈ std30, γ = tcChainVec c δ) := by
    intro u₀ hu₀
    obtain ⟨δ₀, h0, δ₁, h1, e01, δ₂, h2, e12, e02, δ₃, h3, e23, e13, e03,
      δ₄, h4, e34, e24, e14, e04, hLast⟩ := hA5 u₀ hu₀
    obtain ⟨hL1, hL2⟩ := hLast
    have l0 : δ₀.length = 6 := hlenA _ _ hl1.1 hl1.2 δ₀ h0
    have l1 : δ₁.length = 6 := hlenA _ _ hl1.1 hl1.2 δ₁ h1
    have r2 : δ₂ ∈ e6RootList := List.mem_of_mem_filter h2
    have l2 : δ₂.length = 6 := hlen6 δ₂ r2
    have l3 : δ₃.length = 6 := hlenA _ _ hl2.1 hl2.2 δ₃ h3
    have l4 : δ₄.length = 6 := hlenA _ _ hl2.1 hl2.2 δ₄ h4
    have r0 : δ₀ ∈ e6RootList := e6fl_a2_root p₁ hp₁ δ₀ h0
    have r1 : δ₁ ∈ e6RootList := e6fl_a2_root p₁ hp₁ δ₁ h1
    have r3 : δ₃ ∈ e6RootList := e6fl_a2_root p₂ hp₂ δ₃ h3
    have r4 : δ₄ ∈ e6RootList := e6fl_a2_root p₂ hp₂ δ₄ h4
    have g0 : e6ip δ₀ δ₀ = 2 := e6fl_diag δ₀ r0
    have g1 : e6ip δ₁ δ₁ = 2 := e6fl_diag δ₁ r1
    have g2 : e6ip δ₂ δ₂ = 2 := e6fl_diag δ₂ r2
    have g3 : e6ip δ₃ δ₃ = 2 := e6fl_diag δ₃ r3
    have g4 : e6ip δ₄ δ₄ = 2 := e6fl_diag δ₄ r4
    have e10 : e6ip δ₁ δ₀ = -1 := by rw [← e6fl_e6ip_comm l0 l1]; exact e01
    have e21 : e6ip δ₂ δ₁ = -1 := by rw [← e6fl_e6ip_comm l1 l2]; exact e12
    have e32 : e6ip δ₃ δ₂ = -1 := by rw [← e6fl_e6ip_comm l2 l3]; exact e23
    have e43 : e6ip δ₄ δ₃ = -1 := by rw [← e6fl_e6ip_comm l3 l4]; exact e34
    have e20 : e6ip δ₂ δ₀ = 0 := by rw [← e6fl_e6ip_comm l0 l2]; exact e02
    have e30 : e6ip δ₃ δ₀ = 0 := by rw [← e6fl_e6ip_comm l0 l3]; exact e03
    have e40 : e6ip δ₄ δ₀ = 0 := by rw [← e6fl_e6ip_comm l0 l4]; exact e04
    have e31 : e6ip δ₃ δ₁ = 0 := by rw [← e6fl_e6ip_comm l1 l3]; exact e13
    have e41 : e6ip δ₄ δ₁ = 0 := by rw [← e6fl_e6ip_comm l1 l4]; exact e14
    have e42 : e6ip δ₄ δ₂ = 0 := by rw [← e6fl_e6ip_comm l2 l4]; exact e24
    have hD : ∀ j : Fin 5, (![δ₀, δ₁, δ₂, δ₃, δ₄] j).length = 6 := by
      intro j
      fin_cases j
      exacts [l0, l1, l2, l3, l4]
    have hG : ∀ j k : Fin 5,
        e6ip (![δ₀, δ₁, δ₂, δ₃, δ₄] j) (![δ₀, δ₁, δ₂, δ₃, δ₄] k) = a5gram j k := by
      intro j k
      fin_cases j <;> fin_cases k <;>
        simp [a5gram, g0, g1, g2, g3, g4, e01, e10, e12, e21, e23, e32, e34, e43,
          e02, e20, e03, e30, e04, e40, e13, e31, e14, e41, e24, e42]
    have hGram : ∀ j k : Fin 5, iform (tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] j))
        (tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] k)) = a5gram j k := by
      intro j k
      rw [← e6fl_e6ip_iform (hD j) (hD k)]
      exact hG j k
    have hDr : ∀ k : Fin 5, ![δ₀, δ₁, δ₂, δ₃, δ₄] k ∈ e6RootList := by
      intro k
      fin_cases k
      exacts [r0, r1, r2, r3, r4]
    refine ⟨fun k => tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] k), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact hroot _ (hDr k)
    · intro j k
      exact hGram j k
    · show tcOfL δ₀ ∈ tcA2Set α₁ β₁
      rw [hA1, ofFn_ofL l0]
      exact h0
    · show tcOfL δ₁ ∈ tcA2Set α₁ β₁
      rw [hA1, ofFn_ofL l1]
      exact h1
    · show tcOfL δ₃ ∈ tcA2Set α₂ β₂
      rw [hA2, ofFn_ofL l3]
      exact h3
    · show tcOfL δ₄ ∈ tcA2Set α₂ β₂
      rw [hA2, ofFn_ofL l4]
      exact h4
    · show tcOfL δ₂ ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂
      rw [hXU, ofFn_ofL l2]
      exact ((e6fl_lineL_mem _ _ _ _ _ _ _ _).1 h2).2.1
    · show ((iform (tcOfL δ₂) (tcOfL c3), iform (tcOfL δ₂) (tcOfL d3)) = u₀ ∨
          (iform (tcOfL δ₂) (tcOfL c3), iform (tcOfL δ₂) (tcOfL d3)) = (-u₀.1, -u₀.2))
      rw [hT1 _ c3 hc3l, hT1 _ d3 hd3l, ofFn_ofL l2]
      exact ((e6fl_lineL_mem _ _ _ _ _ _ _ _).1 h2).2.2
    · have key : ∀ γ : Fin Tag.E6.rank → ℤ,
          (List.ofFn γ ∈ tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2 ∨
            List.ofFn γ ∈ tcLineL p₁.1 p₁.2 p₂.1 p₂.2 c3 d3 u₀) ↔
          ∃ c ∈ std30, γ = tcChainVec c (fun k => tcOfL (![δ₀, δ₁, δ₂, δ₃, δ₄] k)) := by
        intro γ
        constructor
        · intro h
          have hm : List.ofFn γ ∈ tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2 ++
              tcLineL p₁.1 p₁.2 p₂.1 p₂.2 c3 d3 u₀ := List.mem_append.2 h
          have hm2 : List.ofFn γ ∈ std30.map (fun c => tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄) := hL1 _ hm
          obtain ⟨c, hc, hcg⟩ := List.mem_map.1 hm2
          have hcg' : tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄ = List.ofFn γ := hcg
          refine ⟨c, hc, ?_⟩
          rw [e6fl_chainVec_eq' (e6fl_std30_len c hc) l0 l1 l2 l3 l4, hcg', tcOfL_ofFn]
        · rintro ⟨c, hc, hγc⟩
          have hlen : (tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄).length = 6 :=
            e6fl_comb5_len (e6fl_std30_len c hc) l0 l1 l2 l3 l4
          have hfc : List.ofFn γ = tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄ := by
            rw [hγc, e6fl_chainVec_eq' (e6fl_std30_len c hc) l0 l1 l2 l3 l4, ofFn_ofL hlen]
          have hm2 : List.ofFn γ ∈ std30.map (fun c => tcComb5 c δ₀ δ₁ δ₂ δ₃ δ₄) :=
            List.mem_map.2 ⟨c, hc, hfc.symm⟩
          exact List.mem_append.1 (hL2 _ hm2)
      intro γ hγ
      have hγr : List.ofFn γ ∈ e6RootList := mem_e6RootList_of_isRoot hγ
      constructor
      · rintro (h | ⟨hn, hc⟩)
        · exact (key γ).1 (Or.inl ((hXU γ).1 h))
        · rw [hT1 γ c3 hc3l, hT1 γ d3 hd3l] at hc
          exact (key γ).1 (Or.inr ((e6fl_lineL_mem _ _ _ _ _ _ _ _).2
            ⟨hγr, fun h => hn ((hXU γ).2 h), hc⟩))
      · intro h
        rcases (key γ).2 h with h1 | h1
        · exact Or.inl ((hXU γ).2 h1)
        · obtain ⟨-, hn, hc⟩ := (e6fl_lineL_mem _ _ _ _ _ _ _ _).1 h1
          refine Or.inr ⟨fun hγX => hn ((hXU γ).1 hγX), ?_⟩
          rw [hT1 γ c3 hc3l, hT1 γ d3 hd3l]
          exact hc
  exact ⟨tcOfL c3, tcOfL d3, ⟨hroot c3 hc3r, hroot d3 hd3r, hiff, ⟨a1c, a1d, b1c, b1d⟩,
    ⟨a2c, a2d, b2c, b2d⟩, C1, C2, C3, C4, hchain⟩⟩

end CFSG.StandardType.TableCRes

end
