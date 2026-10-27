module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4F
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Fischer
open scoped IsMulCommutative

@[expose] def ptSetEq (l l' : List ℕ) : Bool :=
  l.all (fun a => l'.contains a) && l'.all fun a => l.contains a

theorem mem_iff_of_ptSetEq {l l' : List ℕ} (h : ptSetEq l l' = true) (a : ℕ) :
    a ∈ l ↔ a ∈ l' := by
  simp only [ptSetEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun ha => h.1 a ha, fun ha => h.2 a ha⟩

theorem ptOf_zero (c : ℕ) : 0 ∈ ptOf c := List.mem_cons_self

theorem ptOf_self (c : ℕ) : c ∈ ptOf c := List.mem_cons_of_mem _ List.mem_cons_self

theorem ptOf_xor_all : ∀ c < 64, ∀ a ∈ ptOf c, ∀ b ∈ ptOf c, a ^^^ b ∈ ptOf c := by decide

theorem ptOf_lt_all : ∀ c < 64, ∀ a ∈ ptOf c, a < 64 := by decide

theorem ptOf_nodup_all : ∀ c < 64, c ≠ 0 → (ptOf c).Nodup := by decide

theorem zs6_presv_ptOf : ∀ c < 64, ∀ z ∈ zs6, ∀ a ∈ ptOf c, z.app a ∈ ptOf c := by decide

theorem ptOf_length (c : ℕ) : (ptOf c).length = 4 := rfl

theorem hyp_pts_l2c : ∀ d ∈ oVecL, d ∈ l2c →
    ptSetEq (ptOf d) (ptOf 1) = true ∨ ptSetEq (ptOf d) (ptOf 4) = true := by decide

theorem non_pts_l2c : ∀ d ∈ List.range 64, d ≠ 0 → d ∉ oVecL → d ∈ l2c →
    ptSetEq (ptOf d) (ptOf 5) = true ∨ ptSetEq (ptOf d) (ptOf 9) = true ∨
      ptSetEq (ptOf d) (ptOf 13) = true := by decide

theorem pts_facts : ptOf 1 ⊆ l2c ∧ ptOf 4 ⊆ l2c ∧ ptOf 5 ⊆ l2c ∧ ptOf 9 ⊆ l2c ∧
    ptOf 13 ⊆ l2c ∧ 4 ∈ oVecL ∧ 1 ∈ oVecL ∧ 9 ∉ oVecL ∧ 13 ∉ oVecL ∧ 5 ∈ p1c ∧ 9 ≠ 0 ∧
    13 ≠ 0 ∧ 1 ∉ ptOf 4 ∧ 5 ∉ ptOf 9 ∧ 5 ∉ ptOf 13 ∧ 9 ∉ ptOf 13 := by decide

theorem p1c_eq_ptOf : ∀ a, a ∈ p1c ↔ a ∈ ptOf 5 := fun _ => Iff.rfl

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem subG_congr {C : Coding ↥V} {l l' : List ℕ} {h0 : 0 ∈ l}
    {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} {h0' : 0 ∈ l'} {hx' : ∀ a ∈ l', ∀ b ∈ l', a ^^^ b ∈ l'}
    (h : ∀ a, a ∈ l ↔ a ∈ l') : C.subG l h0 hx = C.subG l' h0' hx' := by
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨hg, (h _).1 hc⟩
  · rintro ⟨hg, hc⟩
    exact ⟨hg, (h _).2 hc⟩

theorem Vt_eq_ptOf
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {t : G} (ht : t ∈ V) :
    Vt L t = C.subG (ptOf (C.cd ⟨t, ht⟩)) (ptOf_zero _) (ptOf_xor_all _ (C.cd_lt _)) := by
  set c := C.cd ⟨t, ht⟩ with hcd
  have hc := C.cd_lt ⟨t, ht⟩
  have hXN := XOf_le_normalizer_subG h1222 h hC (l := ptOf c) (h0 := ptOf_zero _)
    (hx := ptOf_xor_all _ hc) (zs6_presv_ptOf c hc)
  have htS : t ∈ C.subG (ptOf c) (ptOf_zero _) (ptOf_xor_all _ hc) :=
    (C.mem_subG ⟨t, ht⟩).2 (ptOf_self c)
  apply le_antisymm
  · rw [Vt, conjClosure, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Subgroup.mem_normalizer_iff.1 (hXN hx) _).1 (Subgroup.zpow_mem _ htS n)
  · obtain ⟨w, hw⟩ := hC.2 w6 w6_gm6
    have hwX : w ∈ autOn (XOf L) V := (mem_autOn_XOf h1222 h hC w).2 (by rw [hw]; decide)
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn'.1 hwX
    obtain ⟨w', hw'⟩ := hC.2 (w6.comp w6) (zs6_sub_gm6 _ (by decide))
    have hwX' : w' ∈ autOn (XOf L) V := (mem_autOn_XOf h1222 h hC w').2 (by rw [hw']; decide)
    obtain ⟨x', hxN', hxX', rfl⟩ := mem_autOn'.1 hwX'
    have hmem : ∀ z ∈ XOf L, z * t * z⁻¹ ∈ Vt L t := fun z hz =>
      Subgroup.subset_closure ⟨z, hz, t, Subgroup.mem_zpowers t, rfl⟩
    intro g hg
    obtain ⟨hgV, hgc⟩ := hg
    have hcd' : ∀ (z : G) (hz : z ∈ Subgroup.normalizer (V : Set G)),
        C.cd ⟨z * t * z⁻¹, (Subgroup.mem_normalizer_iff.1 hz t).1 ht⟩ =
          (C.cB (conjAct V ⟨z, hz⟩)).app c := fun z hz => cd_conj C hz ⟨t, ht⟩
    simp only [ptOf, List.mem_cons, List.not_mem_nil, or_false] at hgc
    rcases hgc with e | e | e | e
    · have : (⟨g, hgV⟩ : ↥V) = 1 := C.cd_eq_zero.1 e
      rw [show g = 1 from congrArg Subtype.val this]
      exact (Vt L t).one_mem
    · have : (⟨g, hgV⟩ : ↥V) = ⟨t, ht⟩ := C.cd_injective e
      rw [show g = t from congrArg Subtype.val this]
      have := hmem 1 (XOf L).one_mem
      simpa using this
    · have : (⟨g, hgV⟩ : ↥V) = ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN t).1 ht⟩ :=
        C.cd_injective (by rw [e, hcd' x hxN, hw, w6_app c hc])
      rw [show g = x * t * x⁻¹ from congrArg Subtype.val this]
      exact hmem x hxX
    · have : (⟨g, hgV⟩ : ↥V) = ⟨x' * t * x'⁻¹, (Subgroup.mem_normalizer_iff.1 hxN' t).1 ht⟩ :=
        C.cd_injective (by
          rw [e, hcd' x' hxN', hw', B6.app_comp, w6_app c hc, w6_app _ (wV_lt c hc)])
      rw [show g = x' * t * x'⁻¹ from congrArg Subtype.val this]
      exact hmem x' hxX'

omit [Finite G] in
theorem map_subG_ptOf {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ L) {c : ℕ} (hc : c < 64) :
    (C.subG (ptOf c) (ptOf_zero c) (ptOf_xor_all c hc)).map (MulAut.conj x).toMonoidHom =
      C.subG (ptOf ((C.cB (conjAct V ⟨x, hx⟩)).app c)) (ptOf_zero _)
        (ptOf_xor_all _ (B6.app_lt (C.cB_valid _) c)) := by
  set B := C.cB (conjAct V ⟨x, hx⟩) with hB
  have hlin : IsLin B := gm6_isLin ((hC.1 _).1 (conjAct_mem_autOn hxL hx))
  have himg : ∀ a ∈ ptOf c, B.app a ∈ ptOf (B.app c) := by
    intro a ha
    simp only [ptOf, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl (B6.app_zero B)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl (hlin c hc)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hlin _ (wV_lt c hc), hlin c hc])))
  apply le_antisymm
  · rintro _ ⟨g, ⟨hgV, hgc⟩, rfl⟩
    have hm := (Subgroup.mem_normalizer_iff.1 hx g).1 hgV
    refine ⟨hm, ?_⟩
    have e := cd_conj C hx ⟨g, hgV⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e ⊢
    rw [e]
    exact himg _ hgc
  ·
    intro g hg
    obtain ⟨hgV, hgc⟩ := hg
    have hxi : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hx
    have hm' : x⁻¹ * g * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 hxi g).1 hgV
      simpa using this
    refine ⟨x⁻¹ * g * x, ⟨hm', ?_⟩, by simp [mul_assoc]⟩
    have ew : C.cd ⟨x⁻¹ * g * x, hm'⟩ =
        (C.cB (conjAct V ⟨x⁻¹, hxi⟩)).app (C.cd ⟨g, hgV⟩) := by
      rw [← cd_conj C hxi ⟨g, hgV⟩]
      congr 1
      exact Subtype.ext (by simp)
    have hBinv : (C.cB (conjAct V ⟨x⁻¹, hxi⟩)).comp B = B6.id := by
      rw [hB, ← C.cB_mul, ← map_mul, ← C.cB_one]
      congr 1
      rw [show (⟨x⁻¹, hxi⟩ : ↥(Subgroup.normalizer (V : Set G))) * ⟨x, hx⟩ = 1 from
        Subtype.ext (inv_mul_cancel x), map_one]
    have : ∃ a ∈ ptOf c, C.cd ⟨g, hgV⟩ = B.app a := by
      simp only [ptOf, List.mem_cons, List.not_mem_nil, or_false] at hgc ⊢
      rcases hgc with e | e | e | e
      · exact ⟨0, Or.inl rfl, by rw [e, B6.app_zero]⟩
      · exact ⟨c, Or.inr (Or.inl rfl), e⟩
      · exact ⟨wV c, Or.inr (Or.inr (Or.inl rfl)), by rw [e, hlin c hc]⟩
      · exact ⟨wV (wV c), Or.inr (Or.inr (Or.inr rfl)), by
          rw [e, hlin _ (wV_lt c hc), hlin c hc]⟩
    obtain ⟨a, ha, hga⟩ := this
    show C.cd ⟨x⁻¹ * g * x, hm'⟩ ∈ ptOf c
    rw [ew, hga, ← B6.app_comp, hBinv, B6.id_app a (ptOf_lt_all c hc a ha)]
    exact ha

omit [Finite G] in
theorem exists_L_map_to {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {g : B6} (hg : g ∈ gm6) {c d : ℕ} (hd : d < 64)
    (hgd : g.app d = c) :
    ∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G), (C.cB (conjAct V ⟨l, hl⟩)).app c = d := by
  obtain ⟨a, rfl⟩ := hC.2 g hg
  obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hg)
  refine ⟨x⁻¹, L.inv_mem hxL, Subgroup.inv_mem _ hx, ?_⟩
  have e : conjAct V ⟨x⁻¹, Subgroup.inv_mem _ hx⟩ = (conjAct V ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, ← hgd, ← B6.app_comp, ← C.cB_mul, inv_mul_cancel, C.cB_one, B6.id_app d hd]

omit [Finite G] in
theorem conjAct_mul_code {C : Coding ↥V} {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (c : ℕ) :
    (C.cB (conjAct V ⟨x * y, Subgroup.mul_mem _ hx hy⟩)).app c =
      (C.cB (conjAct V ⟨x, hx⟩)).app ((C.cB (conjAct V ⟨y, hy⟩)).app c) := by
  rw [conjAct_mul', C.cB_mul, B6.app_comp]

theorem isFPoint_ptOf
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {d : ℕ} (hd : d < 64) (hd0 : d ≠ 0) :
    IsFPoint L V (C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd)) := by
  refine ⟨⟨C.subG_le _ _ _, XOf_le_normalizer_subG h1222 h hC (zs6_presv_ptOf d hd)⟩, ?_⟩
  rw [C.card_subG (ptOf_nodup_all d hd hd0) (ptOf_lt_all d hd)]
  rfl

theorem subG_ptOf_le_V2
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) {d : ℕ} (hd : d < 64)
    (hdl : ptOf d ⊆ l2c) : C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd) ≤ V2 T L V := by
  rw [V2_eq h hC]
  rintro g ⟨hg, hc⟩
  exact ⟨hg, hdl hc⟩

theorem mem_l2c_of_le_V2
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) {d : ℕ} (hd : d < 64)
    (hle : C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd) ≤ V2 T L V) : d ∈ l2c := by
  have hmem : (C.dc d : G) ∈ C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd) :=
    (C.mem_subG (C.dc d)).2 (by rw [C.cd_dc d hd]; exact ptOf_self d)
  have := hle hmem
  rw [V2_eq h hC] at this
  have := (C.mem_subG (C.dc d)).1 this
  rwa [C.cd_dc d hd] at this

theorem ncard_Vt_conj
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {t : G}
    (ht : t ∈ V) (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
        ∃ l ∈ L, W = (Vt L t).map (MulAut.conj l).toMonoidHom}.ncard = 2 := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hct := cd_t_mem_oVecL h1222 h hC ht h18
  have hctl := C.cd_lt ⟨t, ht⟩
  have hVt := Vt_eq_ptOf h1222 h hC.1 ht
  obtain ⟨hp1, hp4, -, -, -, h4o, -, -, -, -, -, -, h14, -, -, -⟩ := pts_facts
  set P1 := C.subG (ptOf 1) (ptOf_zero 1) (ptOf_xor_all 1 (by norm_num)) with hP1
  set P4 := C.subG (ptOf 4) (ptOf_zero 4) (ptOf_xor_all 4 (by norm_num)) with hP4
  obtain ⟨g₁, hg₁, hg₁t⟩ := cert4_hyp_trans _ hct
  obtain ⟨a₁, rfl⟩ := hC.1.2 g₁ hg₁
  obtain ⟨x₁, hx₁, hx₁L, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hg₁)
  have hconj₁ : (Vt L t).map (MulAut.conj x₁).toMonoidHom = P1 := by
    rw [hVt, map_subG_ptOf hC.1 hx₁ hx₁L hctl]
    exact subG_congr fun a => by rw [hg₁t]
  obtain ⟨g₂, hg₂, hg₂4⟩ := cert4_hyp_trans _ h4o
  obtain ⟨x₂, hx₂L, hx₂, hx₂c⟩ := exists_L_map_to hC.1 hg₂ (by norm_num) hg₂4
  have hconj₂ : (Vt L t).map (MulAut.conj (x₂ * x₁)).toMonoidHom = P4 := by
    rw [hVt, map_subG_ptOf hC.1 (Subgroup.mul_mem _ hx₂ hx₁) (L.mul_mem hx₂L hx₁L) hctl]
    exact subG_congr fun a => by rw [conjAct_mul_code hx₂ hx₁, hg₁t, hx₂c]
  have hset : {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
      ∃ l ∈ L, W = (Vt L t).map (MulAut.conj l).toMonoidHom} = {P1, P4} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, hW2, l, hl, rfl⟩
      have hlN := L_le_normalizer h hl
      rw [hVt, map_subG_ptOf hC.1 hlN hl hctl] at hW2 ⊢
      have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
      have hd : (C.cB (conjAct V ⟨l, hlN⟩)).app (C.cd ⟨t, ht⟩) ∈ oVecL :=
        (MVbar_code h hC.1 (hLM (conjAct_mem_autOn hl hlN))).2.1 _ hct
      have hdl := mem_l2c_of_le_V2 h hC (B6.app_lt (C.cB_valid _) _) hW2
      rcases hyp_pts_l2c _ hd hdl with e | e
      · exact Or.inl (subG_congr (mem_iff_of_ptSetEq e))
      · exact Or.inr (subG_congr (mem_iff_of_ptSetEq e))
    · rintro (rfl | rfl)
      · exact ⟨isFPoint_ptOf h1222 h hC.1 (by norm_num) (by norm_num),
          subG_ptOf_le_V2 h hC (by norm_num) hp1, x₁, hx₁L, hconj₁.symm⟩
      · exact ⟨isFPoint_ptOf h1222 h hC.1 (by norm_num) (by norm_num),
          subG_ptOf_le_V2 h hC (by norm_num) hp4, x₂ * x₁, L.mul_mem hx₂L hx₁L, hconj₂.symm⟩
  rw [hset, Set.ncard_pair]
  intro e
  have hmem : (C.dc 1 : G) ∈ P1 :=
    (C.mem_subG (C.dc 1)).2 (by rw [C.cd_dc 1 (by norm_num)]; decide)
  rw [e] at hmem
  have := (C.mem_subG (C.dc 1)).1 hmem
  rw [C.cd_dc 1 (by norm_num)] at this
  exact h14 this

theorem five_not_oVecL : 5 ∉ oVecL := by decide

omit [Finite G] in
theorem subG_ne_of_code {C : Coding ↥V} {l l' : List ℕ} {h0 : 0 ∈ l}
    {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} {h0' : 0 ∈ l'} {hx' : ∀ a ∈ l', ∀ b ∈ l', a ^^^ b ∈ l'}
    {c : ℕ} (hc : c < 64) (hcl : c ∈ l) (hcl' : c ∉ l') : C.subG l h0 hx ≠ C.subG l' h0' hx' := by
  intro e
  have hmem : (C.dc c : G) ∈ C.subG l h0 hx :=
    (C.mem_subG (C.dc c)).2 (by rw [C.cd_dc c hc]; exact hcl)
  rw [e] at hmem
  have := (C.mem_subG (C.dc c)).1 hmem
  rw [C.cd_dc c hc] at this
  exact hcl' this

theorem ncard_V1_conj
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
        ∃ l ∈ L, W = (V1 T L V).map (MulAut.conj l).toMonoidHom}.ncard = 3 := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  obtain ⟨-, -, hp5, hp9, hp13, -, -, h9o, h13o, -, h90, h130, -, h59, h513, h913⟩ := pts_facts
  have hV1 : V1 T L V = C.subG (ptOf 5) (ptOf_zero 5) (ptOf_xor_all 5 (by norm_num)) :=
    (V1_eq h hC).trans (subG_congr p1c_eq_ptOf)
  set P5 := C.subG (ptOf 5) (ptOf_zero 5) (ptOf_xor_all 5 (by norm_num)) with hP5
  set P9 := C.subG (ptOf 9) (ptOf_zero 9) (ptOf_xor_all 9 (by norm_num)) with hP9
  set P13 := C.subG (ptOf 13) (ptOf_zero 13) (ptOf_xor_all 13 (by norm_num)) with hP13
  have hconj : ∀ {d : ℕ} (hd : d < 64), d ≠ 0 → d ∉ oVecL →
      ∃ l ∈ L, (V1 T L V).map (MulAut.conj l).toMonoidHom =
        C.subG (ptOf d) (ptOf_zero d) (ptOf_xor_all d hd) := by
    intro d hd hd0 hdo
    obtain ⟨g, hg, hgd⟩ := cert4_off_trans _ (List.mem_range.2 hd) hd0 hdo 5 (by decide)
      (by norm_num)
    obtain ⟨x, hxL, hx, hxc⟩ := exists_L_map_to hC.1 hg hd hgd
    refine ⟨x, hxL, ?_⟩
    rw [hV1, map_subG_ptOf hC.1 hx hxL (by norm_num)]
    exact subG_congr fun a => by rw [hxc]
  have hset : {W : Subgroup G | IsFPoint L V W ∧ W ≤ V2 T L V ∧
      ∃ l ∈ L, W = (V1 T L V).map (MulAut.conj l).toMonoidHom} = {P5, P9, P13} := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, hW2, l, hl, rfl⟩
      have hlN := L_le_normalizer h hl
      rw [hV1, map_subG_ptOf hC.1 hlN hl (by norm_num)] at hW2 ⊢
      set B := C.cB (conjAct V ⟨l, hlN⟩) with hBd
      have hdl := mem_l2c_of_le_V2 h hC (B6.app_lt (C.cB_valid _) _) hW2
      have hd0 : B.app 5 ≠ 0 := by
        intro h0
        have := C.cB_app_injective (conjAct V ⟨l, hlN⟩) (by norm_num : 5 < 64)
          (by norm_num : 0 < 64) (by rw [h0, B6.app_zero])
        exact absurd this (by norm_num)
      have hdo : B.app 5 ∉ oVecL := by
        intro hd
        have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
        have hi : (conjAct V ⟨l, hlN⟩)⁻¹ ∈ h.hyp.MVbar :=
          h.hyp.MVbar.inv_mem (hLM (conjAct_mem_autOn hl hlN))
        have h5 := (MVbar_code h hC.1 hi).2.1 _ hd
        rw [← B6.app_comp, ← C.cB_mul, inv_mul_cancel, C.cB_one,
          B6.id_app 5 (by norm_num)] at h5
        exact five_not_oVecL h5
      rcases non_pts_l2c _ (List.mem_range.2 (B6.app_lt (C.cB_valid _) _)) hd0 hdo hdl with
        e | e | e
      · exact Or.inl (subG_congr (mem_iff_of_ptSetEq e))
      · exact Or.inr (Or.inl (subG_congr (mem_iff_of_ptSetEq e)))
      · exact Or.inr (Or.inr (subG_congr (mem_iff_of_ptSetEq e)))
    · rintro (rfl | rfl | rfl)
      · refine ⟨isFPoint_ptOf h1222 h hC.1 (by norm_num) (by norm_num),
          subG_ptOf_le_V2 h hC (by norm_num) hp5, 1, L.one_mem, ?_⟩
        rw [hV1, map_subG_ptOf hC.1 (Subgroup.one_mem _) L.one_mem (by norm_num)]
        refine subG_congr fun a => ?_
        rw [show conjAct V ⟨1, Subgroup.one_mem _⟩ = 1 from map_one (conjAct V), C.cB_one,
          B6.id_app 5 (by norm_num)]
      · obtain ⟨l, hl, e⟩ := hconj (by norm_num) h90 h9o
        exact ⟨isFPoint_ptOf h1222 h hC.1 (by norm_num) (by norm_num),
          subG_ptOf_le_V2 h hC (by norm_num) hp9, l, hl, e.symm⟩
      · obtain ⟨l, hl, e⟩ := hconj (by norm_num) h130 h13o
        exact ⟨isFPoint_ptOf h1222 h hC.1 (by norm_num) (by norm_num),
          subG_ptOf_le_V2 h hC (by norm_num) hp13, l, hl, e.symm⟩
  rw [hset]
  exact Set.ncard_eq_three.2 ⟨P5, P9, P13, subG_ne_of_code (by norm_num) (ptOf_self 5) h59,
    subG_ne_of_code (by norm_num) (ptOf_self 5) h513, subG_ne_of_code (by norm_num) (ptOf_self 9)
      h913, rfl⟩

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Fischer

theorem lemma12_7_4_of
    (h1222 : Stmt12_2_2) (h128 : Stmt12_2_8) : Lemma12_7_4 := by
  intro G _ _ T L V h
  have : IsMulCommutative ↥V := (card_eq_of_1222 h1222 h).1
  refine ⟨lemma12_7_4_part1_of h1222 h, fun t ht h18 => ?_⟩
  obtain ⟨C, hC, h1⟩ := exists_coding_t h1222 h ht h18
  have hVt := Vt_eq h1222 h hC ht h1
  refine ⟨⟨F4, inferInstance, inferInstance, Nat.card_eq_fintype_card.trans card_F4, ?_, ?_⟩,
    ?_, ⟨V_eq_commutator h hC ht h1, V_le_Lt h1222 h hC ht h1, Lt_eq_theta h1222 h128 h hC ht h1,
      Lt_quot_equiv h1222 h hC ht h1, Lt_perfect h1222 h hC ht h1⟩,
    ncard_Vt_conj h1222 h ht h18, ncard_V1_conj h1222 h⟩
  · rw [hVt]
    exact normalizer_Vt_equiv hC
  · rw [hVt]
    exact isNaturalSection_Vt h hC
  · rw [hVt]
    exact isIndecomposable_Vt h1222 h hC

end CFSG.Quasithin.H13.S127.Mod

end
