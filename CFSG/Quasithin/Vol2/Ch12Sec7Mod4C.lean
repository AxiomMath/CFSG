module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4B
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec7ModU

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Fischer
open scoped IsMulCommutative

theorem decF_mod (c : ℕ) : decF (c % 4) = decF c := by
  simp only [decF, Nat.mod_mod]

theorem decF_xor {a b : ℕ} (ha : a < 64) (hb : b < 64) : decF (a ^^^ b) = decF a + decF b := by
  have := congrFun (decV_xor ha hb) 0
  simpa [decV] using this

theorem decF_sV {c v : ℕ} (hc : c < 4) (hv : v < 64) : decF (sV c v) = decF c * decF v := by
  have := congrFun (decV_sV hc hv) 0
  simpa [decV] using this

theorem decF_eq_zero_iff (c : ℕ) : decF c = 0 ↔ c % 4 = 0 := by
  constructor
  · intro h
    exact congrArg (fun x : F4 => (x.code : ℕ)) h
  · intro h
    apply f4_ext
    apply Fin.ext
    exact h

theorem mod_four_lt (c : ℕ) : c % 4 < 4 := Nat.mod_lt _ (by norm_num)

theorem xor_xor_cancel (a b c : ℕ) : (a ^^^ b) ^^^ (a ^^^ c) = b ^^^ c := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b, Nat.xor_comm b a, Nat.xor_assoc a b c,
    ← Nat.xor_assoc a a, Nat.xor_self, Nat.zero_xor]

theorem det_blk_matOf (B : B6) : (blk (matOf B)).det = decF (det2 B) := by
  rw [Matrix.det_fin_two, det2, decF_xor (sV_lt_64 _ (mod_four_lt _) _ (by omega))
    (sV_lt_64 _ (mod_four_lt _) _ (by omega)), decF_sV (mod_four_lt _) (by omega),
    decF_sV (mod_four_lt _) (by omega), decF_mod, decF_mod, decF_mod, decF_mod,
    CharTwo.sub_eq_add]
  rfl

theorem pt1_iff_quot : ∀ c < 64, ((c >>> 2) % 4 = 0 ∧ (c >>> 4) % 4 = 0) ↔ c ∈ pt1 := by
  decide

theorem mem_StatedSL_of_det {A : Matrix.GeneralLinearGroup (Fin 2) F4}
    (h : (A : Matrix (Fin 2) (Fin 2) F4).det = 1) :
    A ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 F4 :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem card_StatedSL2 : Nat.card (CFSG.Assembly.LowTwoRank.StatedSL 2 F4) = 60 := by
  rw [← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F4).toEquiv,
    Matrix.card_SL_field, card_F4]
  decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem stab1_sub {B : B6} (hB : B ∈ stab1) :
    B ∈ gm6 ∧ ∀ c ∈ pt1, B.app c = c := by
  rw [stab1, List.mem_filter] at hB
  have h1 : B.app 1 = 1 := by simpa using hB.2
  have h2 : B.app 2 = 2 := by
    have := gm6_isLin hB.1 1 (by norm_num)
    rwa [show wV 1 = 2 from rfl, h1] at this
  refine ⟨hB.1, fun c hc => ?_⟩
  rcases (mem_pt1_iff c (pt1_lt c hc)).1 hc with rfl | rfl | rfl | rfl
  · exact B6.app_zero B
  · exact h1
  · exact h2
  · rw [show (3 : ℕ) = 1 ^^^ 2 from rfl, B6.app_xor, h1, h2]

omit [Finite G] in
theorem mem_autOn_inf_centralizer_pt1 {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V ↔
      C.cB a ∈ stab1 := by
  constructor
  · intro ha
    obtain ⟨x, hxN, hxP, rfl⟩ := mem_autOn'.1 ha
    obtain ⟨hxL, hxc⟩ := Subgroup.mem_inf.1 hxP
    rw [stab1, List.mem_filter]
    refine ⟨(hC.1 _).1 (conjAct_mem_autOn hxL hxN), ?_⟩
    have hv : (C.dc 1 : G) ∈ C.subG pt1 pt1_zero pt1_xor :=
      (C.mem_subG (C.dc 1)).2 (by rw [C.cd_dc 1 (by norm_num)]; decide)
    have hcomm := Subgroup.mem_centralizer_iff.1 hxc _ hv
    have := (commute_iff_code C hxN (C.dc 1)).1 hcomm.symm
    rw [C.cd_dc 1 (by norm_num)] at this
    simpa using this
  · intro ha
    obtain ⟨hgm, hfix⟩ := stab1_sub ha
    obtain ⟨y, hyN, hyL, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hgm)
    refine conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨hyL, Subgroup.mem_centralizer_iff.2 ?_⟩) hyN
    intro w hw
    obtain ⟨hwV, hwc⟩ := hw
    exact ((commute_iff_code C hyN ⟨w, hwV⟩).2 (hfix _ hwc)).symm

theorem stab1_nodup : stab1.Nodup := gm6_nodup.filter _

omit [Finite G] in
theorem card_autOn_C
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    Nat.card ↥(autOn (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V) =
      60 := by
  classical
  set H := autOn (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V with hHd
  have e : ↥H ≃ {B : B6 // B ∈ stab1} :=
    Equiv.ofBijective (fun a => ⟨C.cB a, (mem_autOn_inf_centralizer_pt1 hC a).1 a.2⟩)
      ⟨fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab)), fun B => by
        obtain ⟨a, ha⟩ := hC.2 B.1 (stab1_sub B.2).1
        exact ⟨⟨a, (mem_autOn_inf_centralizer_pt1 hC a).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e]
  have e2 : {B : B6 // B ∈ stab1} ≃ ↥stab1.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup stab1_nodup,
    cert4_card_stab1]

section Quot

variable {W : Type} [CommGroup W]

@[expose] def quotMap (C : Coding W) : W →* Multiplicative (Fin 2 → F4) where
  toFun v := Multiplicative.ofAdd fun i => decV (C.cd v) i.succ
  map_one' := by
    rw [C.cd_one, decV_zero]
    rfl
  map_mul' u v := by
    rw [C.cd_mul, decV_xor (C.cd_lt u) (C.cd_lt v)]
    rfl

theorem quotMap_surjective (C : Coding W) : Function.Surjective (quotMap C) := by
  intro y
  refine ⟨C.dc (encV (Fin.cons 0 (Multiplicative.toAdd y))), ?_⟩
  show Multiplicative.ofAdd (fun i => decV (C.cd (C.dc _)) i.succ) = y
  rw [C.cd_dc _ (encV_lt _), decV_encV]
  rfl

theorem mem_ker_quotMap (C : Coding W) (v : W) : v ∈ (quotMap C).ker ↔ C.cd v ∈ pt1 := by
  rw [MonoidHom.mem_ker, ← pt1_iff_quot _ (C.cd_lt v)]
  constructor
  · intro h
    have e := congrArg Multiplicative.toAdd h
    have e1 := congrFun e 0
    have e2 := congrFun e 1
    exact ⟨(decF_eq_zero_iff _).1 e1, (decF_eq_zero_iff _).1 e2⟩
  · rintro ⟨h1, h2⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact (decF_eq_zero_iff _).2 h1
    · exact (decF_eq_zero_iff _).2 h2

end Quot

@[expose] noncomputable def blkSL
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    ↥(autOn (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V) →*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F4) :=
  (blkHom C (fun a ha => ⟨(stab1_sub ((mem_autOn_inf_centralizer_pt1 hC a).1 ha)).1,
    (presv_iff pt1 _).2 fun c hc => by
      rw [(stab1_sub ((mem_autOn_inf_centralizer_pt1 hC a).1 ha)).2 c hc]
      exact hc⟩)).codRestrict (CFSG.Assembly.LowTwoRank.StatedSL 2 F4) fun a =>
    mem_StatedSL_of_det (by
    rw [coe_blkHom, det_blk_matOf,
      cert4_det_one _ ((mem_autOn_inf_centralizer_pt1 hC a).1 a.2)]
    rfl)

omit [Finite G] in
theorem blkSL_bijective
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) : Function.Bijective (blkSL hC) := by
  have hinj : Function.Injective (blkSL hC) := fun a b hab =>
    blkHom_injective C _ (congrArg Subtype.val hab)
  exact hinj.bijective_of_nat_card_le (by rw [card_StatedSL2, card_autOn_C hC])

theorem isNaturalSection_Vt
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    IsNaturalSection (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V
      (C.subG pt1 pt1_zero pt1_xor)
      ((Subgroup.centralizer (V : Set G)).subgroupOf
        (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)))
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F4) := by
  set A := L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G) with hA
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans (L_le_normalizer h)
  refine ⟨hAN, (blkSL hC).comp (autOnSurj hAN),
    (blkSL_bijective hC).2.comp (autOnSurj_surjective hAN), ?_, quotMap C,
    quotMap_surjective C, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (blkSL_bijective hC).1, ker_autOnSurj]
  · ext v
    rw [mem_ker_quotMap, Subgroup.mem_subgroupOf, C.mem_subG]
  · intro a u v huv
    have hv : v = conjAct V ⟨a, hAN a.2⟩ u :=
      Subtype.ext (by rw [huv, conjAct_val, Subgroup.coe_inv])
    have ha := (mem_autOn_inf_centralizer_pt1 hC _).1 (conjAct_mem_autOn a.2 (hAN a.2))
    obtain ⟨hgm, hfix⟩ := stab1_sub ha
    obtain ⟨h1, h2⟩ := matOf_col0 (B := C.cB (conjAct V ⟨a, hAN a.2⟩)) (by
      rw [← B6.app_c0, hfix 1 (by decide)]
      norm_num)
    show (fun i => decV (C.cd v) i.succ) =
      (blk (matOf (C.cB (conjAct V ⟨a, hAN a.2⟩)))).mulVec fun i => decV (C.cd u) i.succ
    rw [hv, C.cd_apply, ← matOf_mulVec hgm (C.cd_lt u), blk_mulVec h1 h2]

omit [Finite G] [IsMulCommutative ↥V] in
theorem conj_mem_of_le_normalizer {A W : Subgroup G} (hA : A ≤ Subgroup.normalizer (W : Set G))
    {x w : G} (hx : x ∈ A) (hw : w ∈ W) : x * w * x⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (hA hx) w).1 hw

omit [Finite G] in
theorem dc_app_mem_of_stab1 {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {W : Subgroup G}
    (hAW : L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G) ≤
      Subgroup.normalizer (W : Set G)) {c : ℕ} (hc : c < 64) (hcW : (C.dc c : G) ∈ W) {B : B6}
    (hB : B ∈ stab1) : (C.dc (B.app c) : G) ∈ W := by
  obtain ⟨a, rfl⟩ := hC.2 B (stab1_sub hB).1
  obtain ⟨x, hx, hxA, rfl⟩ := mem_autOn'.1 ((mem_autOn_inf_centralizer_pt1 hC a).2 hB)
  have hm := conj_mem_of_le_normalizer hAW hxA hcW
  have e := cd_conj C hx (C.dc c)
  rw [C.cd_dc c hc] at e
  rw [← e, C.dc_cd]
  exact hm

omit [Finite G] in
theorem le_of_comm_codes
    {C : Coding ↥V} {W : Subgroup G}
    (hW : ∀ g ∈ stab1, ∀ c < 64, (C.dc (c ^^^ g.app c) : G) ∈ W) : V ≤ W := by
  have hspan := dc_spanX_mem (C := C) (W := W)
    (l := stab1.flatMap fun g => (List.range 64).map fun c => c ^^^ g.app c) (by
      intro d hd
      obtain ⟨g, hg, hd⟩ := List.mem_flatMap.1 hd
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      have hc' := List.mem_range.1 hc
      exact ⟨xor_lt_64' hc' (B6.app_lt (gm6_valid g (stab1_sub hg).1) c), hW g hg c hc'⟩)
  intro v hv
  have hd := (hspan _ (mem_of_spanHas cert4_comm_span _ (List.mem_range.2 (C.cd_lt ⟨v, hv⟩)))).2
  rw [C.dc_cd] at hd
  exact hd

omit [Finite G] in
theorem le_sup_of_not_le
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) {W : Subgroup G}
    (hAW : L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G) ≤
      Subgroup.normalizer (W : Set G)) {w : ↥V} (hwW : (w : G) ∈ W) (hw : C.cd w ∉ pt1) :
    V ≤ W ⊔ C.subG pt1 pt1_zero pt1_xor := by
  have hcW : (C.dc (C.cd w) : G) ∈ W := by rw [C.dc_cd]; exact hwW
  have hspan := dc_spanX_mem (C := C) (W := W ⊔ C.subG pt1 pt1_zero pt1_xor)
    (l := pt1 ++ stab1.map (·.app (C.cd w))) (by
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · refine ⟨pt1_lt d hd, le_sup_right (a := W) ?_⟩
        exact (C.mem_subG (C.dc d)).2 (by rw [C.cd_dc d (pt1_lt d hd)]; exact hd)
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hd
        exact ⟨B6.app_lt (gm6_valid g (stab1_sub hg).1) _, le_sup_left (b := C.subG pt1 pt1_zero
          pt1_xor) (dc_app_mem_of_stab1 hC hAW (C.cd_lt w) hcW hg)⟩)
  intro v hv
  have hd := (hspan _ (mem_of_spanHas (cert4_irr_t _ (List.mem_range.2 (C.cd_lt w)) hw) _
    (List.mem_range.2 (C.cd_lt ⟨v, hv⟩)))).2
  rw [C.dc_cd] at hd
  exact hd

theorem index_le_of_sup {W P : Subgroup G} (hWV : W ≤ V) (hPV : P ≤ V) (hsup : V ≤ W ⊔ P) :
    (W.subgroupOf V).index ≤ Nat.card P := by
  have htop : W.subgroupOf V ⊔ P.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWV hPV]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_top, iff_true]
    exact hsup x.2
  have e := Subgroup.relIndex_sup_left (P.subgroupOf V) (W.subgroupOf V)
  rw [htop, Subgroup.relIndex_top_right] at e
  rw [e, Subgroup.relIndex]
  have hcard : Nat.card (P.subgroupOf V) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPV).toEquiv
  rw [← hcard]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)

theorem isIndecomposable_Vt
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    IsIndecomposableUnder (L ⊓ Subgroup.centralizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V := by
  set P := C.subG pt1 pt1_zero pt1_xor with hPd
  have hP4 : Nat.card P = 4 := C.card_subG pt1_nodup pt1_lt
  have hPV : P ≤ V := C.subG_le _ _ _
  refine ⟨fun hb => ?_, fun V₁ V₂ h1V h2V hA1 hA2 hinf hsup => ?_⟩
  · have := card_V h1222 h
    rw [hb, Subgroup.card_bot] at this
    norm_num at this
  have hnorm : V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro x hx
    apply normalizer_of_maps
    intro w hw
    have hxw : x * w = w * x := by
      have := mul_comm (⟨x, h1V hx⟩ : ↥V) ⟨w, h2V hw⟩
      exact congrArg Subtype.val this
    rw [hxw, mul_inv_cancel_right]
    exact hw
  have hprod : ∀ v ∈ V, ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, v₁ * v₂ = v := by
    intro v hv
    have hv' : v ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by rw [hsup]; exact hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hnorm] at hv'
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv'
    exact ⟨v₁, hv₁, v₂, hv₂, rfl⟩
  have key : ∀ {X Y : Subgroup G}, X ≤ V → Y ≤ V →
      L ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      (∀ v ∈ V, ∃ x ∈ X, ∃ y ∈ Y, x * y = v) → X ⊓ Y = ⊥ → X ≤ P → X = ⊥ := by
    intro X Y hXV hYV hAY hXY hXYb hXP
    have hVY : V ≤ Y := by
      apply le_of_comm_codes (C := C)
      intro g hg c hc
      obtain ⟨x, hx, y, hy, hxy⟩ := hXY _ (C.dc c).2
      have hfix := (stab1_sub hg).2
      have hcx : g.app (C.cd ⟨x, hXV hx⟩) = C.cd ⟨x, hXV hx⟩ :=
        hfix _ ((C.mem_subG ⟨x, hXV hx⟩).1 (hXP hx))
      have hcd : c = C.cd ⟨x, hXV hx⟩ ^^^ C.cd ⟨y, hYV hy⟩ := by
        rw [← C.cd_mul, ← C.cd_dc c hc]
        congr 1
        exact Subtype.ext hxy.symm
      have hyc : (C.dc (C.cd ⟨y, hYV hy⟩) : G) ∈ Y := by rw [C.dc_cd]; exact hy
      have hgy := dc_app_mem_of_stab1 hC hAY (C.cd_lt _) hyc hg
      have e : c ^^^ g.app c = C.cd ⟨y, hYV hy⟩ ^^^ g.app (C.cd ⟨y, hYV hy⟩) := by
        rw [hcd, B6.app_xor, hcx, xor_xor_cancel]
      rw [e, C.dc_xor (C.cd_lt _) (B6.app_lt (gm6_valid g (stab1_sub hg).1) _), Subgroup.coe_mul]
      exact Y.mul_mem hyc hgy
    rw [eq_bot_iff]
    intro x hx
    rw [← hXYb]
    exact ⟨hx, hVY (hXV hx)⟩
  by_cases h1P : V₁ ≤ P
  · exact Or.inl (key h1V h2V hA2 hprod hinf h1P)
  by_cases h2P : V₂ ≤ P
  · refine Or.inr (key h2V h1V hA1 (fun v hv => ?_) (by rw [inf_comm]; exact hinf) h2P)
    obtain ⟨x, hx, y, hy, hxy⟩ := hprod v hv
    refine ⟨y, hy, x, hx, ?_⟩
    rw [← hxy]
    exact congrArg Subtype.val (mul_comm (⟨y, h2V hy⟩ : ↥V) ⟨x, h1V hx⟩)
  exfalso
  obtain ⟨w₁, hw₁, hw₁P⟩ := Set.not_subset.1 h1P
  obtain ⟨w₂, hw₂, hw₂P⟩ := Set.not_subset.1 h2P
  have hc1 : C.cd ⟨w₁, h1V hw₁⟩ ∉ pt1 := fun hc => hw₁P ((C.mem_subG _).2 hc)
  have hc2 : C.cd ⟨w₂, h2V hw₂⟩ ∉ pt1 := fun hc => hw₂P ((C.mem_subG _).2 hc)
  have i1 := index_le_of_sup h1V hPV (le_sup_of_not_le hC hA1 (w := ⟨w₁, h1V hw₁⟩) hw₁ hc1)
  have i2 := index_le_of_sup h2V hPV (le_sup_of_not_le hC hA2 (w := ⟨w₂, h2V hw₂⟩) hw₂ hc2)
  have hbot : V₁.subgroupOf V ⊓ V₂.subgroupOf V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ V₁ ⊓ V₂ := ⟨hx.1, hx.2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hle := Subgroup.index_inf_le (H := V₁.subgroupOf V) (K := V₂.subgroupOf V)
  rw [hbot, Subgroup.index_bot, card_V h1222 h] at hle
  rw [hP4] at i1 i2
  have : (V₁.subgroupOf V).index * (V₂.subgroupOf V).index ≤ 4 * 4 := Nat.mul_le_mul i1 i2
  omega

end CFSG.Quasithin.H13.S127.Mod

end
