module

public import CFSG.Quasithin.Vol2.Ch12Sec6L28b
public import CFSG.Quasithin.Vol2.Ch12Sec6L28c
public import CFSG.Quasithin.Vol2.Ch12Sec6L23a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

namespace S126L28

section Pre

variable {G : Type} [Group G] {V A : Subgroup G}

@[expose] noncomputable def preB (V A : Subgroup G) (B : Subgroup (MulAut ↥V)) : Subgroup G :=
  A ⊓ (B.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_preB {B : Subgroup (MulAut ↥V)} {x : G} :
    x ∈ preB V A B ↔
      x ∈ A ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G), conjAct V ⟨x, hx⟩ ∈ B := by
  constructor
  · rintro ⟨hxA, y, hy, rfl⟩
    exact ⟨hxA, y.2, hy⟩
  · rintro ⟨hxA, hx, hB⟩
    exact ⟨hxA, ⟨x, hx⟩, hB, rfl⟩

theorem preB_le (B : Subgroup (MulAut ↥V)) : preB V A B ≤ A := inf_le_left

theorem preB_mono {B B' : Subgroup (MulAut ↥V)} (h : B ≤ B') : preB V A B ≤ preB V A B' :=
  inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

theorem autOn_preB {B : Subgroup (MulAut ↥V)} (hB : B ≤ autOn A V) : autOn (preB V A B) V = B := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨-, y', hy', hyy'⟩ := Subgroup.mem_subgroupOf.1 hy
    rw [show y = y' from Subtype.ext hyy'.symm]
    exact hy'
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hB hx
    exact ⟨y, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hy, y, hx, rfl⟩, rfl⟩

theorem range_actionOn (hAN : A ≤ Subgroup.normalizer (V : Set G)) :
    (A4.actionOn V A hAN).range = autOn A V := by
  ext a
  rw [MonoidHom.mem_range, A4.mem_autOn_iff hAN]

theorem subgroupOf_preB (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (B : Subgroup (MulAut ↥V)) : (preB V A B).subgroupOf A = B.comap (A4.actionOn V A hAN) := by
  ext a
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_preB]
  constructor
  · rintro ⟨-, _, hB⟩
    exact hB
  · intro h
    exact ⟨a.2, hAN a.2, h⟩

theorem relIndex_preB (hAN : A ≤ Subgroup.normalizer (V : Set G)) (B : Subgroup (MulAut ↥V)) :
    (preB V A B).relIndex A = B.relIndex (autOn A V) := by
  rw [Subgroup.relIndex, subgroupOf_preB hAN, Subgroup.index_comap, range_actionOn hAN]

variable [IsMulCommutative ↥V]

theorem mem_centralizer_of_mem_fixV {B : Subgroup (MulAut ↥V)} {v : ↥V} (hv : v ∈ fixV B) :
    (v : G) ∈ Subgroup.centralizer (preB V A B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨-, hgN, hgB⟩ := mem_preB.1 hg
  have h : g * (v : G) * g⁻¹ = v := congrArg Subtype.val (hv _ hgB)
  calc g * v = g * v * g⁻¹ * g := by group
    _ = v * g := by rw [h]

theorem mem_fixV_of_mem_normalizer (hAN : A ≤ Subgroup.normalizer (V : Set G)) {y : G}
    (hdisj : V ⊓ conjSubgroup V y = ⊥) (hAy : A ≤ conjSubgroup V y) {v : ↥V}
    (hv : (v : G) ∈ Subgroup.normalizer (conjSubgroup V y : Set G)) :
    v ∈ fixV (autOn A V) := by
  intro x hx
  obtain ⟨a, rfl⟩ := (A4.mem_autOn_iff hAN).1 hx
  apply Subtype.ext
  rw [A4.actionOn_apply_coe]
  have haV : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hAN a.2) v).1 v.2
  have hc : (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ ∈ V ⊓ conjSubgroup V y := by
    refine ⟨V.mul_mem haV (V.inv_mem v.2), ?_⟩
    have ha : (a : G) ∈ conjSubgroup V y := hAy a.2
    have h1 : (v : G) * (a : G)⁻¹ * (v : G)⁻¹ ∈ conjSubgroup V y :=
      (Subgroup.mem_normalizer_iff.1 hv _).1 ((conjSubgroup V y).inv_mem ha)
    have h2 := (conjSubgroup V y).mul_mem ha h1
    rwa [show (a : G) * ((v : G) * (a : G)⁻¹ * (v : G)⁻¹) =
      (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ by group] at h2
  rw [hdisj, Subgroup.mem_bot] at hc
  exact mul_inv_eq_one.1 hc

theorem mem_aSet_autOn' [Finite G] (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) {X : Subgroup G} {y : G} (hr : 3 ≤ E3.rParam V)
    (hdisj : V ⊓ conjSubgroup V y = ⊥) (hAy : A ≤ conjSubgroup V y) (hAX : A ≤ X)
    (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autOn A V ∈ E3.aSet (3 - E3.mQuot (conjSubgroup V y) A) (autOn X V) := by
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAy (E3.isElemAbelian_conjSubgroup hV y)
  refine ⟨A4.autOn_mono hAX, autOn_ne_bot_of_not_le_centralizer hAN hAC,
    isElemAbelian2_autOn hV hAel hAN, fun B hB hBk => ?_⟩
  refine le_antisymm (fun v hv => ?_) (fun v hv x hx => hv x (hB hx))
  have hB'k : E3.mQuot (conjSubgroup V y) (preB V A B) < 3 := by
    have h1 := E3.mQuot_add (V := conjSubgroup V y) (preB_le B) hAy
    have h2 : E3.mQuot A (preB V A B) = E3.mQuot (autOn A V) B := by
      unfold E3.mQuot
      rw [relIndex_preB hAN]
    omega
  have hCN : V ⊓ Subgroup.centralizer (preB V A B : Set G) ≤
      Subgroup.normalizer (conjSubgroup V y : Set G) := by
    by_contra hC
    have h1 := E3.e3_4_one (le_inf ((preB_le B).trans hAy) ((preB_le B).trans hAN)) hC
    have h2 : ((3 : ℕ) : ℕ∞) ≤ E3.mQuot (conjSubgroup V y) (preB V A B) := hr.trans h1
    have h3 : 3 ≤ E3.mQuot (conjSubgroup V y) (preB V A B) := by exact_mod_cast h2
    omega
  exact mem_fixV_of_mem_normalizer hAN hdisj hAy (hCN ⟨v.2, mem_centralizer_of_mem_fixV hv⟩)

end Pre

section Coord

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def imgD (F : Frame126 T L V) (y : G) (X : Subgroup G) : Subgroup D8 :=
  ((conjSubgroup X y⁻¹).subgroupOf V).map F.β

omit [IsMulCommutative ↥V] in
theorem conj_inv_le {y : G} {X : Subgroup G} (hX : X ≤ conjSubgroup V y) :
    conjSubgroup X y⁻¹ ≤ V := by
  have h := E3.conjSubgroup_mono_left y⁻¹ hX
  rwa [E3.conjSubgroup_conj_inv] at h

theorem card_imgD (F : Frame126 T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G}
    {X : Subgroup G} (hX : X ≤ conjSubgroup V y) : Nat.card (imgD F y X) = Nat.card X := by
  rw [imgD, Subgroup.card_map_of_injective (S126L24.beta_injective F hZ),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (conj_inv_le hX)).toEquiv,
    E3.card_conjSubgroup]

theorem imgD_mono (F : Frame126 T L V) (y : G) {X X' : Subgroup G} (h : X ≤ X') :
    imgD F y X ≤ imgD F y X' :=
  Subgroup.map_mono fun _ hx => E3.conjSubgroup_mono_left y⁻¹ h hx

theorem imgD_injective (F : Frame126 T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {y : G} {X X' : Subgroup G} (hX : X ≤ conjSubgroup V y) (hX' : X' ≤ conjSubgroup V y)
    (h : imgD F y X = imgD F y X') : X = X' := by
  have h1 := Subgroup.map_injective (S126L24.beta_injective F hZ) h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left (conj_inv_le hX),
    inf_of_le_left (conj_inv_le hX')] at h1
  rw [← E3.conjSubgroup_inv_conj X y, h1, E3.conjSubgroup_inv_conj]

theorem isTS_imgD (F : Frame126 T L V) {y : G} {X : Subgroup G}
    (h : ∀ a ∈ X, a ≠ 1 → F.Wt4 (y * a * y⁻¹)) : IsTS (imgD F y X) := by
  rintro _ ⟨x, hx, rfl⟩ hx1
  have hxX : y⁻¹ * x * y ∈ X := by
    have h1 := mem_conjSubgroup_iff.1 (Subgroup.mem_subgroupOf.1 hx)
    rwa [inv_inv] at h1
  have hx1' : y⁻¹ * (x : G) * y ≠ 1 := fun e => hx1 (by
    have : x = 1 := Subtype.ext (by
      calc (x : G) = y * (y⁻¹ * x * y) * y⁻¹ := by group
        _ = 1 := by rw [e]; group)
    rw [this, map_one])
  obtain ⟨hv, h4⟩ := h _ hxX hx1'
  have e : (⟨y * (y⁻¹ * x * y) * y⁻¹, hv⟩ : ↥V) = x := Subtype.ext (by group)
  rwa [e] at h4

end Coord

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem inf_eq_bot_of_not_le (h1227 : Lemma12_6_27) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G} {A : Subgroup G}
    (hAy : A ≤ conjSubgroup V y) (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    V ⊓ conjSubgroup V y = ⊥ := by
  by_contra hne
  have h := h1227 G T L V F hH hZ y hne
  apply hAC
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hv
  exact (Subgroup.mem_centralizer_iff.1 hv' a (hAy ha)).symm

theorem centralizer_le_conj (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) {y a : G} (hay : a ∈ conjSubgroup V y)
    (ha1 : a ≠ 1) (h4 : ¬ F.Wt4 (y * a * y⁻¹)) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (conjSubgroup V y : Set G) := by
  have hxV : y * a * y⁻¹ ∈ V := mem_conjSubgroup_iff.1 hay
  have hx1 : y * a * y⁻¹ ≠ 1 := fun h => ha1 (by
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group)
  have hC := S126L20.centralizer_le_of_not_wt4 h331 h1222 h1262 F hH hxV hx1 h4
  intro c hc
  rw [← E3.conjSubgroup_normalizer, mem_conjSubgroup_iff]
  apply hC
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  calc y * c * y⁻¹ * (y * a * y⁻¹) = y * (c * a) * y⁻¹ := by group
    _ = y * (a * c) * y⁻¹ := by rw [hc]
    _ = y * a * y⁻¹ * (y * c * y⁻¹) := by group

theorem setup (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (h1219 : Lemma12_6_19) (h1227 : Lemma12_6_27) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {A : Subgroup G} {y : G} (hAT : A ≤ T)
    (hAy : A ≤ conjSubgroup V y) (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    A ≤ Subgroup.normalizer (V : Set G) ∧ V ⊓ conjSubgroup V y = ⊥ ∧
      autOn A V ∈ E3.aSet (3 - E3.mQuot (conjSubgroup V y) A) hH.hyp.MVbar := by
  obtain ⟨-, hTV, hVe, -, -⟩ := S126L23a.basics h1222 F hH
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTV
  have hdisj := inf_eq_bot_of_not_le h1227 F hH hZ hAy hAC
  have hr := (S126L20.rParam_bounds h331 h1222 h1262 F hH (h1219 G T L V F hH).1).1
  exact ⟨hAN, hdisj, mem_aSet_autOn' hAN hVe hr hdisj hAy
    (le_inf (hAT.trans hH.hyp.normalizes) hAN) hAC⟩

theorem part3_core (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (h1227 : Lemma12_6_27)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 T) : A ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hAT, y, hAy, hk⟩ := hA
  by_contra hAC
  obtain ⟨-, -, hmem⟩ := setup h331 h1222 h1262 h1219 h1227 F hH hZ hAT hAy hAC
  rw [hk, (lemma12_6_28_one_two F hH hZ).1] at hmem
  exact hmem

theorem part4_core (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (h1227 : Lemma12_6_27)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 1 T) : A ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hAT, y, hAy, hk⟩ := hA
  by_contra hAC
  obtain ⟨hAN, hdisj, hmem⟩ := setup h331 h1222 h1262 h1219 h1227 F hH hZ hAT hAy hAC
  rw [hk] at hmem
  obtain ⟨-, D, hDA, hD8, hE⟩ := (lemma12_6_28_one_two F hH hZ).2 _ hmem
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃, n₁₂, n₁₃, n₂₃⟩ :=
    (Set.two_lt_ncard_iff (Set.finite_of_ncard_pos (by omega))).1 hE
  obtain ⟨-, -, hVe, -, -⟩ := S126L23a.basics h1222 F hH
  have hV64 : Nat.card V = 64 := by
    rw [S126L20.card_V F, hZ, Subgroup.card_bot]
  have hVy2 : IsPGroup 2 (conjSubgroup V y) :=
    E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hVe) y
  have hA32 : Nat.card A = 32 := by
    have h := E3.card_eq_two_pow_mul hVy2 hAy
    rw [E3.card_conjSubgroup, hV64, hk] at h
    omega
  have hcard : ∀ P : Subgroup (MulAut ↥V), P ≤ autOn A V →
      Nat.card (preB V A P) * P.relIndex (autOn A V) = 32 := by
    intro P _
    have h := Subgroup.relIndex_mul_card (H := preB V A P) (K := A)
    rw [inf_of_le_left (preB_le P), relIndex_preB hAN, hA32] at h
    rw [mul_comm]
    exact h
  have hEi : ∀ E ∈ ESet (autOn A V) D, Nat.card (preB V A E) = 8 := by
    intro E hE'
    obtain ⟨hDE, hEA, hDE2, -⟩ := hE'
    have h1 := Subgroup.relIndex_mul_relIndex D E (autOn A V) hDE hEA
    rw [hDE2, hD8] at h1
    have h2 := hcard E hEA
    have h3 : E.relIndex (autOn A V) = 4 := by omega
    rw [h3] at h2
    omega
  have hDi : Nat.card (preB V A D) = 4 := by
    have h := hcard D hDA
    rw [hD8] at h
    omega
  have hTS : ∀ E ∈ ESet (autOn A V) D, ∀ a ∈ preB V A E, a ≠ 1 → F.Wt4 (y * a * y⁻¹) := by
    intro E hE' a ha ha1
    by_contra h4
    obtain ⟨-, -, -, hlt⟩ := hE'
    obtain ⟨v, hvE, hvA⟩ := IsConcreteLE.exists_of_lt hlt
    have hC := centralizer_le_conj h331 h1222 h1262 F hH (hAy (preB_le E ha)) ha1 h4
    have hvc : (v : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha) (mem_centralizer_of_mem_fixV hvE)
    exact hvA (mem_fixV_of_mem_normalizer hAN hdisj hAy (hC hvc))
  have hle : ∀ E ∈ ESet (autOn A V) D, preB V A E ≤ conjSubgroup V y := fun E _ =>
    (preB_le E).trans hAy
  have hne : ∀ E ∈ ESet (autOn A V) D, ∀ E' ∈ ESet (autOn A V) D, E ≠ E' →
      imgD F y (preB V A E) ≠ imgD F y (preB V A E') := by
    intro E hE' E' hE'' hEE' h
    apply hEE'
    have h1 := imgD_injective F hZ (hle E hE') (hle E' hE'') h
    rw [← autOn_preB hE'.2.1, h1, autOn_preB hE''.2.1]
  have hc : ∀ E ∈ ESet (autOn A V) D, Nat.card (imgD F y (preB V A E)) = 8 := fun E hE' => by
    rw [card_imgD F hZ (hle E hE'), hEi E hE']
  exact not_three_ts (D := imgD F y (preB V A D))
    (by rw [card_imgD F hZ ((preB_le D).trans hAy), hDi])
    (imgD_mono F y (preB_mono hE₁.1)) (imgD_mono F y (preB_mono hE₂.1))
    (imgD_mono F y (preB_mono hE₃.1)) (hc _ hE₁) (hc _ hE₂) (hc _ hE₃)
    (isTS_imgD F (hTS _ hE₁)) (isTS_imgD F (hTS _ hE₂)) (isTS_imgD F (hTS _ hE₃))
    (hne _ hE₁ _ hE₂ n₁₂) (hne _ hE₁ _ hE₃ n₁₃) (hne _ hE₂ _ hE₃ n₂₃)

end S126L28

theorem lemma12_6_28_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19)
    (h1227 : Lemma12_6_27) : Lemma12_6_28 := by
  intro G _ _ T L V _ F hH hZ
  obtain ⟨hVT, hTV, hVe, -, -⟩ := S126L23a.basics h1222 F hH
  have hW0 : E3.wClos V 0 T ≤ Subgroup.centralizer (V : Set G) :=
    E3.wClos_le_of_forall fun _ hA =>
      S126L28.part3_core h331 h1222 h1262 h1219 h1227 F hH hZ hA
  have hW1 : E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G) :=
    E3.wClos_le_of_forall fun _ hA =>
      S126L28.part4_core h331 h1222 h1262 h1219 h1227 F hH hZ hA
  have hw : ((2 : ℕ) : ℕ∞) ≤ E3.wParam T V := E3.le_wParam_of_wClos_le fun j hj => by
    interval_cases j
    · exact le_inf (E3.wClos_le 0 T) hW0
    · exact le_inf (E3.wClos_le 1 T) hW1
  have hV64 : Nat.card V = 2 ^ 6 := by
    rw [S126L20.card_V F, hZ, Subgroup.card_bot]
    norm_num
  have hi : 0 < rk ↥V := by
    unfold rk
    rw [hV64, padicValNat.prime_pow]
    norm_num
  have hw0 : ((0 : ℕ) : ℕ∞) < E3.wParam T V := lt_of_lt_of_le (by norm_num) hw
  refine ⟨(lemma12_6_28_one_two F hH hZ).1, (lemma12_6_28_one_two F hH hZ).2, ⟨hW0, ?_⟩,
    ⟨hW1, lt_of_lt_of_le (by norm_num) hw⟩⟩
  exact (E3.e3_34_two hVe ⟨S126L23a.isSylowIn_top hH, hVT, hTV⟩
    (S126L23a.isUniqueM_Q h331 h3228 h1222 F hH) hi hw0).1

end CFSG.Quasithin.H13
