module

public import CFSG.Quasithin.Background.D15Three
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin.Ch3y

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F D15Proof
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_mul_le_of_le {A L N : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hLN : L ≤ N) :
    (Subgroup.centralizer (A : Set G)).relIndex L * (centralizerMod L N A).relIndex N ≤
      (Subgroup.centralizer (A : Set G)).relIndex N := by
  set C := Subgroup.centralizer (A : Set G) with hCdef
  set D := centralizerMod L N A with hDdef
  have hDN : D ≤ N := centralizerMod_le_left L N A
  have hLD : L ≤ D := by
    intro l hl
    refine ⟨hLN hl, Subgroup.le_normalizer hl, fun a ha => ?_⟩
    have h1 : a * l⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) _).mp (L.inv_mem hl)
    have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h1
  have hCD : C ⊓ N ≤ D := by
    rintro x ⟨hxC, hxN⟩
    refine ⟨hxN, hNL hxN, fun a ha => ?_⟩
    have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
    have e : x * a * x⁻¹ * a⁻¹ = 1 := by
      rw [← hxa]
      group
    rw [e]
    exact L.one_mem
  have e2 : (C ⊓ D) ⊓ N = C ⊓ N :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left hCD) inf_le_right)
  have e3 : (C ⊓ D).relIndex N = C.relIndex N := by
    rw [← Subgroup.inf_relIndex_right (C ⊓ D) N, e2, Subgroup.inf_relIndex_right]
  have e1 : C.relIndex N = C.relIndex D * D.relIndex N := by
    have := Subgroup.relIndex_inf_mul_relIndex C D N
    rw [inf_eq_left.mpr hDN, e3] at this
    exact this.symm
  have h1 : C.relIndex L ≤ C.relIndex D :=
    Subgroup.relIndex_le_of_le_right hLD Subgroup.index_ne_zero_of_finite
  calc C.relIndex L * D.relIndex N ≤ C.relIndex D * D.relIndex N := Nat.mul_le_mul_right _ h1
    _ = C.relIndex N := e1.symm

theorem pow_mul_le_relIndex_between {H U A : Subgroup G} (hUH : U ≤ H) (hAH : A ≤ H) {k : ℕ}
    (hk : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N')
    {W N : Subgroup G} {n : ℕ} (h : F112W.IsChiefSeriesBetween H U W N n) :
    (Subgroup.centralizer (A : Set G)).relIndex W * k ^ n ≤
      (Subgroup.centralizer (A : Set G)).relIndex N := by
  induction h with
  | refl => simp
  | @central N L n hstep hc _ ih =>
    exact ih.trans (Subgroup.relIndex_le_of_le_right hstep.2.2.1.le
      Subgroup.index_ne_zero_of_finite)
  | @noncentral N L n hstep hnc _ ih =>
    have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
    have h1 := relIndex_mul_le_of_le (A := A) (L := L) (N := N) (hAH.trans hHL)
      ((hstep.1.1.trans hUH).trans hHL) hstep.2.2.1.le
    calc (Subgroup.centralizer (A : Set G)).relIndex W * k ^ (n + 1)
        = ((Subgroup.centralizer (A : Set G)).relIndex W * k ^ n) * k := by ring
      _ ≤ (Subgroup.centralizer (A : Set G)).relIndex L * (centralizerMod L N A).relIndex N :=
          Nat.mul_le_mul ih (hk L N hstep hnc)
      _ ≤ (Subgroup.centralizer (A : Set G)).relIndex N := h1

theorem step_bound {H U A : Subgroup G} (hUH : U ≤ H) (hAH : A ≤ H) {k : ℕ}
    (hk : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N')
    {L N : Subgroup G} (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) {c : ℕ}
    (hser : IsChiefSeriesFrom H U U c) :
    k ^ (c - 1) * (centralizerMod L N A).relIndex N ≤
      (Subgroup.centralizer (A : Set G)).relIndex U := by
  have hL : IsNormalIn H U L := hstep.2.1
  have hN : IsNormalIn H U N := hstep.1
  have hU : IsNormalIn H U U := F112W.isNormalIn_of_isChiefSeriesFrom hser
  obtain ⟨n₁, hn₁⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := U) L hL
  obtain ⟨n₂, hn₂⟩ := F112W.exists_isChiefSeriesBetween hN U hU hN.1
  have hn1 : IsChiefSeriesFrom H U N (n₁ + 1) := IsChiefSeriesFrom.noncentral hstep hnc hn₁
  have hcc : c = n₂ + (n₁ + 1) := F112W.isChiefSeriesFrom_unique hUH hser (hn₂.append hn1)
  have h1 : k ^ n₁ ≤ (Subgroup.centralizer (A : Set G)).relIndex L :=
    D15Proof.pow_le_relIndex hUH hAH hk hn₁
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hL
  have h2 := relIndex_mul_le_of_le (A := A) (L := L) (N := N) (hAH.trans hHL)
    ((hN.1.trans hUH).trans hHL) hstep.2.2.1.le
  have h3 := pow_mul_le_relIndex_between hUH hAH hk hn₂
  have hc1 : c - 1 = n₁ + n₂ := by omega
  calc k ^ (c - 1) * (centralizerMod L N A).relIndex N
      = k ^ n₁ * (centralizerMod L N A).relIndex N * k ^ n₂ := by rw [hc1, pow_add]; ring
    _ ≤ (Subgroup.centralizer (A : Set G)).relIndex L * (centralizerMod L N A).relIndex N * k ^ n₂ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ ≤ (Subgroup.centralizer (A : Set G)).relIndex N * k ^ n₂ := Nat.mul_le_mul_right _ h2
    _ ≤ (Subgroup.centralizer (A : Set G)).relIndex U := h3

theorem index_eq_two_pow_rkIdx {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (X : Subgroup W) : X.index = 2 ^ rkIdx X := by
  have h1 : Nat.card X = 2 ^ rk X := card_eq_two_pow hW X
  have h2 : Nat.card W = 2 ^ rk W := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have h3 := rk_add_rkIdx X
  have h4 := Subgroup.card_mul_index X
  rw [h1, h2, ← h3, pow_add] at h4
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h4

theorem sq_relIndex_le_of_two_le_qInt {G₁ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G)) (hq : (2 : WithTop ℚ) ≤ qInt G₁ V hV)
    {E : Subgroup G} (hEG₁ : E ≤ G₁) (hE : IsElemAbelian 2 E) (hquad : ⁅⁅V, E⁆, E⁆ = ⊥)
    (hnc : ¬ E ≤ Subgroup.centralizer (V : Set G)) :
    ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 ≤
      (Subgroup.centralizer (E : Set G)).relIndex V := by
  let _ := commGroupOfElemAbelian hV
  have hEN : E ≤ Subgroup.normalizer (V : Set G) := hEG₁.trans hG₁V
  have hne : autOn E V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hEN hnc
  have hel : IsElemAbelian2 (autOn E V) := isElemAbelian2_autOn hV hE hEN
  have hcard : Nat.card (autOn E V) = (Subgroup.centralizer (V : Set G)).relIndex E := by
    rw [card_autOn_eq_relIndex hEN, Subgroup.inf_relIndex_left]
  have hfix : Nat.card (fixV (autOn E V)) =
      Nat.card (V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) := card_fixV_autOn_eq hV hEN
  have hindex : (fixV (autOn E V)).index = (Subgroup.centralizer (E : Set G)).relIndex V := by
    have e1 := Subgroup.card_mul_index (fixV (autOn E V))
    have e2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (E : Set G)) V
    rw [inf_eq_left.mpr inf_le_left, Subgroup.inf_relIndex_left] at e2
    rw [hfix] at e1
    have hpos : 0 < Nat.card (V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) := Nat.card_pos
    have e3 : Nat.card (V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        (fixV (autOn E V)).index = Nat.card (V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
          (Subgroup.centralizer (E : Set G)).relIndex V := by
      rw [e1, mul_comm, e2]
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  have hb : Nat.card (autOn E V) = 2 ^ rk (autOn E V) := card_eq_two_pow_of_isPGroup hel.isPGroup
  have hrk : 0 < rk (autOn E V) := hel.rk_pos hne
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hq' : ((2 : ℚ) : WithTop ℚ) ≤ kq (autOn G₁ V) 2 := by
    have : (2 : WithTop ℚ) = ((2 : ℚ) : WithTop ℚ) := rfl
    rw [← this]
    exact hq
  have h2 := le_kq_iff.mp hq' (autOn E V) ⟨autOn_le_autOn V hEG₁, hne, hel⟩
    (commSeries_autOn_two_eq_bot hV hquad)
  unfold rAV at h2
  have hrkq : (0 : ℚ) < rk (autOn E V) := by exact_mod_cast hrk
  rw [le_div_iff₀ hrkq] at h2
  have h3 : 2 * rk (autOn E V) ≤ rkIdx (fixV (autOn E V)) := by exact_mod_cast h2
  calc ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 = (2 ^ rk (autOn E V)) ^ 2 := by
        rw [← hcard, hb]
    _ = 2 ^ (2 * rk (autOn E V)) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ rkIdx (fixV (autOn E V)) := Nat.pow_le_pow_right (by norm_num) h3
    _ = (fixV (autOn E V)).index := (index_eq_two_pow_rkIdx hV2 _).symm
    _ = (Subgroup.centralizer (E : Set G)).relIndex V := hindex

omit [Finite G] in
theorem relIndex_conj_le {G₁ V R₂ : Subgroup G}
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ G₁ → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 2 ≤
        (Subgroup.centralizer (E₀ : Set G)).relIndex V)
    (hR₂G₁ : R₂ ≤ G₁) {g : G} (hg : g ∈ Subgroup.normalizer (R₂ : Set G)) {E : Subgroup G}
    (hER₂ : E ≤ R₂) (hE : IsElemAbelian 2 E) (hquad : ⁅⁅cjSub g V, E⁆, E⁆ = ⊥)
    (hnc : ¬ E ≤ Subgroup.centralizer (cjSub g V : Set G)) :
    ((Subgroup.centralizer (cjSub g V : Set G)).relIndex E) ^ 2 ≤
      (Subgroup.centralizer (E : Set G)).relIndex (cjSub g V) := by
  have hE₀R₂ : cjSub g⁻¹ E ≤ R₂ := cjSub_le (Subgroup.inv_mem _ hg) hER₂
  have hquad₀ : ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ = ⊥ := by
    have e : (⁅⁅cjSub g V, E⁆, E⁆).map (MulAut.conj g⁻¹).toMonoidHom =
        ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
      have h1 : (cjSub g V).map (MulAut.conj g⁻¹).toMonoidHom = V := cjSub_inv_cjSub g V
      rw [h1]
      rfl
    rw [← e, hquad, Subgroup.map_bot]
  have hnc₀ : ¬ cjSub g⁻¹ E ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hnc
    have := cjSub_mono (g := g) hle
    rwa [cjSub_cjSub_inv, cjSub_centralizer] at this
  have h := hq _ (hE₀R₂.trans hR₂G₁) (isElemAbelian_cjSub hE) hquad₀ hnc₀
  have r1 : (cjSub g (Subgroup.centralizer (V : Set G))).relIndex (cjSub g (cjSub g⁻¹ E)) =
      (Subgroup.centralizer (V : Set G)).relIndex (cjSub g⁻¹ E) :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have r2 : (cjSub g (Subgroup.centralizer (cjSub g⁻¹ E : Set G))).relIndex (cjSub g V) =
      (Subgroup.centralizer (cjSub g⁻¹ E : Set G)).relIndex V :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  rw [cjSub_centralizer, cjSub_cjSub_inv] at r1 r2
  rw [r1, r2]
  exact h

theorem relIndex_decomp {U W E : Subgroup G} (hWU : W ≤ U) :
    (Subgroup.centralizer (U : Set G)).relIndex E =
        (Subgroup.centralizer (U : Set G)).relIndex (Subgroup.centralizer (W : Set G) ⊓ E) *
          (Subgroup.centralizer (W : Set G)).relIndex E ∧
      (Subgroup.centralizer ((Subgroup.centralizer (W : Set G) ⊓ E : Subgroup G) : Set G)).relIndex
          U * (Subgroup.centralizer (E : Set G)).relIndex W ≤
        (Subgroup.centralizer (E : Set G)).relIndex U := by
  set E' := Subgroup.centralizer (W : Set G) ⊓ E with hE'def
  have hE'E : E' ≤ E := inf_le_right
  have hCUW : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le fun x hx => hWU hx
  constructor
  · have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G))
      (Subgroup.centralizer (W : Set G)) E
    rw [inf_eq_left.mpr hCUW] at this
    exact this.symm
  · have hCEE' : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (E' : Set G) :=
      Subgroup.centralizer_le fun x hx => hE'E hx
    have e2 : (Subgroup.centralizer (E : Set G)).relIndex U =
        (Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E' : Set G) ⊓ U) *
          (Subgroup.centralizer (E' : Set G)).relIndex U := by
      have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (E : Set G))
        (Subgroup.centralizer (E' : Set G)) U
      rw [inf_eq_left.mpr hCEE'] at this
      exact this.symm
    have hWE' : W ≤ Subgroup.centralizer (E' : Set G) ⊓ U :=
      le_inf (Subgroup.le_centralizer_iff.mp inf_le_left) hWU
    have i3 : (Subgroup.centralizer (E : Set G)).relIndex W ≤
        (Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E' : Set G) ⊓ U) :=
      Subgroup.relIndex_le_of_le_right hWE' Subgroup.index_ne_zero_of_finite
    rw [e2, mul_comm]
    exact Nat.mul_le_mul_right _ i3

theorem sq_relIndex_le_nonstrict {V H B : Subgroup G}
    (hQ : ∀ h ∈ H, ∀ E : Subgroup G, E ≤ B → ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) →
      ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub h V)) :
    ∀ E : Subgroup G, E ≤ B →
      ((Subgroup.centralizer (conjClosure V H : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (conjClosure V H) := by
  set U := conjClosure V H with hUdef
  intro E
  induction E using WellFoundedLT.induction with
  | _ E ih =>
    intro hEB
    by_cases hEU : E ≤ Subgroup.centralizer (U : Set G)
    · rw [Subgroup.relIndex_eq_one.mpr hEU, one_pow]
      exact Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    obtain ⟨h, hh, hEW⟩ : ∃ h ∈ H, ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) := by
      by_contra hall
      push Not at hall
      exact hEU (le_centralizer_conjClosure_of_forall hall)
    set W := cjSub h V with hWdef
    set E' := Subgroup.centralizer (W : Set G) ⊓ E with hE'def
    have hWU : W ≤ U := cjSub_le_conjClosure hh
    have hE'E : E' ≤ E := inf_le_right
    have hE'lt : E' < E := lt_of_le_of_ne hE'E fun he => hEW (he ▸ inf_le_left)
    have ih1 := ih E' hE'lt (hE'E.trans hEB)
    have hq := hQ h hh E hEB hEW
    obtain ⟨e1, e2⟩ := relIndex_decomp (U := U) (W := W) (E := E) hWU
    rw [e1, mul_pow]
    exact (Nat.mul_le_mul ih1 hq).trans e2

theorem sq_eq_of_eq {V H B : Subgroup G}
    (hQ : ∀ h ∈ H, ∀ E : Subgroup G, E ≤ B → ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) →
      ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub h V))
    {h : G} (hh : h ∈ H) (hBW : ¬ B ≤ Subgroup.centralizer (cjSub h V : Set G))
    (heq : ((Subgroup.centralizer (conjClosure V H : Set G)).relIndex B) ^ 2 =
      (Subgroup.centralizer (B : Set G)).relIndex (conjClosure V H)) :
    ((Subgroup.centralizer (cjSub h V : Set G)).relIndex B) ^ 2 =
      (Subgroup.centralizer (B : Set G)).relIndex (cjSub h V) := by
  set U := conjClosure V H with hUdef
  set W := cjSub h V with hWdef
  set E' := Subgroup.centralizer (W : Set G) ⊓ B with hE'def
  have hWU : W ≤ U := cjSub_le_conjClosure hh
  have ih1 := sq_relIndex_le_nonstrict (V := V) (H := H) (B := B) hQ E' inf_le_right
  have hq := hQ h hh B le_rfl hBW
  obtain ⟨e1, e2⟩ := relIndex_decomp (U := U) (W := W) (E := B) hWU
  rw [e1, mul_pow] at heq
  have h4 := Nat.mul_le_mul ih1 hq
  have h5 : (Subgroup.centralizer ((E' : Subgroup G) : Set G)).relIndex U *
      (Subgroup.centralizer (B : Set G)).relIndex W =
      ((Subgroup.centralizer (U : Set G)).relIndex E') ^ 2 *
        ((Subgroup.centralizer (W : Set G)).relIndex B) ^ 2 :=
    le_antisymm (heq ▸ e2) h4
  by_contra hne
  have hlt := lt_of_le_of_ne hq hne
  have hXpos : 0 < (Subgroup.centralizer ((E' : Subgroup G) : Set G)).relIndex U :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (ne_of_gt (Nat.mul_lt_mul_of_le_of_lt ih1 hlt hXpos)) h5

theorem eq_of_le_of_relIndex_le {K₁ K₂ A : Subgroup G} (h : K₁ ≤ K₂) (hK₂A : K₂ ≤ A)
    (hidx : K₁.relIndex A ≤ K₂.relIndex A) : K₁ = K₂ := by
  have h1 := Subgroup.relIndex_mul_relIndex K₁ K₂ A h hK₂A
  have hpos : 0 < K₂.relIndex A := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h2 : K₁.relIndex K₂ * K₂.relIndex A ≤ 1 * K₂.relIndex A := by
    rw [h1, one_mul]
    exact hidx
  have h3 : K₁.relIndex K₂ ≤ 1 := Nat.le_of_mul_le_mul_right h2 hpos
  have h4 : K₁.relIndex K₂ = 1 := le_antisymm h3
    (Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite)
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp h4)

section Chain

variable {G₁ G₂ T V M₂ : Subgroup G}

theorem chain_two (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (hD125 : D125 G₂ T (conjClosure V G₂))
    (hq2 : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c)
    {A : Subgroup G} (hAT : A ≤ T) (hAe : IsElemAbelian 2 A)
    (hAq : ⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥)
    (hAnc : ¬ A ≤ Subgroup.centralizer (conjClosure V G₂ : Set G))
    (hAoff : Nat.card (conjClosure V G₂) ≤
      (A ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex A *
        Nat.card (conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :
    c = 2 ∧
    (Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex (pCoreOf 2 G₂ ⊓ A) =
      (pCoreOf 2 G₂).relIndex A ∧
    (Subgroup.centralizer (A : Set G)).relIndex (conjClosure V G₂) =
      ((pCoreOf 2 G₂).relIndex A) ^ 2 ∧
    (Subgroup.centralizer ((pCoreOf 2 G₂ ⊓ A : Subgroup G) : Set G)).relIndex (conjClosure V G₂) =
      ((pCoreOf 2 G₂).relIndex A) ^ 2 ∧
    (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
      (centralizerMod L N A).relIndex N = (pCoreOf 2 G₂).relIndex A ∧
        centralizerMod L A N = pCoreOf 2 G₂ ⊓ A) ∧
    (∀ k ∈ G₂, ¬ (pCoreOf 2 G₂ ⊓ A) ≤ Subgroup.centralizer (cjSub k V : Set G) →
      ((Subgroup.centralizer (cjSub k V : Set G)).relIndex (pCoreOf 2 G₂ ⊓ A)) ^ 2 =
        (Subgroup.centralizer ((pCoreOf 2 G₂ ⊓ A : Subgroup G) : Set G)).relIndex (cjSub k V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.reduced.2.2.1
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₁ : T ≤ G₁ := h.sylow₁.1
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := commutator_ne_bot h
  have hAG₂ : A ≤ G₂ := hAT.trans hTG₂
  set B := R₂ ⊓ A with hBdef
  have hBA : B ≤ A := inf_le_right
  have hCAU : A ⊓ Subgroup.centralizer (U : Set G) ≤ R₂ :=
    inf_centralizer_le_pCoreOf hmp hG₂U hUP hAT
  have ha0 : 0 < R₂.relIndex A := Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hb0 : 0 < (Subgroup.centralizer (U : Set G)).relIndex B :=
    Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hab : (Subgroup.centralizer (U : Set G)).relIndex A =
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G)) R₂ A
    have e : (Subgroup.centralizer (U : Set G) ⊓ R₂).relIndex A =
        (Subgroup.centralizer (U : Set G)).relIndex A := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G) ⊓ R₂),
        ← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G)) A]
      congr 1
      refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left ?_)
        inf_le_right)
      rintro x ⟨hxC, hxA⟩
      exact hCAU ⟨hxA, hxC⟩
    rw [e] at this
    exact this.symm
  have hi : (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
    have hpos : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := Nat.card_pos
    have hoff' : Nat.card U ≤ (Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := by
      rw [Subgroup.inf_relIndex_left] at hAoff
      rwa [inf_comm] at hAoff
    rw [← hab]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e2]
    exact hoff'
  have hk : ∀ L' N' : Subgroup G, IsChiefStep G₂ U L' N' → ¬ IsCentralStep G₂ L' N' →
      R₂.relIndex A ≤ (centralizerMod L' N' A).relIndex N' := by
    intro L' N' hstep hnc
    have hquadN : ⁅⁅N', A⁆, A⁆ ≤ L' := by
      have : ⁅⁅N', A⁆, A⁆ ≤ ⁅⁅U, A⁆, A⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hstep.1.1 le_rfl) le_rfl
      rw [hAq] at this
      exact this.trans bot_le
    refine (Subgroup.relIndex_le_of_le_left
      (centralizerMod_le_pCoreOf hmp hUT hstep hnc hAT) (relIndex_ne_zero _ _)).trans ?_
    exact hD125 L' N' hstep hnc A hAT hAe hquadN
  have hpow : (R₂.relIndex A) ^ c ≤ (Subgroup.centralizer (A : Set G)).relIndex U :=
    pow_le_relIndex hUG₂ hAG₂ hk hser
  have hii : (R₂.relIndex A) ^ 2 ≤ (Subgroup.centralizer (A : Set G)).relIndex U :=
    (Nat.pow_le_pow_right ha0 hc).trans hpow
  have hq2' : ∀ E₀ : Subgroup G, E₀ ≤ G₁ → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 2 ≤
        (Subgroup.centralizer (E₀ : Set G)).relIndex V :=
    fun E₀ hE hEe hquad hnc => sq_relIndex_le_of_two_le_qInt hV h.reduced.2.1 hq2 hE hEe hquad hnc
  have hQ : ∀ k ∈ G₂, ∀ E : Subgroup G, E ≤ B →
      ¬ E ≤ Subgroup.centralizer (cjSub k V : Set G) →
      ((Subgroup.centralizer (cjSub k V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub k V) := by
    intro k hk' E hEB hnc
    have hEA : E ≤ A := hEB.trans hBA
    have hquad : ⁅⁅cjSub k V, E⁆, E⁆ = ⊥ := by
      have : ⁅⁅cjSub k V, E⁆, E⁆ ≤ ⁅⁅U, A⁆, A⁆ := Subgroup.commutator_mono
        (Subgroup.commutator_mono (cjSub_le_conjClosure hk') hEA) hEA
      rw [hAq] at this
      exact le_bot_iff.mp this
    exact relIndex_conj_le hq2' (hR₂T.trans hTG₁) (hG₂R₂ hk') (hEB.trans inf_le_left)
      (isElemAbelian_mono hEA hAe) hquad hnc
  have hiii := sq_relIndex_le_nonstrict (V := V) (H := G₂) (B := B) hQ B le_rfl
  have hiv : (Subgroup.centralizer (B : Set G)).relIndex U ≤
      (Subgroup.centralizer (A : Set G)).relIndex U :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le fun x hx => hBA hx)
      (relIndex_ne_zero _ _)
  obtain ⟨heq, hvb⟩ := eq_of_le_mul ha0 hb0 hi hii hiii hiv
  have hu : (Subgroup.centralizer (A : Set G)).relIndex U = (R₂.relIndex A) ^ 2 := by
    refine le_antisymm ?_ hii
    calc (Subgroup.centralizer (A : Set G)).relIndex U
        ≤ (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := hi
      _ = (R₂.relIndex A) ^ 2 := by rw [← heq]; ring
  have hv : (Subgroup.centralizer (B : Set G)).relIndex U = (R₂.relIndex A) ^ 2 := by
    rw [hvb, ← heq]
  have ha2 : 2 ≤ R₂.relIndex A := by
    by_contra hlt
    have ha1 : R₂.relIndex A = 1 := by omega
    have hAR₂ : A ≤ R₂ := Subgroup.relIndex_eq_one.mp ha1
    have hb1 : (Subgroup.centralizer (U : Set G)).relIndex B = 1 := by rw [← heq, ha1]
    have hBU : B ≤ Subgroup.centralizer (U : Set G) := Subgroup.relIndex_eq_one.mp hb1
    have hBeq : B = A := inf_eq_right.mpr hAR₂
    exact hAnc (hBeq ▸ hBU)
  have hc2 : c = 2 := by
    have h1 : (R₂.relIndex A) ^ c ≤ (R₂.relIndex A) ^ 2 := hu ▸ hpow
    have := (Nat.pow_le_pow_iff_right (by omega : 1 < R₂.relIndex A)).mp h1
    omega
  refine ⟨hc2, heq.symm, hu, hv, fun L N hstep hnc => ?_, fun k hk' hBW => ?_⟩
  ·
    have hb := step_bound hUG₂ hAG₂ hk hstep hnc hser
    have hu₀ : (centralizerMod L N A).relIndex N ≤ R₂.relIndex A := by
      have h1 : R₂.relIndex A * (centralizerMod L N A).relIndex N ≤
          R₂.relIndex A * R₂.relIndex A := by
        have := hb
        rw [hc2, hu] at this
        simpa [sq] using this
      exact Nat.le_of_mul_le_mul_left h1 ha0
    have hu₀eq : (centralizerMod L N A).relIndex N = R₂.relIndex A :=
      le_antisymm hu₀ (hk L N hstep hnc)
    refine ⟨hu₀eq, ?_⟩
    have hquadN : ⁅⁅N, A⁆, A⁆ ≤ L := by
      have : ⁅⁅N, A⁆, A⁆ ≤ ⁅⁅U, A⁆, A⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hstep.1.1 le_rfl) le_rfl
      rw [hAq] at this
      exact this.trans bot_le
    have hD'B : centralizerMod L A N ≤ B :=
      le_inf (centralizerMod_le_pCoreOf hmp hUT hstep hnc hAT) (centralizerMod_le_left L A N)
    have hD'A : centralizerMod L A N ≤ A := centralizerMod_le_left L A N
    have hidx : (centralizerMod L A N).relIndex A ≤ B.relIndex A := by
      have h1 := hD125 L N hstep hnc A hAT hAe hquadN
      have h2 : B.relIndex A = R₂.relIndex A := by
        rw [hBdef, Subgroup.inf_relIndex_right R₂ A]
      rw [h2, ← hu₀eq]
      exact h1
    exact eq_of_le_of_relIndex_le hD'B hBA hidx
  ·
    exact sq_eq_of_eq (V := V) (H := G₂) (B := B) hQ hk' hBW hvb.symm

theorem c_eq_two (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (hD125 : D125 G₂ T (conjClosure V G₂))
    (hq2 : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) : c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUe : IsElemAbelian 2 U := isElemAbelian_conjClosure h hnff hVR₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := commutator_ne_bot h
  obtain ⟨A₀, hA₀, hA₀U⟩ : ∃ A₀, IsMaxElemAbelian T A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer (U : Set G) := by
    by_contra hall
    push Not at hall
    have hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (U : Set G) :=
      iSup₂_le fun A hA => le_inf hA.1 (hall A hA)
    apply h.not_thompsonJ_le_pCoreOf hnff
    rw [← h.thompsonJ_eq hnff]
    exact hJ.trans (inf_centralizer_le_pCoreOf hmp hG₂U hUP le_rfl)
  have hA₀N : A₀ ≤ Subgroup.normalizer (U : Set G) := (hA₀.1.trans hTG₂).trans hG₂U
  obtain ⟨A, hAA₀, hAU, hAquad, hAoff⟩ := exists_quadratic_offender hUe hA₀N hA₀.2.1 hA₀U
    (card_le_relIndex_mul_card hUe hUT hA₀)
  exact (chain_two h hnff hVR₂ hD125 hq2 hc hser (hAA₀.trans hA₀.1)
    (isElemAbelian_mono hAA₀ hA₀.2.1) hAquad hAU hAoff).1

end Chain

end CFSG.Quasithin.Ch3y
