module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Red
public import CFSG.Quasithin.H13.GoldschmidtC137L3Off
public import CFSG.Quasithin.Background.C124AsmNormal

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cjSub_one_gc (A : Subgroup G) : cjSub 1 A = A := by
  ext x
  rw [mem_cjSub]
  simp

theorem isPGroup_pCoreOf_two_gc [Finite G] (P : Subgroup G) : IsPGroup 2 (pCoreOf 2 P) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P

structure L32Ctx (X T L P W : Subgroup G) (u : G) : Prop where
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hTP : T ≤ P
  hPX : P < X
  hred : IsTwoReducedIn X W
  hWL : ⁅W, L⁆ = W
  hW8 : Nat.card W = 8
  huW : u ∈ W
  hu1 : u ≠ 1
  hP : P = X ⊓ centralizer ({u} : Set G)

namespace L32Ctx

variable [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
include h

omit [Finite G] in
theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

omit [Finite G] in
theorem hXN : X ≤ normalizer (W : Set G) := h.hred.2.1

omit [Finite G] in
theorem hWe : IsElemAbelian 2 W := h.hred.2.2.1

omit [Finite G] in
theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T :=
  pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

omit [Finite G] in
theorem hpu {p : G} (hp : p ∈ P) : p * u * p⁻¹ = u := by
  have h1 : p ∈ centralizer ({u} : Set G) := by
    have := h.hP ▸ hp
    exact this.2
  have h2 := Subgroup.mem_centralizer_iff.1 h1 u rfl
  rw [← h2, mul_inv_cancel_right]

theorem autI_L_top : autI h.hWe L = ⊤ :=
  (autI_L_eq_top h.hL h.lie h.hXN h.hWe h.hWL h.hW8).1

@[expose] def uM : IntMod W h.hWe := IntMod.mk h.hWe ⟨u, h.huW⟩

omit [Finite G] in
theorem uM_ne_one : uM h ≠ 1 := fun h1 => h.hu1 (congrArg IntMod.val h1)

theorem autI_P_eq_stabM (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec) :
    autI h.hWe P = stabM φ (uM h) := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, hp, rfl⟩ := (mem_autI h.hWe).1 ha
    rw [mem_stabM]
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact h.hpu hp
  · intro ha
    rw [mem_stabM] at ha
    have hla : a ∈ autI h.hWe L := by rw [h.autI_L_top]; trivial
    obtain ⟨l, hlL, rfl⟩ := (mem_autI h.hWe).1 hla
    refine (mem_autI h.hWe).2 ⟨l, ?_, rfl⟩
    have h1 := congrArg IntMod.val ha
    rw [convI_apply_val] at h1
    have hc : (l : G) ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have h2 : (l : G) * u = u * l := by
        calc (l : G) * u = ((l : G) * u * (l : G)⁻¹) * l := by group
          _ = u * l := by rw [show (l : G) * u * (l : G)⁻¹ = u from h1]
      exact h2.symm
    rw [h.hP]
    exact ⟨h.hLX hlL, hc⟩

theorem autI_eq_v4M_of_normal (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec) {Y : Subgroup G}
    (hYR : Y ≤ pCoreOf 2 P) (hY : ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y)
    (hY1 : autI h.hWe Y ≠ ⊥) : autI h.hWe Y = v4M φ (uM h) (uM_ne_one h) := by
  refine normal2_stabM φ (uM_ne_one h) _ ?_ ?_ ?_ hY1
  · rw [← h.autI_P_eq_stabM φ]
    exact autI_mono h.hWe (hYR.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P))
  · intro g hg n hn
    rw [← h.autI_P_eq_stabM φ] at hg
    obtain ⟨p, hp, rfl⟩ := (mem_autI h.hWe).1 hg
    obtain ⟨y, hy, rfl⟩ := (mem_autI h.hWe).1 hn
    refine (mem_autI h.hWe).2 ⟨p * y * p⁻¹, ?_, by simp [map_mul, map_inv]⟩
    simpa using hY _ hp _ hy
  · intro k
    obtain ⟨y, hy, hk⟩ := (mem_autI h.hWe).1 k.2
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf_two_gc P ⟨(y : G), hYR hy⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hj' : (y : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have : convI h.hWe (y ^ 2 ^ j) = 1 := by
      rw [convI_eq_one_iff]
      rw [Subgroup.coe_pow, hj']
      exact one_mem _
    rw [map_pow] at this
    show (k : MulAut (IntMod W h.hWe)) ^ 2 ^ j = 1
    rw [← hk]
    exact this

theorem autI_X_top : autI h.hWe X = ⊤ :=
  top_le_iff.1 (h.autI_L_top ▸ autI_mono h.hWe h.hLX)

theorem autI_R_eq_v4M (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec)
    (hR1 : autI h.hWe (pCoreOf 2 P) ≠ ⊥) :
    autI h.hWe (pCoreOf 2 P) = v4M φ (uM h) (uM_ne_one h) :=
  h.autI_eq_v4M_of_normal φ le_rfl (fun p hp y hy => by
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp
    exact (Subgroup.mem_normalizer_iff.1 this y).1 hy |> fun h' => by simpa using h') hR1

omit [Finite G] in
theorem exists_A_of_mem_offenderImages {R : Subgroup G} {B : Subgroup (MulAut (IntMod W h.hWe))}
    (hB : B ∈ C124.offenderImagesConjIn h.hWe X R) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian R A₀ ∧ Nat.card (autI h.hWe A₀) = Nat.card B := by
  obtain ⟨hB0, A, rfl, g, hg, hmax⟩ := hB
  refine ⟨cjSub g⁻¹ A, hmax, ?_⟩
  rw [← autI_cjSub h.hWe (h.hXN (X.inv_mem hg)) A]
  exact Nat.card_congr ((autI h.hWe A).equivMapOfInjective _
    (MulAut.conj _).injective).toEquiv.symm

theorem exists_offender_order_two (φ : IntMod W h.hWe ≃* Multiplicative L3.Vec)
    (hst : IsStableFF (autI h.hWe X) (C124.offenderImagesConjIn h.hWe X (pCoreOf 2 P))) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian (pCoreOf 2 P) A₀ ∧ Nat.card (autI h.hWe A₀) = 2 := by
  set R := pCoreOf 2 P with hR
  obtain ⟨B, hB⟩ := hst.1
  obtain ⟨A₁, hA₁, hc1⟩ := h.exists_A_of_mem_offenderImages hB
  have hB1 : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot _).2 hB.1
  have hN1 : autI h.hWe A₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hc1
    omega
  have hAR : A₁ ≤ R := hA₁.1
  have hRne : autI h.hWe R ≠ ⊥ := fun hb =>
    hN1 (le_bot_iff.1 (hb ▸ autI_mono h.hWe hAR))
  have hV4 := h.autI_R_eq_v4M φ hRne
  have hNle : autI h.hWe A₁ ≤ v4M φ (uM h) (uM_ne_one h) := hV4 ▸ autI_mono h.hWe hAR
  have hdvd : Nat.card (autI h.hWe A₁) ∣ 4 := by
    rw [← card_v4M φ (uM_ne_one h)]
    exact Subgroup.card_dvd_of_le hNle
  have hN1' : 1 < Nat.card (autI h.hWe A₁) := (Subgroup.one_lt_card_iff_ne_bot _).2 hN1
  have hcases : Nat.card (autI h.hWe A₁) = 2 ∨ Nat.card (autI h.hWe A₁) = 4 := by
    have h4 : Nat.card (autI h.hWe A₁) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hk : Nat.card (autI h.hWe A₁)
    · omega
    · exact absurd hdvd (by norm_num)
    · omega
  rcases hcases with h2 | h4
  · exact ⟨A₁, hA₁, h2⟩
  ·
    have hNeq : autI h.hWe A₁ = v4M φ (uM h) (uM_ne_one h) :=
      Subgroup.eq_of_le_of_card_ge hNle (by rw [card_v4M φ (uM_ne_one h), h4])
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      ((Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [card_v4M φ (uM_ne_one h)]; norm_num) :
        v4M φ (uM h) (uM_ne_one h) ≠ ⊥)
    have ha1 : (a : MulAut (IntMod W h.hWe)) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    have ha2 : (a : MulAut (IntMod W h.hWe)) ^ 2 = 1 := v4M_sq φ a.2
    set B' := Subgroup.zpowers (a : MulAut (IntMod W h.hWe)) with hB'
    have hB'card : Nat.card B' = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [hB', Nat.card_zpowers]
      exact orderOf_eq_prime ha2 ha1
    have hB'le : B' ≤ autI h.hWe A₁ := by
      rw [hNeq, hB']
      exact Subgroup.zpowers_le.2 a.2
    have hFF : FFLe (autI h.hWe X) B' (autI h.hWe A₁) := by
      refine ⟨⟨?_, ?_, isElemAbelian2_zpowers_gc ha2⟩, ⟨?_, hN1, ?_⟩, hB'le, ?_⟩
      · rw [h.autI_X_top]; exact le_top
      · intro hb
        rw [hb, Subgroup.card_bot] at hB'card
        omega
      · rw [h.autI_X_top]; exact le_top
      · rw [hNeq]
        exact isElemAbelian2_v4M φ _ _
      · rw [card_fixV_zpowers_invol φ ha2 ha1, hB'card, hNeq, card_fixV_v4M φ (uM_ne_one h),
          card_v4M φ (uM_ne_one h)]
    have hNmem : autI h.hWe A₁ ∈ C124.offenderImagesConjIn h.hWe X R :=
      ⟨hN1, A₁, rfl, 1, X.one_mem, by rwa [inv_one, cjSub_one_gc]⟩
    have hB'mem := hst.2.2.2 _ hNmem B' hFF
    obtain ⟨A₀, hA₀, hc0⟩ := h.exists_A_of_mem_offenderImages hB'mem
    exact ⟨A₀, hA₀, by rw [hc0, hB'card]⟩

end L32Ctx

end CFSG.Quasithin.H13.U3.GC137
