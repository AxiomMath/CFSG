module

public import CFSG.Quasithin.EmptyFaithful.SzN28Lt
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveD
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem17C
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem18A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem18B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem twelve_three_of_eq_ch619 {V V₁ L T : Subgroup G} (S : L128A.Setting V V₁ L T) {g : G}
    (hg : L128A.Good V₁ L g) {U : Subgroup G} (hU : L128A.uA V V₁ = U) (D : HatModelU U)
    (hU4 : 4 < (centerOf U).relIndex U) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
        (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
          rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
        (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
        (D.img (rconj (centerOf U) g)) := by
  subst hU
  exact S.twelve_three hg D hU4 haV haZ

variable {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem g111_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G} (hl : l ∈ lsCh617 T L V)
    (hlH : l ∉ hCh611 T) {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {B : LinearMap.BilinForm (ZMod 2) A} {β : ↥(uCh611 T L V) →* Multiplicative A}
    {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v₁ : A} {Wsp : Submodule (ZMod 2) A}
    (hv₁ : ∀ z : ↥(uCh611 T L V), (z : G) ∈ ch6ZS T L V →
      (z : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β z) = v₁)
    (hW : ∀ a : A, a ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l ∧ Multiplicative.toAdd (β e) = a) :
    G111Hyp B ρ.range v₁ Wsp (((conjSubgroup (uCh611 T L V) l ⊓
        Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ)
        (((conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf (hCh611 T)).map ρ) := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617 h331 h432 h512 h614 h615 hl hlH
  have hU := h.uA_eq_ch617 h331 h432 h512 h614 h615
  have hNZ := h.normalizer_Z_eq_ch617 h331 h432 h512 h614 h615
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hHN : hCh611 T ≤ Subgroup.normalizer (uCh611 T L V : Set G) :=
    hCh611_le_normalizer_u T L V
  obtain ⟨z, -, -, d, -, -, -, haS, haZ, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  set a := d⁻¹ * z * d with ha
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [h.inf_centerOf_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt] at this
    exact haZ this
  have key := twelve_three_of_eq_ch619 S hg hU (realHat_ch618 hR)
    (h.four_lt_ch618 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt) haS haZ
  have hW' : uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) =
      L128A.wA (ch6ZS T L V) (zCh611 T) := (h.wA_eq_ch617 h331 h432 h512 h614 h615).symm
  rw [hW', h.E_eq_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hg,
    h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
    hNZ] at key
  have hXH : conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      hCh611 T := inf_le_right.trans (Subgroup.centralizer_le hZZS)
  have hZX : conjSubgroup (centerOf (uCh611 T L V)) l ≤
      conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have := L128A.Setting.rconj_centerOf_le_rconj_wA (ch6ZS T L V) (zCh611 T) l
    rwa [h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
      hU] at this
  have e1 := realHat_img_self_ch618 hR hHN
  have e2 := realHat_img_ch618 hR hHN hXH
  have e3 := realHat_img_ch618 hR hHN (hZX.trans hXH)
  have e4 : (realHat_ch618 hR).π a = v₁ := by
    rw [realHat_pi_ch618 hR haU]
    exact hv₁ ⟨a, haU⟩ haS haZU
  have e5 := realHat_hat_ch618 hR (E := uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l) Wsp hW
  rw [e1, e2, e3, e4, e5] at key
  exact key

theorem conj_centerOf_le_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {l : G} (hl : l ∈ lsCh617 T L V) :
    conjSubgroup (centerOf (uCh611 T L V)) l ≤ hCh611 T := by
  have hU := h.uA_eq_ch617 h331 h432 h512 h614 h615
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZX : conjSubgroup (centerOf (uCh611 T L V)) l ≤
      conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have := L128A.Setting.rconj_centerOf_le_rconj_wA (ch6ZS T L V) (zCh611 T) l
    rwa [h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
      hU] at this
  exact hZX.trans (inf_le_right.trans (Subgroup.centralizer_le hZZS))

theorem conj_mem_h_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {l w : G} (hl : l ∈ lsCh617 T L V)
    (hw : w ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) : l * w * l⁻¹ ∈ hCh611 T := by
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hlN : l⁻¹ ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    Subgroup.inv_mem _ (ls_le_ch617 hl).2
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hs : l⁻¹ * z * l⁻¹⁻¹ ∈ ch6ZS T L V := (Subgroup.mem_normalizer_iff.mp hlN z).mp (hZZS hz)
  rw [inv_inv] at hs
  have hc := Subgroup.mem_centralizer_iff.mp hw _ hs
  calc z * (l * w * l⁻¹) = l * ((l⁻¹ * z * l) * w) * l⁻¹ := by group
    _ = l * (w * (l⁻¹ * z * l)) * l⁻¹ := by rw [hc]
    _ = l * w * l⁻¹ * z := by group

theorem conj_mem_conj_centerOf_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {l w y : G} (hl : l ∈ lsCh617 T L V)
    (hw : w ∈ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hy : y ∈ conjSubgroup (centerOf (uCh611 T L V)) l) :
    w * y * w⁻¹ ∈ conjSubgroup (centerOf (uCh611 T L V)) l := by
  rw [mem_conjSubgroup_iff] at hy ⊢
  have hlw := h.conj_mem_h_ch619 h331 h432 h512 h614 h615 hl hw
  have hN := (Subgroup.mem_normalizer_iff.mp
    (hCh611_le_normalizer_centerOf_ch615 T L V hlw) _).mp hy
  have e : l * (w * y * w⁻¹) * l⁻¹ = l * w * l⁻¹ * (l * y * l⁻¹) * (l * w * l⁻¹)⁻¹ := by group
  rw [e]
  exact hN

omit [Finite G] h in
theorem centerOf_le_centralizer_ZS_ch619 :
    centerOf (uCh611 T L V) ≤ Subgroup.centralizer (ch6ZS T L V : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (le_conjClosure _ _))

theorem commute_ZU_conj_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) {u y : G} (hu : u ∈ centerOf (uCh611 T L V))
    (hy : y ∈ conjSubgroup (centerOf (uCh611 T L V)) l) : u * y = y * u := by
  have hyH := h.conj_centerOf_le_ch619 h331 h432 h512 h614 h615 hl hy
  have h1 : u * y * u⁻¹ * y⁻¹ ∈ centerOf (uCh611 T L V) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hCh611_le_normalizer_centerOf_ch615 T L V hyH) _).mp (Subgroup.inv_mem _ hu)
    have e : u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu this
  have h2 : u * y * u⁻¹ * y⁻¹ ∈ conjSubgroup (centerOf (uCh611 T L V)) l :=
    Subgroup.mul_mem _ (h.conj_mem_conj_centerOf_ch619 h331 h432 h512 h614 h615 hl
      (centerOf_le_centralizer_ZS_ch619 hu) hy) (Subgroup.inv_mem _ hy)
  have h3 : u * y * u⁻¹ * y⁻¹ ∈ centerOf (uCh611 T L V) ⊓
      conjSubgroup (centerOf (uCh611 T L V)) l := ⟨h1, h2⟩
  rw [h.one_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl hlH,
    Subgroup.mem_bot] at h3
  calc u * y = (u * y * u⁻¹ * y⁻¹) * (y * u) := by group
    _ = y * u := by rw [h3, one_mul]

theorem comm_mem_conj_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) {y w : G}
    (hy : y ∈ conjSubgroup (centerOf (uCh611 T L V)) l)
    (hw : w ∈ uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    y * w * y⁻¹ * w⁻¹ ∈ conjSubgroup (zCh611 T) l := by
  have hyH := h.conj_centerOf_le_ch619 h331 h432 h512 h614 h615 hl hy
  have hl' : l⁻¹ ∈ lsCh617 T L V := Subgroup.inv_mem _ hl
  have hlH' : l⁻¹ ∉ hCh611 T := fun h' => hlH (by simpa using Subgroup.inv_mem _ h')
  have hc1 : y * w * y⁻¹ * w⁻¹ ∈ conjSubgroup (centerOf (uCh611 T L V)) l := by
    have := h.conj_mem_conj_centerOf_ch619 h331 h432 h512 h614 h615 hl hw.2
      (Subgroup.inv_mem _ hy)
    have e : y * w * y⁻¹ * w⁻¹ = y * (w * y⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy this
  have hc2 : y * w * y⁻¹ * w⁻¹ ∈ uCh611 T L V :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hyH) _).mp
      hw.1) (Subgroup.inv_mem _ hw.1)
  have h2 := h.two_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl' hlH'
  rw [h.one_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl' hlH', bot_sup_eq] at h2
  rw [mem_conjSubgroup_iff] at hc1 ⊢
  have hmem : l * (y * w * y⁻¹ * w⁻¹) * l⁻¹ ∈ centerOf (uCh611 T L V) ⊓
      conjSubgroup (uCh611 T L V) l⁻¹ := by
    refine Subgroup.mem_inf.mpr ⟨hc1, ?_⟩
    rw [mem_conjSubgroup_iff]
    have e : l⁻¹ * (l * (y * w * y⁻¹ * w⁻¹) * l⁻¹) * l⁻¹⁻¹ = y * w * y⁻¹ * w⁻¹ := by group
    rw [e]
    exact hc2
  rw [h2] at hmem
  exact hmem

theorem exists_comm_eq_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) {A : Type} [AddCommGroup A]
    [Module (ZMod 2) A] {B : LinearMap.BilinForm (ZMod 2) A}
    {β : ↥(uCh611 T L V) →* Multiplicative A} {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    (h3 : ∀ γ ∈ ρ.range, γ ≠ 1 → ∃ a b : A, γ a ≠ a ∧ γ b ≠ b ∧ γ a - a ≠ γ b - b)
    {y : G} (hy : y ∈ conjSubgroup (centerOf (uCh611 T L V)) l) (hyH : y ∈ hCh611 T)
    (hy1 : ρ ⟨y, hyH⟩ ≠ 1) {z : G} (hzZ : z ∈ zCh611 T) (hz1 : z ≠ 1) :
    ∃ w ∈ uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G),
      y * w * y⁻¹ * w⁻¹ = l⁻¹ * z * l := by
  classical
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  obtain ⟨z', -, -, d, -, -, -, haS, haZ, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  set a := d⁻¹ * z' * d with ha
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  set v₁ : A := Multiplicative.toAdd (β ⟨a, haU⟩) with hv₁
  set γ := ρ ⟨y, hyH⟩ with hγ
  obtain ⟨x, hxB, hxγ⟩ : ∃ x : A, B x v₁ = 0 ∧ γ x ≠ x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a₁, b₁, h1, h2, h3'⟩ := h3 γ ⟨⟨y, hyH⟩, rfl⟩ hy1
    have hB1 : B a₁ v₁ ≠ 0 := fun hz => h1 (hcon a₁ hz)
    have hB2 : B b₁ v₁ ≠ 0 := fun hz => h2 (hcon b₁ hz)
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    have hB3 : B (a₁ + b₁) v₁ = 0 := by
      rw [map_add, LinearMap.add_apply, key _ hB1, key _ hB2]
      decide
    have h4 := hcon _ hB3
    rw [map_add] at h4
    apply h3'
    have huw : (γ a₁ - a₁) + (γ b₁ - b₁) = 0 := by
      calc (γ a₁ - a₁) + (γ b₁ - b₁) = (γ a₁ + γ b₁) - (a₁ + b₁) := by abel
        _ = 0 := by rw [h4]; exact sub_self _
    exact (eq_neg_of_add_eq_zero_left huw).trans
      (neg_eq_of_add_eq_zero_right (SzN28.add_self_zmod_two _))
  obtain ⟨w, hw⟩ := hR.1 (Multiplicative.ofAdd x)
  have hwx : Multiplicative.toAdd (β w) = x := by rw [hw, toAdd_ofAdd]
  have hwa : (w : G) * a * (w : G)⁻¹ * a⁻¹ = 1 := by
    by_contra hne
    have := (hR.2.2.2 w ⟨a, haU⟩).mpr hne
    rw [hwx] at this
    exact this hxB
  have hwz : ∀ z' ∈ zCh611 T, z' * (w : G) = (w : G) * z' := fun z' hz' =>
    Subgroup.mem_centralizer_iff.mp (hUH w.2) z' hz'
  have hwS : (w : G) ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hwa' : a * (w : G) = (w : G) * a := by
      calc a * (w : G) = ((w : G) * a * (w : G)⁻¹ * a⁻¹)⁻¹ * ((w : G) * a) := by group
        _ = (w : G) * a := by rw [hwa, inv_one, one_mul]
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 haZ haS hs with e | e | e | e
    · rw [e, one_mul, mul_one]
    · rw [e]; exact hwz z hzZ
    · rw [e]; exact hwa'
    · rw [e, mul_assoc, hwa', ← mul_assoc, hwz z hzZ, mul_assoc]
  have hwW : (w : G) ∈ uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := ⟨w.2, hwS⟩
  refine ⟨w, hwW, ?_⟩
  have hcZ := h.comm_mem_conj_ch619 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl hlH
    hy hwW
  have hyw : y * (w : G) * y⁻¹ ∈ uCh611 T L V :=
    (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hyH) _).mp w.2
  have hc1 : y * (w : G) * y⁻¹ * (w : G)⁻¹ ≠ 1 := by
    intro hc
    apply hxγ
    have e : (⟨y * (w : G) * y⁻¹, hyw⟩ : ↥(uCh611 T L V)) = w := by
      apply Subtype.ext
      show y * (w : G) * y⁻¹ = w
      calc y * (w : G) * y⁻¹ = (y * (w : G) * y⁻¹ * (w : G)⁻¹) * w := by group
        _ = w := by rw [hc, one_mul]
    have := hR.2.2.1 ⟨y, hyH⟩ w ⟨y * (w : G) * y⁻¹, hyw⟩ rfl
    rw [e, hwx] at this
    exact this.symm
  rw [mem_conjSubgroup_iff] at hcZ
  have hne : l * (y * (w : G) * y⁻¹ * (w : G)⁻¹) * l⁻¹ ≠ 1 := by
    intro h1
    apply hc1
    calc y * (w : G) * y⁻¹ * (w : G)⁻¹ =
        l⁻¹ * (l * (y * (w : G) * y⁻¹ * (w : G)⁻¹) * l⁻¹) * l := by group
      _ = 1 := by rw [h1]; group
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 haZ haS (hZZS hcZ) with e | e | e | e
  · exact absurd e hne
  · calc y * (w : G) * y⁻¹ * (w : G)⁻¹ =
        l⁻¹ * (l * (y * (w : G) * y⁻¹ * (w : G)⁻¹) * l⁻¹) * l := by group
      _ = l⁻¹ * z * l := by rw [e]
  · exact absurd (e ▸ hcZ) haZ
  · exfalso
    apply haZ
    have : a = z⁻¹ * (l * (y * (w : G) * y⁻¹ * (w : G)⁻¹) * l⁻¹) := by rw [e]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzZ) hcZ

theorem inf_centralizerMod_le_ch619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {P : Subgroup G} (hPH : P ≤ hCh611 T)
    (hPn : hCh611 T ≤ Subgroup.normalizer (P : Set G))
    (hPZ : P ≤ Subgroup.centralizer (centerOf (uCh611 T L V) : Set G)) :
    P ⊓ centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) ≤
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  have hO2 := (h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615).2.2.1
  have hZUN := hCh611_le_normalizer_centerOf_ch615 T L V
  refine hO2 _ (inf_le_left.trans hPH) (A1a.le_normalizer_inf hPn
    (le_normalizer_centralizerMod hZUN Subgroup.le_normalizer (hCh611_le_normalizer_u T L V)))
    fun p hp => ⟨1, ?_⟩
  obtain ⟨hpP, hpC⟩ := hp
  obtain ⟨hpH, -, hpU⟩ := mem_centralizerMod.mp hpC
  rw [pow_one]
  refine mem_centralizerMod.mpr ⟨Subgroup.pow_mem _ hpH 2,
    Subgroup.centralizer_le_normalizer _ (Subgroup.pow_mem _ hpH 2), fun u hu => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, p * u * p⁻¹ * u⁻¹ = c := ⟨_, rfl⟩
  have hcZU : c ∈ centerOf (uCh611 T L V) := hc ▸ hpU u hu
  have hpc : c * p = p * c := Subgroup.mem_centralizer_iff.mp (hPZ hpP) c hcZU
  have e1 : p * u * p⁻¹ = c * u := by rw [← hc]; group
  have e2 : p ^ 2 * u * (p ^ 2)⁻¹ * u⁻¹ = c * c := by
    have e3 : p ^ 2 * u * (p ^ 2)⁻¹ * u⁻¹ = p * (p * u * p⁻¹) * p⁻¹ * u⁻¹ := by
      rw [pow_two]; group
    rw [e3, e1]
    have e4 : p * (c * u) * p⁻¹ * u⁻¹ = (p * c) * u * p⁻¹ * u⁻¹ := by group
    rw [e4, ← hpc]
    have e5 : c * p * u * p⁻¹ * u⁻¹ = c * (p * u * p⁻¹) * u⁻¹ := by group
    rw [e5, e1]
    group
  rw [e2, ← pow_two]
  exact h.sq_mem_ch615 h331 h432 h512 h614 h615 hcZU.1

end Hyp6Sec2

end CFSG.Quasithin.H13
