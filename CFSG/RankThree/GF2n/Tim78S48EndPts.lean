module

public import CFSG.RankThree.GF2n.Tim78S48EndSplit
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.GF2n.Tim78S42

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Meet45 (B Q P : Subgroup G) : Prop :=
  ∀ r : G, conjSubgroup r B ⊓ Q ≠ ⊥ → conjSubgroup r B ≤ P

namespace EndHelp

theorem conj_inv_conj (r : G) (A : Subgroup G) : conjSubgroup r⁻¹ (conjSubgroup r A) = A := by
  rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem conj_le_conj_iff (r : G) {A A' : Subgroup G} :
    conjSubgroup r A ≤ conjSubgroup r A' ↔ A ≤ A' :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj r).injective

theorem conj_eq_bot_iff (r : G) {A : Subgroup G} : conjSubgroup r A = ⊥ ↔ A = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj r).injective

theorem conj_le_of_mem_normalizer {L : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (L : Set G)) {A : Subgroup G} (hA : A ≤ L) :
    conjSubgroup r A ≤ L := by
  have := (conj_le_conj_iff r).mpr hA
  rwa [conjSubgroup_eq_self_iff.mpr hr] at this

theorem sup_comm_of {A₁ A₂ Y : Subgroup G} (h₁ : ∀ x ∈ A₁, ∀ y ∈ Y, x * y = y * x)
    (h₂ : ∀ x ∈ A₂, ∀ y ∈ Y, x * y = y * x) : ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ Y, x * y = y * x := by
  have : A₁ ⊔ A₂ ≤ Subgroup.centralizer (Y : Set G) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (h₁ x hx y hy).symm)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (h₂ x hx y hy).symm)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (this hx) y hy).symm

theorem inf_conj_eq_bot_of_ne [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
    {r₁ r₂ : G} (h : conjSubgroup r₁ B ≠ conjSubgroup r₂ B) :
    conjSubgroup r₁ B ⊓ conjSubgroup r₂ B = ⊥ := by
  have e : conjSubgroup (r₂ * r₁⁻¹) (conjSubgroup r₁ B) = conjSubgroup r₂ B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have := inf_conjSubgroup_eq_bot_of_isTI (isTI_conjSubgroup H.ti r₁) (g := r₂ * r₁⁻¹)
    (by rw [e]; exact fun h' => h h'.symm)
  rwa [e] at this

end EndHelp

open EndHelp

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G}
  {C L : Subgroup G} (E : EndgameData M B Q P T g C L) (H : Hyp4 M B Q P T)
include E H

theorem L_inf_Q : L ⊓ Q = C := by
  refine le_antisymm (fun l hl => ?_) (le_inf E.C_le_L (E.C_le_Q H))
  have hlL := hl.1
  rw [E.hL] at hlL
  obtain ⟨c, hc, z, hz, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (E.C_cent y hy x hx).symm) hlL
  have hzQ : z ∈ Q := by
    have := Q.mul_mem (Q.inv_mem (E.C_le_Q H hc)) hl.2
    simpa using this
  have : z ∈ conjSubgroup g B ⊓ Q := ⟨hz, hzQ⟩
  rw [E.Bg_inf, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hc

theorem L_inf_P : L ⊓ P = C :=
  le_antisymm ((inf_le_inf_left L H.P_le_Q).trans (E.L_inf_Q H).le)
    (le_inf E.C_le_L E.C_le_P)

theorem conj_inf_Q {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) :
    L ⊓ conjSubgroup r Q = conjSubgroup r C := by
  have hrL : conjSubgroup r L = L := conjSubgroup_eq_self_iff.mpr hr
  calc L ⊓ conjSubgroup r Q = conjSubgroup r L ⊓ conjSubgroup r Q := by rw [hrL]
    _ = conjSubgroup r (L ⊓ Q) := (conjSubgroup_inf r L Q).symm
    _ = conjSubgroup r C := by rw [E.L_inf_Q H]

theorem conj_inf_P {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) :
    L ⊓ conjSubgroup r P = conjSubgroup r C := by
  have hrL : conjSubgroup r L = L := conjSubgroup_eq_self_iff.mpr hr
  calc L ⊓ conjSubgroup r P = conjSubgroup r L ⊓ conjSubgroup r P := by rw [hrL]
    _ = conjSubgroup r (L ⊓ P) := (conjSubgroup_inf r L P).symm
    _ = conjSubgroup r C := by rw [E.L_inf_P H]

theorem pt_le_conjC (h45 : Meet45 B Q P) {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G))
    {D : Subgroup G} (hD : D ∈ classIn B L) (hne : D ⊓ conjSubgroup r C ≠ ⊥) :
    D ≤ conjSubgroup r C := by
  obtain ⟨⟨r', rfl⟩, hDL⟩ := hD
  have h1 : conjSubgroup (r⁻¹ * r') B ⊓ Q ≠ ⊥ := by
    intro hbot
    apply hne
    have : conjSubgroup r⁻¹ (conjSubgroup r' B ⊓ conjSubgroup r C) = ⊥ := by
      rw [conjSubgroup_inf, conj_inv_conj, ← conjSubgroup_mul]
      rw [eq_bot_iff]
      exact (inf_le_inf_left _ (E.C_le_Q H)).trans hbot.le
    exact (conj_eq_bot_iff r⁻¹).mp this
  have h2 := h45 _ h1
  have h3 : conjSubgroup r' B ≤ conjSubgroup r P := by
    have := (conj_le_conj_iff r).mpr h2
    rwa [← conjSubgroup_mul, mul_inv_cancel_left] at this
  rw [← E.conj_inf_P H hr]
  exact le_inf hDL h3

theorem symm_Q {r r' : G} (h : conjSubgroup r' B ≤ conjSubgroup r Q)
    (hne : conjSubgroup r' B ≠ conjSubgroup r B) : conjSubgroup r B ≤ conjSubgroup r' Q := by
  have h1 : conjSubgroup (r⁻¹ * r') B ≤ Q := by
    have := (conj_le_conj_iff r⁻¹).mpr h
    rwa [← conjSubgroup_mul, conj_inv_conj] at this
  have h2 : conjSubgroup (r⁻¹ * r') B ≠ B := by
    intro heq
    apply hne
    have := congrArg (conjSubgroup r) heq
    rwa [← conjSubgroup_mul, mul_inv_cancel_left] at this
  have h3 := H.le_conjSubgroup_Q h1 h2
  have := (conj_le_conj_iff r).mpr h3
  rwa [← conjSubgroup_mul, mul_inv_cancel_left] at this

theorem Bg_ne_bot : conjSubgroup g B ≠ ⊥ := fun h => H.B_ne_bot ((conj_eq_bot_iff g).mp h)

omit H in
theorem B_mem_classIn : B ∈ classIn B L := ⟨⟨1, (conjSubgroup_one B).symm⟩, E.B_le_L⟩

omit H in
theorem conjC_le_L {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) : conjSubgroup r C ≤ L :=
  conj_le_of_mem_normalizer hr E.C_le_L

theorem B_inf_conjC (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    B ⊓ conjSubgroup g C = ⊥ := by
  by_contra hne
  have hB : B ≤ conjSubgroup g C := E.pt_le_conjC H h45 hg E.B_mem_classIn hne
  have hBQ : conjSubgroup 1 B ≤ conjSubgroup g Q := by
    rw [conjSubgroup_one]
    exact hB.trans ((conj_le_conj_iff g).mpr (E.C_le_Q H))
  have h1 := E.symm_Q H hBQ (by rw [conjSubgroup_one]; exact (E.Bg_ne_B H).symm)
  rw [conjSubgroup_one] at h1
  have h2 : conjSubgroup g B ≤ conjSubgroup g B ⊓ Q := le_inf le_rfl h1
  rw [E.Bg_inf] at h2
  exact E.Bg_ne_bot H (le_bot_iff.mp h2)

omit H in
theorem card_L : Nat.card L = Nat.card C * Nat.card B := by
  have h := Subgroup.relIndex_mul_card (H := C) (K := L)
  rw [E.relIndex_L, inf_eq_left.mpr E.C_le_L] at h
  rw [← h, mul_comm]

theorem L_eq_sup (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    B ⊔ conjSubgroup g C = L := by
  have hgC := E.conjC_le_L hg
  have hnorm : B ≤ Subgroup.normalizer (conjSubgroup g C : Set G) :=
    le_normalizer_of_comm fun x hx y hy => E.comm_L (E.B_le_L hx) (hgC hy)
  have h := PartTwo.Sec6.card_sup_mul_card_inf hnorm
  rw [E.B_inf_conjC H h45 hg, Subgroup.card_bot, mul_one, card_conjSubgroup] at h
  refine Subgroup.eq_of_le_of_card_ge (sup_le E.B_le_L hgC) ?_
  rw [h, E.card_L, mul_comm]

theorem C_split (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    CSplit B C (C ⊓ conjSubgroup g C) where
  le_C := inf_le_left
  inf_B := by
    rw [eq_bot_iff]
    exact (inf_le_inf_left B inf_le_right).trans (E.B_inf_conjC H h45 hg).le
  C_le_sup := by
    intro c hc
    have hcL : c ∈ B ⊔ conjSubgroup g C := by rw [E.L_eq_sup H h45 hg]; exact E.C_le_L hc
    obtain ⟨β, hβ, z, hz, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun x hx y hy => E.comm_L (E.conjC_le_L hg hx) (E.B_le_L hy)) hcL
    have hzC : z ∈ C := by
      have := C.mul_mem (C.inv_mem (E.B_le_C hβ)) hc
      simpa using this
    exact Subgroup.mul_mem_sup hβ ⟨hzC, hz⟩

theorem L₀_ne_bot {L₀ : Subgroup G} (S : CSplit B C L₀) : L₀ ≠ ⊥ := by
  intro h
  have hcard := E.card_C_split S
  rw [h, Subgroup.card_bot, mul_one] at hcard
  have h2 := E.card_C
  rw [hcard] at h2
  have h3 : C.relIndex P = 1 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.symm.trans (mul_one _).symm)
  have hPC : P ≤ C := Subgroup.relIndex_eq_one.mp h3
  have hP : P ≤ B := by
    rw [← H.inf_centralizer_P]
    refine le_inf le_rfl fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => E.comm_C (hPC hy) (hPC hx)
  exact (H.B_lt_P.trans_le hP).false

theorem pt_le_L₀ (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G))
    {D : Subgroup G} (hD : D ∈ classIn B L) (hne : D ⊓ (C ⊓ conjSubgroup g C) ≠ ⊥) :
    D ≤ C ⊓ conjSubgroup g C := by
  have h1 : D ⊓ C ≠ ⊥ := fun h =>
    hne (eq_bot_iff.mpr ((inf_le_inf_left D inf_le_left).trans h.le))
  have h2 : D ⊓ conjSubgroup g C ≠ ⊥ := fun h =>
    hne (eq_bot_iff.mpr ((inf_le_inf_left D inf_le_right).trans h.le))
  have h3 := E.pt_le_conjC H h45 (r := 1) (Subgroup.one_mem _) hD (by rwa [conjSubgroup_one])
  rw [conjSubgroup_one] at h3
  exact le_inf h3 (E.pt_le_conjC H h45 hg hD h2)

theorem exists_point_L₀ (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ r ∈ Subgroup.normalizer (L : Set G), conjSubgroup r B ≤ C ⊓ conjSubgroup g C := by
  have S := E.C_split H h45 hg
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (E.L₀_ne_bot H S)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨U, ⟨hU, huU⟩, -⟩ := E.part u (E.C_le_L hu.1) hu1'
  obtain ⟨r, hr, hUr⟩ := E.trans U hU
  have hne : U ⊓ (C ⊓ conjSubgroup g C) ≠ ⊥ := fun h => hu1' (by
    have : u ∈ U ⊓ (C ⊓ conjSubgroup g C) := ⟨huU, hu⟩
    rwa [h, Subgroup.mem_bot] at this)
  exact ⟨r, hr, hUr ▸ E.pt_le_L₀ H h45 hg hU hne⟩

theorem perp_of_le_L₀ (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) {r : G}
    (hr : r ∈ Subgroup.normalizer (L : Set G)) (hD : conjSubgroup r B ≤ C ⊓ conjSubgroup g C) :
    B ≤ conjSubgroup r C ∧ conjSubgroup g B ≤ conjSubgroup r C := by
  have S := E.C_split H h45 hg
  have hDQ : conjSubgroup r B ≤ Q := hD.trans (inf_le_left.trans (E.C_le_Q H))
  have hDB : conjSubgroup r B ≠ B := by
    intro h
    have h1 : B ≤ C ⊓ conjSubgroup g C := h ▸ hD
    have h2 : B ≤ B ⊓ (C ⊓ conjSubgroup g C) := le_inf le_rfl h1
    rw [S.inf_B] at h2
    exact H.B_ne_bot (le_bot_iff.mp h2)
  have hB : B ≤ conjSubgroup r C := by
    have h1 := E.symm_Q H (r := 1) (r' := r) (by rw [conjSubgroup_one]; exact hDQ)
      (by rw [conjSubgroup_one]; exact hDB)
    rw [conjSubgroup_one] at h1
    rw [← E.conj_inf_Q H hr]
    exact le_inf E.B_le_L h1
  have hDQg : conjSubgroup r B ≤ conjSubgroup g Q :=
    hD.trans (inf_le_right.trans ((conj_le_conj_iff g).mpr (E.C_le_Q H)))
  have hDBg : conjSubgroup r B ≠ conjSubgroup g B := by
    intro h
    have h1 : conjSubgroup g B ≤ C := h ▸ (hD.trans inf_le_left)
    have h2 : conjSubgroup g B ≤ C ⊓ conjSubgroup g B := le_inf h1 le_rfl
    rw [E.C_inf] at h2
    exact E.Bg_ne_bot H (le_bot_iff.mp h2)
  have hBg : conjSubgroup g B ≤ conjSubgroup r C := by
    have h1 := E.symm_Q H (r := g) (r' := r) hDQg hDBg
    rw [← E.conj_inf_Q H hr]
    exact le_inf E.Bg_le_L h1
  exact ⟨hB, hBg⟩

theorem exists_pair (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ r₁ ∈ Subgroup.normalizer (L : Set G), ∃ r₂ ∈ Subgroup.normalizer (L : Set G),
      conjSubgroup r₁ B ≤ C ⊓ conjSubgroup g C ∧ conjSubgroup r₂ B ≤ C ⊓ conjSubgroup g C ∧
      ¬ conjSubgroup r₂ B ≤ conjSubgroup r₁ C := by
  have S := E.C_split H h45 hg
  obtain ⟨r₁, hr₁, hD₁⟩ := E.exists_point_L₀ H h45 hg
  by_contra hcon
  push Not at hcon
  have hL₀C : C ⊓ conjSubgroup g C ≤ conjSubgroup r₁ C := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]; exact Subgroup.one_mem _
    obtain ⟨U, ⟨hU, huU⟩, -⟩ := E.part u (E.C_le_L hu.1) hu1
    obtain ⟨r₂, hr₂, hUr⟩ := E.trans U hU
    have hne : U ⊓ (C ⊓ conjSubgroup g C) ≠ ⊥ := fun h => hu1 (by
      have : u ∈ U ⊓ (C ⊓ conjSubgroup g C) := ⟨huU, hu⟩
      rwa [h, Subgroup.mem_bot] at this)
    have hUL₀ := E.pt_le_L₀ H h45 hg hU hne
    have := hcon r₁ hr₁ r₂ hr₂ hD₁ (by rw [← hUr]; exact hUL₀)
    rw [← hUr] at this
    exact this huU
  obtain ⟨hB, hBg⟩ := E.perp_of_le_L₀ H h45 hg hr₁ hD₁
  have hLC : L ≤ conjSubgroup r₁ C := by
    rw [E.hL]
    exact sup_le (S.C_le_sup.trans (sup_le hB hL₀C)) hBg
  have h5 : L ≤ C := by
    have := (conj_le_conj_iff r₁⁻¹).mpr hLC
    rwa [conj_inv_conj, conjSubgroup_eq_self_iff.mpr (Subgroup.inv_mem _ hr₁)] at this
  have h6 : conjSubgroup g B ≤ C ⊓ conjSubgroup g B := le_inf (E.Bg_le_L.trans h5) le_rfl
  rw [E.C_inf] at h6
  exact E.Bg_ne_bot H (le_bot_iff.mp h6)

end EndgameData

end CFSG.RankThree.GF2n.Tim78
