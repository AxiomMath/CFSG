module

public import CFSG.Quasithin.Background.E2TwoProofAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

variable {Y : Type} [Group Y] {T M L : Subgroup Y}

structure TwoConj (T L : Subgroup Y) (t : Y) : Prop where
  mem : t ∈ T
  ne : conjSub t L ≠ L
  conjs : ∀ s ∈ T, conjSub s L = L ∨ conjSub s L = conjSub t L
  comm : ⁅L, conjSub t L⁆ = ⊥
  gen : twoResidual (⊤ : Subgroup Y) = L ⊔ conjSub t L

@[expose] noncomputable def xOne (M L : Subgroup Y) : Subgroup Y := preAut L (autOn M L) ⊓ L

theorem conjSub_inv_eq' {s : Y} (hs : conjSub s L = L) : conjSub s⁻¹ L = L := by
  conv_lhs => rw [← hs]
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem xOne_le' : xOne M L ≤ L := inf_le_right

namespace TwoConj

variable {t : Y} (h2 : TwoConj T L t)
include h2

theorem conjSub_conj_of_eq {s : Y} (hsT : s ∈ T) (hs : conjSub s L = L) :
    conjSub s (conjSub t L) = conjSub t L := by
  rcases h2.conjs (s * t) (T.mul_mem hsT h2.mem) with h | h
  · exfalso
    apply h2.ne
    rw [conjSub_mul] at h
    have := congrArg (conjSub s⁻¹) h
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_inv_eq' hs] at this
  · rwa [conjSub_mul] at h

theorem conjSub_conj_of_ne {s : Y} (hsT : s ∈ T) (hs : conjSub s L ≠ L) :
    conjSub s (conjSub t L) = L := by
  have hs' : conjSub s L = conjSub t L := (h2.conjs s hsT).resolve_left hs
  rcases h2.conjs (s * t) (T.mul_mem hsT h2.mem) with h | h
  · rwa [conjSub_mul] at h
  · exfalso
    apply h2.ne
    rw [conjSub_mul] at h
    have h3 : conjSub s (conjSub t L) = conjSub s L := h.trans hs'.symm
    exact (conjSub s).injective h3

theorem le_normalizer_L : L ⊔ conjSub t L ≤ Subgroup.normalizer (L : Set Y) := by
  refine sup_le Subgroup.le_normalizer ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcx : ∀ x ∈ L, c * x = x * c := fun x hx => by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2.comm hx
    exact Subgroup.mem_centralizer_iff.mp this c hc
  constructor
  · intro hx
    rw [hcx x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := hcx (c * x * c⁻¹) hx
    have : x = c * x * c⁻¹ := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * x * c⁻¹)) := by rw [mul_assoc, ← h1]
        _ = c * x * c⁻¹ := by group
    rw [this]
    exact hx

theorem centralizes_conj {c : Y} (hc : c ∈ conjSub t L) : c ∈ Subgroup.centralizer (L : Set Y) := by
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2.comm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (this hx) c hc).symm

theorem le_normalizer_xOne (hF : Factor T M L) :
    T ≤ Subgroup.normalizer ((xOne M L ⊔ conjSub t (xOne M L) : Subgroup Y) : Set Y) := by
  have hfix : ∀ s ∈ T, conjSub s L = L → conjSub s (xOne M L) ≤ xOne M L := by
    intro s hsT hs x hx
    rw [mem_conjSub] at hx
    have hsN : s ∈ Subgroup.normalizer (L : Set Y) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hs
    have hsN' : s⁻¹ ∈ Subgroup.normalizer (L : Set Y) := inv_mem hsN
    obtain ⟨⟨hxN, hxA⟩, hxL⟩ := hx
    have hxL' : x ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hsN (s⁻¹ * x * s)).mp hxL
      simpa [mul_assoc] using this
    have hxN' : x ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer hxL'
    refine ⟨⟨hxN', ?_⟩, hxL'⟩
    have he : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [he, indAut_mul (mul_mem hsN hxN) hsN', indAut_mul hsN hxN, indAut_inv hsN]
    have hsA : indAut L s ∈ autOn M L := indAut_mem_autOn (hF.minPar.le hsT) hsN
    exact mul_mem (mul_mem hsA hxA) (inv_mem hsA)
  have key : ∀ s ∈ T, conjSub s (xOne M L ⊔ conjSub t (xOne M L)) ≤
      xOne M L ⊔ conjSub t (xOne M L) := by
    intro s hsT
    rw [map_sup]
    by_cases hs : conjSub s L = L
    · refine sup_le_sup (hfix s hsT hs) ?_
      have hu : conjSub (t⁻¹ * s * t) L = L := by
        rw [conjSub_mul, conjSub_mul, h2.conjSub_conj_of_eq hsT hs, ← conjSub_mul,
          inv_mul_cancel, conjSub_one]
      have huT : t⁻¹ * s * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem h2.mem) hsT) h2.mem
      have h1 : conjSub s (conjSub t (xOne M L)) =
          conjSub t (conjSub (t⁻¹ * s * t) (xOne M L)) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
      rw [h1]
      exact (conjSub t).monotone (hfix _ huT hu)
    · refine sup_le ?_ ?_
      ·
        have hs' : conjSub s L = conjSub t L := (h2.conjs s hsT).resolve_left hs
        have hv : conjSub (t⁻¹ * s) L = L := by
          rw [conjSub_mul, hs', ← conjSub_mul, inv_mul_cancel, conjSub_one]
        have hvT : t⁻¹ * s ∈ T := T.mul_mem (T.inv_mem h2.mem) hsT
        have h1 : conjSub s (xOne M L) = conjSub t (conjSub (t⁻¹ * s) (xOne M L)) := by
          rw [← conjSub_mul]
          congr 1
          group
        rw [h1]
        exact ((conjSub t).monotone (hfix _ hvT hv)).trans le_sup_right
      · have hst : conjSub (s * t) L = L := by
          rw [conjSub_mul, h2.conjSub_conj_of_ne hsT hs]
        have hstT : s * t ∈ T := T.mul_mem hsT h2.mem
        rw [← conjSub_mul]
        exact (hfix _ hstT hst).trans le_sup_left
  intro s hs
  exact mem_normalizer_of_conjSub_le (key s hs) (key s⁻¹ (T.inv_mem hs))

theorem xOne_le_M [Finite Y] (hF : Factor T M L) : xOne M L ≤ M := by
  set W := (xOne M L ⊔ conjSub t (xOne M L)) ⊔ T with hW
  have hTW : T ≤ W := le_sup_right
  by_cases hWtop : W = ⊤
  · exfalso
    have hInn : (innAut L).range ≤ autOn M L := by
      rintro _ ⟨x, rfl⟩
      have hxW : (x : Y) ∈ W := by rw [hWtop]; trivial
      obtain ⟨w, hw, s, hs, hws⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (h2.le_normalizer_xOne hF) hxW
      have hcomm : ∀ a ∈ xOne M L, ∀ b ∈ conjSub t (xOne M L), a * b = b * a := by
        intro a ha b hb
        have hb' : b ∈ conjSub t L := (conjSub t).monotone xOne_le' hb
        exact Subgroup.mem_centralizer_iff.mp (h2.centralizes_conj hb') a (xOne_le' ha)
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hw
      have hx₂L : x₂ ∈ conjSub t L := (conjSub t).monotone xOne_le' hx₂
      have hx₁N : x₁ ∈ Subgroup.normalizer (L : Set Y) := hx₁.1.1
      have hx₂N : x₂ ∈ Subgroup.normalizer (L : Set Y) :=
        h2.le_normalizer_L (Subgroup.mem_sup_right hx₂L)
      have hxN : (x : Y) ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer x.2
      have hsN : s ∈ Subgroup.normalizer (L : Set Y) := by
        have : s = (x₁ * x₂)⁻¹ * x := by rw [← hws]; group
        rw [this]
        exact mul_mem (inv_mem (mul_mem hx₁N hx₂N)) hxN
      rw [← indAut_eq_innAut, ← hws, indAut_mul (mul_mem hx₁N hx₂N) hsN, indAut_mul hx₁N hx₂N,
        indAut_eq_one_of_mem_centralizer hx₂N (h2.centralizes_conj hx₂L), mul_one]
      exact mul_mem hx₁.1.2 (indAut_mem_autOn (hF.minPar.le hs) hsN)
    have hmp := hF.minParabolic_autOn
    have hle : autOn ⊤ L ≤ autOn M L :=
      hF.autOn_top_le_sup.trans (sup_le hInn (autOn_le_autOn_of_le hF.minPar.le))
    exact hmp.maximal.1.not_ge hle
  · have hWM : W ≤ M := hF.minPar.le_of_lt hTW (lt_top_iff_ne_top.mpr hWtop)
    exact (le_sup_left.trans le_sup_left).trans hWM

theorem inf_M_eq [Finite Y] (hF : Factor T M L) : M ⊓ L = xOne M L := by
  apply le_antisymm
  · rintro x ⟨hxM, hxL⟩
    exact ⟨⟨Subgroup.le_normalizer hxL, indAut_mem_autOn hxM (Subgroup.le_normalizer hxL)⟩, hxL⟩
  · exact le_inf (h2.xOne_le_M hF) xOne_le'

theorem M_eq [Finite Y] (hF : Factor T M L) : M = (M ⊓ L) ⊔ conjSub t (M ⊓ L) ⊔ T := by
  apply le_antisymm
  · intro m hm
    have hmtop : m ∈ twoResidual (⊤ : Subgroup Y) ⊔ T := by
      rw [sup_comm, sup_twoResidual_eq hF.minPar.isSylow]
      trivial
    have := Factor.twoResidual_normal (Y := Y)
    obtain ⟨o, ho, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmtop
    have hsM : s ∈ M := hF.minPar.le hs
    have hoM : o ∈ M := by
      have := M.mul_mem hm (M.inv_mem hsM)
      simpa using this
    rw [h2.gen] at ho
    have hcomm : ∀ a ∈ L, ∀ b ∈ conjSub t L, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (h2.centralizes_conj hb) a ha
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm ho
    have hlN : l ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer hl
    have hcN : c ∈ Subgroup.normalizer (L : Set Y) := h2.le_normalizer_L (Subgroup.mem_sup_right hc)
    have hlx : l ∈ xOne M L := by
      refine ⟨⟨hlN, ?_⟩, hl⟩
      have h1 : indAut L (l * c) = indAut L l := by
        rw [indAut_mul hlN hcN, indAut_eq_one_of_mem_centralizer hcN (h2.centralizes_conj hc),
          mul_one]
      rw [← h1]
      exact indAut_mem_autOn hoM (mul_mem hlN hcN)
    have hlM : l ∈ M := h2.xOne_le_M hF hlx
    have hcM : c ∈ M := by
      have := M.mul_mem (M.inv_mem hlM) hoM
      simpa using this
    have hct : c ∈ conjSub t (M ⊓ L) := by
      rw [mem_conjSub] at hc ⊢
      refine ⟨?_, hc⟩
      have htM : t ∈ M := hF.minPar.le h2.mem
      have := M.mul_mem (M.mul_mem (M.inv_mem htM) hcM) htM
      exact this
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      ⟨hlM, hl⟩)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right hct))) (Subgroup.mem_sup_right hs)
  · refine sup_le (sup_le inf_le_left ?_) hF.minPar.le
    intro x hx
    rw [mem_conjSub] at hx
    have := M.mul_mem (M.mul_mem (hF.minPar.le h2.mem) hx.1) (M.inv_mem (hF.minPar.le h2.mem))
    simpa [mul_assoc] using this

end TwoConj

end E2P

end CFSG.Quasithin
