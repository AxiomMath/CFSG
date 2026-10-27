module

public import CFSG.Timmesfeld.ARS.Sec12Meets
public import CFSG.Timmesfeld.ARS.Sec12Center

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseM

theorem eq_one_or_eq_of_card_eq_two [Finite G] {X : Subgroup G} (hX : Nat.card X = 2) {x y : G}
    (hx : x ∈ X) (hx1 : x ≠ 1) (hy : y ∈ X) : y = 1 ∨ y = x := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hsub : ({1, x, y} : Set G) ⊆ X := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    exacts [X.one_mem, hx, hy]
  have hcard : ({1, x, y} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm h2)]
    rintro (h | h)
    · exact hx1 h.symm
    · exact h1 h.symm
  have hle : ({1, x, y} : Set G).ncard ≤ (X : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hX] at hle
  omega

theorem mul_self_eq_one_of_card_eq_two {X : Subgroup G} (hX : Nat.card X = 2) {x : G}
    (hx : x ∈ X) : x * x = 1 := by
  have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
  rw [hX, pow_two] at h
  exact congrArg Subtype.val h

theorem eq_one_of_mul_self_eq_one {N : Subgroup G} (hN : IsPGroup 3 N) {g : G} (hg : g ∈ N)
    (h2 : g * g = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN) ⟨g, hg⟩
  have hdvd : orderOf (⟨g, hg⟩ : N) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, h2]))
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exfalso
      have : 3 ∣ 2 := (dvd_pow_self 3 (by omega)).trans hdvd
      omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact congrArg Subtype.val hk

theorem conj_conj_of_mul_self {x : G} (hxx : x * x = 1) (z : G) : x * (x * z * x) * x = z := by
  calc x * (x * z * x) * x = (x * x) * z * (x * x) := by group
    _ = z := by rw [hxx, one_mul, mul_one]

theorem braid_of_opposite [Finite G] {X Y : Subgroup G} (hXY : Opposite X Y) (hY : Nat.card Y = 2)
    {x y : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hxx : x * x = 1) (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hyy : y * y = 1) : y * x * y = x * y * x := by
  obtain ⟨b, hb, hb1, hbe⟩ := hXY.2.1 x hx hx1
  obtain rfl : b = y := (eq_one_or_eq_of_card_eq_two hY hy hy1 hb).resolve_left hb1
  have hmem : b * x * b⁻¹ ∈ conjSub Y x := by
    rw [← hbe]
    exact conj_mem_conjSub b hx
  rw [mem_conjSub] at hmem
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hyy
  rw [hxinv, hbinv] at hmem
  rcases eq_one_or_eq_of_card_eq_two hY hy hy1 hmem with h | h
  · exfalso
    apply hx1
    have h' : b * x * b = 1 := by
      rw [← conj_conj_of_mul_self hxx (b * x * b), h, mul_one, hxx]
    rw [← conj_conj_of_mul_self hyy x, h', mul_one, hyy]
  · rw [← conj_conj_of_mul_self hxx (b * x * b), h]

end CaseM


namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

section Three

variable (hq : Nat.card A = 2) {N : Subgroup G} (hNV : N ≤ levi R A A₀)
  (hnorm : ∀ v ∈ levi R A A₀, ∀ n ∈ N, v * n * v⁻¹ ∈ N) (h3 : IsPGroup 3 N)

include hq in
theorem card_eq_two_of_mem {X : Subgroup G} (hX : X ∈ R) : Nat.card X = 2 :=
  (hS.hyp.root.card_eq hX hS.mem).trans hq

omit hS in
include hnorm in
theorem mul_conj_mem {X : Subgroup G} (hX : X ∈ leviSet R A A₀) {x : G} (hx : x ∈ X)
    (hxx : x * x = 1) {n : G} (hn : n ∈ N) : x * (n * x * n⁻¹) ∈ N := by
  have h1 : x * n * x⁻¹ ∈ N := hnorm x (le_gen hX hx) n hn
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have e : x * (n * x * n⁻¹) = (x * n * x⁻¹) * n⁻¹ := by
    rw [hxinv]
    group
  rw [e]
  exact N.mul_mem h1 (N.inv_mem hn)

include hq hnorm h3 in
theorem conjSub_eq_of_commuting_conjSub {X : Subgroup G} (hX : X ∈ leviSet R A A₀) {n : G}
    (hn : n ∈ N) (hc : Commuting X (conjSub X n)) : conjSub X n = X := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hX2 := hS.card_eq_two_of_mem hq hX.1.1
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX.1.1
  have hxx := CaseM.mul_self_eq_one_of_card_eq_two hX2 hx
  have hcomm := hc x hx _ (conj_mem_conjSub n hx)
  have hg := mul_conj_mem hnorm hX hx hxx hn
  have hyy : (n * x * n⁻¹) * (n * x * n⁻¹) = 1 := by
    calc (n * x * n⁻¹) * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
      _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
  have hgg : (x * (n * x * n⁻¹)) * (x * (n * x * n⁻¹)) = 1 := by
    calc (x * (n * x * n⁻¹)) * (x * (n * x * n⁻¹)) =
        x * ((n * x * n⁻¹) * x) * (n * x * n⁻¹) := by group
      _ = x * (x * (n * x * n⁻¹)) * (n * x * n⁻¹) := by rw [hcomm.eq]
      _ = (x * x) * ((n * x * n⁻¹) * (n * x * n⁻¹)) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  have h1 := CaseM.eq_one_of_mul_self_eq_one h3 hg hgg
  have hnx : n * x * n⁻¹ = x := by
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hxx]
  have hXn2 : Nat.card (conjSub X n) = 2 := hS.card_eq_two_of_mem hq (hR.conjSub_mem hX.1.1 n)
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hX2, hXn2])
  rintro _ ⟨w, hw, rfl⟩
  rcases CaseM.eq_one_or_eq_of_card_eq_two hX2 hx hx1 hw with rfl | rfl
  · simp
  · change n * w * n⁻¹ ∈ X
    rw [hnx]
    exact hw

include hq hNV hnorm h3 in
theorem commuting_conjSub_of_isPGroup_three {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hXY : X ≠ Y) (hc : Commuting X Y) {n : G} (hn : n ∈ N) :
    Commuting (conjSub X n) Y := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hXn : conjSub X n ∈ leviSet R A A₀ := Levi.conjSub_mem_leviSet_of_mem_levi hR hX (hNV hn)
  by_contra hnc
  have hopp : Opposite (conjSub X n) Y := hS.opposite_of_not_commuting hXn hY hnc
  have hX2 := hS.card_eq_two_of_mem hq hX.1.1
  have hY2 := hS.card_eq_two_of_mem hq hY.1.1
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX.1.1
  obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hY.1.1
  have hxx := CaseM.mul_self_eq_one_of_card_eq_two hX2 hx
  have hyy := CaseM.mul_self_eq_one_of_card_eq_two hY2 hy
  have hx'1 : n * x * n⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 h)
  have hx'x' : (n * x * n⁻¹) * (n * x * n⁻¹) = 1 := by
    calc (n * x * n⁻¹) * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
      _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
  have hbraid := CaseM.braid_of_opposite hopp hY2 (conj_mem_conjSub n hx) hx'1 hx'x' hy hy1 hyy
  have h3' : ((n * x * n⁻¹) * y) * ((n * x * n⁻¹) * y) * ((n * x * n⁻¹) * y) = 1 := by
    calc ((n * x * n⁻¹) * y) * ((n * x * n⁻¹) * y) * ((n * x * n⁻¹) * y) =
        (n * x * n⁻¹) * (y * (n * x * n⁻¹) * y) * (n * x * n⁻¹) * y := by group
      _ = (n * x * n⁻¹) * ((n * x * n⁻¹) * y * (n * x * n⁻¹)) * (n * x * n⁻¹) * y := by
          rw [hbraid]
      _ = ((n * x * n⁻¹) * (n * x * n⁻¹)) * y * ((n * x * n⁻¹) * (n * x * n⁻¹)) * y := by group
      _ = 1 := by rw [hx'x', one_mul, mul_one, hyy]
  have hm : x * (n * x * n⁻¹) ∈ N := mul_conj_mem hnorm hX hx hxx hn
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hc' : y * (x * (n * x * n⁻¹)) * y ∈ N := by
    have := hnorm y (le_gen hY hy) _ hm
    rwa [hyinv] at this
  have hgc : (x * y) * (y * (x * (n * x * n⁻¹)) * y) = (n * x * n⁻¹) * y := by
    calc (x * y) * (y * (x * (n * x * n⁻¹)) * y) = x * (y * y) * x * (n * x * n⁻¹) * y := by
          group
      _ = (x * x) * (n * x * n⁻¹) * y := by rw [hyy, mul_one]
      _ = (n * x * n⁻¹) * y := by rw [hxx, one_mul]
  set g := x * y with hgdef
  set c := y * (x * (n * x * n⁻¹)) * y with hcdef
  have hgg : g * g = 1 := by
    have hxy : Commute x y := hc x hx y hy
    calc g * g = x * (y * x) * y := by rw [hgdef]; group
      _ = x * (x * y) * y := by rw [hxy.eq]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  have hgV : g ∈ levi R A A₀ := (levi R A A₀).mul_mem (le_gen hX hx) (le_gen hY hy)
  have hgcg : g * c * g⁻¹ ∈ N := hnorm g hgV c hc'
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have h3'' : (g * c) * (g * c) * (g * c) = 1 := by
    rw [hgc]
    exact h3'
  have e : (g * c * g) * c * (g * c * g) * g = 1 := by
    calc (g * c * g) * c * (g * c * g) * g = (g * c) * (g * c) * (g * c) * (g * g) := by group
      _ = 1 := by rw [h3'', hgg, one_mul]
  have hgN : g ∈ N := by
    rw [eq_inv_of_mul_eq_one_right e]
    rw [hginv] at hgcg
    exact N.inv_mem (N.mul_mem (N.mul_mem hgcg hc') hgcg)
  have hg1 := CaseM.eq_one_of_mul_self_eq_one h3 hgN hgg
  have hxy : y = x := by
    rw [hgdef] at hg1
    rw [eq_inv_of_mul_eq_one_right hg1, inv_eq_of_mul_eq_one_right hxx]
  apply hXY
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hX2, hY2])
  intro w hw
  rcases CaseM.eq_one_or_eq_of_card_eq_two hX2 hx hx1 hw with rfl | rfl
  · exact Y.one_mem
  · rw [← hxy]
    exact hy


include hq hNV in
theorem eq_bot_of_forall_conjSub_eq (hfix : ∀ X ∈ leviSet R A A₀, ∀ n ∈ N, conjSub X n = X) :
    N = ⊥ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hcomm : ∀ X ∈ leviSet R A A₀, ∀ x ∈ X, Commute n x := by
    intro X hX x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Commute.one_right n
    have hX2 := hS.card_eq_two_of_mem hq hX.1.1
    have hmem : n * x * n⁻¹ ∈ X := by
      rw [← hfix X hX n hn]
      exact conj_mem_conjSub n hx
    rcases CaseM.eq_one_or_eq_of_card_eq_two hX2 hx hx1 hmem with h | h
    · exact absurd (conj_eq_one_iff.1 h) hx1
    · rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
      exact h
  have hle : levi R A A₀ ≤ Subgroup.centralizer ({n} : Set G) := iSup₂_le fun X hX x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm X hX x hx).eq.symm
  have hc : (⟨n, hNV hn⟩ : levi R A A₀) ∈ Subgroup.center (levi R A A₀) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨v, hv⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv)
  rw [hS.center_levi_eq_bot, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

include hq hNV hnorm h3 in
theorem exists_conjSub_eq_of_special
    (hmoved : ∀ X ∈ leviSet R A A₀, ∃ m ∈ N, conjSub X m ≠ X) {B Y : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hY : Y ∈ leviSet R A A₀) (hs : Special R B Y) {y : G}
    (hy : y ∈ Y) : ∃ n ∈ N, conjSub B n = conjSub B y := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  by_cases hy1 : y = 1
  · exact ⟨1, N.one_mem, by rw [hy1]⟩
  have hY2 := hS.card_eq_two_of_mem hq hY.1.1
  have hyV : y ∈ levi R A A₀ := le_gen hY hy
  have hconjΔ : ∀ {X D : Subgroup G}, X ∈ deltaSet R A A₀ D → ∀ {g : G}, g ∈ levi R A A₀ →
      conjSub X g ∈ deltaSet R A A₀ (conjSub D g) := fun hX _ hg =>
    ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hg, conjSub_mem_lambdaSet hR hX.2 _⟩
  obtain ⟨hK, hKB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hY hs
  obtain ⟨E, hEB, hEK⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hK hKB
  obtain ⟨F, ⟨hFB, hFK⟩, hFE⟩ := hS.exists_ne_mem_deltaSet_inter hB hK hKB ⟨hEB, hEK⟩
  obtain ⟨Z, hZ, hEZ⟩ := Levi.exists_opposite_mem_leviSet hS.hyp hA hS.sec8.2 hS.opp hEB.1
  have hEne : E ≠ ⊥ := hR.ne_bot _ hEB.1.1.1
  have hZB : Z ∉ deltaSet R A A₀ B := fun h =>
    hEZ.not_commuting hEne (hS.commuting_of_mem_deltaSet' hB hEB h)
  have hsZ : Special R B Z := (hS.mem_deltaSet_or_special hB hZ).resolve_left hZB
  obtain ⟨hL, hLB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hZ hsZ
  obtain ⟨D₁, hD₁B, hD₁L⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hL hLB
  obtain ⟨D₂, ⟨hD₂B, hD₂L⟩, hD₂D₁⟩ := hS.exists_ne_mem_deltaSet_inter hB hL hLB ⟨hD₁B, hD₁L⟩
  have hDZ : ∀ {D : Subgroup G}, D ∈ deltaSet R A A₀ B → D ∈ deltaSet R A A₀ ⁅B, Z⁆ →
      D ≠ E := fun hD hDL h => hEZ.not_commuting hEne
        (h ▸ (hS.commuting_iff_mem_deltaSet_commutator hB hZ hsZ hD).2 hDL)
  obtain ⟨D, hDB, hDE, hDF⟩ : ∃ D ∈ deltaSet R A A₀ B, D ≠ E ∧ D ≠ F := by
    by_cases h : D₁ = F
    · exact ⟨D₂, hD₂B, hDZ hD₂B hD₂L, fun h' => hD₂D₁ (h'.trans h.symm)⟩
    · exact ⟨D₁, hD₁B, hDZ hD₁B hD₁L, h⟩
  obtain ⟨m, hm, hmD⟩ := hmoved D hDB.1
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDB.1.1.1
  have hD2 := hS.card_eq_two_of_mem hq hDB.1.1.1
  have hdd := CaseM.mul_self_eq_one_of_card_eq_two hD2 hd
  have hn : d * (m * d * m⁻¹) ∈ N := mul_conj_mem hnorm hDB.1 hd hdd hm
  set n := d * (m * d * m⁻¹) with hndef
  have hcent : ∀ {W : Subgroup G}, W ∈ deltaSet R A A₀ B → D ≠ W → ∀ w ∈ W, Commute n w := by
    intro W hW hDW w hw
    have h1 : Commute d w := hS.commuting_of_mem_deltaSet' hB hDB hW d hd w hw
    have h2 : Commute (m * d * m⁻¹) w :=
      (hS.commuting_conjSub_of_isPGroup_three hq hNV hnorm h3 hDB.1 hW.1 hDW
        (hS.commuting_of_mem_deltaSet' hB hDB hW) hm) _ (conj_mem_conjSub m hd) w hw
    exact h1.mul_left h2
  have hcentE := hcent hEB hDE
  have hcentF := hcent hFB hDF
  have hDm : Opposite D (conjSub D m) := by
    rcases (show conjSub D m = D ∨ Opposite D (conjSub D m) from by
      by_cases he : conjSub D m = D
      · exact Or.inl he
      · exact Or.inr (hS.opposite_of_not_commuting hDB.1
          (Levi.conjSub_mem_leviSet_of_mem_levi hR hDB.1 (hNV hm))
          fun hc => he (hS.conjSub_eq_of_commuting_conjSub hq hnorm h3 hDB.1 hm hc))) with h | h
    · exact absurd h hmD
    · exact h
  have hd'1 : m * d * m⁻¹ ≠ 1 := fun h => hd1 (conj_eq_one_iff.1 h)
  have hDd' : conjSub D (m * d * m⁻¹) ≠ D :=
    (Sec5.opposite_conjSub_self hDm (conj_mem_conjSub m hd) hd'1).1.symm
  have hDn : conjSub D n ≠ D := by
    intro h
    rw [hndef, conjSub_mul] at h
    apply hDd'
    have h' := congrArg (fun H => conjSub H d⁻¹) h
    simp only [Plane.conjSub_conjSub_inv] at h'
    rw [h', conjSub_of_mem (D.inv_mem hd)]
  have hnB : conjSub B n ≠ B := by
    intro hBn
    have hDnB : conjSub D n ∈ deltaSet R A A₀ B := by
      have := hconjΔ hDB (hNV hn)
      rwa [hBn] at this
    exact hDn (hS.conjSub_eq_of_commuting_conjSub hq hnorm h3 hDB.1 hn
      (hS.commuting_of_mem_deltaSet' hB hDB hDnB))
  have hline : ∀ B' ∈ lambdaStar R A A₀, E ∈ deltaSet R A A₀ B' → F ∈ deltaSet R A A₀ B' →
      B' = B ∨ B' = conjSub B y ∨ B' = ⁅B, Y⁆ := by
    intro B' hB' hEB' hFB'
    by_cases h1 : B' = B
    · exact Or.inl h1
    by_cases h2 : B' = ⁅B, Y⁆
    · exact Or.inr (Or.inr h2)
    have hB'B : B' ∈ lambdaSet R B := hS.mem_lambdaSet_of_mem_deltaSet_inter hB hB'
      (Ne.symm h1) ⟨hEB, hEB'⟩ ⟨hFB, hFB'⟩ (Ne.symm hFE)
    have hB'K : B' ∈ lambdaSet R ⁅B, Y⁆ := hS.mem_lambdaSet_of_mem_deltaSet_inter hK hB'
      (Ne.symm h2) ⟨hEK, hEB'⟩ ⟨hFK, hFB'⟩ (Ne.symm hFE)
    have hle : B' ≤ B ⊔ ⁅B, Y⁆ := hS.le_sup_of_mem_lambdaSet hB hK hB' hKB hB'B hB'K
    obtain ⟨y', hy', hy'B⟩ := CaseB.exists_conjSub_eq_of_le_sup hR hiso hB.1.1.1 hY.1.1
      hB'.1.1.1 hs hle h2
    rcases CaseM.eq_one_or_eq_of_card_eq_two hY2 hy hy1 hy' with rfl | rfl
    · left
      rw [← hy'B, conjSub_one]
    · right; left
      exact hy'B.symm
  have hpow : ∀ k : ℕ, conjSub B (n ^ k) ∈ lambdaStar R A A₀ ∧
      E ∈ deltaSet R A A₀ (conjSub B (n ^ k)) ∧ F ∈ deltaSet R A A₀ (conjSub B (n ^ k)) := by
    intro k
    have hnk : n ^ k ∈ levi R A A₀ := hNV (N.pow_mem hn k)
    have hEk : conjSub E (n ^ k) = E := conjSub_of_forall_commute fun e he =>
      (hcentE e he).pow_left k
    have hFk : conjSub F (n ^ k) = F := conjSub_of_forall_commute fun e he =>
      (hcentF e he).pow_left k
    refine ⟨conjSub_mem_lambdaStar_of_mem_levi hR hB hnk, ?_, ?_⟩
    · have := hconjΔ hEB hnk
      rwa [hEk] at this
    · have := hconjΔ hFB hnk
      rwa [hFk] at this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h3) ⟨n, hn⟩
  have hn3 : n ^ (3 ^ k) = 1 := by
    have h := pow_orderOf_eq_one (⟨n, hn⟩ : N)
    rw [hk] at h
    exact congrArg Subtype.val h
  have hfixpow : ∀ {g : G}, conjSub B g = B → ∀ j : ℕ, conjSub B (g ^ j) = B := by
    intro g hg j
    induction j with
    | zero => rw [pow_zero, conjSub_one]
    | succ j ih => rw [pow_succ, conjSub_mul, hg, ih]
  have hB2 : conjSub B (n ^ 2) ≠ B := by
    intro h2
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have e : n = (n ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = 3 ^ k + 1 by omega, pow_succ, hn3, one_mul]
    exact hnB (by rw [e]; exact hfixpow h2 _)
  have hB12 : conjSub B (n ^ 2) ≠ conjSub B n := by
    intro h
    rw [pow_two, conjSub_mul] at h
    exact hnB (RankOne.map_conj_inj.1 h)
  rcases hline _ (hpow 1).1 (hpow 1).2.1 (hpow 1).2.2 with h1 | h1 | h1
  · exact absurd (by simpa using h1) hnB
  · exact ⟨n, hn, by simpa using h1⟩
  · rcases hline _ (hpow 2).1 (hpow 2).2.1 (hpow 2).2.2 with h2 | h2 | h2
    · exact absurd h2 hB2
    · exact ⟨n ^ 2, N.pow_mem hn 2, h2⟩
    · exact absurd (h2.trans (by simpa using h1.symm)) hB12


include hq hNV hnorm h3 in
theorem exists_conjSub_eq_of_moved
    (hmoved : ∀ X ∈ leviSet R A A₀, ∃ m ∈ N, conjSub X m ≠ X) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) : ∃ n ∈ N, conjSub B n = C := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hS.mem hS.sec8.2
    hS.max hS.opp hB hC
  let H : Subgroup G :=
    { carrier := {v | v ∈ levi R A A₀ ∧
        ∀ B ∈ lambdaStar R A A₀, ∃ n ∈ N, conjSub B n = conjSub B v}
      one_mem' := ⟨one_mem _, fun B _ => ⟨1, N.one_mem, rfl⟩⟩
      mul_mem' := by
        rintro v w ⟨hvV, hv⟩ ⟨hwV, hw⟩
        refine ⟨mul_mem hvV hwV, fun B hB => ?_⟩
        obtain ⟨n₁, hn₁, h₁⟩ := hw B hB
        obtain ⟨n₂, hn₂, h₂⟩ := hv _ (conjSub_mem_lambdaStar_of_mem_levi hR hB hwV)
        refine ⟨n₂ * n₁, N.mul_mem hn₂ hn₁, ?_⟩
        rw [conjSub_mul, conjSub_mul, h₁, h₂]
      inv_mem' := by
        rintro v ⟨hvV, hv⟩
        refine ⟨inv_mem hvV, fun B hB => ?_⟩
        obtain ⟨n, hn, h⟩ := hv _ (conjSub_mem_lambdaStar_of_mem_levi hR hB (inv_mem hvV))
        have hB' : conjSub (conjSub B v⁻¹) v = B := by
          rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
        rw [hB'] at h
        refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
        calc conjSub B n⁻¹ = conjSub (conjSub (conjSub B v⁻¹) n) n⁻¹ := by rw [h]
          _ = conjSub B v⁻¹ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one] }
  have hle : levi R A A₀ ≤ H := iSup₂_le fun X hX x hx => by
    refine ⟨le_gen hX hx, fun B hB => ?_⟩
    rcases hS.mem_deltaSet_or_special hB hX with hXB | hs
    · refine ⟨1, N.one_mem, ?_⟩
      rw [conjSub_one, conjSub_of_forall_commute fun b hb => (hXB.2.1.2.2 b hb x hx).symm]
    · exact hS.exists_conjSub_eq_of_special hq hNV hnorm h3 hmoved hB hX hs hx
  exact (hle hv).2 B hB

end Three

theorem eq_bot_of_isPGroup_three (hconn : LeviConnected R A A₀) (hq : Nat.card A = 2)
    {N : Subgroup G} (hNV : N ≤ levi R A A₀) (hnorm : ∀ v ∈ levi R A A₀, ∀ n ∈ N, v * n * v⁻¹ ∈ N)
    (h3 : IsPGroup 3 N) : N = ⊥ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hA := hS.mem
  by_contra hne
  have hconjΔ : ∀ {X D : Subgroup G}, X ∈ deltaSet R A A₀ D → ∀ {g : G}, g ∈ levi R A A₀ →
      conjSub X g ∈ deltaSet R A A₀ (conjSub D g) := fun hX _ hg =>
    ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hg, conjSub_mem_lambdaSet hR hX.2 _⟩
  obtain ⟨X₀, hX₀, m₀, hm₀, hne₀⟩ : ∃ X ∈ leviSet R A A₀, ∃ m ∈ N, conjSub X m ≠ X := by
    by_contra h
    push Not at h
    exact hne (hS.eq_bot_of_forall_conjSub_eq hq hNV h)
  have hmoved : ∀ X ∈ leviSet R A A₀, ∃ m ∈ N, conjSub X m ≠ X := by
    intro X hX
    obtain ⟨v, hv, rfl⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hR (fun _ h => h.1.1)
      (hconn X₀ hX₀ X hX)
    have hcompΔ : ∀ D, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X₀ D →
        D ∈ leviSet R A A₀ := by
      intro D hD
      cases hD with
      | refl => exact hX₀
      | tail _ h => exact h.2.1
    have hvV : v ∈ levi R A A₀ :=
      (iSup₂_le fun D hD x hx => le_gen (hcompΔ D hD) hx : (⨆ D ∈ {D | Relation.ReflTransGen
        (oppGraph (leviSet R A A₀)) X₀ D}, D) ≤ levi R A A₀) hv
    refine ⟨v * m₀ * v⁻¹, hnorm v hvV m₀ hm₀, fun h => hne₀ ?_⟩
    rw [← conjSub_mul, show v * m₀ * v⁻¹ * v = v * m₀ by group, conjSub_mul] at h
    exact RankOne.map_conj_inj.1 h
  obtain ⟨B, hB, -⟩ := hS.exists_special_lambdaStar
  have h7 : ∀ X ∈ leviSet R A A₀, ∃ n ∈ N, conjSub X n ∈ deltaSet R A A₀ B := by
    intro X hX
    obtain ⟨B', hB', hXB'⟩ := hS.exists_mem_deltaSet hX
    obtain ⟨n, hn, hnB⟩ := hS.exists_conjSub_eq_of_moved hq hNV hnorm h3 hmoved hB' hB
    exact ⟨n, hn, by rw [← hnB]; exact hconjΔ hXB' (hNV hn)⟩
  have h8 : ∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, (∀ n ∈ N, conjSub X n ≠ Y) →
      Commuting X Y := by
    intro X hX Y hY hXY
    obtain ⟨n₁, hn₁, h₁⟩ := h7 X hX
    obtain ⟨n₂, hn₂, h₂⟩ := h7 Y hY
    have hne₁₂ : conjSub X n₁ ≠ conjSub Y n₂ := fun h => hXY (n₂⁻¹ * n₁)
      (N.mul_mem (N.inv_mem hn₂) hn₁) (by
        rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one])
    have hc := hS.commuting_of_mem_deltaSet' hB h₁ h₂
    have hc1 := hS.commuting_conjSub_of_isPGroup_three hq hNV hnorm h3 h₁.1 h₂.1 hne₁₂ hc
      (N.inv_mem hn₁)
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hc1
    have hne₂ : conjSub Y n₂ ≠ X := fun h => hXY n₂⁻¹ (N.inv_mem hn₂) (by
      rw [← h, ← conjSub_mul, inv_mul_cancel, conjSub_one])
    have hc2 := hS.commuting_conjSub_of_isPGroup_three hq hNV hnorm h3 h₂.1 hX hne₂ hc1.symm
      (N.inv_mem hn₂)
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hc2
    exact hc2.symm
  obtain ⟨E, hEB⟩ := deltaSet_nonempty hS.hyp hA hS.sec8.2 hS.opp hB
  obtain ⟨Z, hZ, hEZ⟩ := Levi.exists_opposite_mem_leviSet hS.hyp hA hS.sec8.2 hS.opp hEB.1
  have hEne : E ≠ ⊥ := hR.ne_bot _ hEB.1.1.1
  have hZB : Z ∉ deltaSet R A A₀ B := fun h =>
    hEZ.not_commuting hEne (hS.commuting_of_mem_deltaSet' hB hEB h)
  have hsZ : Special R B Z := (hS.mem_deltaSet_or_special hB hZ).resolve_left hZB
  obtain ⟨hL, hLB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hZ hsZ
  obtain ⟨F, hFB, hFL⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hL hLB
  have hFE : F ≠ E := fun h => hEZ.not_commuting hEne
    (h ▸ (hS.commuting_iff_mem_deltaSet_commutator hB hZ hsZ hFB).2 hFL)
  have hclass : ∀ D, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E D →
      ∃ n ∈ N, conjSub E n = D := by
    intro D hD
    induction hD with
    | refl => exact ⟨1, N.one_mem, conjSub_one E⟩
    | tail hab hbc ih =>
      obtain ⟨n, hn, hnb⟩ := ih
      rename_i b c
      clear hab
      by_contra hcl
      push Not at hcl
      have hnc : ∀ m ∈ N, conjSub b m ≠ c := fun m hm h => hcl (m * n) (N.mul_mem hm hn)
        (by rw [conjSub_mul, hnb, h])
      exact hbc.2.2.not_commuting (hR.ne_bot _ hbc.1.1.1) (h8 b hbc.1 c hbc.2.1 hnc)
  obtain ⟨n, hn, hnF⟩ := hclass F (hconn E hEB.1 F hFB.1)
  have hc : Commuting E (conjSub E n) := by
    rw [hnF]
    exact hS.commuting_of_mem_deltaSet' hB hEB hFB
  exact hFE (hnF.symm.trans (hS.conjSub_eq_of_commuting_conjSub hq hnorm h3 hEB.1 hn hc))



theorem eq_bot_of_normal_isPGroup_three (hconn : LeviConnected R A A₀) (hq : Nat.card A = 2)
    (N : Subgroup (levi R A A₀)) (hN : N.Normal) (h3 : IsPGroup 3 N) : N = ⊥ := by
  have key := hS.eq_bot_of_isPGroup_three hconn hq (N := N.map (levi R A A₀).subtype)
    (fun _ ⟨n, _, hn⟩ => hn ▸ n.2) (fun v hv _ ⟨n, hn, hne⟩ => ?_) (h3.map _)
  · exact (Subgroup.map_eq_bot_iff_of_injective N (levi R A A₀).subtype_injective).1 key
  · refine ⟨⟨v, hv⟩ * n * ⟨v, hv⟩⁻¹, hN.conj_mem n hn ⟨v, hv⟩, ?_⟩
    rw [← hne]
    rfl

end Sec12

end CFSG.Timmesfeld.ARS
