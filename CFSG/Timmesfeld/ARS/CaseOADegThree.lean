module

public import CFSG.Timmesfeld.ARS.CaseOADegLevi
public import CFSG.Timmesfeld.ARS.Sec12Three

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem ne_of_mem₁_of_mem₂ {X Y : Subgroup G} (hX : X ∈ Δ₁) (hY : Y ∈ Δ₂) : X ≠ Y := by
  rintro rfl
  obtain ⟨E₁, -, he₁⟩ := hD.comp₁
  obtain ⟨E₂, -, he₂⟩ := hD.comp₂
  exact hD.comp_ne (he₁.trans ((Sec9.comp_eq_comp (he₁ ▸ hX) (he₂ ▸ hY)).trans he₂.symm))

theorem exists_mem₂_deltaSet {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    ∃ E ∈ Δ₂, E ∈ deltaSet R A A₀ B := by
  have hS := hD.sec12
  obtain ⟨P, hP, -, -, -, -⟩ := hD.sl2
  rcases hS.mem_deltaSet_or_special hB (hD.mem_leviSet₂ hP) with h | hs
  · exact ⟨P, hP, h⟩
  · obtain ⟨-, Q, hQ, hPQ, hBQ⟩ := exists_opposite_of_mem_lambdaStar hD.hyp hD.mem hD.ne hD.opp
      (hD.mem_leviSet₂ hP) hB hs
    exact ⟨Q, hD.mem₂_of_opposite hP hQ hPQ, hQ, mem_lambdaSet_comm hQ.1.1 hBQ⟩

theorem gen₂_le_levi : gen Δ₂ ≤ levi R A A₀ :=
  Sec9.gen_le_levi fun _ hX => hD.mem_leviSet₂ hX

section Three

variable (hq : Nat.card A = 2) {N : Subgroup G} (hNV : N ≤ gen Δ₁)
  (hnorm : ∀ v ∈ levi R A A₀, ∀ n ∈ N, v * n * v⁻¹ ∈ N) (h3 : IsPGroup 3 N)

include hq hNV hnorm h3 in
theorem exists_conjSub_eq_of_special₁
    (hmoved : ∀ X ∈ Δ₁, ∃ m ∈ N, conjSub X m ≠ X) {B Y : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hY : Y ∈ Δ₁) (hs : Special R B Y) {y : G}
    (hy : y ∈ Y) : ∃ n ∈ N, conjSub B n = conjSub B y := by
  have hS := hD.sec12
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hNV' : N ≤ levi R A A₀ := hNV.trans hD.gen₁_le_levi
  have hYl := hD.mem_leviSet₁ hY
  by_cases hy1 : y = 1
  · exact ⟨1, N.one_mem, by rw [hy1]⟩
  have hY2 := hS.card_eq_two_of_mem hq hYl.1.1
  have hconjΔ : ∀ {X D : Subgroup G}, X ∈ deltaSet R A A₀ D → ∀ {g : G}, g ∈ levi R A A₀ →
      conjSub X g ∈ deltaSet R A A₀ (conjSub D g) := fun hX _ hg =>
    ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hg, conjSub_mem_lambdaSet hR hX.2 _⟩
  obtain ⟨hK, hKB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hYl hs
  obtain ⟨E, hE₂, hEB⟩ := hD.exists_mem₂_deltaSet hB
  have hEK : E ∈ deltaSet R A A₀ ⁅B, Y⁆ :=
    (hS.commuting_iff_mem_deltaSet_commutator hB hYl hs hEB).1 (hD.commuting_of_mem hY hE₂).symm
  obtain ⟨F, ⟨hFB, hFK⟩, hFE⟩ := hS.exists_ne_mem_deltaSet_inter hB hK hKB ⟨hEB, hEK⟩
  obtain ⟨Z, hZ, hEZ⟩ := hD.exists_opposite₂ hE₂
  have hEne : E ≠ ⊥ := hR.ne_bot _ hEB.1.1.1
  have hZB : Z ∉ deltaSet R A A₀ B := fun h =>
    hEZ.not_commuting hEne (hS.commuting_of_mem_deltaSet' hB hEB h)
  have hsZ : Special R B Z :=
    (hS.mem_deltaSet_or_special hB (hD.mem_leviSet₂ hZ)).resolve_left hZB
  obtain ⟨hL, hLB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB
    (hD.mem_leviSet₂ hZ) hsZ
  obtain ⟨D₁, hD₁B, hD₁L⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hL hLB
  obtain ⟨D₂, ⟨hD₂B, hD₂L⟩, hD₂D₁⟩ := hS.exists_ne_mem_deltaSet_inter hB hL hLB ⟨hD₁B, hD₁L⟩
  have hD₁ : ∀ {D : Subgroup G}, D ∈ deltaSet R A A₀ B → D ∈ deltaSet R A A₀ ⁅B, Z⁆ → D ∈ Δ₁ := by
    intro D hDB hDL
    refine (hD.mem_or_mem hDB.1).resolve_right fun hD₂ => ?_
    have hDZ : Commuting D Z :=
      (hS.commuting_iff_mem_deltaSet_commutator hB (hD.mem_leviSet₂ hZ) hsZ hDB).2 hDL
    by_cases he : D = Z
    · exact hZB (he ▸ hDB)
    · exact (hD.opposite_of_mem₂ hD₂ hZ he).not_commuting (hR.ne_bot _ hDB.1.1.1) hDZ
  obtain ⟨D, hDB, hD₁', hDE, hDF⟩ : ∃ D ∈ deltaSet R A A₀ B, D ∈ Δ₁ ∧ D ≠ E ∧ D ≠ F := by
    by_cases h : D₁ = F
    · exact ⟨D₂, hD₂B, hD₁ hD₂B hD₂L, hD.ne_of_mem₁_of_mem₂ (hD₁ hD₂B hD₂L) hE₂,
        fun h' => hD₂D₁ (h'.trans h.symm)⟩
    · exact ⟨D₁, hD₁B, hD₁ hD₁B hD₁L, hD.ne_of_mem₁_of_mem₂ (hD₁ hD₁B hD₁L) hE₂, h⟩
  obtain ⟨m, hm, hmD⟩ := hmoved D hD₁'
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDB.1.1.1
  have hD2 := hS.card_eq_two_of_mem hq hDB.1.1.1
  have hdd := CaseM.mul_self_eq_one_of_card_eq_two hD2 hd
  have hn : d * (m * d * m⁻¹) ∈ N := Sec12.mul_conj_mem hnorm hDB.1 hd hdd hm
  set n := d * (m * d * m⁻¹) with hndef
  have hcent : ∀ {W : Subgroup G}, W ∈ deltaSet R A A₀ B → D ≠ W → ∀ w ∈ W, Commute n w := by
    intro W hW hDW w hw
    have h1 : Commute d w := hS.commuting_of_mem_deltaSet' hB hDB hW d hd w hw
    have h2 : Commute (m * d * m⁻¹) w :=
      (hS.commuting_conjSub_of_isPGroup_three hq hNV' hnorm h3 hDB.1 hW.1 hDW
        (hS.commuting_of_mem_deltaSet' hB hDB hW) hm) _ (conj_mem_conjSub m hd) w hw
    exact h1.mul_left h2
  have hcentE := hcent hEB hDE
  have hcentF := hcent hFB hDF
  have hDm : Opposite D (conjSub D m) := by
    by_cases he : conjSub D m = D
    · exact absurd he hmD
    · exact hS.opposite_of_not_commuting hDB.1
        (Levi.conjSub_mem_leviSet_of_mem_levi hR hDB.1 (hNV' hm))
        fun hc => he (hS.conjSub_eq_of_commuting_conjSub hq hnorm h3 hDB.1 hm hc)
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
      have := hconjΔ hDB (hNV' hn)
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
    obtain ⟨y', hy', hy'B⟩ := CaseB.exists_conjSub_eq_of_le_sup hR hiso hB.1.1.1 hYl.1.1
      hB'.1.1.1 hs hle h2
    rcases CaseM.eq_one_or_eq_of_card_eq_two hY2 hy hy1 hy' with rfl | rfl
    · left
      rw [← hy'B, conjSub_one]
    · right; left
      exact hy'B.symm
  have hpow : ∀ k : ℕ, conjSub B (n ^ k) ∈ lambdaStar R A A₀ ∧
      E ∈ deltaSet R A A₀ (conjSub B (n ^ k)) ∧ F ∈ deltaSet R A A₀ (conjSub B (n ^ k)) := by
    intro k
    have hnk : n ^ k ∈ levi R A A₀ := hNV' (N.pow_mem hn k)
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
theorem exists_conjSub_eq_of_mem_gen₁
    (hmoved : ∀ X ∈ Δ₁, ∃ m ∈ N, conjSub X m ≠ X) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) {v : G} (hv : v ∈ gen Δ₁) :
    ∃ n ∈ N, conjSub B n = conjSub B v := by
  have hS := hD.sec12
  have hR := hS.hyp.root
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
  have hle : gen Δ₁ ≤ H := gen_le fun X hX x hx => by
    refine ⟨hD.gen₁_le_levi (le_gen hX hx), fun B hB => ?_⟩
    rcases hS.mem_deltaSet_or_special hB (hD.mem_leviSet₁ hX) with hXB | hs
    · refine ⟨1, N.one_mem, ?_⟩
      rw [conjSub_one, conjSub_of_forall_commute fun b hb => (hXB.2.1.2.2 b hb x hx).symm]
    · exact hD.exists_conjSub_eq_of_special₁ hq hNV hnorm h3 hmoved hB hX hs hx
  exact (hle hv).2 B hB

include hq hNV hnorm h3 in
theorem eq_bot_of_isPGroup_three : N = ⊥ := by
  have hS := hD.sec12
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hA := hS.mem
  have hNV' : N ≤ levi R A A₀ := hNV.trans hD.gen₁_le_levi
  by_contra hne
  have hconjΔ : ∀ {X D : Subgroup G}, X ∈ deltaSet R A A₀ D → ∀ {g : G}, g ∈ levi R A A₀ →
      conjSub X g ∈ deltaSet R A A₀ (conjSub D g) := fun hX _ hg =>
    ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hg, conjSub_mem_lambdaSet hR hX.2 _⟩
  have hN₂ : ∀ {X : Subgroup G}, X ∈ Δ₂ → ∀ n ∈ N, conjSub X n = X := fun hX n hn =>
    conjSub_of_forall_commute fun x hx => hD.commuting_gen _ (hNV hn) x (le_gen hX hx)
  obtain ⟨X₀, hX₀, m₀, hm₀, hne₀⟩ : ∃ X ∈ Δ₁, ∃ m ∈ N, conjSub X m ≠ X := by
    by_contra h
    push Not at h
    refine hne (hS.eq_bot_of_forall_conjSub_eq hq hNV' fun X hX => ?_)
    rcases hD.mem_or_mem hX with hX₁ | hX₂
    · exact h X hX₁
    · exact hN₂ hX₂
  have hmoved : ∀ X ∈ Δ₁, ∃ m ∈ N, conjSub X m ≠ X := by
    intro X hX
    obtain ⟨v, hv, rfl⟩ := Sec9.exists_conjSub_eq hD.hyp hD.comp₁ hX₀ hX
    refine ⟨v * m₀ * v⁻¹, hnorm v (hD.gen₁_le_levi hv) m₀ hm₀, fun h => hne₀ ?_⟩
    rw [← conjSub_mul, show v * m₀ * v⁻¹ * v = v * m₀ by group, conjSub_mul] at h
    exact RankOne.map_conj_inj.1 h
  obtain ⟨B, hB, -⟩ := hS.exists_special_lambdaStar
  have h7 : ∀ X ∈ Δ₁, ∃ n ∈ N, conjSub X n ∈ deltaSet R A A₀ B := by
    intro X hX
    obtain ⟨B', hB', hXB'⟩ := hS.exists_mem_deltaSet (hD.mem_leviSet₁ hX)
    obtain ⟨v, hv, hvB⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hA hS.sec8.2
      hS.max hS.opp hB hB'
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := CaseOA.exists_eq_mul_of_mem_levi hD.hyp hA hD.ne hD.opp
      hD.card_comps hD.comp₁ hD.comp₂ hD.comp_ne hv
    have hc12 : v₁ * v₂ = v₂ * v₁ := (hD.commuting_gen _ hv₁ _ hv₂).eq
    have hv₂l : v₂⁻¹ ∈ levi R A A₀ := hD.gen₂_le_levi (inv_mem hv₂)
    have h1 := hconjΔ hXB' hv₂l
    have hXe : conjSub X v₂⁻¹ = X := conjSub_of_forall_commute fun x hx =>
      (hD.commuting_gen _ (le_gen hX hx) _ (inv_mem hv₂)).symm
    have hBe : conjSub B' v₂⁻¹ = conjSub B v₁ := by
      rw [← hvB, ← conjSub_mul, hc12, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hXe, hBe] at h1
    obtain ⟨n, hn, hnB⟩ := hD.exists_conjSub_eq_of_mem_gen₁ hq hNV hnorm h3 hmoved hB hv₁
    refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
    have h2 := hconjΔ h1 (hNV' (N.inv_mem hn))
    rwa [← hnB, ← conjSub_mul, inv_mul_cancel, conjSub_one] at h2
  have h8 : ∀ X ∈ Δ₁, ∀ Y ∈ Δ₁, (∀ n ∈ N, conjSub X n ≠ Y) → Commuting X Y := by
    intro X hX Y hY hXY
    obtain ⟨n₁, hn₁, h₁⟩ := h7 X hX
    obtain ⟨n₂, hn₂, h₂⟩ := h7 Y hY
    have hne₁₂ : conjSub X n₁ ≠ conjSub Y n₂ := fun h => hXY (n₂⁻¹ * n₁)
      (N.mul_mem (N.inv_mem hn₂) hn₁) (by
        rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one])
    have hc := hS.commuting_of_mem_deltaSet' hB h₁ h₂
    have hc1 := hS.commuting_conjSub_of_isPGroup_three hq hNV' hnorm h3 h₁.1 h₂.1 hne₁₂ hc
      (N.inv_mem hn₁)
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hc1
    have hne₂ : conjSub Y n₂ ≠ X := fun h => hXY n₂⁻¹ (N.inv_mem hn₂) (by
      rw [← h, ← conjSub_mul, inv_mul_cancel, conjSub_one])
    have hc2 := hS.commuting_conjSub_of_isPGroup_three hq hNV' hnorm h3 h₂.1
      (hD.mem_leviSet₁ hX) hne₂ hc1.symm (N.inv_mem hn₂)
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hc2
    exact hc2.symm
  obtain ⟨E, hE₂, hEB⟩ := hD.exists_mem₂_deltaSet hB
  obtain ⟨Z, hZ, hEZ⟩ := hD.exists_opposite₂ hE₂
  have hEne : E ≠ ⊥ := hR.ne_bot _ hEB.1.1.1
  have hZB : Z ∉ deltaSet R A A₀ B := fun h =>
    hEZ.not_commuting hEne (hS.commuting_of_mem_deltaSet' hB hEB h)
  have hsZ : Special R B Z :=
    (hS.mem_deltaSet_or_special hB (hD.mem_leviSet₂ hZ)).resolve_left hZB
  obtain ⟨hL, hLB, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB
    (hD.mem_leviSet₂ hZ) hsZ
  obtain ⟨D₁, hD₁B, hD₁L⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hL hLB
  obtain ⟨D₂, ⟨hD₂B, hD₂L⟩, hD₂D₁⟩ := hS.exists_ne_mem_deltaSet_inter hB hL hLB ⟨hD₁B, hD₁L⟩
  have hDΔ₁ : ∀ {D : Subgroup G}, D ∈ deltaSet R A A₀ B → D ∈ deltaSet R A A₀ ⁅B, Z⁆ →
      D ∈ Δ₁ := by
    intro D hDB hDL
    refine (hD.mem_or_mem hDB.1).resolve_right fun hD₂ => ?_
    have hDZ : Commuting D Z :=
      (hS.commuting_iff_mem_deltaSet_commutator hB (hD.mem_leviSet₂ hZ) hsZ hDB).2 hDL
    by_cases he : D = Z
    · exact hZB (he ▸ hDB)
    · exact (hD.opposite_of_mem₂ hD₂ hZ he).not_commuting (hR.ne_bot _ hDB.1.1.1) hDZ
  have hD₁₁ := hDΔ₁ hD₁B hD₁L
  have hD₂₁ := hDΔ₁ hD₂B hD₂L
  have hclass : ∀ D, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) D₁ D →
      ∃ n ∈ N, conjSub D₁ n = D := by
    intro D hDp
    have hsub : ∀ {D'}, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) D₁ D' → D' ∈ Δ₁ := by
      intro D' hD'
      obtain ⟨E₀, -, he⟩ := hD.comp₁
      rw [he] at hD₁₁ ⊢
      exact hD₁₁.trans hD'
    induction hDp with
    | refl => exact ⟨1, N.one_mem, conjSub_one D₁⟩
    | @tail b c hab hbc ih =>
      obtain ⟨n, hn, hnb⟩ := ih
      by_contra hcl
      push Not at hcl
      have hnc : ∀ m ∈ N, conjSub b m ≠ c := fun m hm h => hcl (m * n) (N.mul_mem hm hn)
        (by rw [conjSub_mul, hnb, h])
      exact hbc.2.2.not_commuting (hR.ne_bot _ hbc.1.1.1)
        (h8 b (hsub hab) c (hsub (hab.tail hbc)) hnc)
  have hpath : Relation.ReflTransGen (oppGraph (leviSet R A A₀)) D₁ D₂ := by
    obtain ⟨E₀, -, he⟩ := hD.comp₁
    rw [he] at hD₁₁ hD₂₁
    exact (Sec3.reflTransGen_oppGraph_symm hD₁₁).trans hD₂₁
  obtain ⟨n, hn, hnD⟩ := hclass D₂ hpath
  have hc : Commuting D₁ (conjSub D₁ n) := by
    rw [hnD]
    exact hS.commuting_of_mem_deltaSet' hB hD₁B hD₂B
  exact hD₂D₁ (hnD.symm.trans (hS.conjSub_eq_of_commuting_conjSub hq hnorm h3 hD₁B.1 hn hc))

include hq in
theorem eq_bot_of_normal_isPGroup_three (N : Subgroup ↥(gen Δ₁)) (hN : N.Normal)
    (h3 : IsPGroup 3 N) : N = ⊥ := by
  have key := hD.eq_bot_of_isPGroup_three hq (N := N.map (gen Δ₁).subtype)
    (fun _ ⟨n, _, hn⟩ => hn ▸ n.2) (fun v hv _ ⟨n, hn, hne⟩ => ?_) (h3.map _)
  · exact (Subgroup.map_eq_bot_iff_of_injective N (gen Δ₁).subtype_injective).1 key
  · obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := CaseOA.exists_eq_mul_of_mem_levi hD.hyp hD.mem hD.ne
      hD.opp hD.card_comps hD.comp₁ hD.comp₂ hD.comp_ne hv
    have hc : v₂ * (n : G) * v₂⁻¹ = n := by
      rw [(hD.commuting_gen _ n.2 _ hv₂).symm.eq, mul_inv_cancel_right]
    refine ⟨⟨v₁, hv₁⟩ * n * ⟨v₁, hv₁⟩⁻¹, hN.conj_mem n hn ⟨v₁, hv₁⟩, ?_⟩
    rw [← hne]
    change v₁ * (n : G) * v₁⁻¹ = v₁ * v₂ * n * (v₁ * v₂)⁻¹
    rw [mul_inv_rev, show v₁ * v₂ * (n : G) * (v₂⁻¹ * v₁⁻¹) = v₁ * (v₂ * n * v₂⁻¹) * v₁⁻¹ by
      group, hc]

theorem o3 : (∃ X ∈ restrict Δ₁ (gen Δ₁), Nat.card X = 2) →
    ∀ N : Subgroup ↥(gen Δ₁), N.Normal → IsPGroup 3 N → N = ⊥ := by
  rintro ⟨_, ⟨X, ⟨hX, hXV⟩, rfl⟩, h2⟩ N hN h3
  have hq : Nat.card A = 2 := by
    rw [← h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXV).toEquiv]
    exact hD.hyp.root.card_eq hD.mem (hD.mem_leviSet₁ hX).1.1
  exact hD.eq_bot_of_normal_isPGroup_three hq N hN h3

end Three

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
