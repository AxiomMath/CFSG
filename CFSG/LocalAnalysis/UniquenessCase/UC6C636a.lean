module

public import CFSG.LocalAnalysis.UniquenessCase.UC6O633Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22

namespace UC6

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_centralizer_uc6 {P₀ : Subgroup G} {n : G} (hn : n ∈ normalizer (P₀ : Set G)) :
    n ∈ normalizer ((centralizer (P₀ : Set G) : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (P₀ : Set G), ∀ c ∈ centralizer (P₀ : Set G),
      n' * c * n'⁻¹ ∈ centralizer (P₀ : Set G) := by
    intro n' hn' c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : n'⁻¹ * x * n' ∈ P₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hn') x).1 hx
      simpa using this
    have hcx := hc _ hx'
    calc x * (n' * c * n'⁻¹) = n' * ((n'⁻¹ * x * n') * c) * n'⁻¹ := by group
      _ = n' * (c * (n'⁻¹ * x * n')) * n'⁻¹ := by rw [hcx]
      _ = (n' * c * n'⁻¹) * x := by group
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact key n hn c
  · intro hc
    have := key n⁻¹ (inv_mem hn) _ hc
    simpa [mul_assoc] using this

theorem mem_normalizer_inftyOf_uc6 {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G)) :
    n ∈ normalizer ((inftyOf H : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (H : Set G), ∀ z ∈ inftyOf H, n' * z * n'⁻¹ ∈ inftyOf H := by
    intro n' hn' z hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨Subgroup.normalizerMonoidHom H ⟨n', hn'⟩ x, ?_, by simp⟩
    have hfix : (derivedSeries ↥H (Nat.card H)).map
        (Subgroup.normalizerMonoidHom H ⟨n', hn'⟩).toMonoidHom = derivedSeries ↥H (Nat.card H) :=
      Subgroup.characteristic_iff_map_eq.1 inferInstance _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · exact key n hn z
  · intro hz
    have := key n⁻¹ (inv_mem hn) _ hz
    simpa [mul_assoc] using this

theorem mem_normalizer_Opp_uc6 {X : Subgroup G} {n : G} (hn : n ∈ normalizer (X : Set G)) (p : ℕ) :
    n ∈ normalizer ((Opp p X : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (X : Set G), ∀ y ∈ Opp p X, n' * y * n'⁻¹ ∈ Opp p X := by
    intro n' hn' y hy
    have hy' : y ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = p ^ k} := hy
    clear hy
    show n' * y * n'⁻¹ ∈ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = p ^ k}
    induction hy' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxX, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨(mem_normalizer_iff.1 hn' x).1 hxX, k, ?_⟩
      rw [← hk]
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj n') x
    | one => simp
    | mul x y _ _ hx hy =>
      have e : n' * (x * y) * n'⁻¹ = (n' * x * n'⁻¹) * (n' * y * n'⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : n' * x⁻¹ * n'⁻¹ = (n' * x * n'⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · exact key n hn z
  · intro hz
    have := key n⁻¹ (inv_mem hn) _ hz
    simpa [mul_assoc] using this

theorem normal_dichotomy_uc6 {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (center Q))) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (center Q) x ∈ (⊥ : Subgroup (Q ⧸ center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ center Q, M ⊔ center Q⁆ := by rw [hMZ]; rfl
      rw [e]
      have hn : (M ⊔ center Q).Normal := by rw [hMZ]; infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf] at hle
    exact top_le_iff.mp hle

namespace Mz614

variable (m : Mz614 G)

theorem normalizer_Z_le_normalizer_L : normalizer (m.Z : Set G) ≤ normalizer (m.L : Set G) := by
  intro n hn
  exact mem_normalizer_Opp_uc6 (mem_normalizer_inftyOf_uc6 (mem_normalizer_centralizer_uc6 hn)) m.r

theorem commutator_L_eq (hq : CFSG.Open.IsQuasisimple ↥m.L) : ⁅m.L, m.L⁆ = m.L := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥m.L) ⊤ m.L.subtype
  have htop : (⊤ : Subgroup ↥m.L).map m.L.subtype = m.L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅(⊤ : Subgroup ↥m.L), ⊤⁆ = ⊤ := hq.1
  rw [htop] at h
  rw [← h, h1]
  exact htop

theorem OL_le_centralizer (hq : CFSG.Open.IsQuasisimple ↥m.L) (hr : m.r ∣ Nat.card ↥m.L) :
    m.OL ≤ centralizer (m.L : Set G) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rcases normal_dichotomy_uc6 hq (CFSG.pPrimeCore m.r ↥m.L) with hc | htop
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [mem_centralizer_iff]
    intro l hl
    have := mem_center_iff.1 (hc hp) ⟨l, hl⟩
    exact congrArg Subtype.val this
  · exfalso
    have hcop : Nat.Coprime m.r (Nat.card (CFSG.pPrimeCore m.r ↥m.L)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact m.hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hr)

theorem le_centralizer_of_comm_le_OL (hq : CFSG.Open.IsQuasisimple ↥m.L) (hr : m.r ∣ Nat.card ↥m.L)
    {Q : Subgroup G} (hQ : ⁅Q, m.L⁆ ≤ m.OL) : Q ≤ centralizer (m.L : Set G) := by
  have hQc : ⁅Q, m.L⁆ ≤ centralizer (m.L : Set G) := hQ.trans (m.OL_le_centralizer hq hr)
  have h1 : ⁅⁅Q, m.L⁆, m.L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hQc
  have h2 : ⁅⁅m.L, Q⁆, m.L⁆ = ⊥ := by rw [Subgroup.commutator_comm m.L Q]; exact h1
  have h3 : ⁅⁅m.L, m.L⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [m.commutator_L_eq hq] at h3
  exact Subgroup.le_centralizer_iff.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)

end Mz614

end UC6

end CFSG.LocalAnalysis.UniquenessCase
