module

public import Certificates.Certificate712501
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartComp

public section

namespace CFSG.StandardType.E6Heart

private theorem ggE6f_Qh_eq (t : ℕ) :
    Qh (yOf t) = ((Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) : ℕ) : ZMod 3) := by
  unfold yOf
  rw [Qh_mk, ← qOf_eq (Certificates.E6Heart.repL t) (repL_length t)]

private theorem ggE6f_natCast_eq (n q : ℕ) (hn : n < 3) (hq : q < 3) :
    ((n : ℕ) : ZMod 3) = ((q : ℕ) : ZMod 3) ↔ n = q := by
  interval_cases n <;> interval_cases q <;> decide

private theorem ggE6f_Qh_zero_iff (t : ℕ) :
    Qh (yOf t) = 0 ↔ Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 0 := by
  rw [ggE6f_Qh_eq]
  exact ggE6f_natCast_eq _ 0 (qOf_lt _) (by norm_num)

private theorem ggE6f_Qh_one_iff (t : ℕ) :
    Qh (yOf t) = 1 ↔ Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 1 := by
  rw [ggE6f_Qh_eq]
  exact ggE6f_natCast_eq _ 1 (qOf_lt _) (by norm_num)

private theorem ggE6f_core (y : H) (hy : y ≠ 0) :
    (Qh y = 0 → ∀ c : (graph y).ConnectedComponent, compSize y c ≤ 6) ∧
    (Qh y ≠ 0 → ∃ c₀ : (graph y).ConnectedComponent,
      compSize y c₀ = (if Qh y = 1 then 24 else 30) ∧
      Nat.card (compKernel y c₀) = 3 ∧
      ∀ c : (graph y).ConnectedComponent, 6 < compSize y c → c = c₀) := by
  obtain ⟨hroots, _hrad, hgood, _hc0, _hc1, _hc2⟩ :=
    check_spec Certificates.certificate712501
  obtain ⟨t, ht⟩ := yOf_bijective.surjective y
  change yOf t = y at ht
  rw [← ht] at hy ⊢
  have htne : t ≠ 0 := by
    intro h
    exact hy (by rw [h]; exact yOf_zero)
  obtain ⟨hcl, hq0, hqne⟩ := goodAt_spec (t : ℕ) (hgood t htne)
  obtain ⟨f, hfsurj, hfsize, hfker, hfmem⟩ := graph_components hroots t hcl
  constructor
  · intro hQ0 c
    have hq0' : Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 0 :=
      (ggE6f_Qh_zero_iff (t : ℕ)).mp hQ0
    obtain ⟨i, rfl⟩ := hfsurj c
    rw [hfsize i]
    exact hq0 hq0' i.1 i.2
  · intro hQne
    have hqne' : Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) ≠ 0 := by
      intro h
      exact hQne ((ggE6f_Qh_zero_iff (t : ℕ)).mpr h)
    obtain ⟨huniq, i₀, hi₀mem, hi₀len, hi₀ker⟩ := hqne hqne'
    refine ⟨f ⟨i₀, hi₀mem⟩, ?_, ?_, ?_⟩
    · rw [hfsize ⟨i₀, hi₀mem⟩, hi₀len]
      by_cases hA : Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 1
      · have hB : Qh (yOf t) = 1 := (ggE6f_Qh_one_iff (t : ℕ)).mpr hA
        simp [hA, hB]
      · have hB : Qh (yOf t) ≠ 1 := fun h => hA ((ggE6f_Qh_one_iff (t : ℕ)).mp h)
        simp [hA, hB]
    · rw [hfker ⟨i₀, hi₀mem⟩, hi₀ker]
    · intro c hc
      obtain ⟨j, rfl⟩ := hfsurj c
      rw [hfsize j] at hc
      have hbig : 6 < (Certificates.E6Heart.compOf
          (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i₀).length := by
        rw [hi₀len]; split <;> norm_num
      rcases huniq i₀ hi₀mem hbig j j.2 with hj | hj
      · omega
      · exact ((hfmem ⟨i₀, hi₀mem⟩ j).mpr hj).symm

theorem e6_heart_big_component_kernel (y : H) (hy : y ≠ 0)
    (c : (graph y).ConnectedComponent) (hc : 6 < compSize y c) :
    Nat.card (compKernel y c) = 3 := by
  obtain ⟨h0, hne⟩ := ggE6f_core y hy
  by_cases hQ0 : Qh y = 0
  · exact absurd (h0 hQ0 c) (by omega)
  · obtain ⟨c₀, _hsize, hker, huniq⟩ := hne hQ0
    rw [huniq c hc, hker]

end CFSG.StandardType.E6Heart

end

