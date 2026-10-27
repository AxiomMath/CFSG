module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreTransfer
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Quasithin.H13.NPLCLV

theorem not_sq_dvd_20160 {p : ℕ} (hpp : p.Prime) (h5 : 5 ≤ p) : ¬ p ^ 2 ∣ 20160 := by
  intro hdvd
  have hle : p ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
  have hp141 : p ≤ 141 := by nlinarith
  interval_cases p <;> (try norm_num at hpp) <;> (try norm_num at hdvd) <;> omega

theorem not_dvd_card_ker {H A : Type} [Group H] [Group A] [Finite H]
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q) (hq : CFSG.IsQuasisimple (H ⧸ Q))
    (φ : H →* A) (hφ : Function.Surjective φ) (hA : Nat.card A = 20160)
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : ¬ p ∣ Nat.card φ.ker := by
  have hpp : p.Prime := Fact.out
  haveI : Finite A := Finite.of_surjective φ hφ
  obtain ⟨M, hM⟩ : ∃ M : Subgroup H, M = φ.ker ⊔ Q := ⟨_, rfl⟩
  haveI : M.Normal := by rw [hM]; infer_instance
  have hKM : φ.ker ≤ M := by rw [hM]; exact le_sup_left
  have hQM : Q ≤ M := by rw [hM]; exact le_sup_right
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hcomap : (Q.map φ).comap φ = ⊤ := by
      rw [Subgroup.comap_map_eq, sup_comm, ← hM]
      exact htop
    have hQtop : Q.map φ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨h, rfl⟩ := hφ a
      have hh : h ∈ (Q.map φ).comap φ := by
        rw [hcomap]
        exact Subgroup.mem_top h
      exact Subgroup.mem_comap.mp hh
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (IsPGroup.map hQ φ)
    rw [hQtop, Subgroup.card_top, hA] at hn
    have h3 : (3 : ℕ) ∣ 2 ^ n := by
      rw [← hn]
      omega
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hπ : Function.Surjective (QuotientGroup.mk' Q : H →* H ⧸ Q) :=
    QuotientGroup.mk'_surjective Q
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (H ⧸ Q), N = M.map (QuotientGroup.mk' Q) := ⟨_, rfl⟩
  haveI : N.Normal := by
    rw [hN]
    exact Subgroup.Normal.map ‹M.Normal› _ hπ
  have hNtop : N ≠ ⊤ := by
    intro htop
    apply hMtop
    have hc : N.comap (QuotientGroup.mk' Q) = ⊤ := by
      rw [htop, Subgroup.comap_top]
    rw [hN, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQM] at hc
    exact hc
  have hNZ : N ≤ Subgroup.center (H ⧸ Q) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq N with h | h
    · exact h
    · exact absurd h hNtop
  have hKidx : φ.ker.index = 20160 := by
    rw [← hA]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have hNidx : N.index = M.index := by
    have hker : (QuotientGroup.mk' Q : H →* H ⧸ Q).ker ≤ M := by
      rw [QuotientGroup.ker_mk']
      exact hQM
    rw [hN]
    exact Subgroup.index_map_eq (H := M) hπ hker
  have hchain : (Subgroup.center (H ⧸ Q)).index ∣ 20160 := by
    have h1 : (Subgroup.center (H ⧸ Q)).index ∣ N.index := Subgroup.index_dvd_of_le hNZ
    have h2 : M.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hKM
    rw [hNidx] at h1
    rw [← hKidx]
    exact h1.trans h2
  have hsq : ¬ p ^ 2 ∣ Nat.card ((H ⧸ Q) ⧸ Subgroup.center (H ⧸ Q)) := fun h =>
    not_sq_dvd_20160 hpp hp (h.trans hchain)
  obtain ⟨hperf, -, -⟩ := hq
  haveI : Finite (H ⧸ Q) := Finite.of_surjective _ hπ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (H ⧸ Q)) :=
    CFSG.AGLEmbeddingD2.McLaughlin.not_dvd_card_center_of_perfect hperf.commutator_eq_top hsq
  have hNZp : ¬ p ∣ Nat.card N := fun h => hZ (h.trans (Subgroup.card_dvd_of_le hNZ))
  have hQp : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
    intro h
    rw [hk] at h
    have h2 : p ∣ 2 := hpp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hMcard : Nat.card M = Nat.card N * Nat.card Q := by
    haveI : Finite (H ⧸ M) := Finite.of_surjective _ (QuotientGroup.mk'_surjective M)
    have hpos : 0 < M.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := M))
    have e1 : Nat.card M * M.index = Nat.card H := Subgroup.card_mul_index (H := M)
    have e2 : Nat.card Q * Nat.card (H ⧸ Q) = Nat.card H := Subgroup.card_mul_index (H := Q)
    have e3 : Nat.card N * N.index = Nat.card (H ⧸ Q) := Subgroup.card_mul_index (H := N)
    rw [hNidx] at e3
    have key : Nat.card M * M.index = (Nat.card N * Nat.card Q) * M.index := by
      rw [e1, ← e2, ← e3]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos key
  have hMp : ¬ p ∣ Nat.card M := by
    rw [hMcard]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
    · exact hNZp h'
    · exact hQp h'
  intro h
  exact hMp (h.trans (Subgroup.card_dvd_of_le hKM))

end CFSG.Quasithin.H13.NPLCLV
