module

public import CFSG.Quasithin.MS93.S33Base

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def actTriv (h : PUHyp M T L) : Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ u ∈ Uq M T L, ⁅u, m⁆ ∈ Subgroup.centralizer (L : Set G)}
  mul_mem' := by
    rintro a b ⟨ha, hau⟩ ⟨hb, hbu⟩
    refine ⟨mul_mem ha hb, fun u hu => ?_⟩
    have e : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hc := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_centralizer (h.le_normalizer) ha) _).mp (hbu u hu)
    rw [e]
    exact mul_mem (hau u hu) hc
  one_mem' := ⟨one_mem _, fun u _ => by
    rw [commutatorElement_one_right]
    exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, hau⟩
    refine ⟨inv_mem ha, fun u hu => ?_⟩
    have e : ⁅u, a⁻¹⁆ = a⁻¹ * ⁅u, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    have hc := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_centralizer (h.le_normalizer) (inv_mem ha)) _).mp (inv_mem (hau u hu))
    rw [e]
    simpa [mul_assoc] using hc

theorem mem_actTriv (h : PUHyp M T L) {m : G} :
    m ∈ actTriv h ↔ m ∈ M ∧ ∀ u ∈ Uq M T L, ⁅u, m⁆ ∈ Subgroup.centralizer (L : Set G) :=
  Iff.rfl

theorem actTriv_le (h : PUHyp M T L) : actTriv h ≤ M := fun _ hm => hm.1

theorem le_normalizer_actTriv (h : PUHyp M T L) :
    M ≤ Subgroup.normalizer (actTriv h : Set G) := by
  have key : ∀ g ∈ M, ∀ m ∈ actTriv h, g * m * g⁻¹ ∈ actTriv h := by
    rintro g hg m ⟨hm, hmu⟩
    refine ⟨mul_mem (mul_mem hg hm) (inv_mem hg), fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ Uq M T L := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_Uq (T := T) h.le_normalizer (inv_mem hg)) u).mp hu
      simpa using this
    have e : ⁅u, g * m * g⁻¹⁆ = g * ⁅g⁻¹ * u * g, m⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_centralizer (h.le_normalizer) hg) _).mp (hmu _ hu')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨key g hg m, fun hm' => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hm'
  simpa [mul_assoc] using this

theorem not_le_actTriv (h : PUHyp M T L) : ¬ L ≤ actTriv h := by
  intro hL
  apply h.Uq_ne_bot
  have hle : Uq M T L ≤ Subgroup.centralizer (L : Set G) := by
    rw [← h.Uq_comm, Subgroup.commutator_le]
    intro u hu l hl
    exact (hL hl).2 u hu
  rw [← h.Uq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hle

theorem centralizer_of_actTriv (h : PUHyp M T L) {m : G} (hm : m ∈ actTriv h) :
    m ∈ Subgroup.centralizer (Uq M T L : Set G) := by
  have hNL : ⁅actTriv h, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (actTriv_le h) (le_normalizer_actTriv h) (not_le_actTriv h)
  have hQU : pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) :=
    h.pCoreOf_le_centralizer_Z0q.trans (Subgroup.centralizer_le (Uq_le_Z0q h.L_le))
  have hK : Subgroup.zpowers m ≤ actTriv h := (Subgroup.zpowers_le).2 hm
  have h1 : ⁅⁅Uq M T L, Subgroup.zpowers m⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro u hu k hk
    exact (hK hk).2 u hu
  have h2 : ⁅⁅Subgroup.zpowers m, L⁆, Uq M T L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact ((Subgroup.commutator_mono hK le_rfl).trans hNL).trans hQU
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [Subgroup.commutator_comm L, h.Uq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (h3 hu) m (Subgroup.mem_zpowers m)).symm

theorem mem_pCoreOf_of_actTriv (h : PUHyp M T L) {t : G} (ht : t ∈ T) (htr : t ∈ actTriv h) :
    t ∈ pCoreOf 2 M := by
  rw [← inf_centralizer_Uq h]
  exact ⟨ht, centralizer_of_actTriv h htr⟩

end CFSG.Quasithin.MS93.S33
