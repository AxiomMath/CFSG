
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Clos
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Act

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.E2P.SporB
open CFSG.Sporadic.Mathieu (m24a m24b m24_hyp)

@[expose] def memIdx : Array ℕ := #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9]

@[expose] noncomputable def m24CtxE [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    LatCtx G24 24 (List ℕ) :=
  m24Ctx

section Lattice

theorem m24_hL [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : m24CtxE.D.Om.map (fun o => o.lbl.size) = memIdx := m24_Om_map

theorem m24_all [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : ∀ Z : Subgroup G24, m24CtxE.S ≤ Z →
    ∃ j ≤ memIdx.size, Z = memberOrTop memIdx.size m24CtxE.Y j := lat_all m24CtxE m24_hL

theorem m24_card_Y [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : ∀ j < memIdx.size, Nat.card (m24CtxE.Y j) = memIdx[j]! * 2 ^ 10 :=
  lat_card m24CtxE m24_hL

theorem m24_S_isPGroup [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : IsPGroup 2 m24CtxE.S := m24CtxE.S_isPGroup

theorem m24_S_sylow' [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : IsSylowTwoOf m24CtxE.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m24CtxE.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m24CtxE.S
  have hN : m24CtxE.D.O.lbl.size = 239085 := m24_O_size
  rw [m24CtxE.S_card, m24CtxE.hΓ, hN] at h1
  have h2 : m24CtxE.S.index = 239085 := by
    have : m24CtxE.k = 10 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem overgroup_member [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {Z : Subgroup G24} (hSZ : m24CtxE.S ≤ Z) (hne : Z ≠ ⊤) :
    ∃ j < 13, Z = m24CtxE.Y j ∧ Nat.card Z = memIdx[j]! * 2 ^ 10 := by
  obtain ⟨j, hj, hZ⟩ := m24_all Z hSZ
  have hsz : memIdx.size = 13 := rfl
  by_cases hjl : j < 13
  · refine ⟨j, hjl, ?_, ?_⟩
    · rw [memberOrTop, ite_eq_left (by rw [hsz]; exact hjl)] at hZ
      exact hZ
    · rw [memberOrTop, ite_eq_left (by rw [hsz]; exact hjl)] at hZ
      rw [hZ]
      exact m24_card_Y j (by rw [hsz]; exact hjl)
  · exfalso
    apply hne
    have : j = 13 := by omega
    rw [memberOrTop, ite_eq_right (by rw [hsz]; omega)] at hZ
    exact hZ

end Lattice

theorem idx_315 : ∀ j < 13, memIdx[j]! = 315 → j = 1 := by decide

theorem idx_63 : ∀ j < 13, memIdx[j]! = 63 → j = 2 := by decide

theorem idx_21 : ∀ j < 13, memIdx[j]! = 21 → j = 4 ∨ j = 6 := by decide

theorem idx_5 : ∀ j < 13, 5 ∣ memIdx[j]! * 2 ^ 10 → j = 1 ∨ j = 3 := by decide

theorem idx_7 : ∀ j < 13, 7 ∣ memIdx[j]! * 2 ^ 10 → j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by decide

theorem idx_9_7 : ∀ j < 13, 9 ∣ memIdx[j]! * 2 ^ 10 → 7 ∣ memIdx[j]! * 2 ^ 10 →
    j = 1 ∨ j = 2 := by decide

theorem idx_dvd_35 : ∀ j < 13, 5 ∣ memIdx[j]! * 2 ^ 10 → 7 ∣ memIdx[j]! * 2 ^ 10 →
    memIdx[j]! = 315 := by decide

end CFSG.Quasithin.A312M24
