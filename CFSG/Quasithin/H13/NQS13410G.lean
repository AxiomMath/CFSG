module

public import CFSG.Quasithin.H13.NQS13410A

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_Z_le_four {K W : Subgroup G} (hTW : T ≤ normalizer (W : Set G))
    (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K) (hcZ : Nat.card ↥(U3.cZ T K) ≤ 2)
    (hcase : Nat.card ↥(W ⊓ centralizer (T : Set G)) ≤ 2 ∨
      (U3.cZ T K ≤ W ∧ Nat.card ↥(W ⊓ centralizer (T : Set G)) ≤ 4)) :
    Nat.card ↥(quasithinOmegaOneCenter T) ≤ 4 := by
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZT : Z ≤ centralizer (T : Set G) := fun x hx => (U3.s134_Z_le_center T hx).2
  have hZTT : Z ≤ T := fun x hx => (U3.s134_Z_le_center T hx).1
  have hcN : U3.cZ T K ≤ normalizer (W : Set G) := (inf_le_left.trans hZTT).trans hTW
  have hZWT : Z ⊓ W ≤ W ⊓ centralizer (T : Set G) := fun x hx =>
    mem_inf.2 ⟨(mem_inf.1 hx).2, hZT (mem_inf.1 hx).1⟩
  rcases hcase with h2 | ⟨hcW, h4⟩
  ·
    have hsurj : Function.Surjective fun p : ↥(Z ⊓ W) × ↥(U3.cZ T K) =>
        (⟨(p.1 : G) * p.2, mul_mem (mem_inf.1 p.1.2).1 (mem_inf.1 p.2.2).1⟩ : ↥Z) := by
      rintro ⟨x, hx⟩
      obtain ⟨w, hw, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hcN (hZW hx)
      have hwZ : w ∈ Z := by
        have : w = w * c * c⁻¹ := by group
        rw [this]
        exact mul_mem hx (inv_mem (mem_inf.1 hc).1)
      exact ⟨(⟨w, mem_inf.2 ⟨hwZ, hw⟩⟩, ⟨c, hc⟩), rfl⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod] at h1
    have h3 : Nat.card ↥(Z ⊓ W) ≤ 2 :=
      (Subgroup.card_le_of_le hZWT).trans h2
    calc Nat.card ↥Z ≤ Nat.card ↥(Z ⊓ W) * Nat.card ↥(U3.cZ T K) := h1
      _ ≤ 2 * 2 := Nat.mul_le_mul h3 hcZ
      _ = 4 := rfl
  ·
    have hZW' : Z ≤ W := hZW.trans (sup_le le_rfl hcW)
    exact (Subgroup.card_le_of_le (le_inf hZW' hZT)).trans h4

theorem five_six (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) {K : Subgroup G}
    (hKM : ¬ K ≤ normalizer (L : Set G)) {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hKz : K ≤ centralizer ({z} : Set G))
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) ≤ 4) :
    Nat.card ↥(quasithinOmegaOneCenter T) = 4 ∧ quasithinOmegaOneCenter T = fsuV1 T V ∧
      Nat.card ↥(U3.cZ T L) = 2 ∧ U3.cZ T K = zpowers z ∧
      V ⊓ centralizer (L : Set G) = U3.cZ T L := by
  have hZL := U3.s134_card_Z h1332 hC58 h317 h56 S hHM
  have hV1Z : fsuV1 T V ≤ quasithinOmegaOneCenter T := inf_le_right
  have hV1 := S.card_V1
  have hZ : fsuV1 T V = quasithinOmegaOneCenter T :=
    eq_of_le_of_card_ge hV1Z (by rw [hV1]; exact hZ4)
  have hZ4' : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [← hZ, hV1]
  have hZL2 : Nat.card ↥(U3.cZ T L) = 2 := by
    show Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)) = 2
    omega
  refine ⟨hZ4', hZ.symm, hZL2, cZ_K_eq S hKM hzZ hz1 hKz hZL, ?_⟩
  exact eq_of_le_of_card_ge S.ZV_le_ZL (by rw [hZL2, S.card_ZV])

end CFSG.Quasithin.H13.NQS134
