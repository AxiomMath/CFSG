module

public import Certificates.Kernel.Co1Sub.OrderT
public import CFSG.Certificates.Kernel.Co1Sub.FlagSound

public section

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TabMatGrp CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co1.Native (co1Data)

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem nF_parts : fTP.length = 1 ∧ fAP.length = 3 ∧ fBP.length = 405 := by
  have h := ch120801_nF
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq,
    lenL_eq_length, lenL_eq_length, lenL_eq_length] at h
  exact h

theorem P0_mul : MatP 24 P0 * MatP 24 (fTPi.getD 0 0) = 1 := by
  obtain ⟨k, hk, e⟩ := flag_root ch120801_fT (by rw [nF_parts.1]; omega)
  have hk0 : k = 0 := by rw [nF_parts.1] at hk; omega
  subst hk0
  have hm := (flagAt_full ch120801_fT (k := 0) (by rw [nF_parts.1]; omega)).1
  rw [← MatP_mul, ← mulS_eq, ← e, hm, MatP_oneS]

@[expose] noncomputable def B0 : GL (Fin 24) (ZMod 2) :=
  ⟨MatP 24 P0, MatP 24 (fTPi.getD 0 0), P0_mul,
    (mul_eq_one_comm (M := Matrix (Fin 24) (Fin 24) (ZMod 2))).mp P0_mul⟩

theorem val_B0 : (B0 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = MatP 24 P0 := rfl

theorem subG_eq (idx : List ℕ) :
    subG idx = Subgroup.closure {g | ∃ i < idx.length, auxG (idx.getD i 0) = g} := by
  refine le_antisymm (subG_le_closure idx) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.subset_closure
    ⟨_, by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi, rfl⟩

theorem pick_gens {idx : List ℕ} (hidx : ∀ i ∈ idx, i < 301) :
    (pickL aM idx).length = idx.length ∧ ∀ i < (pickL aM idx).length,
      MatP 24 ((pickL aM idx).getD i 0) = matOf φJ (auxG (idx.getD i 0)) := by
  obtain ⟨hl, hB, -⟩ := pick_parts hidx ⊤ fun _ _ => Subgroup.mem_top _
  exact ⟨hl, fun i hi => (hB i hi).1⟩

theorem card_subG_flag {idx : List ℕ} (hidx : ∀ i ∈ idx, i < 301) {P Pi R : List Nat}
    (h : flagK (pickL aM idx) P0 P Pi R = true) (hN : 0 < P.length) :
    Nat.card (subG idx) = P.length * Nat.card ↥(subG idx ⊓ flagStab φJ B0) := by
  obtain ⟨hl, hg⟩ := pick_gens hidx
  have e : Nat.card (Subgroup.closure {g | ∃ i < (pickL aM idx).length,
      auxG (idx.getD i 0) = g}) = P.length * Nat.card ↥(Subgroup.closure
        {g | ∃ i < (pickL aM idx).length, auxG (idx.getD i 0) = g} ⊓ flagStab φJ B0) :=
    card_flag hg h val_B0 hN
  rw [hl, ← subG_eq] at e
  exact e

theorem tI_le_stab : subG tI ≤ flagStab φJ B0 := by
  obtain ⟨hl, hg⟩ := pick_gens (idx := tI) (by decide)
  have h : Subgroup.closure {g | ∃ i < (pickL aM tI).length, auxG (tI.getD i 0) = g} ≤
      flagStab φJ B0 := le_flagStab hg ch120801_fT val_B0 nF_parts.1
  rw [hl, ← subG_eq] at h
  exact h

theorem card_dvd_of_pow32 (K : Subgroup (J (co1Data ())))
    (hK : ∀ x ∈ K, x ^ 32 = 1) : Nat.card K ∣ 2 ^ 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 K := fun g =>
    ⟨5, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hK g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  have hd := Subgroup.card_subgroup_dvd_card K
  rw [CFSG.Sporadic.Bridge.Co1.card_J, hn,
    (by norm_num : (4157776806543360000 : ℕ) = 2 ^ 21 * 1982582476875)] at hd
  rw [hn]
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 1982582476875)).dvd_of_dvd_mul_right hd

theorem card_stab {idx : List ℕ} (htI : ∀ i ∈ tI, i ∈ idx) :
    Nat.card ↥(subG idx ⊓ flagStab φJ B0) = 2 ^ 21 := by
  refine le_antisymm (Nat.le_of_dvd (by norm_num) (card_dvd_of_pow32 _ fun x hx =>
    pow32_of_flagStab Subtype.val_injective (Subgroup.mem_inf.1 hx).2)) ?_
  rw [← card_subG_tI]
  refine Subgroup.card_le_of_le (le_inf ?_ tI_le_stab)
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact auxG_mem_subG (htI i hi)

theorem card_subG_aI : Nat.card (subG aI) = 3 * 2 ^ 21 := by
  rw [card_subG_flag (by decide) ch120801_fA (by rw [nF_parts.2.1]; omega), nF_parts.2.1,
    card_stab (by decide)]

theorem card_subG_bI : Nat.card (subG bI) = 405 * 2 ^ 21 := by
  rw [card_subG_flag (by decide) ch120801_fB (by rw [nF_parts.2.2]; omega), nF_parts.2.2,
    card_stab (by decide)]

theorem sup_subG_aI_bI : subG aI ⊔ subG bI = ⊤ := by
  have hsplit : ∀ i ∈ hI, i ∈ aI ∨ i ∈ bI := by decide
  refine eq_top_of_hI _ fun i hi => ?_
  rcases hsplit i hi with h | h
  · exact Subgroup.mem_sup_left (auxG_mem_subG h)
  · exact Subgroup.mem_sup_right (auxG_mem_subG h)

end CFSG.KD.Co1Sub

end
