module

public import Certificates.Kernel.Co1Sub.Bind
public import CFSG.Certificates.Kernel.Co1Sub.LutSound
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TabMatGrp CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co1.Native (co1Data)

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

noncomputable abbrev subG (idx : List ℕ) : Subgroup (J (co1Data ())) :=
  Subgroup.closure {g | ∃ i ∈ idx, auxG i = g}

theorem fTP_length : fTP.length = 1 := by
  have h := ch120801_nF
  rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenL_eq_length] at h
  exact h.1

theorem subG_le_closure (idx : List ℕ) :
    subG idx ≤ Subgroup.closure {g | ∃ i < idx.length, auxG (idx.getD i 0) = g} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  exact Subgroup.subset_closure ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem pow32_subG_tI : ∀ x ∈ subG tI, x ^ 32 = 1 := by
  obtain ⟨hl, hB, -⟩ := pick_parts (idx := tI) (by decide) ⊤ fun _ _ => Subgroup.mem_top _
  have hg : ∀ i < (pickL aM tI).length, MatP 24 ((pickL aM tI).getD i 0) =
      matOf φJ (auxG (tI.getD i 0)) := fun i hi => (hB i hi).1
  have h := pow32_of_flag (φ := φJ) Subtype.val_injective hg ch120801_fT fTP_length
  intro x hx
  refine h x ?_
  have hc := subG_le_closure tI hx
  rwa [hl]

theorem isPGroup_subG_tI : IsPGroup 2 (subG tI) := fun g =>
  ⟨5, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow32_subG_tI g g.2)⟩

theorem card_subG_tI_dvd : Nat.card (subG tI) ∣ 2 ^ 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 isPGroup_subG_tI
  have hd := Subgroup.card_subgroup_dvd_card (subG tI)
  rw [CFSG.Sporadic.Bridge.Co1.card_J, hn,
    (by norm_num : (4157776806543360000 : ℕ) = 2 ^ 21 * 1982582476875)] at hd
  rw [hn]
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 1982582476875)).dvd_of_dvd_mul_right hd

end CFSG.KD.Co1Sub

end
