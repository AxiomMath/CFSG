
module

public import CFSG.Sporadic.Schreier.J4SOddLocalBase1

public import CFSG.Sporadic.Schreier.J4SOddCheck
public import CFSG.Sporadic.Schreier.J4SOddLemmas
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

theorem conjOrbit_H_eq
    {n : J} (hn : n ∈ N) :
    {m | ∃ h ∈ H, m = h * n * h⁻¹} = conjOrbit K n := by
  ext m
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_mem_H hh
    refine ⟨k, hk, ?_⟩
    have h1 : k * n * k⁻¹ ∈ N := conj_mem_N_of_mem_H k (K_le_H hk) n hn
    calc a * k * n * (a * k)⁻¹ = a * (k * n * k⁻¹) * a⁻¹ := by group
      _ = k * n * k⁻¹ := by rw [N_comm a ha _ h1, mul_inv_cancel_right]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, K_le_H hk, rfl⟩

theorem card_H_inf_centralizer
    {n : J} (hn : n ∈ N) {s : ℕ} (hs : (conjOrbit K n).ncard = s) :
    Nat.card (H ⊓ Subgroup.centralizer {n} : Subgroup J) * s = Nat.card H := by
  rw [← hs, ← conjOrbit_H_eq hn]
  exact card_inf_centralizer_mul_ncard H n

section Local

variable {t : J}

theorem oddCoreImage_inf_H
    (ht : t ∈ N) : oddCoreImage (Subgroup.centralizer {t}) ⊓ H = ⊥ :=
  inf_eq_bot_of_odd conj_mem_N_of_mem_H
    QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le isPGroup_N
    (odd_card_oddCoreImage _) (N_conj_oddCoreImage ht)

theorem card_oddCoreImage_mul_dvd
    (ht : t ∈ N) :
    Nat.card (oddCoreImage (Subgroup.centralizer {t})) *
      Nat.card (H ⊓ Subgroup.centralizer {t} : Subgroup J) ∣ Nat.card J := by
  set C := Subgroup.centralizer ({t} : Set J) with hC
  have h := card_mul_card_dvd (H := C) (N := oddCoreImage C) (oddCoreImage_le C)
    (D := H ⊓ C) inf_le_right (fun h hh n hn => oddCoreImage_conj C hh hn)
  have hbot : (oddCoreImage C ⊓ (H ⊓ C) : Subgroup J) = ⊥ := by
    rw [← inf_assoc, oddCoreImage_inf_H ht, bot_inf_eq]
  rw [hbot, Subgroup.card_bot, one_mul] at h
  exact h.trans (Subgroup.card_subgroup_dvd_card C)

theorem oddCoreImage_eq_bot_of_le
    (ht : t ∈ N)
    (h : N ≤ Subgroup.centralizer (oddCoreImage (Subgroup.centralizer {t}) : Set J)) :
    oddCoreImage (Subgroup.centralizer {t}) = ⊥ := by
  have hRH : oddCoreImage (Subgroup.centralizer {t}) ≤ H := by
    intro r hr
    rw [← normalizer_N]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun n hn => ?_)
    exact (Subgroup.mem_centralizer_iff.1 (h hn) r hr).symm
  rw [eq_bot_iff, ← oddCoreImage_inf_H ht]
  exact le_inf le_rfl hRH

end Local

end CFSG.Sporadic.J4Schreier
