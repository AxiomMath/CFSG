module

public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M12Data
import CFSG.Sporadic.Schreier.M12
import CFSG.Sporadic.Schreier.M12Check
import CFSG.GH74.Generic.S1.Exo.Q3SingleM12
import Certificates.Certificate2193
import Certificates.Certificate3086
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.GH74.Generic.S1.Exo

namespace CertificateChecks.Batch15068

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.GH74.Generic.S1.Exo

theorem pow_three_or_five {g : Equiv.Perm (Fin 12)} (ho : orderOf g = 15) (x : Fin 12) :
    (g ^ 3) x = x ∨ (g ^ 5) x = x := by
  have h15 : Function.IsPeriodicPt g 15 x := by
    change (g ^ 15) x = x
    rw [← ho, pow_orderOf_eq_one]
    rfl
  have hle : Function.minimalPeriod g x ≤ 12 := by
    simpa using Function.minimalPeriod_le_card (f := ⇑g) (x := x)
  have key : ∀ m ≤ 12, m ∣ 15 → m ∣ 3 ∨ m ∣ 5 := by decide
  rcases key _ hle h15.minimalPeriod_dvd with h | h
  · exact Or.inl (Function.isPeriodicPt_iff_minimalPeriod_dvd.2 h)
  · exact Or.inr (Function.isPeriodicPt_iff_minimalPeriod_dvd.2 h)

theorem orderOf_ne_fifteen {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12) :
    orderOf g ≠ 15 := by
  intro ho
  have hfix : ∀ k, (k = 3 ∨ k = 5) →
      (Finset.univ.filter fun x => (g ^ k) x = x).card < 5 := by
    intro k hk
    by_contra hc
    obtain ⟨S, hS, hS5⟩ := Finset.exists_subset_card_eq (not_lt.1 hc)
    have h1 := m12_fix_five (g ^ k) (pow_mem hg k) (S.orderEmbOfFin hS5).toEmbedding
      fun i => (Finset.mem_filter.1 (hS (S.orderEmbOfFin_mem hS5 i))).2
    have hd : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at hd
    rcases hk with rfl | rfl <;> norm_num at hd
  have hcov : (Finset.univ : Finset (Fin 12)) ⊆ (Finset.univ.filter fun x => (g ^ 3) x = x) ∪
      (Finset.univ.filter fun x => (g ^ 5) x = x) := by
    intro x _
    rcases pow_three_or_five ho x with h | h <;> simp [h]
  have hc := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have h3 := hfix 3 (Or.inl rfl)
  have h5 := hfix 5 (Or.inr rfl)
  omega

theorem m12_no_fifteen_0 :
    (CFSG.Sporadic.Schreier.orderTables CFSG.Sporadic.Schreier.m12Certificate 15).length = 0 := by
  have h := card_orderOf_eq (by norm_num) m12Certificate m12Certificate_check (m := 15)
    (by norm_num)
  rw [m12Certificate_originalSubgroup] at h
  rw [← h, Nat.card_eq_zero]
  exact Or.inl ⟨fun x => orderOf_ne_fifteen x.1.2 (by rw [Subgroup.orderOf_coe]; exact x.2)⟩

end CertificateChecks.Batch15068

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15068 : (CFSG.Sporadic.Schreier.orderTables CFSG.Sporadic.Schreier.m12Certificate 15).length = 0 := CertificateChecks.Batch15068.m12_no_fifteen_0

end Certificates
