module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.QTwo

theorem prime_dvd_card_mulAut_of_card_six {S : Type} [Group S] [Finite S] (hS : Nat.card S = 6)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ Nat.card (MulAut S)) : q = 2 ∨ q = 3 := by
  classical
  by_contra h
  simp only [not_or] at h
  obtain ⟨h2, h3⟩ := h
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hq5 : 5 ≤ q := by
    have h2q : 2 ≤ q := hq.two_le
    have h4 : q ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) hq
    omega
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' (G := MulAut S) q hd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hS]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 (by rw [hS]; norm_num)
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; omega
  have hScard : Fintype.card S = 6 := by rw [← Nat.card_eq_fintype_card]; exact hS
  have hcardT : Fintype.card {t : S // t ≠ 1} = 5 := by
    have hcompl := Fintype.card_subtype_compl (fun t : S => t = 1)
    have hone : Fintype.card {t : S // t = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨1, rfl⟩, fun y => Subtype.ext y.2⟩
    rw [hScard, hone] at hcompl
    simpa using hcompl
  have hGcard : Fintype.card (Subgroup.zpowers φ) = q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hφ]
  have hOrbit : ∀ s : S,
      Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s) = 1 ∨
        Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s) = q := by
    intro s
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Subgroup.zpowers φ) s
    have hdvd : Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s) ∣ q := by
      rw [← hGcard]
      exact ⟨_, hOS.symm⟩
    exact hq.eq_one_or_self_of_dvd _ hdvd
  have hfix : ∀ s : S, φ s = s := by
    intro s
    by_contra hsne
    have hs1 : s ≠ 1 := by intro h; exact hsne (by rw [h, map_one])
    have hOsub : MulAction.orbit (Subgroup.zpowers φ) s ⊆ {t : S | t ≠ 1} := by
      intro t ht
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ht
      rw [← hg]
      intro hgt
      have hgg : (↑g : MulAut S) s = 1 := by
        change g • s = 1
        exact hgt
      exact hs1 ((↑g : MulAut S).injective (by rw [hgg, map_one]))
    have hcard_le : Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s) ≤ 5 := by
      calc Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s)
          ≤ Fintype.card {t : S // t ≠ 1} :=
            Fintype.card_le_of_injective (Set.inclusion hOsub) (Set.inclusion_injective hOsub)
        _ = 5 := hcardT
    rcases hOrbit s with h1 | hqO
    ·
      let u : Subgroup.zpowers φ := ⟨φ, Subgroup.mem_zpowers φ⟩
      have hu : u • s ∈ MulAction.orbit (Subgroup.zpowers φ) s := MulAction.mem_orbit s u
      have hpair : (⟨u • s, hu⟩ : MulAction.orbit (Subgroup.zpowers φ) s) =
          (⟨s, MulAction.mem_orbit_self s⟩ : MulAction.orbit (Subgroup.zpowers φ) s) :=
        Fintype.card_le_one_iff.mp (le_of_eq h1) _ _
      exact hsne (by simpa [u] using congrArg Subtype.val hpair)
    ·
      have hq_eq5 : q = 5 := by omega
      have hcardEq : Fintype.card (MulAction.orbit (Subgroup.zpowers φ) s) =
          Fintype.card {t : S // t ≠ 1} := by rw [hqO, hq_eq5, hcardT]
      have hsurj : Function.Surjective (Set.inclusion hOsub) :=
        ((Fintype.bijective_iff_injective_and_card (Set.inclusion hOsub)).mpr
          ⟨Set.inclusion_injective hOsub, hcardEq⟩).2
      have hconst : ∀ t : {x : S // x ≠ 1}, orderOf (t : S) = orderOf s := by
        intro t
        obtain ⟨o, ho⟩ := hsurj t
        have htO : (t : S) ∈ MulAction.orbit (Subgroup.zpowers φ) s := by
          have : (o : S) = (t : S) := congrArg Subtype.val ho
          rw [← this]
          exact o.2
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp htO
        rw [← hg]
        change orderOf ((↑g : MulAut S) s) = orderOf s
        exact MulEquiv.orderOf_eq (↑g : MulAut S) s
      have hs2 : orderOf s = 2 := (hconst ⟨a, ha1⟩).symm.trans ha
      have hs3 : orderOf s = 3 := (hconst ⟨b, hb1⟩).symm.trans hb
      omega
  have hφ1 : φ = 1 := MulEquiv.ext (fun x => by simpa using hfix x)
  have hord1 : orderOf φ = 1 := by rw [hφ1, orderOf_one]
  exact hq.ne_one (hφ ▸ hord1)

end CFSG.StandardType.QTwo

end
