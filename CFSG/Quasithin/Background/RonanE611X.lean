module

public import CFSG.Quasithin.Background.RonanE611Lift
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_eq_of_surj {K X : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hXK : X ≤ K) (hsurj : ∀ a ∈ (convHom hV K hK).range, ∃ x : ↥K, (x : G) ∈ X ∧
      convHom hV K hK x = a) : autI hV X = autI hV K := by
  refine le_antisymm (autI_mono hV hXK) ?_
  intro a ha
  rw [← range_convHom hV K hK] at ha
  obtain ⟨x, hxX, hx⟩ := hsurj a ha
  rw [← hx]
  have := convI_mem_autI hV (K := X) hxX (hK x.2)
  exact this

theorem exists_X_of_coprime {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hcyc : IsCyclic ↥(autI hV K))
    (hcop : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(autI hV K) →
      ¬ p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G))) :
    ∃ X : Subgroup G, X ≤ K ∧ IsCyclic ↥X ∧ Nat.card ↥X = Nat.card ↥(autI hV K) ∧
      autI hV X = autI hV K := by
  have hrange := range_convHom hV K hK
  have hker := ker_convHom hV K hK
  have hcyc' : IsCyclic ↥(convHom hV K hK).range := by rw [hrange]; exact hcyc
  have hcard1 : Nat.card ↥(convHom hV K hK).range = Nat.card ↥(autI hV K) := by rw [hrange]
  have hcard2 : Nat.card ↥(convHom hV K hK).ker = Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcop' : Nat.Coprime (Nat.card ↥(convHom hV K hK).ker) (Nat.card ↥(convHom hV K hK).range) := by
    rw [hcard1, hcard2]
    refine Nat.coprime_of_dvd (fun p hp hpd => ?_)
    intro hpd'
    exact hcop p hp hpd' hpd
  obtain ⟨X, hXK, hXc, hXcard, hXsurj⟩ := exists_complement_of_coprime (convHom hV K hK) hcyc' hcop'
  exact ⟨X, hXK, hXc, hXcard.trans hcard1, autI_eq_of_surj hV hK hXK hXsurj⟩

theorem exists_X_of_exponent {B K : Subgroup G} (hBK : B ≤ K)
    (hK : K ≤ Subgroup.normalizer (V : Set G)) (hcyc : IsCyclic ↥(autI hV K))
    (hodd : Odd (Nat.card ↥(autI hV K))) (hautB : autI hV B = autI hV K)
    (hexp : ∀ g ∈ B, ∃ k : ℕ, (g ^ Nat.card ↥(autI hV K)) ^ (2 ^ k) = 1) :
    ∃ X : Subgroup G, X ≤ B ∧ IsCyclic ↥X ∧ Nat.card ↥X = Nat.card ↥(autI hV K) ∧
      autI hV X = autI hV K := by
  have hB : B ≤ Subgroup.normalizer (V : Set G) := hBK.trans hK
  have hrange := range_convHom hV B hB
  have hrange' : (convHom hV B hB).range = autI hV K := by rw [hrange, hautB]
  have hcyc' : IsCyclic ↥(convHom hV B hB).range := by rw [hrange']; exact hcyc
  have hcard1 : Nat.card ↥(convHom hV B hB).range = Nat.card ↥(autI hV K) := by rw [hrange']
  have hodd' : Odd (Nat.card ↥(convHom hV B hB).range) := by rw [hcard1]; exact hodd
  have hexp' : ∀ g : ↥B, ∃ k : ℕ,
      (g ^ Nat.card ↥(convHom hV B hB).range) ^ (2 ^ k) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := hexp g g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [hcard1]
    simpa using hk
  obtain ⟨X, hXB, hXc, hXcard, hXsurj⟩ :=
    exists_cyclic_of_exponent (convHom hV B hB) hcyc' hodd' hexp'
  refine ⟨X, hXB, hXc, hXcard.trans hcard1, ?_⟩
  rw [← hautB]
  exact autI_eq_of_surj hV hB hXB hXsurj

end CFSG.Quasithin.RonanE611
