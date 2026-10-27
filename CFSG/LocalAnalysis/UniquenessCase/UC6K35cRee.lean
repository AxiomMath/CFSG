module

public import CFSG.LieType.SeitzGeneration.ExcReeG2Rank
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem card_lt_sq_of_lieModel_twistedG2 {L : Type} [Group L] [Finite L] {n : ℕ}
    (hm : LieModel L .twistedG2 0 3 n) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {F : Subgroup L}
    (hF : IsElemAbelian p F) : Nat.card F < p ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hF.isPGroup hcon
  obtain ⟨-, hrt⟩ := hm.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, ⟨a', ha', hfa'⟩, hiso⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier L 3 n hrt
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hrt
  have ha : 1 ≤ a := by omega
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X CFSG.LieType.Ree.ReeTag.G2.prime :=
    charP_of_card_eq_prime_pow (p := 3) (f := n) (by rw [← Nat.card_eq_fintype_card, hXcard])
  obtain ⟨E⟩ := hiso a X hfa hXcard ⟨e2⟩
  have hX : Nat.card X = 3 ^ (2 * a + 1) := by rw [← hfa]; exact hXcard
  have hp3 : 3 < p := by omega
  have hF₀ : IsElemAbelian p (F'.map F.subtype) := (hF.mono (Subgroup.map_subtype_le F'))
  have hF₁ : IsElemAbelian p ((F'.map F.subtype).map E.toMonoidHom) := hF₀.map E.toMonoidHom
  have hF₂ : IsElemAbelian p (((F'.map F.subtype).map E.toMonoidHom).map
      (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype) := hF₁.map _
  refine CFSG.LieType.SeitzGeneration.no_plane_reeGamma_G2 ha hX hp hp3
    (Subgroup.map_subtype_le _) hF₂.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype_injective,
    Subgroup.card_map_of_injective E.injective,
    Subgroup.card_map_of_injective F.subtype_injective, hF']

theorem false_of_lieModel_twistedG2_of_dvd {L : Type} [Group L] [Finite L] {n : ℕ}
    (hm : LieModel L .twistedG2 0 3 n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 3 ^ n + 3 ^ ((n + 1) / 2) + 1 ∨ p ∣ 3 ^ n - 3 ^ ((n + 1) / 2) + 1)
    {E : Subgroup L} (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : False := by
  have hn1 : 1 ≤ n := by
    obtain ⟨-, hrt⟩ := hm.reeTitsModel (by simp [reeTitsTags])
    obtain ⟨-, -, -, ⟨a', ha', hfa'⟩, -⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier L 3 n hrt
    omega
  have h3n : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
  have h3k : 3 ∣ 3 ^ ((n + 1) / 2) := dvd_pow_self 3 (by omega)
  have hp3 : p ≠ 3 := by
    rintro rfl
    rcases hdvd with h | h
    · have := (Nat.dvd_add_right (h3n.add h3k)).1 h
      omega
    · have h' : 3 ∣ 3 ^ n - 3 ^ ((n + 1) / 2) := Nat.dvd_sub h3n h3k
      have := (Nat.dvd_add_right h').1 h
      omega
  have h5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p <;> simp_all (config := {decide := true})
    · exact h
  have := card_lt_sq_of_lieModel_twistedG2 hm hp h5 hE
  omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
