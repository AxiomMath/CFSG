module

public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item18ResProof

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

variable {k : Type} [Field k]

theorem l34_centralizer_eq_of_mem (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) {x : projectiveSL 3 k} (hx : x ∈ E) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (projectiveSL 3 k)) = E := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hx₀1 : x₀ ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  obtain ⟨n, hn, hnx⟩ := exists_mem_normalizer_conj_eq hk hu hx₀ hx₀1
  have hxe : (MulAut.conj g).toMonoidHom x₀ = MulAut.conj (g * n) (aP u) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hnx]
    group
  rw [hxe, ← map_centralizer_singleton (MulAut.conj (g * n)) (aP u), centralizer_aP hk hu]
  have hnE : (eZero k).map (MulAut.conj n).toMonoidHom = eZero k :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [map_mul, show ((MulAut.conj g * MulAut.conj n : MulAut (projectiveSL 3 k)).toMonoidHom) =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj n).toMonoidHom from rfl, ← Subgroup.map_map,
    hnE]

theorem l34_eq_bot_of_le_normalizer (hk : Nat.card k = 4) {E Q : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) (hQ : IsPGroup 2 Q) (hEQ : E ≤ Subgroup.normalizer (Q : Set _)) :
    Q = ⊥ := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hE
  have hexp : ∀ x : E, x ^ 3 = 1 := by
    intro x
    have hx : (x : projectiveSL 3 k) ∈ (eZero k).map (MulAut.conj g).toMonoidHom := hg ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hyx, ← map_pow, pow_three_of_mem_eZero hk hy, map_one,
      Subgroup.coe_one]
  have hcop : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three E Q hexp (by rw [hE]; norm_num) hcop hEQ
  rw [hgen, eq_bot_iff]
  refine iSup₂_le fun x hx1 => ?_
  have hx1' : (x : projectiveSL 3 k) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rw [l34_centralizer_eq_of_mem hk hE x.2 hx1']
  intro y hy
  have hy2 : IsPGroup 2 (Q ⊓ E : Subgroup _) := hQ.to_le inf_le_left
  have hy3 : IsPGroup 3 (Q ⊓ E : Subgroup _) := by
    have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
    exact hE3.to_le inf_le_right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot : (Q ⊓ E : Subgroup _) = ⊥ := by
    obtain ⟨a, ha⟩ := hy2.exists_card_eq
    obtain ⟨b, hb⟩ := hy3.exists_card_eq
    have h1 : Nat.card (Q ⊓ E : Subgroup _) = 1 := by
      have h2 : 2 ^ a = 3 ^ b := ha.symm.trans hb
      have h3 : a = 0 := by
        by_contra hne
        have : 2 ∣ 3 ^ b := h2 ▸ dvd_pow_self 2 hne
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this) (by norm_num)
      rw [ha, h3, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [hbot] at hy
  exact hy

end CFSG.RankThree.PartTwo.Sec18.Item18ResProof
