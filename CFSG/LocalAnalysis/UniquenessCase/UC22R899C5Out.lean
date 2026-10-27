module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C5Frat
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c5_exists_fixed {M T L : Subgroup G} (hT : IsSylowOf 2 T M)
    (hodd : Odd (conjSetOf M L).ncard) :
    ∃ K₀ ∈ conjSetOf M L, T ≤ normalizer (K₀ : Set G) := by
  classical
  have hTM : T ≤ M := hT.le
  let : SMul ↥T ↥(conjSetOf M L) := ⟨fun t K =>
    ⟨(K : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom, uc22r899_map_conj_mem (hTM t.2) K.2⟩⟩
  let : MulAction ↥T ↥(conjSetOf M L) :=
    { one_smul := fun K => Subtype.ext (by
        show (K : Subgroup G).map (MulAut.conj ((1 : ↥T) : G)).toMonoidHom = K
        ext x
        simp)
      mul_smul := fun a b K => Subtype.ext (by
        show (K : Subgroup G).map (MulAut.conj ((a * b : ↥T) : G)).toMonoidHom =
          ((K : Subgroup G).map (MulAut.conj (b : G)).toMonoidHom).map
            (MulAut.conj (a : G)).toMonoidHom
        rw [uc22p22d_map_conj_map_conj]
        rfl) }
  have hcard : ¬ 2 ∣ Nat.card ↥(conjSetOf M L) := by
    rw [Nat.card_coe_set_eq]
    exact hodd.not_two_dvd_nat
  obtain ⟨K, hK⟩ := hT.isPGroup.nonempty_fixed_point_of_prime_not_dvd_card _ hcard
  refine ⟨K, K.2, fun t ht => ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact congrArg Subtype.val (hK ⟨t, ht⟩)

theorem uc22r899c5_exists_mem_normalizer_T {D : Data G} {L K : Subgroup G}
    (hodd : Odd (conjSetOf D.M L).ncard) (hK : K ∈ conjSetOf D.M L) {n : ℕ}
    (hL2 : IsL2 (Bar2 K) n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (haM : a ∈ D.M)
    (haK : a ∈ normalizer (K : Set G)) (hap : a ^ p = 1)
    (hout : UC6S846.rhoL K ⟨a, haK⟩ ∉ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range) :
    ∃ x ∈ normalizer (D.T : Set G), orderOf x = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₀, hK₀, hTK₀⟩ := uc22r899c5_exists_fixed D.sylowM hodd
  obtain ⟨g, hgM, hg⟩ : ∃ g ∈ D.M, K₀.map (MulAut.conj g).toMonoidHom = K := by
    obtain ⟨a₀, ha₀, rfl⟩ := hK₀
    obtain ⟨b, hb, rfl⟩ := hK
    exact ⟨b * a₀⁻¹, D.M.mul_mem hb (D.M.inv_mem ha₀), by
      rw [uc22p22d_map_conj_map_conj, inv_mul_cancel_right]⟩
  set TK : Subgroup G := D.T.map (MulAut.conj g).toMonoidHom with hTKdef
  have hmem : ∀ y : G, y ∈ TK ↔ g⁻¹ * y * g ∈ D.T := fun y => by
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ht
    · intro h
      exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hTKN : TK ≤ normalizer (K : Set G) := by
    rw [← hg]
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom ⟨t, hTK₀ ht, rfl⟩
  have hTKM : TK ≤ D.M := by
    rintro _ ⟨t, ht, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hgM (D.sylowM.le ht)) (D.M.inv_mem hgM)
  have hTKs : IsSylowOf 2 TK D.M := isSylowOf_of_card hTKM (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact D.sylowM.card_eq)
  set H : Subgroup G := D.M ⊓ normalizer (K : Set G) with hH
  have hTKH : IsSylowOf 2 TK H := hTKs.of_le (le_inf hTKM hTKN) inf_le_left
  let ψ : ↥H →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K))).comp
      ((UC6S846.rhoL K).comp (Subgroup.inclusion inf_le_right))
  have ha : ψ ⟨a, haM, haK⟩ ≠ 1 := fun h => hout ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨x, -, hxN, hxo⟩ :=
    uc22r899c5_exists_orderOf_mem_normalizer (uc22p22g_outer_comm hL2) hp hp2 hTKH ψ
      ⟨haM, haK⟩ hap ha
  refine ⟨g⁻¹ * x * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 : h ∈ D.T ↔ g * h * g⁻¹ ∈ TK := by
      rw [hmem]
      simp [mul_assoc]
    have e2 : g * h * g⁻¹ ∈ TK ↔ x * (g * h * g⁻¹) * x⁻¹ ∈ TK :=
      (Subgroup.mem_normalizer_iff.1 hxN) _
    have e3 : x * (g * h * g⁻¹) * x⁻¹ ∈ TK ↔ g⁻¹ * x * g * h * (g⁻¹ * x * g)⁻¹ ∈ D.T := by
      rw [hmem]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    exact e1.trans (e2.trans e3)
  · have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
    simpa [MulAut.conj_apply] using this.trans hxo

end CFSG.LocalAnalysis.UniquenessCase.UC22
