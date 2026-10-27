module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusIndex
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusInclusion

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem twE6_torus_meet_gamma_dvd
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (Fr : L →+* L)
    (halg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c) (D : LangDatum TwistTag.E6.tag L)
    (hFr : ∀ c, Fr c = c ^ 2) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) :
    Nat.card (D.torus.subgroupOf D.Γ) * 3 ∣ Nat.card D.torus := by
  obtain ⟨w, hw⟩ := D.n_weyl
  obtain ⟨ω, -, hωw⟩ := (coxeterSystem Tag.E6).exists_reduced_word w
  have hn : D.n = canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [hw, ← hωw]
    rfl
  obtain ⟨-, hcard⟩ := twE6_image_le_torus_index Fr hFr D hΦ ω hn
  have hle := twE6_torus_gamma_le_image Fr hFr halg D hΦ ω hn
  have hsub : Nat.card (D.torus.subgroupOf D.Γ) = Nat.card ↥(D.torus ⊓ D.Γ) := by
    rw [← Subgroup.card_map_of_injective D.Γ.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hdvd : Nat.card ↥(D.torus ⊓ D.Γ) ∣ Nat.card (twE6Image Fr ω) :=
    Subgroup.card_dvd_of_le hle
  rw [hsub, ← hcard]
  exact Nat.mul_dvd_mul_right hdvd 3

end CFSG.StandardType.TwE6Tori

end
