module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6SylowSplit
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Open CFSG.RankThree.PartOne.KE

theorem ggWeylLaw_twistedE6_one
    {p f : ℕ} (hpq : p ∣ 2 ^ f - 1) (hp3 : 3 ≤ p) :
    GGWeylLaw .twistedE6 p f (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) 1 := by
  have h : ¬ p ∣ 2 ^ f + 1 := by
    intro hc
    have hpow : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsub : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by omega
    have h2 : p ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub hc hpq
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  intro u
  rw [eps_eq_one_iff p f |>.2 hpq, piB_twistedE6_of_not_dvd f h, one_smul, one_smul]
  rfl

theorem twE6LangPos_one_of_conj
    {f : ℕ} {E : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hE : E ≤ ggFixGp .twistedE6 f) {g : ModGL (langTag .twistedE6) GGL}
    (hg : g ∈ ggFixGp .twistedE6 f)
    (hsplit : ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup (langTag .twistedE6) GGL) :
    TwE6LangPos f E 1 g := by
  have hgΦ : ggPhi .twistedE6 f g = g := hg.2
  refine ⟨hg.1, ?_, ?_⟩
  · rw [canonicalRep_one, mul_one]
    exact hgΦ
  · rw [canonicalRep_one]
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    show g⁻¹ * x * (g⁻¹)⁻¹ ∈ twistedTorusOf 1 (ggPhi .twistedE6 f)
    rw [mem_twistedTorusOf]
    refine ⟨?_, ?_⟩
    · rw [inv_inv]
      exact hsplit x hx
    · have hxΦ : ggPhi .twistedE6 f x = x := (hE hx).2
      rw [one_mul, inv_one, mul_one, inv_inv]
      simp only [map_mul, map_inv, hgΦ, hxΦ]


theorem twE6TTSplit_holds :
    ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ∣ 2 ^ f - 1 →
      ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
        IsPGroup p ↥E → TwE6LawPos p f E := by
  intro f hf p hp hp5 hpq E hE hEp
  obtain ⟨g, hg, hsplit⟩ := twE6_pSubgroup_split hf hp hp5 hpq hE hEp
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), 1, g, twE6LangPos_one_of_conj hE hg hsplit,
    ggWeylLaw_twistedE6_one hpq (by omega)⟩

end CFSG.StandardType.LieKnownR2.ExcPos
