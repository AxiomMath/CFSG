module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Lang.E6Descent

section LangPos


theorem twE6LangPos_of_inv_mul {f : ℕ} {E : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hE : E ≤ ggFixGp .twistedE6 f) {w : WeylGroup (langTag .twistedE6)}
    {g : ModGL (langTag .twistedE6) GGL} (hg : g ∈ adjointGroup (langTag .twistedE6) GGL)
    (hgn : g⁻¹ * ggPhi .twistedE6 f g =
      canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
    (hT : ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup (langTag .twistedE6) GGL) :
    TwE6LangPos f E w g := by
  have hΦg : ggPhi .twistedE6 f g =
      g * canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w := by
    rw [← hgn, mul_inv_cancel_left]
  refine ⟨hg, hΦg, ?_⟩
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  show g⁻¹ * x * (g⁻¹)⁻¹ ∈
    twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
      (ggPhi .twistedE6 f)
  rw [mem_twistedTorusOf]
  refine ⟨?_, ?_⟩
  · rw [inv_inv]
    exact hT x hx
  · have hxΦ : ggPhi .twistedE6 f x = x := (hE hx).2
    simp only [map_mul, map_inv, hΦg, hxΦ]
    group

end LangPos

section Law


theorem ggWeylLaw_twE6W0 {p f : ℕ} (hp : 3 ≤ p) (hpf : p ∣ 2 ^ f + 1)
    (ht : GGExcFive .twistedE6) : GGWeylLaw .twistedE6 p f ht twE6W0 := by
  intro u
  have hndvd : ¬ p ∣ 2 ^ f - 1 := by
    intro h1
    have hpow : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsub : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by omega
    have h2 : p ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub hpf h1
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hε : eps p f = -1 := by
    unfold eps
    rw [if_neg hndvd]
  have hcongr : permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
      (1 : Equiv.Perm (Fin ((ggU (absTag .twistedE6) 6 f).D.rank)))) u = u := by
    rw [show (1 : Equiv.Perm (Fin ((ggU (absTag .twistedE6) 6 f).D.rank))) = Equiv.refl _ from
      Equiv.Perm.one_def]
    rw [Equiv.permCongr_refl]
    rfl
  rw [hε, piB_twistedE6_of_dvd f hpf, neg_one_smul, hcongr]
  have hγ2 : permLattice CFSG.RankThree.E6.e6Rho
      (permLattice CFSG.RankThree.E6.e6Rho u) = u := by
    ext j
    fin_cases j <;> rfl
  have h := twE6W0_smul (permLattice CFSG.RankThree.E6.e6Rho u)
  rw [hγ2] at h
  exact h

theorem twE6LawPos_of_lang {p f : ℕ} (hp : 3 ≤ p) (hpf : p ∣ 2 ^ f + 1)
    {E : Subgroup (ModGL (langTag .twistedE6) GGL)} (hE : E ≤ ggFixGp .twistedE6 f)
    {g : ModGL (langTag .twistedE6) GGL} (hg : g ∈ adjointGroup (langTag .twistedE6) GGL)
    (hgn : g⁻¹ * ggPhi .twistedE6 f g =
      canonicalRep (coxeterSystem (langTag .twistedE6)) GGL twE6W0)
    (hT : ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup (langTag .twistedE6) GGL) :
    TwE6LawPos p f E := by
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), twE6W0, g,
    twE6LangPos_of_inv_mul hE hg hgn hT, ?_⟩
  exact ggWeylLaw_twE6W0 hp hpf _

end Law

end CFSG.StandardType.LieKnownR2.ExcPos
