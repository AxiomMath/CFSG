module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.Embedding

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem sector_hconj (w : WeylGroup ReeTag.F4.tag) (E : Subgroup (ModGL ReeTag.F4.tag L))
    (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (m : ℕ)
    (hE : Nat.card E = m ^ 2) {p : ℕ} (hp : p.Prime)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2) :
    ∃ g₀ : ModGL ReeTag.F4.tag L, g₀ ∈ adjointGroup ReeTag.F4.tag L ∧
      Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∧
      ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
        ∃ c : ReeTag.F4.reeGamma K a,
          g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  refine ⟨g₀, hg₀adj, hFg₀, fun x hx => ?_⟩
  set E' : Subgroup (ModGL ReeTag.F4.tag L) := E.map (MulAut.conj g₀).toMonoidHom with hE'
  have hE'θ : ∀ u ∈ E', ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = u := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hEF he)
    exact D.exists_theta_of_fixed hadj hfix
  let T : Subgroup (ReeTag.F4.reeGamma K a) := E'.comap (thetaGamma L a)
  have hTcard : Nat.card T = m ^ 2 := by
    rw [← hE]
    have e1 : Nat.card E = Nat.card E' :=
      Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj g₀).toMonoidHom
        (MulAut.conj g₀).injective).toEquiv
    rw [e1]
    refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨thetaGamma L a γ.1, γ.2⟩) ⟨?_, ?_⟩)
    · intro γ₁ γ₂ h12
      exact Subtype.ext (thetaGamma_injective L (congrArg Subtype.val h12))
    · rintro ⟨u, hu⟩
      obtain ⟨γ, rfl⟩ := hE'θ u hu
      exact ⟨⟨γ, hu⟩, rfl⟩
  have hTdvd : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ Nat.card T := by
    rw [hTcard]
    exact hpm
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card_dvd T hTdvd hx
  refine ⟨c, ?_⟩
  obtain ⟨e, he, hee⟩ := hc
  have h2 : g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ = e := by
    have : (MulAut.conj g₀) e = thetaGamma L a (c * x * c⁻¹) := hee
    rw [← this]
    simp [MulAut.conj_apply]
    group
  rw [h2]
  exact hEH he

end CFSG.RankThree.PartOne.KLR
