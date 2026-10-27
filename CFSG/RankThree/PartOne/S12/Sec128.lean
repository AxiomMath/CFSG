module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Sec128

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {d y : G}

theorem mem_normalizer_of_commutator_mem (hdE : d ∈ E)
    (h : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) :
    y ∈ Subgroup.normalizer (E : Set G) := by
  have hforward : ∀ e ∈ E, y * e * y⁻¹ ∈ E := fun e he => by
    have h1 : y * e * y⁻¹ * e⁻¹ ∈ E := Subgroup.zpowers_le.mpr hdE (h e he)
    simpa [mul_assoc] using E.mul_mem h1 he
  let f : E → E := fun e => ⟨y * e * y⁻¹, hforward e e.2⟩
  have hinj : Function.Injective f := fun e e' hee' => by
    apply Subtype.ext
    have := congrArg Subtype.val hee'
    simpa [f] using this
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => hforward e he, fun he => ?_⟩
  obtain ⟨e', he'⟩ := hsurj ⟨y * e * y⁻¹, he⟩
  have h2 : y * (e' : G) * y⁻¹ = y * e * y⁻¹ := congrArg Subtype.val he'
  have h3 : (e' : G) = e := by simpa using h2
  exact h3 ▸ e'.2

theorem torusHasTransvection_of_commutators {p : ℕ} [Fact p.Prime] (hE : IsElementaryAbelian p E)
    (hdE : d ∈ E) (hd1 : d ≠ 1) {a : G} (haE : a ∈ E) (hyd : y * d * y⁻¹ = d)
    (hya : y * a * y⁻¹ ≠ a) (h : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) :
    torusHasTransvection p E := by
  have hy : y ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_of_commutator_mem hdE h
  set φ : MulAut E := E.normalizerMonoidHom ⟨y, hy⟩ with hφ
  have hφapp : ∀ e : E, ((φ e : E) : G) = y * e * y⁻¹ := fun e => rfl
  set d' : E := ⟨d, hdE⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hd'p : orderOf d' = p := by
    have hpow : d' ^ p = 1 := Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p)
      (A := E) d hdE)
    exact orderOf_eq_prime hpow hd'1
  have hmoved : ∀ e : E, φ e * e⁻¹ ∈ Subgroup.zpowers d' := fun e => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h e e.2)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simpa [hφapp] using hk
  have hle : autMoved E φ ≤ Subgroup.zpowers d' :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨e, rfl⟩; exact hmoved e)
  have hne : φ ≠ 1 := fun h1 => hya (by
    have := congrArg (fun ψ : MulAut E => ((ψ ⟨a, haE⟩ : E) : G)) h1
    simpa [hφapp] using this)
  have hmovedne : autMoved E φ ≠ ⊥ := fun hb => hne (by
    ext e
    have hmem : φ e * e⁻¹ ∈ autMoved E φ := Subgroup.subset_closure ⟨e, rfl⟩
    rw [hb, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    simpa using congrArg Subtype.val hmem)
  have hcard : Nat.card (autMoved E φ) = p := by
    have hdvd : Nat.card (autMoved E φ) ∣ p := by
      rw [← hd'p, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hmovedne
    · exact h1
  have hfix : d' ∈ autFixed E φ := by
    show φ d' = d'
    exact Subtype.ext (by simpa [hφapp, hd'] using hyd)
  exact ⟨φ, MonoidHom.mem_range.mpr ⟨_, rfl⟩, hne, hcard,
    hle.trans (Subgroup.zpowers_le.mpr hfix)⟩

end Sec128

end CFSG.RankThree.PartOne
