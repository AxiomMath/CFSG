module

public import CFSG.LocalAnalysis.StandardType.GGTDModelLiftTwo
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Transfer

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem TypeA.inducedSub_eq_map_conj_of_lift (hψ : Function.Surjective ψ)
    (Λ : R →* MulAut L') (hΛmap : ∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹)
    {A : Subgroup (MulAut L')} (hAΛ : ∀ a ∈ A, ∃ e, Λ e = a) :
    TypeA.inducedSub ψ A = (A.comap Λ).map (MulAut.conj : R →* MulAut R) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
    obtain ⟨e, he⟩ := hAΛ a ha
    have hφeq : φ = MulAut.conj e := by
      ext r
      obtain ⟨l, rfl⟩ := hψ r
      rw [hφa, ← he, hΛmap]
      rfl
    refine ⟨e, ?_, hφeq.symm⟩
    change Λ e ∈ A
    rwa [he]
  · rintro ⟨e, he, rfl⟩
    exact TypeA.mem_inducedSub.mpr ⟨Λ e, he, fun l => (hΛmap e l).symm⟩

theorem ggTorusSelfCent_inducedSub_of_two [Finite L'] (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (h2 : IsPGroup 2 ψ.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut L')}
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A) :
    GGTorusSelfCent p (TypeA.inducedSub ψ A) := by
  intro r hr hrp
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hro : Nat.Coprime (orderOf r) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hrp) (Nat.coprime_two_right.mpr hpodd)
  obtain ⟨l, hl, hlo⟩ := CFSG.RankThree.PartOne.SRC.exists_lift_coprime ψ hψ Nat.prime_two hro
  have hlodd : Odd (orderOf l) := Nat.coprime_two_right.mp hlo
  have hlp : l ^ p = 1 := by
    have hk : l ^ p ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hl, hrp]
    refine eq_one_of_isPGroup_two_of_pow_odd h2 hlodd hk ?_
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hfix : ∀ a ∈ A, a l = l := by
    intro a ha
    obtain ⟨φ, hφ⟩ := hA a ha
    have hφE : φ ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hφ⟩
    refine eq_of_map_eq_of_pow_odd hker h2 hpodd ?_ ?_ hlp
    · rw [← hφ, hl, hr φ hφE]
    · rw [← map_pow, hlp, map_one]
  refine TypeA.mem_inducedSub.mpr ⟨MulAut.conj l, hsc l hfix hlp, fun l' => ?_⟩
  rw [← hl]
  simp only [MulAut.conj_apply, map_mul, map_inv]

variable (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
  (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
  (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))

theorem mulAutCongr_ggConjAut {g : L'}
    (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hg' : MulAut.conj (ψ g) ∈
      Subgroup.normalizer ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R))) :
    MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hA).symm
      (ggConjAut (TypeA.inducedSub ψ A) hg') = ggConjAut A hg := by
  ext a
  rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← inducedSubEquiv_ggConjAut hψ hker hperf hA rfl hg hg' a, MulEquiv.symm_apply_apply]

theorem map_ggAutomizer_inducedSub :
    (ggAutomizer (MulAut.conj : R →* MulAut R).range (TypeA.inducedSub ψ A)).map
        (MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hA).symm).toMonoidHom =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨c, ⟨r, rfl⟩, hcN, hfc⟩ := mem_ggAutomizer_iff.mp hf
    obtain ⟨g, rfl⟩ := hψ r
    have hg := inducedSub_conj_mem_normalizer hker hperf hA rfl hcN
    have hfe : f = ggConjAut (TypeA.inducedSub ψ A) hcN :=
      MulEquiv.ext fun b => Subtype.ext (hfc b)
    rw [hfe]
    change MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hA).symm
      (ggConjAut (TypeA.inducedSub ψ A) hcN) ∈ _
    rw [mulAutCongr_ggConjAut hψ hker hperf hA hg hcN]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨g, rfl⟩) hg
  · intro f hf
    obtain ⟨c, ⟨g, rfl⟩, hcN, hfc⟩ := mem_ggAutomizer_iff.mp hf
    have hg' := conj_mem_normalizer_inducedSub ψ hcN
    have hfe : f = ggConjAut A hcN := MulEquiv.ext fun b => Subtype.ext (hfc b)
    refine ⟨ggConjAut (TypeA.inducedSub ψ A) hg',
      ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨ψ g, rfl⟩) hg', ?_⟩
    rw [hfe]
    exact mulAutCongr_ggConjAut hψ hker hperf hA hcN hg'

end Transfer

end CFSG.StandardType

end
