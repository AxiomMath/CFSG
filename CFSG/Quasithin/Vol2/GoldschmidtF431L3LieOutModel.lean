module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutHyp
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3OutOrder

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

theorem autStab_transport {D P : Type} [Group D] [Group P] (E : D ≃* P) {P' : Subgroup D}
    {r : Subgroup P} (hP : P'.map E.toMonoidHom = Subgroup.normalizer (r : Set P))
    (hcore : pCoreOf 2 (Subgroup.normalizer (r : Set P)) = r) {φ : MulAut D}
    (hφ : φ ∈ autStab P') : ∀ p, p ∈ r ↔ (MulAut.congr E φ) p ∈ r := by
  set S : Subgroup D := r.map E.symm.toMonoidHom with hS
  have hnS : (Subgroup.normalizer (r : Set P)).map E.symm.toMonoidHom =
      Subgroup.normalizer (S : Set D) := by
    ext g
    rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E.symm r g]
  have hPS : P' = Subgroup.normalizer (S : Set D) := by
    rw [← hnS, ← hP, Subgroup.map_map]
    ext g
    simp
  have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
    rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hcore]
  have h1 := (mem_autStab_iff_of_normalizer hcoreS φ).mp (hPS ▸ hφ)
  intro p
  have h2 : p ∈ r ↔ E.symm p ∈ S := by
    rw [hS, Subgroup.mem_map_equiv]
    simp
  have h3 : (MulAut.congr E φ) p ∈ r ↔ φ (E.symm p) ∈ S := by
    rw [hS, Subgroup.mem_map_equiv]
    simp [MulAut.congr_apply]
  rw [h2, h3]
  exact h1 _

end CFSG.Quasithin.H13.F431.L3

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Borel252 CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3

theorem f431L3OutLie (f : ℕ) : F431L3OutLie f := by
  intro hf D _ hD A heven
  obtain ⟨F, hFf, hFfin, hFchar, E, hFcard, hP⟩ := l3Amalgam_borel hD A
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  obtain ⟨R₁, R₂, s₁, s₂, hdat, hRv, h1, h2⟩ : ∃ (R₁ R₂ : Subgroup (projectiveSL 3 F))
      (s₁ s₂ : projectiveSL 3 F), L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      ((R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) ∧
      A.P1.map E.toMonoidHom = Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)) ∧
      A.P2.map E.toMonoidHom = Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, _, _, hdata, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨_, _, _, _, hdata.swap, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  have hfinD : Finite D := Finite.of_injective E E.injective
  have hfinX : Finite (projectiveSL 3 F) := Finite.of_equiv D E.toEquiv
  have hfinAut : Finite (MulAut D) := finite_mulAut_of_finite
  have hgen := f431Generation_psl3 f D hD A
  have hK : ∀ d : D, (MulAut.conj d : MulAut D) ∈ A.K := fun d => hgen ⟨d, rfl⟩
  have hcen := (f431ModelFacts_psl3 f D hD).2
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdc : d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut D => φ g) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen] at hdc
    exact Subgroup.mem_bot.mp hdc
  set ΦD : D →* ↥A.K := (MulAut.conj : D →* MulAut D).codRestrict A.K hK with hΦD
  set Φ : projectiveSL 3 F →* ↥A.K := ΦD.comp E.symm.toMonoidHom with hΦ
  have hΦD_inj : Function.Injective ΦD := fun a b h => hinj (congrArg Subtype.val h)
  have hΦinj : Function.Injective Φ := hΦD_inj.comp E.symm.injective
  have hrange : Φ.range = ΦD.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨E d, by simp [hΦ]⟩
  have hnorm : Φ.range.Normal := by
    rw [hrange]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨d, rfl⟩ := hn
    exact ⟨(g : MulAut D) d, (codRestrict_conj_conj hK g d).symm⟩
  have hindex : ¬ Odd Φ.range.index := by
    have hcard := Subgroup.card_mul_index Φ.range
    have hrc : Nat.card Φ.range = Nat.card D := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
      exact Nat.card_congr E.symm.toEquiv
    rw [hrc] at hcard
    have hpos : 0 < Nat.card D := Nat.card_pos
    have : Φ.range.index = Nat.card ↥A.K / Nat.card D := by
      rw [← hcard, Nat.mul_div_cancel_left _ hpos]
    rw [this]
    exact heven
  have key : ∀ (P : Subgroup D) (r : Subgroup (projectiveSL 3 F)) (N' : Subgroup ↥A.K),
      P.map E.toMonoidHom = Subgroup.normalizer (r : Set (projectiveSL 3 F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (projectiveSL 3 F))) = r →
      (∀ x : ↥A.K, x ∈ N' ↔ (x : MulAut D) ∈ autStab P) →
      N' = Subgroup.normalizer ((r.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    intro P r N' hP hcore hN'
    set S : Subgroup D := r.map E.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (projectiveSL 3 F))).map E.symm.toMonoidHom =
        Subgroup.normalizer (S : Set D) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E.symm r g]
    have hPS : P = Subgroup.normalizer (S : Set D) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
      rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hcore]
    have hrS : r.map Φ = S.map ΦD := by
      rw [hS, Subgroup.map_map]
    ext x
    rw [hN' x, hrS, mem_normalizer_map_codRestrict_iff hK hinj S x, hPS,
      mem_autStab_iff_of_normalizer hcoreS]
  have hKM : ∀ x : ↥A.K, (x : MulAut D) ∈ A.Mbar := fun x => (sup_le inf_le_left inf_le_left :
    A.K ≤ A.Mbar) x.2
  have hN1 : A.Mb1 = Subgroup.normalizer ((R₁.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    refine key A.P1 R₁ A.Mb1 h1 hdat.borel.core₁ ?_
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  have hN2 : A.Mb2 = Subgroup.normalizer ((R₂.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    refine key A.P2 R₂ A.Mb2 h2 hdat.borel.core₂ ?_
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  set ρ : ↥A.K →* MulAut (projectiveSL 3 F) :=
    (MulAut.congr E).toMonoidHom.comp A.K.subtype with hρ
  have hρinj : Function.Injective ρ := (MulAut.congr E).injective.comp A.K.subtype_injective
  have hΦρ : ∀ (h : ↥A.K) (p : projectiveSL 3 F), Φ (ρ h p) = h * Φ p * h⁻¹ := by
    intro h p
    show ΦD (E.symm ((MulAut.congr E (h : MulAut D)) p)) = h * ΦD (E.symm p) * h⁻¹
    rw [codRestrict_conj_conj hK h (E.symm p)]
    congr 1
    simp [MulAut.congr_apply]
  have hKle : A.K ≤ (semilinearAutGroup 3 F).comap (MulAut.congr E).toMonoidHom := by
    show A.N1 ⊔ A.N2 ≤ _
    refine sup_le ?_ ?_
    · intro φ hφ
      have hst := autStab_transport E h1 hdat.borel.core₁ hφ.2
      rw [Subgroup.mem_comap]
      rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
      · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
    · intro φ hφ
      have hst := autStab_transport E h2 hdat.borel.core₂ hφ.2
      rw [Subgroup.mem_comap]
      rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
      · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
  have hE : ∀ h : ↥A.K, ρ h ∈ semilinearAutGroup 3 F := fun h => hKle h.2
  have hO := P3.l3OutHyp_of_action hf hFcard ρ hρinj Φ hΦinj hΦρ hE hRv
  have : Φ.range.Normal := hnorm
  exact exists_l3OutDatum_of_data Φ hΦinj hindex hdat hO A.Mb1 A.Mb2 hN1 hN2


theorem f431Out_psl3 {f : ℕ} (hf : 2 ≤ f) : F431Out .PSL 3 f :=
  f431Out_PSL3_of_lie hf (f431L3OutLie f)

end CFSG.Quasithin.H13.F431
