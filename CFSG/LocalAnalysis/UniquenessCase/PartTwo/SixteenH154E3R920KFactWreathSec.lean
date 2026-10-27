module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.GH74.Generic.BProg.B2.T4ElimE8Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem exists_section_of_isL2_three {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : IsL2 (Bar2 X) 3) :
    ∃ (T : Subgroup Q) (E : Type) (_ : Group E) (_ : Finite E) (π : ↥T →* E) (σ : ↥T ≃* ↥T)
      (f : E ≃* E), IsPGroup 2 ↥T ∧ Function.Surjective π ∧ (∀ e : E, e * e = 1) ∧
        Nat.card E = 8 ∧ (∀ t, π (σ t) = f (π t)) ∧
        ∀ F : Subgroup E, (∀ e ∈ F, f e ∈ F) → F = ⊥ ∨ F = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, hFfield, hFfin, hFcard, -, ⟨eBar⟩⟩ := uc22p22g_isL2_psl hX
  letI : Field F := hFfield
  letI : Finite F := hFfin
  let Gp : Type := CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F
  let P : Sylow 2 Gp := Classical.choice Sylow.nonempty
  let S : Sylow 2 (Bar2 X) :=
    Sylow.mapSurjective (f := eBar.symm.toMonoidHom) eBar.symm.surjective P
  have hScoe : (S : Subgroup (Bar2 X)) =
      (P : Subgroup Gp).map
        eBar.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (P := P) (f := eBar.symm.toMonoidHom) eBar.symm.surjective
  have hPel : IsElementaryAbelian 2 ↥(P : Subgroup Gp) :=
    (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_sylow_elementary_card 3 hFcard P).1
  have hPcard : Nat.card ↥(P : Subgroup Gp) = 8 := by
    have h := (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_sylow_elementary_card
      3 hFcard P).2
    rw [hFcard] at h
    norm_num at h
    exact h
  have hPnorm : Nat.card ↥(Subgroup.normalizer (P : Set Gp)) = 56 := by
    have h := CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_sylow_normalizer_card
      3 hFcard P
    rw [h, hFcard]
    norm_num
  have hSel : IsElementaryAbelian 2 ↥(S : Subgroup (Bar2 X)) := by
    haveI := hPel
    rw [hScoe]
    exact IsElementaryAbelian.map eBar.symm.toMonoidHom
  have hScard : Nat.card ↥(S : Subgroup (Bar2 X)) = 8 := by
    rw [hScoe, Subgroup.card_map_of_injective eBar.symm.injective]
    exact hPcard
  have hNcard : Nat.card ↥(Subgroup.normalizer
      ((S : Subgroup (Bar2 X)) : Set (Bar2 X))) = 56 := by
    rw [hScoe, CFSG.ShultStronglyClosedTI.TwoCoreGrowth.normalizer_card_map_equiv
      ((P : Subgroup Gp)) eBar.symm]
    exact hPnorm
  have hPcent : Subgroup.centralizer ((P : Subgroup Gp) : Set Gp) = (P : Subgroup Gp) := by
    obtain ⟨u, huP, hu1⟩ : ∃ u ∈ (P : Subgroup Gp), u ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one (P : Subgroup Gp) with hbot | h
      · exfalso
        rw [hbot] at hPcard
        simp at hPcard
      · exact h
    haveI := hPel
    refine le_antisymm ?_ (Subgroup.le_centralizer (P : Subgroup Gp))
    intro g hg
    rw [← CFSG.ShultStronglyClosedTI.LinearModel.sylow_centralizer_eq hFcard P huP hu1]
    exact Subgroup.centralizer_le (by rintro y rfl; exact huP) hg
  have hScent : Subgroup.centralizer ((S : Subgroup (Bar2 X)) : Set (Bar2 X)) =
      (S : Subgroup (Bar2 X)) := by
    haveI := hSel
    refine le_antisymm ?_ (Subgroup.le_centralizer (S : Subgroup (Bar2 X)))
    intro g hg
    have hgP : eBar g ∈ (P : Subgroup Gp) := by
      have hmem : eBar g ∈ Subgroup.centralizer ((P : Subgroup Gp) : Set Gp) := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hsS : eBar.symm p ∈ (S : Subgroup (Bar2 X)) := by
          rw [hScoe]
          exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
        have hcomm : eBar.symm p * g = g * eBar.symm p :=
          (Subgroup.mem_centralizer_iff.mp hg) (eBar.symm p) hsS
        calc p * eBar g = eBar (eBar.symm p) * eBar g := by rw [MulEquiv.apply_symm_apply]
          _ = eBar (eBar.symm p * g) := by rw [map_mul]
          _ = eBar (g * eBar.symm p) := by rw [hcomm]
          _ = eBar g * eBar (eBar.symm p) := by rw [map_mul]
          _ = eBar g * p := by rw [MulEquiv.apply_symm_apply]
      rwa [hPcent] at hmem
    rw [hScoe]
    exact Subgroup.mem_map.mpr ⟨eBar g, hgP, by simp⟩
  have h7dvd : 7 ∣ Nat.card ↥(Subgroup.normalizer
      ((S : Subgroup (Bar2 X)) : Set (Bar2 X))) := by
    rw [hNcard]
    norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer ((S : Subgroup (Bar2 X)) : Set (Bar2 X)))) 7 h7dvd
  let f : ↥(S : Subgroup (Bar2 X)) ≃* ↥(S : Subgroup (Bar2 X)) :=
    Subgroup.normalizerMonoidHom (S : Subgroup (Bar2 X)) y
  have hf7 : f ^ 7 = 1 := by
    change (Subgroup.normalizerMonoidHom (S : Subgroup (Bar2 X)) y) ^ 7 = 1
    rw [← map_pow, show y ^ 7 = 1 from by rw [← hy7]; exact pow_orderOf_eq_one y,
      map_one]
  have hf_ne : f ≠ 1 := by
    intro hf1
    have hyC : (y : Bar2 X) ∈
        Subgroup.centralizer ((S : Subgroup (Bar2 X)) : Set (Bar2 X)) := by
      have hyker : y ∈ (Subgroup.normalizerMonoidHom (S : Subgroup (Bar2 X))).ker := by
        rw [MonoidHom.mem_ker]
        exact hf1
      rw [Subgroup.normalizerMonoidHom_ker] at hyker
      exact Subgroup.mem_subgroupOf.mp hyker
    have hyS : (y : Bar2 X) ∈ (S : Subgroup (Bar2 X)) :=
      (congrArg (fun H : Subgroup (Bar2 X) => (y : Bar2 X) ∈ H) hScent).mp hyC
    have hyG : orderOf (y : Bar2 X) = 7 := (Subgroup.orderOf_coe y).trans hy7
    have h7 : 7 ∣ Nat.card ↥(S : Subgroup (Bar2 X)) := by
      have h := Subgroup.orderOf_dvd_natCard (S : Subgroup (Bar2 X)) hyS
      rwa [hyG] at h
    rw [hScard] at h7
    omega
  have hford : orderOf f = 7 := by
    have hdvd : orderOf f ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hf7
    rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd (orderOf f) hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) hf_ne
    · exact h7
  have hirr : ∀ F' : Subgroup ↥(S : Subgroup (Bar2 X)),
      (∀ e ∈ F', f e ∈ F') → F' = ⊥ ∨ F' = ⊤ := by
    intro F' hF'
    rcases CFSG.GH74.Generic.BProg.B2.T4.T4ElimE8.inv_subgroup_card
      (R := ↥(S : Subgroup (Bar2 X))) hScard hford F' hF' with h1 | h8
    · exact Or.inl (Subgroup.eq_bot_of_card_eq F' h1)
    · exact Or.inr (Subgroup.eq_top_of_card_eq F' (by rw [h8, hScard]))
  let N : Subgroup ↥X := CFSG.pCore 2 ↥X
  let π₀ : ↥X →* Bar2 X := QuotientGroup.mk' N
  let T₀ : Subgroup ↥X := (S : Subgroup (Bar2 X)).comap π₀
  let T : Subgroup Q := T₀.map X.subtype
  let eT : ↥T₀ ≃* ↥T := Subgroup.equivMapOfInjective T₀ X.subtype X.subtype_injective
  let φ : ↥T₀ →* ↥(S : Subgroup (Bar2 X)) :=
    (π₀.comp T₀.subtype).codRestrict _ (fun t => Subgroup.mem_comap.mp t.2)
  let π : ↥T →* ↥(S : Subgroup (Bar2 X)) := φ.comp eT.symm.toMonoidHom
  have hT0 : IsPGroup 2 ↥T₀ := by
    refine IsPGroup.comap_of_ker_isPGroup (p := 2)
      (H := (S : Subgroup (Bar2 X))) S.isPGroup' π₀ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hT : IsPGroup 2 ↥T := IsPGroup.map hT0 X.subtype
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨x', hx'⟩ := QuotientGroup.mk'_surjective N (e : Bar2 X)
    refine ⟨⟨x', Subgroup.mem_comap.mpr (by rw [hx']; exact e.2)⟩, ?_⟩
    exact Subtype.ext hx'
  have hπsurj : Function.Surjective π := hφsurj.comp eT.symm.surjective
  have hpow : ∀ e : ↥(S : Subgroup (Bar2 X)), e * e = 1 := by
    intro e
    have h : e ^ 2 = 1 := by
      haveI := hSel
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 ↥(S : Subgroup (Bar2 X))) e
    simpa [pow_two] using h
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (y : Bar2 X)
  have hxT₀ : x ∈ Subgroup.normalizer (T₀ : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hx]
    exact Subgroup.mem_normalizer_iff.mp y.2 (π₀ t)
  let σ₀ : ↥T₀ ≃* ↥T₀ := Subgroup.normalizerMonoidHom T₀ ⟨x, hxT₀⟩
  let σ : ↥T ≃* ↥T := eT.symm.trans (σ₀.trans eT)
  have hσf : ∀ t : ↥T, π (σ t) = f (π t) := by
    intro t
    obtain ⟨t₀, rfl⟩ := eT.surjective t
    have h1 : π (eT t₀) = φ t₀ := by simp [π]
    have h2 : σ (eT t₀) = eT (σ₀ t₀) := by simp [σ]
    rw [h2, h1]
    have h3 : π (eT (σ₀ t₀)) = φ (σ₀ t₀) := by simp [π]
    rw [h3]
    apply Subtype.ext
    have hσ₀val : ((σ₀ t₀ : ↥T₀) : ↥X) = x * (t₀ : ↥X) * x⁻¹ := rfl
    change π₀ ((σ₀ t₀ : ↥T₀) : ↥X) =
      (y : Bar2 X) * (φ t₀ : Bar2 X) * (y : Bar2 X)⁻¹
    rw [hσ₀val, map_mul, map_mul, map_inv, hx]
    rfl
  refine ⟨T, ↥(S : Subgroup (Bar2 X)), inferInstance, inferInstance, π, σ, f,
    hT, hπsurj, hpow, hScard, hσf, hirr⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
