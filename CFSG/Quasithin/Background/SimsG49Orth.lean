module

public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.Quasithin.Background.SimsG4Orth
import CFSG.Quasithin.Background.SimsG49Inv
import CFSG.Quasithin.Background.SimsG49OrthCore
import CFSG.Quasithin.Background.SimsG49Pre

public section

namespace CFSG.Quasithin.SimsG4

open OrthA

namespace G49

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {Q : QuadraticForm F V}

private theorem reflK_mem_transvSet (h : OrthHyp B G₀ Q)
    (hprimG : ¬ IsImprimitiveOnV (transvGen G₀)) {r : V} (hrI : r ∈ centreForm Q G₀)
    (hr : Q r = 1) :
    ∃ hmem : reflK Q r ∈ transvSet G₀,
      resHom (F₀ := centreField Q G₀) h.mapsTo ⟨reflK Q r, hmem.1⟩ =
        reflK (formQ Q G₀) ⟨r, hrI⟩ := by
  have hndQ : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0 := fun x hx =>
    h.nondeg x fun y => by rw [← h.polar_eq]; exact hx y
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hr
    exact zero_ne_one hr
  have hmemG : reflK Q r ∈ G₀ := by
    refine (h.mem_iff orthIdent_holds hprimG _).mpr
      ⟨fun x y => ?_, fun x hx => ?_, reflK_isometry Q hr⟩
    · rw [← h.polar_eq, ← h.polar_eq]
      exact polar_map_of_isometry Q (reflK_isometry Q hr) x y
    · rw [reflK_apply]
      refine Submodule.add_mem _ hx ?_
      have hsm := Submodule.smul_mem (centreForm Q G₀)
        (⟨QuadraticMap.polar Q x r, polar_mem_centreField hx hrI⟩ : centreField Q G₀) hrI
      rwa [Subfield.smul_def] at hsm
  refine ⟨⟨hmemG, isTransv_reflK Q hndQ hr0⟩, LinearEquiv.ext fun x => Subtype.ext ?_⟩
  rw [coe_resHom_apply, reflK_apply, reflK_apply]
  simp only [Submodule.coe_add, Submodule.coe_smul, Subfield.smul_def, coe_polar_formQ]

theorem orth_case (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B)
    (hirr : IsIrredOnV G₀) (hD : (transvSet G₀).Nonempty) (hirrG : IsIrredOnV (transvGen G₀))
    (hprimG : ¬ IsImprimitiveOnV (transvGen G₀)) (Q : QuadraticForm F V)
    (hQB : ∀ x y, QuadraticMap.polar Q x y = B x y) (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) :
    (IsSimpleGroup ↥(fStarOf (transvGen G₀)) ∧
        (∃ x ∈ fStarOf (transvGen G₀), ∃ y ∈ fStarOf (transvGen G₀), x * y ≠ y * x) ∧
        (∃ i ∈ invSet B G₀, i ∈ fStarOf (transvGen G₀)) ∧
        IsIrredOnV (fStarOf (transvGen G₀))) ∨
      (∃ k : ℕ, 1 < k ∧ k ∣ n ∧
        Nonempty (↥(fStarOf (transvGen G₀)) ≃*
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) ×
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∧
        G41Case2AtExponent n k B G₀) := by
  have h : OrthHyp B G₀ Q := ⟨halt, hnd, hdim, hSp, hD, hirrG, hQB, hQ⟩
  have hT : transvGen G₀ = G₀ := h.transvGen_eq orthIdent_holds hprimG
  have hprim : ¬ IsImprimitiveOnV G₀ := hT ▸ hprimG
  haveI : Finite V := h.finite
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) DFunLike.coe_injective
  rw [hT]
  have hdim' := h.finrank_form'
  have hnd' := h.nondeg_formQ
  have hf : Function.Injective (resHom (F₀ := centreField Q G₀) h.mapsTo) :=
    resHom_injective h.span_form h.mapsTo
  have hrange : (resHom (F₀ := centreField Q G₀) h.mapsTo).range =
      TauCeti.QuadraticMap.orthogonalGroup (formQ Q G₀) :=
    (h.range_resHom orthIdent_holds hprimG).trans (Subgroup.ext fun _ =>
      mem_orthGroup.trans TauCeti.QuadraticMap.mem_orthogonalGroup_iff.symm)
  by_cases hplus : ∃ U : Submodule (centreField Q G₀) (centreForm Q G₀),
      Module.finrank (centreField Q G₀) U = 2 ∧ ∀ u ∈ U, formQ Q G₀ u = 0
  ·
    right
    have h4 := four_le_card_of_orthPlus (formQ Q G₀) hdim' hnd' hplus (formR Q G₀) formQ_eq_one
      eq_top_of_polar_mem h.isIrredOnV_formQ (h.not_isImprimitiveOnV_formQ hprimG)
    obtain ⟨k, hk, hkn, hK⟩ := OrthA.exists_card_subfield hn (centreField Q G₀)
    have hk1 : 1 < k := by
      by_contra hk1
      have hk1' : k = 1 := by omega
      rw [hK, hk1'] at h4
      norm_num at h4
    obtain ⟨e⟩ := orth_plus_core (formQ Q G₀) hdim' hnd' hplus h4 _ hf hrange
    letI := Fintype.ofFinite (centreField Q G₀)
    letI := Fintype.ofFinite (GaloisField 2 k)
    have hcard : Fintype.card (centreField Q G₀) = Fintype.card (GaloisField 2 k) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, GaloisField.card 2 k hk.ne']
    obtain ⟨σ⟩ := nonempty_sl2_mulEquiv (FiniteField.ringEquivOfCardEq hcard)
    exact ⟨k, hk1, hkn, ⟨e.trans (σ.prodCongr σ)⟩,
      case2_at_of_orth orthIdent_holds n hn B halt hnd hdim G₀ hSp hD hirrG hprimG Q hQB hQ hK⟩
  ·
    left
    obtain ⟨N, hF, hNn, hNs, hnab, hprod, hcos⟩ := orth_minus_core (formQ Q G₀) hdim' hnd'
      (finrank_le_one_of_not_plus (formQ Q G₀) hdim' hplus) _ hf hrange
    rw [hF]
    obtain ⟨r, hr⟩ := h.centreSet_nonempty
    have hrI : r ∈ centreForm Q G₀ := Submodule.subset_span hr
    have hQr' : formQ Q G₀ ⟨r, hrI⟩ = 1 := formQ_eq_one _ hr
    obtain ⟨s, hQs, hsr, hind⟩ :=
      exists_orth_unit (formQ Q G₀) (by rw [hdim']; norm_num) hnd' hQr'
    have hQs' : Q (s : V) = 1 := by
      rw [← coe_formQ, hQs]
      rfl
    have hr0 : r ≠ 0 := by
      rintro rfl
      have h1 := hr.1
      rw [QuadraticMap.map_zero] at h1
      exact zero_ne_one h1
    have hs0 : (s : V) ≠ 0 := by
      intro h0
      rw [h0, QuadraticMap.map_zero] at hQs'
      exact zero_ne_one hQs'
    have hBrs : B r s = 0 := by
      have h1 := congrArg Subtype.val hsr
      rw [coe_polar_formQ] at h1
      rw [← hQB, QuadraticMap.polar_comm]
      exact h1
    obtain ⟨har, hfr⟩ := reflK_mem_transvSet h hprimG hrI hr.1
    obtain ⟨has, hfs⟩ := reflK_mem_transvSet h hprimG s.2 hQs'
    have hab : reflK Q r * reflK Q (s : V) = reflK Q (s : V) * reflK Q r :=
      (SimsG45.transv_commute_iff B halt hnd hr0 one_ne_zero one_ne_zero
        (fun v => by rw [reflK_apply, one_mul, hQB])
        (fun v => by rw [reflK_apply, one_mul, hQB])).mpr hBrs
    have hndQ : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0 := fun x hx =>
      hnd x fun y => by rw [← hQB]; exact hx y
    have hcen : commSpace (reflK Q r) ≠ commSpace (reflK Q (s : V)) := by
      rw [commSpace_reflK Q hndQ hr0, commSpace_reflK Q hndQ hs0]
      intro heq
      have hli₀ : LinearIndependent (centreField Q G₀) ![(s : V), r] := by
        have hmap := hind.map' (centreForm Q G₀).subtype (Submodule.ker_subtype _)
        convert hmap using 1
        ext i
        fin_cases i <;> rfl
      have hliV := linearIndependent_of_form halt hnd h.val h.span_form ![(s : V), r]
        (fun i => by fin_cases i; exacts [s.2, hrI]) hli₀
      obtain ⟨-, hne⟩ := linearIndependent_fin2.mp hliV
      have hsmem : (s : V) ∈ Submodule.span F {r} := by
        rw [heq]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsmem
      exact hne a (by simpa using ha)
    have hinv := mem_invSet_of_commuting B halt hnd har has hab hcen
    have habN := hprod _ _ har.1 has.1 ⟨r, hrI⟩ s hQr' hQs hfr hfs
    have hcosN := hcos _ har.1 ⟨r, hrI⟩ (fun h0 => hr0 (congrArg Subtype.val h0)) hfr
    exact ⟨hNs, hnab, ⟨_, hinv, habN⟩, irreducible_of_index_two hirr hprim hNn har.1 hcosN⟩

end G49

end CFSG.Quasithin.SimsG4
