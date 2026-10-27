module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.F2Fixed
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec51_orth (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (h311bC : Stroth311bCommStatement)
    (h311bK : Stroth311bCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hmod : ∀ (R N P I L₁ L₂ A₁ A₂ : Subgroup G) (φ : ↥R →* GL ι K), φ.range = X →
      φ.ker = N.subgroupOf R → (∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) →
      (∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I) → (∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) →
      IsOppDecomp P I L₁ L₂ A₁ A₂ → L₁ ≤ R → L₂ ≤ R → ∀ {u u' : ι → K}, Q' u = 0 → Q' u' = 0 →
      polar Q' u u' ≠ 0 → (L₁.subgroupOf R).map φ = E.LomGL u →
      (L₂.subgroupOf R).map φ = E.LomGL u' →
      ∃ e : ℕ, Even e ∧ Nat.card P = Nat.card I * Nat.card K ^ e)
    (hsing : NatSingular hc t Q' X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (C L L' N R : Subgroup G), C = conjSubgroup r B → L = LB M Q B → L' = LB M Q C →
        N = hc.CN t → R = Rt M L t →
        (∀ x ∈ N, ∃ a ∈ L ⊓ N, ∃ b ∈ L' ⊓ N, x = a * b) ∧
        Nat.card ↥(L ⊓ L') = Nat.card Q * Nat.card Z ∧
        (∀ s ∈ R, ∀ x ∈ L ⊓ L', ⁅s, x⁆ ∈ Q) ∧
        IsOppDecomp N (L ⊓ L') L L' (L ⊓ N) (L' ⊓ N) := by
  intro r hr hplane C L L' N R hC hL hL' hN hR
  subst hC hL hL' hN hR
  have hcard : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hnotSL : ¬ SLNat hc t := fun hsl => not_slNat_of_orth hc hsl hK E hQ hnat (by omega)
  obtain ⟨T, hT⟩ := exists_centLB hc t
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  obtain ⟨u, hQu, hu0, hBiff, -, hL, hr'⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX
    φ hφ hker ψ hψ (hsing φ hφ hker ψ hψ)
  have hRM : Rt M (LB M Q B) t ≤ M := fun x hx => hc.Rt_le_M t hx
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.mem
  have hφX : ∀ s : ↥(Rt M (LB M Q B) t), (φ s : GL ι K) ∈ X := fun s =>
    hφ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hQu' : ∀ s : ↥(Rt M (LB M Q B) t), Q' ((φ s : Matrix ι ι K) *ᵥ u) = 0 := fun s => by
    rw [E.quad_mulVec (hφX s)]; exact hQu
  have hu'ne : ∀ s : ↥(Rt M (LB M Q B) t), polar Q' u ((φ s : Matrix ι ι K) *ᵥ u) ≠ 0 →
      (φ s : Matrix ι ι K) *ᵥ u ≠ 0 := fun s h h0 => h (by rw [h0]; simp [polar])
  have hRne : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro heq
    have hne := (hr' ⟨r, hr⟩).1.mp hplane
    have hrL : r ∈ LB M Q B := heq ▸ hr
    have hmem : φ ⟨r, hr⟩ ∈ E.LomGL u := by
      rw [← hL]
      exact ⟨⟨r, hr⟩, Subgroup.mem_subgroupOf.mpr hrL, rfl⟩
    exact hne (by rw [E.LomGL_mulVec_self hQ hQu hu0 hmem, polar_self_eq_zero hQu])
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hL35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.2.1
  have hN311 := h311a G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
  have hTcard := h311bK G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
    hnotSL T hT
  have hNNT := h311bC G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ hRne
    hnotSL T hT
  have hNN : ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B := hNNT.trans (fun x hx => ((hT x).mp hx).1)
  refine hc.sec51_assembly hs h35 hN311 hNN T hT hTcard hL35 ?_ ?_ ?_ ?_ ?_ ?_ r hr hplane
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    exact le_sup_secOmega E hQ φ hφ hker hQu (hQu' ⟨s, hs'⟩) hne hL hL2
  ·
    intro s hs' hpl x hx
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    have hxR : x ∈ Rt M (LB M Q B) t := hLR hx.1
    have h1 : φ ⟨x, hxR⟩ ∈ E.LomGL u := by
      rw [← hL]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    have h2 : φ ⟨x, hxR⟩ ∈ E.LomGL ((φ ⟨s, hs'⟩ : Matrix ι ι K) *ᵥ u) := by
      rw [← hL2]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
    have h3' : φ ⟨x, hxR⟩ ∈ E.LomGL u ⊓ E.LomGL ((φ ⟨s, hs'⟩ : Matrix ι ι K) *ᵥ u) := ⟨h1, h2⟩
    rw [(E.LomGL_inf_eq_bot_iff hQ (by omega) hQu (hQu' ⟨s, hs'⟩) hu0
      (hu'ne ⟨s, hs'⟩ hne)).mpr hne, Subgroup.mem_bot] at h3'
    have h4 : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h3'
    rw [hker] at h4
    exact Subgroup.mem_subgroupOf.mp h4
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    obtain ⟨A, hA, w, hw, hQw, hAx⟩ := E.exists_eichler_LomGL hQ h3 hQu hu0
    rw [← hL] at hA
    obtain ⟨l, hl, hlA⟩ := hA
    refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩
    set s' : ↥(Rt M (LB M Q B) t) := ⟨s, hs'⟩ with hs'def
    have hr1 := (hr' (s'⁻¹ * l * s')).1
    have hcoe : ((s'⁻¹ * l * s' : ↥(Rt M (LB M Q B) t)) : G) = s⁻¹ * (l : G) * s := rfl
    rw [hcoe] at hr1
    refine hr1.mpr ?_
    have hφr : φ (s'⁻¹ * l * s') = (φ s')⁻¹ * A * φ s' := by
      rw [map_mul, map_mul, map_inv, hlA]
    rw [hφr, E.polar_conj_mulVec (hφX s'), hAx]
    set u' := (φ s' : Matrix ι ι K) *ᵥ u with hu'
    have ha : polar Q' u' u ≠ 0 := by rw [polar_comm]; exact hne
    have hu'u' : polar Q' u' u' = 0 := polar_self_eq_zero (hQu' s')
    have e : polar Q' u' (u' + polar Q' u' u • w - (polar Q' u' w + Q' w * polar Q' u' u) • u) =
        -(Q' w * polar Q' u' u ^ 2) := by
      rw [sub_eq_add_neg, polar_add_right, polar_add_right, polar_neg_right,
        polar_smul_right_eq, polar_smul_right_eq, hu'u']
      have : polar Q' u' u = polar Q' u' u := rfl
      ring
    rw [e]
    exact neg_ne_zero.mpr (mul_ne_zero hQw (pow_ne_zero 2 ha))
  ·
    intro s hs' hpl
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    have hu'0 := hu'ne ⟨s, hs'⟩ hne
    obtain ⟨A, hA, w, hw, hQw, hAx⟩ := E.exists_eichler_LomGL hQ h3 (hQu' ⟨s, hs'⟩) hu'0
    rw [← hL2] at hA
    obtain ⟨l, hl, hlA⟩ := hA
    refine ⟨(l : G), ?_, ?_⟩
    · rw [hc.LB_conj (hRM hs')]
      exact Subgroup.mem_subgroupOf.mp hl
    · refine ((hr' l).1).mpr ?_
      rw [hlA, hAx]
      set u' := (φ ⟨s, hs'⟩ : Matrix ι ι K) *ᵥ u with hu'
      have hu'u' : polar Q' u u = 0 := polar_self_eq_zero hQu
      have e : polar Q' u (u + polar Q' u u' • w - (polar Q' u w + Q' w * polar Q' u u') • u') =
          -(Q' w * polar Q' u u' ^ 2) := by
        rw [sub_eq_add_neg, polar_add_right, polar_add_right, polar_neg_right,
          polar_smul_right_eq, polar_smul_right_eq, hu'u']
        ring
      rw [e]
      exact neg_ne_zero.mpr (mul_ne_zero hQw (pow_ne_zero 2 hne))
  ·
    intro s hs' hpl hI hdec
    have hne := (hr' ⟨s, hs'⟩).1.mp hpl
    have hL2 := (hr' ⟨s, hs'⟩).2
    rw [← hc.LB_conj (hRM hs')] at hL2
    obtain ⟨e, he, hn'⟩ := hmod (Rt M (LB M Q B) t) (hc.CN t) (hc.CN t) _ _ _ _ _ φ hφ hker
      (fun ρ hρ x hx => hc.CN_conj_mem hs.mem hρ hx) hI
      (fun x hx y hy => hdec.2.2.2.2.2.2.1 x hx y hy) hdec hLR
      (hc.LB_conj_le_Rt_of_mem hs.mem hs') hQu (hQu' ⟨s, hs'⟩) hne hL hL2
    exact ⟨e, he, by rw [hn', hK]⟩
  ·
    refine ⟨Module.finrank K (ι → K) - 2, ?_⟩
    have h := card_inf_mul_card_map hLR φ hker
    rw [hL, E.card_LomGL hQ hQu hu0, hK] at h
    exact h

end CFSG.RankThree.GF2n.Stroth80
