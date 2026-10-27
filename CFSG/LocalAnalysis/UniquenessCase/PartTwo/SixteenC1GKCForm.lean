module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62
open CFSG.LargeExtraspecial.O62.Code

private noncomputable def s16c1c_f {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (v : V₀) : W :=
  β.symm (Multiplicative.ofAdd v)

private theorem s16c1c_f_beta {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) (v : V₀) :
    β (s16c1c_f β v) = Multiplicative.ofAdd v := by
  simp [s16c1c_f]

private theorem s16c1c_f_add {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    (v v' : V₀) :
    s16c1c_f β (v + v') = s16c1c_f β v * s16c1c_f β v' := by
  apply β.injective
  rw [s16c1c_f_beta, map_mul, s16c1c_f_beta, s16c1c_f_beta]
  exact ofAdd_add v v'

private theorem s16c1c_f_zero {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) :
    s16c1c_f β 0 = 1 := by
  simp [s16c1c_f]

private theorem s16c1c_f_injective {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) : Function.Injective (s16c1c_f β) := by
  intro v v' h
  apply Multiplicative.ofAdd.injective
  rw [← s16c1c_f_beta β v, ← s16c1c_f_beta β v', h]

private theorem s16c1c_f_toAdd {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) (x : W) :
    s16c1c_f β (Multiplicative.toAdd (β x)) = x := by
  simp [s16c1c_f]

private theorem s16c1c_finrank_V₀ : Module.finrank (ZMod 2) V₀ = 6 :=
  Module.finrank_fin_fun (ZMod 2)

private theorem s16c1c_qModel_vec1 : qModel true (vec 1) = 0 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec2 : qModel true (vec 2) = 0 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec3 : qModel true (vec 3) = 1 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec4 : qModel true (vec 4) = 0 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec5 : qModel true (vec 5) = 0 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec6 : qModel true (vec 6) = 0 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_vec7 : qModel true (vec 7) = 1 := by
  rw [qModel_vec]; decide

private theorem s16c1c_qModel_zero : qModel true (0 : V₀) = 0 := by
  rw [qModel_true, qMinus_apply]; simp

private theorem s16c1c_vec1_ne : (vec 1 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec2_ne : (vec 2 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec3_ne : (vec 3 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec4_ne : (vec 4 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec5_ne : (vec 5 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec6_ne : (vec 6 : V₀) ≠ 0 := by decide
private theorem s16c1c_vec7_ne : (vec 7 : V₀) ≠ 0 := by decide

private theorem s16c1c_add12 : (vec 1 : V₀) + vec 2 = vec 3 := by decide
private theorem s16c1c_add14 : (vec 1 : V₀) + vec 4 = vec 5 := by decide
private theorem s16c1c_add24 : (vec 2 : V₀) + vec 4 = vec 6 := by decide
private theorem s16c1c_add34 : (vec 3 : V₀) + vec 4 = vec 7 := by decide

private theorem s16c1c_Q0_invariant {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {Q : W → ZMod 2}
    (hQH : QuadInvariant Q H) (g : V₀ ≃ₗ[ZMod 2] V₀) (hg : g ∈ Ω₀ true) (v : V₀) :
    Q (s16c1c_f β (g v)) = Q (s16c1c_f β v) := by
  have hφ : s16c1G_kappa β g ∈ H := (s16c1G_mem_H_iff hβ _).2 ⟨g, hg, rfl⟩
  have hfix : s16c1G_kappa β g (s16c1c_f β v) = s16c1c_f β (g v) := by
    apply β.injective
    rw [s16c1G_kappa_apply, s16c1c_f_beta, s16c1c_f_beta, toAdd_ofAdd]
  rw [← hfix]
  exact hQH _ hφ _

private theorem s16c1c_Q0_const {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {Q : W → ZMod 2}
    (hQH : QuadInvariant Q H) {v v' : V₀} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (h : qModel true v = qModel true v') :
    Q (s16c1c_f β v) = Q (s16c1c_f β v') := by
  have h5 : 5 ≤ Module.finrank (ZMod 2) V₀ := by rw [s16c1c_finrank_V₀]; norm_num
  obtain ⟨g, hg, hgv⟩ := exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
    (qModel_nondegenerate true) h5 hv hv' h
  rw [← hgv]
  exact (s16c1c_Q0_invariant hβ hQH g hg v).symm

private theorem s16c1c_Q0_sing {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {Q : W → ZMod 2}
    (hQH : QuadInvariant Q H) {v : V₀} (hv : v ≠ 0) (hq : qModel true v = 0) :
    Q (s16c1c_f β v) = Q (s16c1c_f β (vec 1)) :=
  s16c1c_Q0_const hβ hQH hv s16c1c_vec1_ne (by rw [hq, s16c1c_qModel_vec1])

private theorem s16c1c_Q0_nonsing {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {Q : W → ZMod 2}
    (hQH : QuadInvariant Q H) {v : V₀} (hv : v ≠ 0) (hq : qModel true v = 1) :
    Q (s16c1c_f β v) = Q (s16c1c_f β (vec 3)) :=
  s16c1c_Q0_const hβ hQH hv s16c1c_vec3_ne (by rw [hq, s16c1c_qModel_vec3])

theorem s16c1c_form_eq {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (hQH : QuadInvariant Q H) (x : W) :
    Q x = qModel true (Multiplicative.toAdd (β x)) := by
  set s : ZMod 2 := Q (s16c1c_f β (vec 1)) with hs
  set t : ZMod 2 := Q (s16c1c_f β (vec 3)) with ht
  have hv1 : Q (s16c1c_f β (vec 1)) = s := hs.symm
  have hv2 : Q (s16c1c_f β (vec 2)) = s :=
    (s16c1c_Q0_sing hβ hQH s16c1c_vec2_ne s16c1c_qModel_vec2).trans hv1
  have hv3 : Q (s16c1c_f β (vec 3)) = t := ht.symm
  have hv4 : Q (s16c1c_f β (vec 4)) = s :=
    (s16c1c_Q0_sing hβ hQH s16c1c_vec4_ne s16c1c_qModel_vec4).trans hv1
  have hv5 : Q (s16c1c_f β (vec 5)) = s :=
    (s16c1c_Q0_sing hβ hQH s16c1c_vec5_ne s16c1c_qModel_vec5).trans hv1
  have hv6 : Q (s16c1c_f β (vec 6)) = s :=
    (s16c1c_Q0_sing hβ hQH s16c1c_vec6_ne s16c1c_qModel_vec6).trans hv1
  have hv7 : Q (s16c1c_f β (vec 7)) = t :=
    (s16c1c_Q0_nonsing hβ hQH s16c1c_vec7_ne s16c1c_qModel_vec7).trans hv3
  have hprod1 : s16c1c_f β (vec 1) * s16c1c_f β (vec 2) = s16c1c_f β (vec 3) := by
    rw [← s16c1c_f_add, s16c1c_add12]
  have hprod12 : s16c1c_f β (vec 1) * s16c1c_f β (vec 2) * s16c1c_f β (vec 4) =
      s16c1c_f β (vec 7) := by
    rw [hprod1, ← s16c1c_f_add, s16c1c_add34]
  have hprod14 : s16c1c_f β (vec 1) * s16c1c_f β (vec 4) = s16c1c_f β (vec 5) := by
    rw [← s16c1c_f_add, s16c1c_add14]
  have hprod24 : s16c1c_f β (vec 2) * s16c1c_f β (vec 4) = s16c1c_f β (vec 6) := by
    rw [← s16c1c_f_add, s16c1c_add24]
  have hkey := hQ.1.1 (s16c1c_f β (vec 1)) (s16c1c_f β (vec 2)) (s16c1c_f β (vec 4))
  rw [polarQ, polarQ, polarQ] at hkey
  rw [hprod12, hprod1, hprod14, hprod24] at hkey
  rw [hv7, hv3, hv4, hv5, hv1, hv6, hv2] at hkey
  have hs0 : s = 0 := by
    rcases zmod2_eq_zero_or_eq_one s with h | h
    · exact h
    · rcases zmod2_eq_zero_or_eq_one t with h' | h'
      · rw [h, h'] at hkey; exact absurd hkey (by decide)
      · rw [h, h'] at hkey; exact absurd hkey (by decide)
  have ht1 : t = 1 := by
    rcases zmod2_eq_zero_or_eq_one t with ht0 | ht1
    · exfalso
      have hQ0 : ∀ v : V₀, Q (s16c1c_f β v) = 0 := by
        intro v
        rcases s16c1G_qModel_cases v with hq | hq
        · by_cases hv0 : v = 0
          · subst hv0
            rw [s16c1c_f_zero β]
            exact s16c1G44_quadF2_one_of hQ.1
          · rw [s16c1c_Q0_sing hβ hQH hv0 hq, hs.symm, hs0]
        · have hv0 : v ≠ 0 := by
            rintro rfl
            rw [s16c1c_qModel_zero] at hq
            exact zero_ne_one hq
          rw [s16c1c_Q0_nonsing hβ hQH hv0 hq, ht.symm, ht0]
      have hfa : s16c1c_f β (vec 1) ≠ 1 := by
        intro h
        apply s16c1c_vec1_ne
        apply s16c1c_f_injective β
        rw [h, s16c1c_f_zero β]
      obtain ⟨y, hy⟩ := hQ.2 (s16c1c_f β (vec 1)) hfa
      have hy0 : y = s16c1c_f β (Multiplicative.toAdd (β y)) :=
        (s16c1c_f_toAdd β y).symm
      rw [polarQ, hy0, ← s16c1c_f_add] at hy
      simp only [hQ0] at hy
      exact hy (by decide)
    · exact ht1
  have hQval : ∀ v : V₀, Q (s16c1c_f β v) = qModel true v := by
    intro v
    rcases s16c1G_qModel_cases v with hq | hq
    · by_cases hv0 : v = 0
      · subst hv0
        rw [s16c1c_f_zero β, hq]
        exact s16c1G44_quadF2_one_of hQ.1
      · rw [s16c1c_Q0_sing hβ hQH hv0 hq, hs.symm, hs0, hq]
    · have hv0 : v ≠ 0 := by
        rintro rfl
        rw [s16c1c_qModel_zero] at hq
        exact zero_ne_one hq
      rw [s16c1c_Q0_nonsing hβ hQH hv0 hq, ht.symm, ht1, hq]
  conv_lhs => rw [← s16c1c_f_toAdd β x]
  exact hQval _

theorem s16c1c_formSing {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaFormSing H := by
  intro Q hQ hQH w hw
  rw [s16c1c_form_eq hβ hQ.1 hQH w]
  have hz := s16c1G_toAdd_ne_zero β hw
  have hcard : Nat.card (ptCent H w) =
      Nat.card (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd (β w))) :=
    (Nat.card_congr (s16c1G_ptCentEquiv hβ w).toEquiv).symm
  rcases s16c1G_qModel_cases (Multiplicative.toAdd (β w)) with h | h
  · rw [h, hcard, s16c1G_card_stab_sing hz h]; simp
  · rw [h, hcard, s16c1G_card_stab_nonsing h]; norm_num

theorem s16c1c_mem_O_of_mem_normalizer {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : s16c1G_kappa β g ∈ normalizer (H : Set (MulAut W))) : g ∈ O₀ true := by
  apply mem_orthogonalGroup_of_normalizes (hV := s16c1c_finrank_V₀) (qModel_nondegenerate true)
  intro x hx
  have hxH : s16c1G_kappa β x ∈ H := (s16c1G_mem_H_iff hβ _).2 ⟨x, hx, rfl⟩
  have hmem : s16c1G_kappa β g * s16c1G_kappa β x * (s16c1G_kappa β g)⁻¹ ∈ H :=
    (mem_normalizer_iff.mp hg (s16c1G_kappa β x)).1 hxH
  have hrew : s16c1G_kappa β g * s16c1G_kappa β x * (s16c1G_kappa β g)⁻¹ =
      s16c1G_kappa β (g * x * g⁻¹) := by
    rw [← map_mul, ← map_inv, ← map_mul]
  rw [hrew] at hmem
  obtain ⟨y, hy, hyeq⟩ := (s16c1G_mem_H_iff hβ (s16c1G_kappa β (g * x * g⁻¹))).1 hmem
  have hgy : g * x * g⁻¹ = y := s16c1G_kappa_injective β hyeq
  rw [hgy]
  exact hy

theorem s16c1c_normIsom {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaNormIsom H := by
  intro Q hQ hQH x hx w
  obtain ⟨g, rfl⟩ := s16c1G44_kappa_surjective β x
  have hgO : g ∈ O₀ true := s16c1c_mem_O_of_mem_normalizer hβ hx
  rw [s16c1c_form_eq hβ hQ.1 hQH, s16c1c_form_eq hβ hQ.1 hQH]
  rw [s16c1G_kappa_apply, toAdd_ofAdd]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
