module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Orb
public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Assembly.LowTwoRank

theorem units_subsingleton {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Subsingleton Kˣ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h := Fintype.card_units (α := K)
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [h2] at h
  have h1 : Fintype.card Kˣ = 1 := h
  exact Fintype.card_le_one_iff_subsingleton.1 h1.le

theorem statedSL_eq_top {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    StatedSL 5 K = ⊤ := by
  have := units_subsingleton hK
  rw [eq_top_iff]
  intro A _
  apply Subgroup.subset_closure
  show (A : Matrix (Fin 5) (Fin 5) K).det = 1
  have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  simpa using congrArg Units.val h1

theorem scalars_trivial {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {g : GL (Fin 5) K}
    (hg : g ∈ StatedScalars (Fin 5) K) : g = 1 := by
  have := units_subsingleton hK
  obtain ⟨c, rfl⟩ := hg
  rw [Subsingleton.elim c 1, map_one]

theorem exists_mulEquiv_gl5 {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : S ≃* StatedProj (StatedSL 5 K)) :
    Nonempty (S ≃* GL (Fin 5) K) := by
  let H := StatedSL 5 K
  let N := (StatedScalars (Fin 5) K).subgroupOf H
  have hN : N ≤ H.subtype.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact scalars_trivial hK hg
  let q : StatedProj H →* GL (Fin 5) K := QuotientGroup.lift N H.subtype hN
  let ρ : S →* GL (Fin 5) K := q.comp e.toMonoidHom
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e g)
    have h1 : q (e g) = 1 := hg
    rw [← hh] at h1
    have h2 : h = 1 := Subtype.ext h1
    rw [h2] at hh
    rw [Subgroup.mem_bot]
    apply e.injective
    rw [map_one, ← hh]
    exact QuotientGroup.mk_one _
  have hsurj : Function.Surjective ρ := by
    intro A
    have hA : A ∈ H := by
      show A ∈ StatedSL 5 K
      rw [statedSL_eq_top hK]
      trivial
    refine ⟨e.symm (QuotientGroup.mk ⟨A, hA⟩), ?_⟩
    show q (e (e.symm (QuotientGroup.mk ⟨A, hA⟩))) = A
    rw [MulEquiv.apply_symm_apply]
    rfl
  exact ⟨MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩⟩

theorem card_gl5 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (GL (Fin 5) K) = 9999360 := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_GL_field, h2]
  simp [Fin.prod_univ_five]

theorem not_core_psl_five {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 5 2 1) : ¬ A5Core S := by
  rintro ⟨Kk, Vv, hVK, hKN, hKcard, hV16, hel, m, hm⟩
  obtain ⟨-, F, _, _, hFcard, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by simpa using hFcard
  obtain ⟨eGL⟩ := exists_mulEquiv_gl5 hF2 e
  have hS : Nat.card S = 9999360 := by
    rw [Nat.card_congr eGL.toEquiv]
    exact card_gl5 hF2
  obtain ⟨x, hxK, hx5⟩ := exists_orderOf_five_of_card_eq_960 hKcard
  have hxN : x ∈ Subgroup.normalizer (Vv : Set S) := hKN hxK
  have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (Vv : Set S))
  rw [hm, hS] at hdvd
  have hN : Nat.card (Subgroup.normalizer (Vv : Set S)) ≤ 15360 := by
    rw [hm]
    by_contra hgt
    have hm5 : 5 ≤ m := by
      by_contra h5
      have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h1 : 2 ^ 5 ∣ 2 ^ m := pow_dvd_pow 2 hm5
    have h2 : 960 * 2 ^ 5 ∣ 960 * 2 ^ m := mul_dvd_mul_left 960 h1
    have h3 := h2.trans hdvd
    norm_num at h3
  let act : S →* ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp eGL.toMonoidHom
  have hact : Function.Injective act := by
    have h1 : Function.Injective
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).toMonoidHom.comp
          Matrix.GeneralLinearGroup.toLin.toMonoidHom) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).injective.comp
        Matrix.GeneralLinearGroup.toLin.injective
    exact h1.comp eGL.injective
  exact L5.l5_core act hF2 (Module.finrank_fin_fun F) hact (by rw [hS]; norm_num) hV16 hx5 hxN hN

end CFSG.Quasithin.H13.CTK
