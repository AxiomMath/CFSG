module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec4.Item426A6Linear
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem twentySeven_dvd {S : Type*} [Group S] [Finite S] {H : Subgroup S} {u : S}
    (hu : ∀ h ∈ H, u * h = h * u) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    {ψ : H →* alternatingGroup (Fin 6)} (hψ : Function.Surjective ψ) : 27 ∣ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 :=
    KFacts.K412.card_alternating_six_seven.1
  have hH : Nat.card H = 360 * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hA6]
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  by_cases huH : u ∈ H
  · have huZ : (⟨u, huH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hu g g.2).symm
    have hψu : ψ ⟨u, huH⟩ = 1 := by
      have h1 : ψ ⟨u, huH⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) :=
        Subgroup.map_center_le_center hψ ⟨_, huZ, rfl⟩
      rw [alternatingGroup.center_eq_bot (by simp)] at h1
      exact h1
    have h3 : 3 ∣ Nat.card ψ.ker := by
      set x : ψ.ker := ⟨⟨u, huH⟩, hψu⟩ with hx
      have h := orderOf_dvd_natCard x
      have hxu : ((x : H) : S) = u := rfl
      rwa [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hxu, hord] at h
    have h27 : 27 ∣ Nat.card H := by
      obtain ⟨k, hk⟩ := h3
      rw [hH, hk]
      exact ⟨40 * k, by ring⟩
    exact h27.trans (Subgroup.card_subgroup_dvd_card H)
  · have hdisj : H ⊓ Subgroup.zpowers u = ⊥ := by
      have hle : H ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers u := inf_le_right
      have hdvd : Nat.card (H ⊓ Subgroup.zpowers u : Subgroup S) ∣ 3 := by
        rw [← hord, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply huH
        have heq : H ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hord])
        have hm : u ∈ H ⊓ Subgroup.zpowers u := by
          rw [heq]
          exact Subgroup.mem_zpowers u
        exact hm.1
    have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (H : Set S) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hu h hh, mul_inv_cancel_right]
        exact hh
      · intro hh
        have hk := hu _ hh
        have h2 : u * h * u⁻¹ = h := by
          have h3 : u * (u * h * u⁻¹) = u * h := by rw [hk]; group
          exact mul_left_cancel h3
        rwa [h2] at hh
    have hcard := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hnorm hdisj
    rw [Nat.card_zpowers, hord] at hcard
    have h27 : 27 ∣ Nat.card (H ⊔ Subgroup.zpowers u : Subgroup S) := by
      rw [hcard, hH]
      exact ⟨40 * Nat.card ψ.ker, by ring⟩
    exact h27.trans (Subgroup.card_subgroup_dvd_card _)

namespace Config426

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem exists_surj (h : Config426 X α P) :
    ∃ φ : P →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      ∀ p : P, (p : X) ∈ Subgroup.center X → φ p = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := h.tripleCover
  set θP := aschbacherSolvableCore 3 P with hθP
  set T := P ⧸ θP with hT
  refine ⟨e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center T)).comp (QuotientGroup.mk' θP)), ?_, ?_⟩
  · exact e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  · intro p hp
    have hpZ : p ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hp g)
    have h1 : QuotientGroup.mk' θP p ∈ Subgroup.center T :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective θP) ⟨p, hpZ, rfl⟩
    have h2 : QuotientGroup.mk' (Subgroup.center T) (QuotientGroup.mk' θP p) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
    change e (QuotientGroup.mk' (Subgroup.center T) (QuotientGroup.mk' θP p)) = 1
    rw [h2, map_one]

theorem five_dvd_card (h : Config426 X α P) : 5 ∣ Nat.card X := by
  obtain ⟨φ, hφ, -⟩ := h.exists_surj
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 :=
    KFacts.K412.card_alternating_six_seven.1
  have hP : Nat.card P = 360 * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hA6]
  have h5 : 5 ∣ Nat.card P := by
    rw [hP]
    exact ⟨72 * Nat.card φ.ker, by ring⟩
  exact h5.trans (Subgroup.card_subgroup_dvd_card P)

theorem false_of_not_five_dvd (h : Config426 X α P) (h5 : ¬ 5 ∣ Nat.card X) : False :=
  h5 h.five_dvd_card

theorem commute_of_eq_conj (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y) {p : X}
    (hp : p ∈ P) : y * p = p * y := by
  have h1 := h.fixed hp
  rw [hα, MulAut.conj_apply] at h1
  calc y * p = y * p * y⁻¹ * y := by group
    _ = p * y := by rw [h1]

theorem pow_three_mem_center (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y) :
    y ^ 3 ∈ Subgroup.center X := by
  have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, ← hα, h.pow_three]
  rw [Subgroup.mem_center_iff]
  intro g
  have h2 : y ^ 3 * g * (y ^ 3)⁻¹ = g := by
    have := congrArg (fun φ : MulAut X => φ g) h1
    simpa only [MulAut.conj_apply, MulAut.one_apply] using this
  calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
    _ = y ^ 3 * g := by group

theorem inner_image (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) :
    QuotientGroup.mk' (Subgroup.center X) y ≠ 1 ∧
      QuotientGroup.mk' (Subgroup.center X) y ^ 3 = 1 ∧
      (∀ q ∈ P.map (QuotientGroup.mk' (Subgroup.center X)),
        QuotientGroup.mk' (Subgroup.center X) y * q = q * QuotientGroup.mk' (Subgroup.center X) y) ∧
      ∃ ψ : P.map (QuotientGroup.mk' (Subgroup.center X)) →* alternatingGroup (Fin 6),
        Function.Surjective ψ := by
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hy
  · rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.pow_three_mem_center hα
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, h.commute_of_eq_conj hα hp]
  · obtain ⟨φ, hφ, hφZ⟩ := h.exists_surj
    let πP : P →* P.map π := π.subgroupMap P
    have hπP : Function.Surjective πP := π.subgroupMap_surjective P
    have hle : πP.ker ≤ φ.ker := by
      intro p hp
      have h1 : π p = 1 := congrArg Subtype.val hp
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hφZ p h1
    refine ⟨(QuotientGroup.lift πP.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective πP hπP).symm.toMonoidHom, ?_⟩
    intro a
    obtain ⟨p, rfl⟩ := hφ a
    refine ⟨πP p, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : (QuotientGroup.quotientKerEquivOfSurjective πP hπP).symm (πP p) =
        (p : P ⧸ πP.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl

theorem twentySeven_dvd_of_inner (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) : 27 ∣ Nat.card (X ⧸ Subgroup.center X) := by
  obtain ⟨hu1, hu3, hu, ψ, hψ⟩ := h.inner_image hα hy
  exact twentySeven_dvd hu hu1 hu3 hψ

theorem false_of_inner_of_section (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {S : Type*} [Group S] (eS : X ⧸ Subgroup.center X ≃* S)
    (hK : ∀ x : S, orderOf x = 3 → ∀ H : Subgroup S, H ≤ Subgroup.centralizer {x} →
      ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f) : False := by
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  set H := P.map π with hH
  obtain ⟨hu1, hu3, hu, ψ, hψ⟩ := h.inner_image hα hy
  have hord : orderOf (eS (π y)) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hu3 hu1
  refine hK (eS (π y)) hord (H.map eS.toMonoidHom) ?_
    (ψ.comp (H.equivMapOfInjective eS.toMonoidHom eS.injective).symm.toMonoidHom) ?_
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change eS q * eS (π y) = eS (π y) * eS q
    rw [← map_mul, ← map_mul, hu q hq]
  · exact hψ.comp (H.equivMapOfInjective eS.toMonoidHom eS.injective).symm.surjective

theorem false_of_inner_matrix (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (e : X ≃* H) : False := by
  obtain ⟨a, ha, b, hb, hcZ, hc1, hc3⟩ := h.comm
  set c := a * b * a⁻¹ * b⁻¹ with hc
  set M : X →* Matrix (Fin 3) (Fin 3) K :=
    (Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp (H.subtype.comp e.toMonoidHom) with hM
  have hMinj : Function.Injective M := fun x x' hxx' =>
    e.injective (Subtype.ext (Units.ext hxx'))
  have hunit : ∀ x : X, IsUnit (M x).det := fun x => by
    have := (Matrix.GeneralLinearGroup.det ((e x : H) : GL (Fin 3) K)).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hcomm : ∀ {u v : X}, u * v = v * u → M u * M v = M v * M u := fun huv => by
    rw [← map_mul, ← map_mul, huv]
  have habc : a * b = c * (b * a) := by rw [hc]; group
  have hca : c * a = a * c := (Subgroup.mem_center_iff.mp hcZ a).symm
  have hcb : c * b = b * c := (Subgroup.mem_center_iff.mp hcZ b).symm
  obtain ⟨μ, hμ⟩ := exists_scalar_of_commute h3 (hunit a) (hunit b)
    (by rw [← map_mul, ← map_mul, ← map_mul, habc]) (hcomm hca) (hcomm hcb)
    (by rw [← map_pow, hc3, map_one]) (fun h1 => hc1 (hMinj (by rw [h1, map_one])))
    (hcomm (h.commute_of_eq_conj hα ha)) (hcomm (h.commute_of_eq_conj hα hb))
  apply hy
  rw [Subgroup.mem_center_iff]
  intro g
  apply hMinj
  rw [map_mul, map_mul, hμ]
  exact (Matrix.scalar_commute μ (fun _ => Commute.all _ _) (M g)).symm

end Config426

end CFSG.RankThree.PartTwo.Sec4.Item426
