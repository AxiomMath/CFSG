module

public import CFSG.Timmesfeld.ARS.Defs
public import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.Data.Fintype.Shrink

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne

namespace ElemAbRankOne

variable {X : Type*} [Group X] {A B : Subgroup X}

theorem map_mulEquiv {Y : Type*} [Group Y] (h : IsElemAbRankOne A B) (e : X ≃* Y) :
    IsElemAbRankOne (A.map e.toMonoidHom) (B.map e.toMonoidHom) :=
  h.map e.surjective (by rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]; exact bot_le)

theorem exists_mulEquiv_SL2 [Finite X] (h : IsElemAbRankOne A B) (hq : 4 ≤ Nat.card A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        A.map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        B.map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  let e : X ≃* Shrink.{0} X := Shrink.mulEquiv.symm
  have hc : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective e.injective
  obtain ⟨n, hn, hcard, φ, hφA, hφB⟩ := rankOne_mulEquiv_SL2 (map_mulEquiv h e) (hc ▸ hq)
  have hcomp : (e.trans φ).toMonoidHom = φ.toMonoidHom.comp e.toMonoidHom := rfl
  refine ⟨n, hn, hc ▸ hcard, e.trans φ, ?_, ?_⟩
  · rw [hcomp, ← Subgroup.map_map, hφA]
  · rw [hcomp, ← Subgroup.map_map, hφB]

theorem isPGroup (h : IsElemAbRankOne A B) : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
  exact h.sq _ a.2

theorem card_eq_two [Finite X] (h : IsElemAbRankOne A B) (hq : ¬ 4 ≤ Nat.card A) :
    Nat.card A = 2 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup h)
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hbot : A = ⊥ := Subgroup.card_eq_one.1 (by rw [hm, pow_zero])
    rw [hbot] at ha
    exact ha1 ha
  have hm1 : m < 2 := by
    by_contra hm2
    exact hq (hm ▸ (Nat.pow_le_pow_right two_pos (not_lt.1 hm2)))
  rw [hm, show m = 1 by omega, pow_one]

theorem center_eq_bot [Finite X] (h : IsElemAbRankOne A B) : Subgroup.center X = ⊥ := by
  by_cases hq : 4 ≤ Nat.card A
  · obtain ⟨n, -, -, φ, -, -⟩ := exists_mulEquiv_SL2 h hq
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hφx : φ x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hx z]
    rw [center_SL2_eq_bot, Subgroup.mem_bot] at hφx
    exact φ.injective (hφx.trans (map_one φ).symm)
  · rw [eq_bot_iff, ← h.hua_eq_bot_of_card_eq_two (card_eq_two h hq), ← h.normalizer_inf_eq_hua]
    intro z hz
    have hfix : ∀ H : Subgroup X, z ∈ Subgroup.normalizer (H : Set X) := fun H => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]
    exact ⟨hfix A, hfix B⟩

theorem eq_one_of_forall_map_conj [Finite X] (h : IsElemAbRankOne A B) {x : X}
    (hx : ∀ y : X, (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj y).toMonoidHom) : x = 1 := by
  have hk : x ∈ IsElemAbRankOne.pointKernel A := by
    rw [IsElemAbRankOne.mem_pointKernel]
    intro C
    obtain ⟨y, rfl⟩ := Point.exists_smul_base C
    exact Point.ext (by rw [Point.val_smul, Point.val_smul_base]; exact hx y)
  have := h.pointKernel_le_center hk
  rwa [center_eq_bot h, Subgroup.mem_bot] at this

theorem not_two_dvd_index [Finite X] (h : IsElemAbRankOne A B) : ¬ 2 ∣ A.index := by
  let e : X ≃* Shrink.{0} X := Shrink.mulEquiv.symm
  have := (map_mulEquiv h e).not_two_dvd_index
  rwa [Subgroup.index_map_of_bijective e.bijective] at this

theorem exists_eq_map_conj [Finite X] (h : IsElemAbRankOne A B) {E : Subgroup X}
    (hE : IsPGroup 2 E) (hcard : Nat.card E = Nat.card A) :
    ∃ x : X, E = A.map (MulAut.conj x).toMonoidHom := by
  have hidx : E.index = A.index := by
    have h1 := E.card_mul_index
    rw [hcard, ← A.card_mul_index] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1)
  let P : Sylow 2 X := (isPGroup h).toSylow (not_two_dvd_index h)
  let Q : Sylow 2 X := hE.toSylow (hidx ▸ not_two_dvd_index h)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨x, ?_⟩
  have := congrArg Sylow.toSubgroup hx
  rw [Sylow.coe_subgroup_smul] at this
  simp only [P, Q, IsPGroup.toSylow_coe] at this
  exact this.symm

theorem sup_map_conj_eq_top (h : IsElemAbRankOne A B) {x y : X}
    (hne : A.map (MulAut.conj x).toMonoidHom ≠ A.map (MulAut.conj y).toMonoidHom) :
    A.map (MulAut.conj x).toMonoidHom ⊔ A.map (MulAut.conj y).toMonoidHom = ⊤ := by
  have key : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ A →
      A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
    intro g hg
    obtain ⟨a, ha, hga⟩ := h.exists_eq_of_map_conj_ne hg
    rw [hga]
    calc A ⊔ B.map (MulAut.conj a).toMonoidHom
        = (A ⊔ B).map (MulAut.conj a).toMonoidHom := by rw [Subgroup.map_sup, map_conj_of_mem ha]
      _ = ⊤ := by rw [h.gen]; exact Subgroup.map_top_of_surjective _ (MulAut.conj a).surjective
  have hne' : A.map (MulAut.conj (x⁻¹ * y)).toMonoidHom ≠ A := by
    intro heq
    apply hne
    rw [map_conj_mul, map_conj_eq_iff, inv_inv] at heq
    exact heq.symm
  have h1 := congrArg (fun H => H.map (MulAut.conj x).toMonoidHom) (key _ hne')
  simp only [Subgroup.map_sup, ← map_conj_mul, mul_inv_cancel_left] at h1
  rw [h1]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective

theorem exists_mulEquiv_SL2_of_mulEquiv [Finite X] (h : IsElemAbRankOne A B) {n : ℕ}
    (hn : n ≠ 0) (hcard : Nat.card A = 2 ^ n)
    (φ₀ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    ∃ φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      A.map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
      B.map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  set S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  have hXS : Nat.card X = Nat.card S := Nat.card_congr φ₀.toEquiv
  have hKn : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  let P₀ : Sylow 2 X := (isPGroup h).toSylow (not_two_dvd_index h)
  have hP₀ : (P₀ : Subgroup X) = A := IsPGroup.toSylow_coe _ _
  have hAX : Nat.card A = 2 ^ (Nat.card X).factorization 2 := by
    have := Sylow.card_eq_multiplicity P₀
    rwa [hP₀] at this
  have hAsyl : Nat.card A = 2 ^ (Nat.card S).factorization 2 := by
    rw [← hXS]
    exact hAX
  let P : Sylow 2 S := Sylow.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective P₀
  have hP : (P : Subgroup S) = A.map φ₀.toMonoidHom :=
    (Sylow.coe_mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective P₀).trans (by rw [hP₀])
  let U : Sylow 2 S := Sylow.ofCard (upperUnipotent (GaloisField 2 n))
    (by rw [card_upperUnipotent, hKn, ← hcard, hAsyl])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P U
  have hgU : (A.map φ₀.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      upperUnipotent (GaloisField 2 n) := by
    have := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, hP, Sylow.coe_ofCard] at this
    exact this
  let φ₁ := φ₀.trans (MulAut.conj g)
  have hφ₁ : φ₁.toMonoidHom = (MulAut.conj g).toMonoidHom.comp φ₀.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  have hφ₁A : A.map φ₁.toMonoidHom = upperUnipotent (GaloisField 2 n) := by
    rw [hφ₁, ← Subgroup.map_map, hgU]
  let D : Sylow 2 X := Sylow.ofCard ((lowerUnipotent (GaloisField 2 n)).map φ₁.symm.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ₁.symm.injective, card_lowerUnipotent, hKn, ← hcard,
      hAX])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P₀ D
  have hDx : A.map (MulAut.conj x).toMonoidHom =
      (lowerUnipotent (GaloisField 2 n)).map φ₁.symm.toMonoidHom := by
    have := congrArg Sylow.toSubgroup hx
    rw [Sylow.coe_subgroup_smul, hP₀, Sylow.coe_ofCard] at this
    exact this
  have hlow : (A.map (MulAut.conj x).toMonoidHom).map φ₁.toMonoidHom =
      lowerUnipotent (GaloisField 2 n) := by
    have hid : φ₁.toMonoidHom.comp φ₁.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun y => φ₁.apply_symm_apply y
    rw [hDx, Subgroup.map_map, hid, Subgroup.map_id]
  have hxA : A.map (MulAut.conj x).toMonoidHom ≠ A := by
    intro hxA
    rw [hxA, hφ₁A] at hlow
    exact upperUnipotent_ne_lowerUnipotent _ hlow
  obtain ⟨a, ha, haeq⟩ := h.exists_eq_of_map_conj_ne hxA
  rw [haeq, map_map_conj] at hlow
  have hφ : (φ₁.trans (MulAut.conj (φ₁ a))).toMonoidHom =
      (MulAut.conj (φ₁ a)).toMonoidHom.comp φ₁.toMonoidHom := MonoidHom.ext fun _ => rfl
  refine ⟨φ₁.trans (MulAut.conj (φ₁ a)), ?_, ?_⟩
  · rw [hφ, ← Subgroup.map_map, hφ₁A]
    apply map_conj_of_mem
    rw [← hφ₁A]
    exact Subgroup.mem_map_of_mem _ ha
  · rw [hφ, ← Subgroup.map_map]
    exact hlow

theorem card_SL2_two : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  let := Fintype.ofFinite (GaloisField 2 1)
  have hK : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 1 one_ne_zero
  rw [Matrix.card_SL_field, hK]
  decide

theorem orderOf_upperElt_mul_lowerElt :
    orderOf (upperElt (GaloisField 2 1) 1 * lowerElt (GaloisField 2 1) 1) = 3 := by
  have h2 : (1 : GaloisField 2 1) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have e1 : ((upperElt (GaloisField 2 1) 1 * lowerElt (GaloisField 2 1) 1 :
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [upperElt, lowerElt, h2]
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, e1, Matrix.SpecialLinearGroup.coe_one]
    simp [pow_succ, Matrix.one_fin_two, h2]
  · intro h1
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) 0 0) h1
    simp only [e1] at this
    simp at this

theorem nonempty_mulEquiv_dihedral_three {D : Type*} [Group D] [Finite D] (ρ σ : D)
    (hgen : ⊤ = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hρ : orderOf ρ = 3) : Nonempty (D ≃* DihedralGroup 3) := by
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    have h1 := orderOf_dvd_of_mem_zpowers hmem
    rw [hρ, orderOf_eq_prime (p := 2) (by rw [pow_two, hσ]) hσ1] at h1
    omega
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen
    (by rw [pow_two, hσ]) hrel hσρ
  rw [hρ] at e
  exact ⟨e⟩

theorem nonempty_SL2_two_mulEquiv_dihedral :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) ≃* DihedralGroup 3) := by
  set S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)
  set u : S := upperElt (GaloisField 2 1) 1
  set l : S := lowerElt (GaloisField 2 1) 1
  have h2 : (1 : GaloisField 2 1) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have huu : u * u = 1 := by
    simp only [u]
    rw [upperElt_mul, h2, upperElt_zero]
  have hll : l * l = 1 := by
    simp only [l]
    rw [lowerElt_mul, h2, lowerElt_zero]
  have hu1 : u ≠ 1 := by
    intro h1
    rw [← upperElt_zero] at h1
    exact one_ne_zero (upperElt_injective _ h1)
  have hord := orderOf_upperElt_mul_lowerElt
  have hgen : ⊤ = Subgroup.zpowers (u * l) ⊔ Subgroup.zpowers u := by
    set H := Subgroup.zpowers (u * l) ⊔ Subgroup.zpowers u
    have h3 : 3 ∣ Nat.card H := by
      have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers (u * l) ≤ H)
      rwa [Nat.card_zpowers, hord] at this
    have h2' : 2 ∣ Nat.card H := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers u ≤ H)
      rwa [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [pow_two, huu]) hu1] at this
    have h6 : 6 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2' h3
    have hle : Nat.card H ≤ 6 := card_SL2_two ▸ Subgroup.card_le_card_group H
    have hpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨k, hk⟩ := h6
    exact (Subgroup.eq_top_of_card_eq H (by rw [card_SL2_two]; omega)).symm
  refine nonempty_mulEquiv_dihedral_three (u * l) u hgen huu hu1 ?_ hord
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hll, ← mul_assoc, huu, one_mul]

theorem nonempty_mulEquiv_SL2_two [Finite X] (h : IsElemAbRankOne A B) (hq : Nat.card A = 2) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  obtain ⟨b, hb, hb1, hab⟩ := h.moufang a ha ha1
  have haa := h.sq a ha
  have hbb := h.symm.sq b hb
  have hab1 : a * b ≠ 1 := by
    intro h1
    have hmem : a ∈ A ⊓ B := ⟨ha, by rw [eq_inv_of_mul_eq_one_left h1]; exact B.inv_mem hb⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hord : orderOf (a * b) = 3 := orderOf_eq_prime (h.mul_pow_three ha ha1 hb hab) hab1
  have hzA : Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha) ?_
    rw [hq, Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [pow_two, haa]) ha1]
  have hzB : Subgroup.zpowers b = B := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hb) ?_
    have hBc : Nat.card B = 2 := by
      obtain ⟨g, hg⟩ := h.exists_eq_map_conj
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hq]
    rw [hBc, Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [pow_two, hbb]) hb1]
  have hgen : ⊤ = Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a := by
    refine le_antisymm ?_ le_top
    rw [← h.gen, ← hzA, ← hzB]
    refine sup_le le_sup_right (Subgroup.zpowers_le.2 ?_)
    have hmem : a⁻¹ * (a * b) ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    rwa [inv_mul_cancel_left] at hmem
  have hrel : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hbb, ← mul_assoc, haa, one_mul]
  obtain ⟨eX⟩ := nonempty_mulEquiv_dihedral_three (a * b) a hgen haa ha1 hrel hord
  obtain ⟨eS⟩ := nonempty_SL2_two_mulEquiv_dihedral
  exact ⟨eX.trans eS.symm⟩

theorem exists_mulEquiv_SL2_two [Finite X] (h : IsElemAbRankOne A B) (hq : Nat.card A = 2) :
    ∃ φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      A.map φ.toMonoidHom = upperUnipotent (GaloisField 2 1) ∧
      B.map φ.toMonoidHom = lowerUnipotent (GaloisField 2 1) :=
  exists_mulEquiv_SL2_of_mulEquiv h one_ne_zero (by rw [hq, pow_one])
    (nonempty_mulEquiv_SL2_two h hq).some

theorem exists_mulEquiv_SL2' [Finite X] (h : IsElemAbRankOne A B) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        A.map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        B.map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  by_cases hq : 4 ≤ Nat.card A
  · obtain ⟨n, hn, hc, φ, h1, h2⟩ := exists_mulEquiv_SL2 h hq
    exact ⟨n, by omega, hc, φ, h1, h2⟩
  · have hq2 := card_eq_two h hq
    obtain ⟨φ, h1, h2⟩ := exists_mulEquiv_SL2_two h hq2
    exact ⟨1, le_refl 1, by rw [hq2, pow_one], φ, h1, h2⟩

end ElemAbRankOne

variable {G : Type*} [Group G]

theorem conjSub_le {H K : Subgroup G} (hH : H ≤ K) {x : G} (hx : x ∈ K) : conjSub H x ≤ K := by
  rintro _ ⟨h, hh, rfl⟩
  exact K.mul_mem (K.mul_mem hx (hH hh)) (K.inv_mem hx)

theorem conjSub_mul (H : Subgroup G) (x y : G) :
    conjSub H (x * y) = conjSub (conjSub H y) x :=
  map_conj_mul H x y

@[simp] theorem conjSub_one (H : Subgroup G) : conjSub H 1 = H := map_conj_one H

theorem mem_conjSub {H : Subgroup G} {g x : G} : x ∈ conjSub H g ↔ g⁻¹ * x * g ∈ H :=
  mem_map_conj

theorem conj_mem_conjSub {H : Subgroup G} (g : G) {x : G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ conjSub H g :=
  conj_mem_map_conj g hx

theorem conjSub_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) : conjSub H g = H :=
  map_conj_of_mem hg

theorem conjSub_of_forall_commute {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, Commute g h) :
    conjSub H g = H := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have e : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g⁻¹ * x * g * g * g⁻¹ := by rw [(hg _ hx).eq]
        _ = g⁻¹ * x * g := by group
    rw [e]
    exact hx
  · intro hx
    rwa [mul_assoc, ← (hg _ hx).eq, inv_mul_cancel_left]

theorem commute_of_mul_self {H : Subgroup G} (hsq : ∀ a ∈ H, a * a = 1) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : Commute a b := by
  have hab : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (H.mul_mem ha hb))).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq _ hb),
    inv_eq_of_mul_eq_one_right (hsq _ ha)] at hab
  exact hab

theorem subgroupOf_inj_of_le {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    H.subgroupOf L = K.subgroupOf L ↔ H = K := by
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hH, inf_of_le_left hK]

theorem mem_map_conj_subgroupOf {H L : Subgroup G} {x : G} (hx : x ∈ L) {u : L} :
    u ∈ (H.subgroupOf L).map (MulAut.conj (⟨x, hx⟩ : L)).toMonoidHom ↔ (u : G) ∈ conjSub H x := by
  rw [map_conj_subgroupOf, Subgroup.mem_subgroupOf]

theorem map_conj_subgroupOf_mk {H L : Subgroup G} {x : G} (hx : x ∈ L) :
    (H.subgroupOf L).map (MulAut.conj (⟨x, hx⟩ : L)).toMonoidHom = (conjSub H x).subgroupOf L :=
  map_conj_subgroupOf ⟨x, hx⟩

namespace Opposite

variable {A B : Subgroup G}

theorem symm (h : Opposite A B) : Opposite B A := ⟨h.1.symm, h.2.2, h.2.1⟩

theorem ne (h : Opposite A B) : A ≠ B := h.1

theorem eq_one_of_conjSub_eq (h : Opposite A B) {a : G} (ha : a ∈ A) (hB : conjSub B a = B) :
    a = 1 := by
  by_contra ha1
  obtain ⟨b, hb, -, hab⟩ := h.2.1 a ha ha1
  rw [hB, map_conj_eq_iff, map_conj_of_mem (B.inv_mem hb)] at hab
  exact h.1 hab

theorem inf_eq_bot (h : Opposite A B) : A ⊓ B = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hx => h.eq_one_of_conjSub_eq hx.1 (conjSub_of_mem hx.2)

theorem not_commute_of_mem (h : Opposite A B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ¬ ∀ b ∈ B, Commute a b :=
  fun hc => ha1 (h.eq_one_of_conjSub_eq ha (conjSub_of_forall_commute hc))

theorem not_commuting (h : Opposite A B) (hA : A ≠ ⊥) : ¬ Commuting A B := by
  intro hc
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  exact h.not_commute_of_mem a.2 (fun h1 => ha1 (Subtype.ext h1)) (hc a a.2)

variable (hsq : ∀ a ∈ A, a * a = 1)
include hsq

theorem isElemAbRankOne_of_mul_self (h : Opposite A B) :
    IsElemAbRankOne (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) := by
  refine ⟨codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup A B), ?_, ?_, ?_, ?_, ?_⟩
  · intro hAB
    exact h.1 ((subgroupOf_inj_of_le le_sup_left le_sup_right).1 hAB)
  · intro a ha a' ha'
    exact Subtype.ext (commute_of_mul_self hsq ha ha').eq
  · intro a ha
    exact Subtype.ext (hsq _ ha)
  · intro a ha ha1
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha (fun h1 => ha1 (Subtype.ext h1))
    refine ⟨⟨b, Subgroup.mem_sup_right hb⟩, hb, fun h1 => hb1 (congrArg Subtype.val h1), ?_⟩
    rw [map_conj_subgroupOf, map_conj_subgroupOf]
    exact congrArg (fun H => Subgroup.subgroupOf H (A ⊔ B)) hab
  · intro b hb hb1
    obtain ⟨a, ha, ha1, hab⟩ := h.2.2 b hb (fun h1 => hb1 (Subtype.ext h1))
    refine ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, fun h1 => ha1 (congrArg Subtype.val h1), ?_⟩
    rw [map_conj_subgroupOf, map_conj_subgroupOf]
    exact congrArg (fun H => Subgroup.subgroupOf H (A ⊔ B)) hab

omit hsq in
theorem conjSub_le_sup {x : G} (hx : x ∈ A ⊔ B) : conjSub A x ≤ A ⊔ B :=
  conjSub_le le_sup_left hx

theorem inf_conjSub_eq_bot (h : Opposite A B) {x y : G} (hx : x ∈ A ⊔ B) (hy : y ∈ A ⊔ B)
    (hne : conjSub A x ≠ conjSub A y) : conjSub A x ⊓ conjSub A y = ⊥ := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have hne' : (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨x, hx⟩ : ↥(A ⊔ B))).toMonoidHom ≠
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨y, hy⟩ : ↥(A ⊔ B))).toMonoidHom := by
    rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk]
    intro heq
    exact hne ((subgroupOf_inj_of_le (conjSub_le_sup hx) (conjSub_le_sup hy)).1 heq)
  have hbot := hr.map_conj_inf_eq_bot hne'
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have huX : u ∈ A ⊔ B := conjSub_le_sup hx hu.1
  have hmem : (⟨u, huX⟩ : ↥(A ⊔ B)) ∈
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨x, hx⟩ : ↥(A ⊔ B))).toMonoidHom ⊓
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨y, hy⟩ : ↥(A ⊔ B))).toMonoidHom :=
    ⟨(mem_map_conj_subgroupOf hx).2 hu.1, (mem_map_conj_subgroupOf hy).2 hu.2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem conjSub_eq_of_commute (h : Opposite A B) {x y u w : G} (hx : x ∈ A ⊔ B)
    (hy : y ∈ A ⊔ B) (hu : u ∈ conjSub A x) (hu1 : u ≠ 1) (hw : w ∈ conjSub A y) (hw1 : w ≠ 1)
    (hc : Commute u w) : conjSub A y = conjSub A x := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have huX : u ∈ A ⊔ B := conjSub_le_sup hx hu
  have hwX : w ∈ A ⊔ B := conjSub_le_sup hy hw
  have heq := hr.eq_of_commute (x := ⟨x, hx⟩) (g := ⟨y, hy⟩) (u := ⟨u, huX⟩) (w := ⟨w, hwX⟩)
    ((mem_map_conj_subgroupOf hx).2 hu) (fun h1 => hu1 (congrArg Subtype.val h1))
    ((mem_map_conj_subgroupOf hy).2 hw) (fun h1 => hw1 (congrArg Subtype.val h1))
    (Subtype.ext hc.eq)
  rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk] at heq
  exact (subgroupOf_inj_of_le (conjSub_le_sup hy) (conjSub_le_sup hx)).1 heq

theorem sup_conjSub_eq (h : Opposite A B) {x y : G} (hx : x ∈ A ⊔ B) (hy : y ∈ A ⊔ B)
    (hne : conjSub A x ≠ conjSub A y) : conjSub A x ⊔ conjSub A y = A ⊔ B := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have hne' : (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨x, hx⟩ : ↥(A ⊔ B))).toMonoidHom ≠
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj (⟨y, hy⟩ : ↥(A ⊔ B))).toMonoidHom := by
    rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk]
    intro heq
    exact hne ((subgroupOf_inj_of_le (conjSub_le_sup hx) (conjSub_le_sup hy)).1 heq)
  have htop := ElemAbRankOne.sup_map_conj_eq_top hr hne'
  rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk] at htop
  have := congrArg (Subgroup.map (A ⊔ B).subtype) htop
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (conjSub_le_sup hx),
    Subgroup.map_subgroupOf_eq_of_le (conjSub_le_sup hy), ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at this

theorem exists_conjSub_eq [Finite G] (h : Opposite A B) {E : Subgroup G} (hE : E ≤ A ⊔ B)
    (h2 : IsPGroup 2 E) (hcard : Nat.card E = Nat.card A) :
    ∃ x ∈ A ⊔ B, E = conjSub A x := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have h2' : IsPGroup 2 (E.subgroupOf (A ⊔ B)) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  have hcard' : Nat.card (E.subgroupOf (A ⊔ B)) = Nat.card (A.subgroupOf (A ⊔ B)) := by
    rw [card_subgroupOf_of_le hE, card_subgroupOf_of_le le_sup_left, hcard]
  obtain ⟨x, hx⟩ := ElemAbRankOne.exists_eq_map_conj hr h2' hcard'
  refine ⟨x, x.2, ?_⟩
  rw [map_conj_subgroupOf_mk (x := (x : G)) x.2] at hx
  exact (subgroupOf_inj_of_le hE (conjSub_le_sup x.2)).1 hx

theorem eq_one_of_mem_centralizer [Finite G] (h : Opposite A B) {x : G} (hx : x ∈ A ⊔ B)
    (hc : x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) : x = 1 := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have hz : (⟨x, hx⟩ : ↥(A ⊔ B)) ∈ Subgroup.center ↥(A ⊔ B) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc g g.2)
  rw [ElemAbRankOne.center_eq_bot hr, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem exists_conjSub_ne [Finite G] (h : Opposite A B) {x : G} (hx : x ∈ A ⊔ B) (hx1 : x ≠ 1) :
    ∃ y ∈ A ⊔ B, conjSub (conjSub A y) x ≠ conjSub A y := by
  by_contra! hcon
  have hr := h.isElemAbRankOne_of_mul_self hsq
  apply hx1
  have := ElemAbRankOne.eq_one_of_forall_map_conj hr (x := ⟨x, hx⟩) fun y => by
    rw [map_conj_subgroupOf_mk (x := (y : G)) y.2, map_conj_subgroupOf]
    exact congrArg (fun H => H.subgroupOf (A ⊔ B)) (hcon _ y.2)
  exact congrArg Subtype.val this

theorem odd_orderOf_mul [Finite G] (h : Opposite A B) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hb1 : b ≠ 1) : Odd (orderOf (a * b)) := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  obtain ⟨g₀, hg₀⟩ := hr.exists_eq_map_conj
  have hne : (A.subgroupOf (A ⊔ B)).map (MulAut.conj (1 : ↥(A ⊔ B))).toMonoidHom ≠
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj g₀).toMonoidHom := by
    rw [map_conj_one, ← hg₀]
    exact hr.ne
  have hmA : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ B)) ∈
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj (1 : ↥(A ⊔ B))).toMonoidHom := by
    rw [map_conj_one]
    exact ha
  have hmB : (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B)) ∈
      (A.subgroupOf (A ⊔ B)).map (MulAut.conj g₀).toMonoidHom := by
    rw [← hg₀]
    exact hb
  have := hr.odd_orderOf_mul hmA (fun h1 => ha1 (congrArg Subtype.val h1)) hmB
    (fun h1 => hb1 (congrArg Subtype.val h1)) hne
  rwa [← Subgroup.orderOf_coe] at this

theorem mul_mul_eq [Finite G] (h : Opposite A B) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hab : conjSub A b = conjSub B a) : a * b * a = b * a * b := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  have hab' : (A.subgroupOf (A ⊔ B)).map
      (MulAut.conj (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B))).toMonoidHom =
      (B.subgroupOf (A ⊔ B)).map
      (MulAut.conj (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ B))).toMonoidHom := by
    rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk, hab]
  have := hr.mul_mul_eq (a := ⟨a, Subgroup.mem_sup_left ha⟩) (b := ⟨b, Subgroup.mem_sup_right hb⟩)
    ha (fun h1 => ha1 (congrArg Subtype.val h1)) hb hab'
  exact congrArg Subtype.val this

omit hsq in
theorem existsUnique_conjSub_eq (h : Opposite A B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃! b, b ∈ B ∧ conjSub A b = conjSub B a := by
  obtain ⟨b, hb, -, hab⟩ := h.2.1 a ha ha1
  refine ⟨b, ⟨hb, hab⟩, fun b' ⟨hb', hab'⟩ => ?_⟩
  have h1 : conjSub A (b'⁻¹ * b) = A := by
    rw [conjSub_mul, hab, ← hab', ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := h.symm.eq_one_of_conjSub_eq (B.mul_mem (B.inv_mem hb') hb) h1
  rw [inv_mul_eq_one] at this
  exact this

end Opposite

end CFSG.Timmesfeld.ARS
