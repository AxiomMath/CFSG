module

public import CFSG.Timmesfeld.RankOne.Bender
public import CFSG.Timmesfeld.RankOne.Quotient
public import CFSG.Timmesfeld.RankOne.Center
public import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.Timmesfeld

open RankOne CFSG.BenderSuzuki.MatrixGroups

namespace IsElemAbRankOne

variable {X : Type*} [Group X] {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem pointKernel_le_center : pointKernel A ≤ Subgroup.center X := by
  intro k hk
  have hkN := h.pointKernel_le hk
  have hAk : ∀ a ∈ A, a * k = k * a := by
    intro a ha
    have h1 : k * a * k⁻¹ * a⁻¹ ∈ A := by
      have := conj_mem_map_conj k ha
      rw [map_conj_eq_self_iff.2 (Subgroup.mem_inf.1 hkN).1] at this
      exact A.mul_mem this (A.inv_mem ha)
    have h2 : k * a * k⁻¹ * a⁻¹ ∈ pointKernel A := by
      rw [show k * a * k⁻¹ * a⁻¹ = k * (a * k⁻¹ * a⁻¹) by group]
      exact Subgroup.mul_mem _ hk ((inferInstance : (pointKernel A).Normal).conj_mem _
        (Subgroup.inv_mem _ hk) a)
    have h3 : k * a * k⁻¹ * a⁻¹ = 1 :=
      h.eq_one_of_map_conj_eq h1
        (map_conj_eq_self_iff.2 (Subgroup.mem_inf.1 (h.pointKernel_le h2)).2)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hBk : ∀ b ∈ B, b * k = k * b := by
    intro b hb
    have h1 : k * b * k⁻¹ * b⁻¹ ∈ B := by
      have := conj_mem_map_conj k hb
      rw [map_conj_eq_self_iff.2 (Subgroup.mem_inf.1 hkN).2] at this
      exact B.mul_mem this (B.inv_mem hb)
    have h2 : k * b * k⁻¹ * b⁻¹ ∈ pointKernel A := by
      rw [show k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) by group]
      exact Subgroup.mul_mem _ hk ((inferInstance : (pointKernel A).Normal).conj_mem _
        (Subgroup.inv_mem _ hk) b)
    have h3 : k * b * k⁻¹ * b⁻¹ = 1 :=
      h.symm.eq_one_of_map_conj_eq h1
        (map_conj_eq_self_iff.2 (Subgroup.mem_inf.1 (h.pointKernel_le h2)).1)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hle : A ⊔ B ≤ Subgroup.centralizer ({k} : Set X) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hAk a ha
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hBk b hb
  rw [h.gen] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have := hle (Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end IsElemAbRankOne

theorem rankOne_two {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    (h : IsElemAbRankOne A B) (hq : Nat.card A = 2) : Nat.card X = 6 :=
  h.card_eq_six hq

theorem rankOne_mulEquiv_SL2 {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    (h : IsElemAbRankOne A B) (hq : 4 ≤ Nat.card A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        A.map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        B.map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  classical
  set K := IsElemAbRankOne.pointKernel A with hKdef
  set f := QuotientGroup.mk' K
  have hker : f.ker ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) := by
    rw [QuotientGroup.ker_mk']
    exact h.pointKernel_le
  have hbar := h.map (QuotientGroup.mk'_surjective K) hker
  have hcardbar : Nat.card (A.map f) = Nat.card A := h.card_map_eq (hker.trans inf_le_right)
  obtain ⟨n, hn2, hn, ⟨e⟩⟩ :=
    hbar.exists_mulEquiv_psl2_of_faithful h.faithfulSMul_quotient (hcardbar ▸ hq)
  rw [hcardbar] at hn
  have hKodd : Odd (Nat.card K) :=
    Odd.of_dvd_nat h.odd_card_normalizer_inf (Subgroup.card_dvd_of_le h.pointKernel_le)
  have hS : Subgroup.closure ((A : Set X) ∪ B) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, h.gen]
  have hSinv : ∀ s ∈ (A : Set X) ∪ B, s * s = 1 := by
    rintro s (hs | hs)
    · exact h.sq s hs
    · exact h.symm.sq s hs
  have hKbot : K = ⊥ := by
    refine eq_bot_of_isCyclic_sylow h.pointKernel_le_center hKodd hS hSinv ?_
    intro r _ hr2 R
    have hcyc := isCyclic_sylow_psl2 hn2 r hr2
      (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R)
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R] at hcyc
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ e.injective)).2 hcyc
  let e₀ : X ≃* X ⧸ K :=
    ((QuotientGroup.quotientMulEquivOfEq hKbot).trans QuotientGroup.quotientBot).symm
  let φ₀ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (e.trans (psl2EquivSL2 (GaloisField 2 n)))
  set S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  have hXS : Nat.card X = Nat.card S := Nat.card_congr φ₀.toEquiv
  have hKn : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hAX : Nat.card A = 2 ^ (Nat.card X).factorization 2 := by
    have := Sylow.card_eq_multiplicity h.sylow
    rwa [h.coe_sylow] at this
  have hAsyl : Nat.card A = 2 ^ (Nat.card S).factorization 2 := by
    rw [← hXS]
    exact hAX
  let P : Sylow 2 S := Sylow.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective h.sylow
  have hP : (P : Subgroup S) = A.map φ₀.toMonoidHom := by
    simp [P, Sylow.coe_mapSurjective]
  let U : Sylow 2 S := Sylow.ofCard (upperUnipotent (GaloisField 2 n))
    (by rw [card_upperUnipotent, hKn, ← hn, hAsyl])
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
    (by rw [Subgroup.card_map_of_injective φ₁.symm.injective, card_lowerUnipotent, hKn, ← hn,
      hAX])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X h.sylow D
  have hDx : A.map (MulAut.conj x).toMonoidHom =
      (lowerUnipotent (GaloisField 2 n)).map φ₁.symm.toMonoidHom := by
    have := congrArg Sylow.toSubgroup hx
    rw [Sylow.coe_subgroup_smul, h.coe_sylow, Sylow.coe_ofCard] at this
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
  refine ⟨n, hn2, hn, φ₁.trans (MulAut.conj (φ₁ a)), ?_, ?_⟩
  · rw [hφ, ← Subgroup.map_map, hφ₁A]
    apply map_conj_of_mem
    rw [← hφ₁A]
    exact Subgroup.mem_map_of_mem _ ha
  · rw [hφ, ← Subgroup.map_map]
    exact hlow

end CFSG.Timmesfeld
