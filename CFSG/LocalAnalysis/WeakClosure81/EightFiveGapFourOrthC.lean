module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section Orth

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem w85g_exists_map_eq_one {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    (hd : 4 ≤ finrank K V) : ∃ a : V, Q a = 1 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  obtain ⟨a₀, ha₀⟩ := exists_map_ne_zero hQ
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q a₀)⁻¹
  refine ⟨s • a₀, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← hs, inv_mul_cancel₀ ha₀]

theorem w85g_natCard_level {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {a : V}
    (ha1 : Q a = 1) :
    Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0} =
      Nat.card K ^ (finrank K V - 2) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  haveI : PerfectRing K 2 := inferInstance
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha1
    exact zero_ne_one ha1
  set f : Module.Dual K V := LinearMap.BilinForm.toDual Q.polarBilin hQ a with hf
  have hf_eval : ∀ x : V, f x = polar Q a x := by
    intro x
    rw [hf, LinearMap.BilinForm.toDual_def, polarBilin_apply_apply]
  set W : Submodule K V := LinearMap.ker f with hW
  have hmemW : ∀ x : V, x ∈ W ↔ polar Q a x = 0 := by
    intro x
    rw [hW, LinearMap.mem_ker, hf_eval]
  have haW : a ∈ W := (hmemW a).mpr (polar_self_eq_zero Q a)
  have hWorth : W = LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K {a}) := by
    ext x
    rw [hmemW, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hx y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [polarBilin_apply_apply, polar_smul_left, hx, smul_zero]
    · intro hx
      have := hx a (Submodule.mem_span_singleton_self a)
      rwa [polarBilin_apply_apply] at this
  have hfinW : finrank K W = finrank K V - 1 := by
    rw [hWorth, LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton ha0]
  set A : Submodule K W := (Submodule.span K {a}).comap W.subtype with hA
  have hAeq : A = Submodule.span K {⟨a, haW⟩} := by
    ext x
    rw [hA, Submodule.mem_comap, Submodule.mem_span_singleton,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, Subtype.ext hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg Subtype.val hc⟩
  have hfinA : finrank K A = 1 := by
    rw [hAeq, finrank_span_singleton]
    intro h
    exact ha0 (congrArg Subtype.val h)
  have hfinQ : finrank K (W ⧸ A) = finrank K V - 2 := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := W) (N := A)
    rw [hfinA, hfinW] at h
    have hV2 : 2 ≤ finrank K V := by
      have hle := Submodule.finrank_le A
      omega
    omega
  have hcardQ : Nat.card (W ⧸ A) = Nat.card K ^ (finrank K V - 2) := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype W := Fintype.ofFinite W
    haveI : Fintype (W ⧸ A) := Fintype.ofFinite (W ⧸ A)
    rw [Nat.card_eq_fintype_card (α := W ⧸ A), Nat.card_eq_fintype_card (α := K),
      Module.card_eq_pow_finrank (K := K) (V := W ⧸ A), hfinQ]
  let F : {x : V // Q x = 1 ∧ polar Q a x = 0} → W ⧸ A :=
    fun x => Submodule.Quotient.mk (⟨x.1, (hmemW x.1).mpr x.2.2⟩ : W)
  have hinj : Function.Injective F := by
    intro x y hxy
    have hmem : (⟨x.1, (hmemW x.1).mpr x.2.2⟩ : W) -
        ⟨y.1, (hmemW y.1).mpr y.2.2⟩ ∈ A := (Submodule.Quotient.eq A).mp hxy
    have hmemV : x.1 - y.1 ∈ Submodule.span K {a} := by
      rw [hA, Submodule.mem_comap] at hmem
      exact hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmemV
    have hxy' : x.1 = y.1 + c • a := by
      rw [hc]
      abel
    have hcross : polar Q y.1 (c • a) = 0 := by
      rw [polar_smul_right, smul_eq_mul, polar_comm Q y.1 a, (hmemW y.1).mp y.2.2, mul_zero]
    have hQ : (1 : K) = 1 + c * c := by
      calc (1 : K) = Q x.1 := x.2.1.symm
        _ = Q (y.1 + c • a) := by rw [hxy']
        _ = Q y.1 + Q (c • a) + polar Q y.1 (c • a) := map_add_eq Q _ _
        _ = 1 + c * c := by
          rw [y.2.1, QuadraticMap.map_smul, smul_eq_mul, ha1, mul_one, hcross, add_zero]
    have hcc : c * c = 0 := by
      have h1 : (1 : K) + c * c = 1 + 0 := by
        rw [add_zero]
        exact hQ.symm
      exact add_left_cancel h1
    have hc0 : c = 0 := by
      apply CharTwo.sq_inj.mp
      simpa [pow_two] using hcc
    exact Subtype.ext (by rw [hxy', hc0, zero_smul, add_zero])
  have hsurj : Function.Surjective F := by
    intro q
    set w : W := Quotient.out q with hw
    let ρ : K ≃+* K := (frobeniusEquiv K 2).symm
    have hρ : ∀ t : K, ρ t ^ 2 = t := fun t => frobeniusEquiv_symm_pow_p K 2 t
    let lam : K := ρ (1 + Q (w : V))
    have hlam : lam ^ 2 = 1 + Q (w : V) := hρ _
    have hcross : polar Q (w : V) (lam • a) = 0 := by
      rw [polar_smul_right, smul_eq_mul, polar_comm Q (w : V) a, (hmemW (w : V)).mp w.2,
        mul_zero]
    have hQx : Q ((w : V) + lam • a) = 1 := by
      rw [map_add_eq, QuadraticMap.map_smul, smul_eq_mul, ha1, mul_one, hcross, add_zero,
        ← pow_two, hlam]
      rw [add_comm (1 : K) (Q (w : V)), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hpolx : polar Q a ((w : V) + lam • a) = 0 := by
      rw [polar_add_right, polar_smul_right, smul_eq_mul, (hmemW (w : V)).mp w.2,
        polar_self_eq_zero, mul_zero, add_zero]
    let x : {x : V // Q x = 1 ∧ polar Q a x = 0} :=
      ⟨(w : V) + lam • a, hQx, hpolx⟩
    refine ⟨x, ?_⟩
    have hcls : F x = Submodule.Quotient.mk w := by
      apply (Submodule.Quotient.eq A).mpr
      rw [hA, Submodule.mem_comap, Submodule.mem_span_singleton]
      refine ⟨lam, ?_⟩
      change lam • a = ((w : V) + lam • a) - (w : V)
      abel
    rw [hcls, hw, Submodule.Quotient.mk_out]
  have hbij : Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0} = Nat.card (W ⧸ A) :=
    Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  rw [hbij, hcardQ]

theorem w85g_even_card_level {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    (hd : 4 ≤ finrank K V) {a : V} (ha1 : Q a = 1) :
    Even (Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0}) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [w85g_natCard_level hQ ha1]
  have hKeven : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
  exact Even.pow_of_ne_zero hKeven (by omega)

theorem w85g_even_card_map_eq_one {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    (hd : 4 ≤ finrank K V) : Even (Nat.card {x : V // Q x = 1}) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  obtain ⟨a, ha1⟩ := w85g_exists_map_eq_one hQ hd
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha1
    exact zero_ne_one ha1
  haveI : Invertible (Q a) := invertibleOfNonzero (by rw [ha1]; exact one_ne_zero)
  let r : V ≃ₗ[K] V := TauCeti.QuadraticMap.reflection Q a
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hrr : r * r = 1 := TauCeti.QuadraticMap.reflection_mul_self Q a
  have hr_apply : ∀ y : V, r y = y + polar Q a y • a := by
    intro y
    have hinv : (⅟(Q a) : K) = 1 := by rw [invOf_eq_inv, ha1, inv_one]
    rw [TauCeti.QuadraticMap.reflection_apply, hinv, one_mul, sub_eq_add_vec K]
  have hr_fix_iff : ∀ y : V, r y = y ↔ polar Q a y = 0 := by
    intro y
    rw [hr_apply]
    constructor
    · intro h
      have h2 : polar Q a y • a = 0 := add_left_cancel (h.trans (add_zero y).symm)
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 ha0
    · intro h
      rw [h, zero_smul, add_zero]
  let S := {x : V // Q x = 1}
  let f : Function.End S :=
    fun x => ⟨r x.1, by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hrO]
      exact x.2⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    show f ^ 2 = 1
    funext x
    apply Subtype.ext
    show r (r x.1) = x.1
    rw [← LinearEquiv.mul_apply, hrr, LinearEquiv.coe_one, id]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) (f := f) (p := 2) (n := 1) hf2
  have hfix_card : Nat.card f.fixedPoints = Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0} := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact (hr_fix_iff x.1.1).mp (congrArg Subtype.val x.2)
    · apply Subtype.ext
      exact (hr_fix_iff y.1).mpr y.2.2
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      rfl
    · intro y
      apply Subtype.ext
      rfl
  have hmod' : Nat.card S ≡ Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0} [MOD 2] := by
    have h1 : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
    rw [h1, ← hfix_card]
    rw [show Nat.card f.fixedPoints = Fintype.card f.fixedPoints from Nat.card_eq_fintype_card]
    exact hmod
  have hT : Even (Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0}) :=
    w85g_even_card_level hQ hd ha1
  rw [Nat.even_iff] at hT ⊢
  have hmod'' : Nat.card S % 2 = Nat.card {x : V // Q x = 1 ∧ polar Q a x = 0} % 2 := hmod'
  exact hmod''.trans hT

end Orth

end CFSG.LocalAnalysis.WeakClosure81

end
