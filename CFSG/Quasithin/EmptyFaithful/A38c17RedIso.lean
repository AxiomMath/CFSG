module

public import CFSG.Quasithin.EmptyFaithful.A38c17RedLine
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

section Isometry

variable {K : Type} [Field K]

theorem sub_mem_span_of_fixes_isotropic (F : ReflForm K (Fin 3 → K)) {w : Fin 3 → K}
    (hw0 : w ≠ 0) (hww : F.β w w = 0) (T : Module.End K (Fin 3 → K)) (hTw : T w = w)
    (hT : ∀ u x, F.β (T u) (T x) = F.β u x) (hdet : LinearMap.det T = 1) :
    ∀ x, F.β w x = 0 → T x - x ∈ K ∙ w := by
  set W : Submodule K (Fin 3 → K) := K ∙ w
  have hWw : w ∈ W := Submodule.mem_span_singleton_self w
  have hW : F.IsTotallyIsotropic W :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (F.mem_perp_span_singleton.mpr hww)
  have hW1 : Module.finrank K W = 1 := finrank_span_singleton hw0
  have hP2 : Module.finrank K (F.perp W) = 2 := by
    have h1 := F.finrank_perp W
    rw [Module.finrank_fin_fun, hW1] at h1
    omega
  obtain ⟨m, hmP, hmW⟩ := IsConcreteLE.exists_of_lt
    (Submodule.lt_of_le_of_finrank_lt_finrank hW (by omega) : W < F.perp W)
  have hwm : F.β w m = 0 := F.mem_perp_span_singleton.mp hmP
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, F.β w v₀ ≠ 0 := by
    by_contra! h
    exact hw0 (F.nondeg w h)
  have hβ : ∀ a b c : K, F.β w (a • w + b • m + c • v₀) = c * F.β w v₀ := by
    intro a b c
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, F.smul_right, hww, hwm]
    ring
  have hli : LinearIndependent K ![w, m, v₀] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • w + c 1 • m + c 2 • v₀ = 0 := by
      simpa [Fin.sum_univ_three] using hc
    have h2 : c 2 = 0 := by
      have h := hβ (c 0) (c 1) (c 2)
      rw [hc', F.β_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hv₀
    rw [h2, zero_smul, add_zero] at hc'
    have h1 : c 1 = 0 := by
      by_contra h1
      refine hmW ((Submodule.smul_mem_iff W h1).mp ?_)
      rw [eq_neg_of_add_eq_zero_right hc']
      exact W.neg_mem (W.smul_mem _ hWw)
    rw [h1, zero_smul, add_zero] at hc'
    have h0 : c 0 = 0 := (smul_eq_zero.mp hc').resolve_right hw0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 3) K (Fin 3 → K), ∀ i, b i = ![w, m, v₀] i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp),
      fun i => by simp [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  have hb0 : b 0 = w := by simpa using hb 0
  have hb1 : b 1 = m := by simpa using hb 1
  have hb2 : b 2 = v₀ := by simpa using hb 2
  have hcoord : ∀ x, x = b.repr x 0 • w + b.repr x 1 • m + b.repr x 2 • v₀ := by
    intro x
    have h := b.sum_repr x
    rw [Fin.sum_univ_three, hb0, hb1, hb2] at h
    exact h.symm
  have hrep : ∀ x, F.β w x = b.repr x 2 * F.β w v₀ := by
    intro x
    conv_lhs => rw [hcoord x]
    exact hβ _ _ _
  have hperp : ∀ x, F.β w x = 0 → b.repr x 2 = 0 := by
    intro x hx
    have h := hrep x
    rw [hx] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hv₀
  have hA : ∀ i j, LinearMap.toMatrix b b T i j = b.repr (T (b j)) i := fun i j => by
    rw [LinearMap.toMatrix_apply]
  have hTw' : T (b 0) = b 0 := by
    rw [hb0]
    exact hTw
  have hA00 : LinearMap.toMatrix b b T 0 0 = 1 := by simp [hA, hTw']
  have hA10 : LinearMap.toMatrix b b T 1 0 = 0 := by simp [hA, hTw']
  have hA20 : LinearMap.toMatrix b b T 2 0 = 0 := by simp [hA, hTw']
  have hcross : ∀ x, F.β w (T x) = F.β w x := by
    intro x
    have := hT w x
    rwa [hTw] at this
  have hA21 : LinearMap.toMatrix b b T 2 1 = 0 := by
    rw [hA, hb1]
    exact hperp _ (by rw [hcross, hwm])
  have hA22 : LinearMap.toMatrix b b T 2 2 = 1 := by
    rw [hA, hb2]
    have h2 := hrep (T v₀)
    rw [hcross] at h2
    exact mul_right_cancel₀ hv₀ (h2.symm.trans (one_mul _).symm)
  have hdetA : (LinearMap.toMatrix b b T).det = 1 := by
    rw [LinearMap.det_toMatrix]
    exact hdet
  rw [Matrix.det_fin_three, hA00, hA10, hA20, hA21, hA22] at hdetA
  have hA11 : LinearMap.toMatrix b b T 1 1 = 1 := by linear_combination hdetA
  intro x hx
  have hx2 : b.repr x 2 = 0 := hperp x hx
  have hTm2 : b.repr (T m) 2 = 0 := by
    have h := hA21
    rwa [hA, hb1] at h
  have hTm1 : b.repr (T m) 1 = 1 := by
    have h := hA11
    rwa [hA, hb1] at h
  obtain ⟨a, ha⟩ : ∃ a : K, T m = a • w + m := by
    refine ⟨b.repr (T m) 0, ?_⟩
    conv_lhs => rw [hcoord (T m)]
    rw [hTm1, hTm2, zero_smul, add_zero, one_smul]
  obtain ⟨r0, r1, hxr⟩ : ∃ r0 r1 : K, x = r0 • w + r1 • m := by
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    conv_lhs => rw [hcoord x]
    rw [hx2, zero_smul, add_zero]
  have e : T x - x = (r1 * a) • w := by
    rw [hxr, map_add, map_smul, map_smul, hTw, ha]
    module
  rw [e]
  exact W.smul_mem _ hWw

theorem fin_three_eq_zero_of_forall_mulVec_eq_zero {B : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ x, B *ᵥ x = 0) : B = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  simp [h]

theorem sub_one_pow_three_eq_zero_of_fixes_isotropic (F : ReflForm K (Fin 3 → K))
    {v : Fin 3 → K} (hv : v ≠ 0) (hvv : F.β v v = 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ u w, F.β (A *ᵥ u) (A *ᵥ w) = F.β u w) (hdet : A.det = 1) (hAv : A *ᵥ v = v) :
    (A - 1) ^ 3 = 0 := by
  have hcross : ∀ x, F.β v (A *ᵥ x) = F.β v x := by
    intro x
    have := hA v x
    rwa [hAv] at this
  have hsub := sub_mem_span_of_fixes_isotropic F hv hvv (Matrix.toLin' A)
    (by rw [Matrix.toLin'_apply]; exact hAv)
    (fun u x => by simpa only [Matrix.toLin'_apply] using hA u x)
    (by rw [LinearMap.det_toLin']; exact hdet)
  have hN : ∀ x, (A - 1) *ᵥ x = A *ᵥ x - x := fun x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hN1 : ∀ x, F.β v ((A - 1) *ᵥ x) = 0 := by
    intro x
    rw [hN, F.β_sub_right, hcross, sub_self]
  have hN2 : ∀ x, F.β v x = 0 → (A - 1) *ᵥ x ∈ K ∙ v := by
    intro x hx
    rw [hN]
    simpa only [Matrix.toLin'_apply] using hsub x hx
  have hN3 : ∀ w ∈ K ∙ v, (A - 1) *ᵥ w = 0 := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, hN, hAv, sub_self, smul_zero]
  apply fin_three_eq_zero_of_forall_mulVec_eq_zero
  intro x
  rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hN3 _ (hN2 _ (hN1 _))

theorem pow_prime_eq_one_of_sub_one_pow_three_eq_zero {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {A : Matrix (Fin 3) (Fin 3) K} (hA : (A - 1) ^ 3 = 0) : A ^ p = 1 := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h1 : (A - 1) ^ p = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp3
    rw [pow_add, hA, zero_mul]
  calc A ^ p = (1 + (A - 1)) ^ p := by rw [add_sub_cancel]
    _ = 1 ^ p + (A - 1) ^ p := add_pow_char_of_commute p (Commute.one_left _)
    _ = 1 := by rw [h1, one_pow, add_zero]

end Isometry

section Unitary

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem su3_pow_eq_one_of_fixes_isotropic (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2)
    {v : Fin 3 → K} (hv : v ≠ 0) (hiso : ∑ i, v i ^ p * v i = 0) {g : ↥(StatedSU 3 p K)}
    (hgv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) : g ^ p = 1 := by
  have hvv : (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).β v v = 0 := by
    rw [unitaryForm_β]
    simpa only [unitaryInvolution_apply, pow_one] using hiso
  have hN := sub_one_pow_three_eq_zero_of_fixes_isotropic
    (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3) hv hvv (su3_preserves_form hK g.2)
    (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU g.2) hgv
  have hpow := pow_prime_eq_one_of_sub_one_pow_three_eq_zero hp2 hN
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hpow]
  rfl

omit [Fact p.Prime] [Finite K] [CharP K p] in
theorem su3_exists_lineChar (M : Subgroup ↥(StatedSU 3 p K)) {v : Fin 3 → K} (hv : v ≠ 0)
    (hvM : ∀ g ∈ M, ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v) :
    ∃ χ : M →* Kˣ, ∀ g : M,
      (((g : ↥(StatedSU 3 p K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
        (χ g : K) • v := by
  choose c hc using fun g : M => hvM g g.2
  have hinj : ∀ a b : K, a • v = b • v → a = b := fun a b h => smul_left_injective K hv h
  let χ0 : M →* K :=
    { toFun := c
      map_one' := by
        apply hinj
        rw [← hc 1, one_smul]
        simp
      map_mul' := fun g h => by
        apply hinj
        rw [← hc (g * h)]
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [← Matrix.mulVec_mulVec, hc h, Matrix.mulVec_smul, hc g, smul_smul, mul_comm] }
  exact ⟨χ0.toHomUnits, fun g => hc g⟩

theorem su3_isotropic_even_index (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(StatedSU 3 p K)) {v : Fin 3 → K} (hv : v ≠ 0)
    (hvM : ∀ g ∈ M, ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v)
    (hiso : ∑ i, v i ^ p * v i = 0) : ¬ Odd M.index := by
  intro hodd
  obtain ⟨χ, hχ⟩ := su3_exists_lineChar M hv hvM
  have hker : IsPGroup p χ.ker := by
    intro x
    refine ⟨1, ?_⟩
    have hx : χ (x : M) = 1 := x.2
    have hfix : (((((x : M) : ↥(StatedSU 3 p K)) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        v = v := by
      rw [hχ, hx, Units.val_one, one_smul]
    have h1 := su3_pow_eq_one_of_fixes_isotropic hp2 hK hv hiso hfix
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hMcard : Nat.card M = p ^ n * Nat.card χ.range := by
    rw [← hn, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange : Nat.card χ.range ∣ p ^ 2 - 1 := by
    have h := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_units, hK] at h
  obtain ⟨b, hb⟩ := hrange
  have hΓ : Nat.card ↥(StatedSU 3 p K) = p ^ 3 * (p ^ 2 - 1) * (p ^ 3 + 1) := by
    have h := CFSG.SectionRank.OddCover.card_statedSU_three (p := p) (f := 1)
      (su3_card_eq_pow_one_sq hK)
    rwa [pow_one] at h
  have hmul := Subgroup.card_mul_index M
  rw [hΓ, hMcard, hb] at hmul
  have hpos : 0 < Nat.card χ.range := Nat.card_pos
  have hcancel : p ^ n * M.index = p ^ 3 * b * (p ^ 3 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card χ.range * (p ^ n * M.index) = p ^ n * Nat.card χ.range * M.index := by ring
      _ = p ^ 3 * (Nat.card χ.range * b) * (p ^ 3 + 1) := hmul
      _ = Nat.card χ.range * (p ^ 3 * b * (p ^ 3 + 1)) := by ring
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hL : Odd (p ^ n * M.index) := (hpodd.pow).mul hodd
  have hR : Even (p ^ 3 * b * (p ^ 3 + 1)) := (hpodd.pow.add_one).mul_left _
  rw [hcancel] at hL
  exact (Nat.not_even_iff_odd.mpr hL) hR

end Unitary

end CFSG.Quasithin.A38c17
