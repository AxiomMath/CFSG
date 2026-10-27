module

public import CFSG.Walter.ReeOrder.Ward.CharTools
public import CFSG.Walter.ReeOrder.Ward.FSCount
public import CFSG.Walter.ReeOrder.Ward.Values

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

variable {G : Type} [Group G] [Fintype G]

theorem inner_conj_left {L : Type} [Group L] [Fintype L] (f Φ : L → ℂ) :
    BlocksInnerProduct (starRingEnd ℂ ∘ f) Φ =
      starRingEnd ℂ (BlocksInnerProduct f (starRingEnd ℂ ∘ Φ)) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

theorem nu_conj {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : nu (starRingEnd ℂ ∘ χ) = nu χ := by
  have h1 : fsIndicator (starRingEnd ℂ ∘ χ) = starRingEnd ℂ (fsIndicator χ) := by
    unfold fsIndicator
    rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
    rfl
  have h2 : starRingEnd ℂ (fsIndicator χ) = fsIndicator χ := by
    rcases (fsIndicator_spec hχ).1 with h | h | h <;> rw [h] <;> simp
  have h3 := nu_spec (irr_conj hχ)
  rw [h1, h2, ← nu_spec hχ] at h3
  exact_mod_cast h3

theorem deg_conj {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : deg (starRingEnd ℂ ∘ χ) = deg χ := by
  have h : ((deg (starRingEnd ℂ ∘ χ) : ℤ) : ℂ) = ((deg χ : ℤ) : ℂ) := by
    rw [deg_eq (irr_conj hχ), deg_eq hχ, Function.comp_apply, conj_one hχ]
  exact_mod_cast h

theorem nu_pow {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {k : ℕ} (hk : (Nat.card G).Coprime k) :
    nu (fun g => χ (g ^ k)) = nu χ := by
  have h1 : fsIndicator (fun g => χ (g ^ k)) = fsIndicator χ := by
    unfold fsIndicator
    congr 1
    refine Fintype.sum_equiv (powCoprime hk) _ _ fun g => ?_
    simp only [powCoprime_apply]
    rw [(Commute.refl g).mul_pow]
  have h3 := nu_spec (irr_pow hχ hk)
  rw [h1, ← nu_spec hχ] at h3
  exact_mod_cast h3

theorem deg_pow {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {k : ℕ} (hk : (Nat.card G).Coprime k) :
    deg (fun g => χ (g ^ k)) = deg χ := by
  have h : ((deg (fun g => χ (g ^ k)) : ℤ) : ℂ) = ((deg χ : ℤ) : ℂ) := by
    rw [deg_eq (irr_pow hχ hk), deg_eq hχ, one_pow]
  exact_mod_cast h

namespace WardSetup

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (S : WardSetup G L q e)

theorem σ_conj (χ : G → ℂ) : S.σ (starRingEnd ℂ ∘ χ) = starRingEnd ℂ ∘ S.σ χ := rfl

theorem conjΦ1 : starRingEnd ℂ ∘ S.W.Φ1 = S.W.Φ1 := by
  funext y
  have h := congrFun S.W.conj_θ4 y
  simp only [Function.comp_apply] at h
  simp only [WardL.Φ1, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, map_sub, map_mul, map_one, map_intCast, h]

theorem conjΦ2 : starRingEnd ℂ ∘ S.W.Φ2 = if e = -1 then S.W.Φ3 else S.W.Φ2 := by
  funext y
  have h2 := congrFun S.W.conj_θ2 y
  have h4 := congrFun S.W.conj_θ4 y
  simp only [Function.comp_apply] at h2 h4
  by_cases he : e = -1
  · rw [ite_eq_left he] at h2 ⊢
    simp only [WardL.Φ2, WardL.Φ3, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_mul, map_neg, map_add, map_intCast, h2, h4]
  · rw [ite_eq_right he] at h2 ⊢
    simp only [WardL.Φ2, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_mul, map_neg, map_add, map_intCast, h2, h4]

theorem conjΦ3 : starRingEnd ℂ ∘ S.W.Φ3 = if e = -1 then S.W.Φ2 else S.W.Φ3 := by
  funext y
  have h3 := congrFun S.W.conj_θ3 y
  have h4 := congrFun S.W.conj_θ4 y
  simp only [Function.comp_apply] at h3 h4
  by_cases he : e = -1
  · rw [ite_eq_left he] at h3 ⊢
    simp only [WardL.Φ2, WardL.Φ3, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_mul, map_neg, map_add, map_intCast, h3, h4]
  · rw [ite_eq_right he] at h3 ⊢
    simp only [WardL.Φ3, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_mul, map_neg, map_add, map_intCast, h3, h4]

theorem conj_d1 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.d1 (starRingEnd ℂ ∘ χ) = S.d1 χ := by
  have h := S.inner_Φ1 (irr_conj hχ)
  rw [S.σ_conj, inner_conj_left, S.conjΦ1, S.inner_Φ1 hχ, map_intCast] at h
  exact_mod_cast h.symm

theorem conj_d2 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    S.d2 (starRingEnd ℂ ∘ χ) = if e = -1 then S.d3 χ else S.d2 χ := by
  have h := S.inner_Φ2 (irr_conj hχ)
  rw [S.σ_conj, inner_conj_left, S.conjΦ2] at h
  by_cases he : e = -1
  · rw [ite_eq_left he] at h ⊢
    rw [S.inner_Φ3 hχ, map_intCast] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right he] at h ⊢
    rw [S.inner_Φ2 hχ, map_intCast] at h
    exact_mod_cast h.symm

theorem conj_d3 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    S.d3 (starRingEnd ℂ ∘ χ) = if e = -1 then S.d2 χ else S.d3 χ := by
  have h := S.inner_Φ3 (irr_conj hχ)
  rw [S.σ_conj, inner_conj_left, S.conjΦ3] at h
  by_cases he : e = -1
  · rw [ite_eq_left he] at h ⊢
    rw [S.inner_Φ2 hχ, map_intCast] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right he] at h ⊢
    rw [S.inner_Φ3 hχ, map_intCast] at h
    exact_mod_cast h.symm

noncomputable def kg : ℕ :=
  (S.W.galois (2 * Nat.card G * Nat.card L)
    (Nat.mul_pos (Nat.mul_pos two_pos Nat.card_pos) Nat.card_pos)).choose

theorem kg_spec : (S.kg).Coprime (2 * Nat.card G * Nat.card L) ∧
    (fun y => S.W.θ2 (y ^ S.kg)) = S.W.θ3 ∧ (fun y => S.W.θ3 (y ^ S.kg)) = S.W.θ2 ∧
    (fun y => S.W.θ4 (y ^ S.kg)) = S.W.θ4 :=
  (S.W.galois (2 * Nat.card G * Nat.card L)
    (Nat.mul_pos (Nat.mul_pos two_pos Nat.card_pos) Nat.card_pos)).choose_spec

theorem kg_cop_G : (Nat.card G).Coprime S.kg :=
  (Nat.Coprime.coprime_dvd_right (⟨2 * Nat.card L, by ring⟩ : Nat.card G ∣
    2 * Nat.card G * Nat.card L) S.kg_spec.1).symm

theorem kg_cop_L : (Nat.card L).Coprime S.kg :=
  (Nat.Coprime.coprime_dvd_right (⟨2 * Nat.card G, by ring⟩ : Nat.card L ∣
    2 * Nat.card G * Nat.card L) S.kg_spec.1).symm

theorem kg_odd : Odd S.kg := by
  have h := Nat.Coprime.coprime_dvd_right (⟨Nat.card G * Nat.card L, by ring⟩ : 2 ∣
    2 * Nat.card G * Nat.card L) S.kg_spec.1
  exact Nat.odd_iff.mpr (Nat.coprime_two_right.mp h |> Nat.odd_iff.mp)

@[expose] noncomputable def pw (χ : G → ℂ) : G → ℂ := fun g => χ (g ^ S.kg)

theorem pw_mem {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.pw χ ∈ BlocksIrr G :=
  irr_pow hχ S.kg_cop_G

theorem σ_pw (χ : G → ℂ) (y : L) : S.σ (S.pw χ) y = S.σ χ (y ^ S.kg) := by
  simp only [σ, pw, map_pow]
  rw [(S.commJ y).mul_pow]
  obtain ⟨m, hm⟩ := S.kg_odd
  rw [hm, pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul]

theorem inner_pw (f Φ Ψ : L → ℂ) (hΦΨ : ∀ y, Ψ (y ^ S.kg) = Φ y) :
    BlocksInnerProduct (fun y => f (y ^ S.kg)) Φ = BlocksInnerProduct f Ψ := by
  unfold BlocksInnerProduct
  congr 1
  refine Fintype.sum_equiv (powCoprime S.kg_cop_L) _ _ fun y => ?_
  simp only [powCoprime_apply, ← hΦΨ y]

theorem Φ1_pw (y : L) : S.W.Φ1 (y ^ S.kg) = S.W.Φ1 y := by
  have h4 := congrFun S.kg_spec.2.2.2 y
  simp [WardL.Φ1, h4]

theorem Φ3_pw (y : L) : S.W.Φ3 (y ^ S.kg) = S.W.Φ2 y := by
  have h3 := congrFun S.kg_spec.2.2.1 y
  have h4 := congrFun S.kg_spec.2.2.2 y
  simp [WardL.Φ2, WardL.Φ3, h3, h4]

theorem Φ2_pw (y : L) : S.W.Φ2 (y ^ S.kg) = S.W.Φ3 y := by
  have h2 := congrFun S.kg_spec.2.1 y
  have h4 := congrFun S.kg_spec.2.2.2 y
  simp [WardL.Φ2, WardL.Φ3, h2, h4]

theorem pw_d1 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.d1 (S.pw χ) = S.d1 χ := by
  have h := S.inner_Φ1 (S.pw_mem hχ)
  rw [show S.σ (S.pw χ) = fun y => S.σ χ (y ^ S.kg) from funext (S.σ_pw χ),
    S.inner_pw _ _ _ S.Φ1_pw, S.inner_Φ1 hχ] at h
  exact_mod_cast h.symm

theorem pw_d2 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.d2 (S.pw χ) = S.d3 χ := by
  have h := S.inner_Φ2 (S.pw_mem hχ)
  rw [show S.σ (S.pw χ) = fun y => S.σ χ (y ^ S.kg) from funext (S.σ_pw χ),
    S.inner_pw _ _ _ S.Φ3_pw, S.inner_Φ3 hχ] at h
  exact_mod_cast h.symm

theorem pw_d3 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.d3 (S.pw χ) = S.d2 χ := by
  have h := S.inner_Φ3 (S.pw_mem hχ)
  rw [show S.σ (S.pw χ) = fun y => S.σ χ (y ^ S.kg) from funext (S.σ_pw χ),
    S.inner_pw _ _ _ S.Φ2_pw, S.inner_Φ2 hχ] at h
  exact_mod_cast h.symm

theorem pw_deg {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : deg (S.pw χ) = deg χ := deg_pow hχ S.kg_cop_G

theorem pw_nu {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : nu (S.pw χ) = nu χ := nu_pow hχ S.kg_cop_G

namespace EtaData

variable {S} (D : S.EtaData)

theorem conj_z {χ : G → ℂ} (h : χ ∈ D.NE) (h' : starRingEnd ℂ ∘ χ ∈ D.NE) :
    z (S := S) (starRingEnd ℂ ∘ χ) = z (S := S) χ := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have h1 := D.τ_NE h' hr hr1
  rw [Function.comp_apply, D.τ_NE h hr hr1, map_intCast] at h1
  exact_mod_cast h1.symm

theorem pw_z {χ : G → ℂ} (h : χ ∈ D.NE) (h' : S.pw χ ∈ D.NE) :
    z (S := S) (S.pw χ) = z (S := S) χ := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have h1 := D.τ_NE h' hr hr1
  have hrk : r ^ S.kg ∈ S.W.Ro := Subgroup.pow_mem _ hr _
  have hrk1 : r ^ S.kg ≠ 1 := by
    intro h1'
    apply hr1
    have hinj := (powCoprime S.kg_cop_L).injective
    apply hinj
    simp only [powCoprime_apply, one_pow]
    exact h1'
  rw [pw, ← map_pow, D.τ_NE h hrk hrk1] at h1
  exact_mod_cast h1.symm

end EtaData

end WardSetup

end CFSG.Walter.Ward
