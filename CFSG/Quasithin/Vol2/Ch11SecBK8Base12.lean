module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base11
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

abbrev vL (u : Fin 3 → K) : I6 → K := Sum.elim u 0

abbrev vR (u : Fin 3 → K) : I6 → K := Sum.elim 0 u

theorem dg_fix_iff (A : GL (Fin 3) K) (v : I6 → K) :
    toAddMap (matAut (dgHom A)) v = v ↔
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inl) = v ∘ Sum.inl ∧
        (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inr) = v ∘ Sum.inr := by
  rw [toAddMap_matAut, dgHom_mulVec]
  constructor
  · intro h
    exact ⟨by funext j; exact congrFun h (Sum.inl j), by funext j; exact congrFun h (Sum.inr j)⟩
  · rintro ⟨h1, h2⟩
    funext i
    rcases i with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i

theorem mem_dgSub_of_fix [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) {f : Fin 3 → K}
    (hf : f ≠ 0) (h1 : ∀ c : K, toAddMap x (vL (c • f)) = vL (c • f))
    (h2 : ∀ c : K, toAddMap x (vR (c • f)) = vR (c • f)) : x ∈ dgSub K := by
  obtain ⟨σ, Φ, M, hΦ, hxf⟩ := exists_semilinear_tens hx
  have comp : ∀ (v : I6 → K) (u₁ u₂ : Fin 3 → K), toAddMap x v = Sum.elim u₁ u₂ →
      toAddMap Φ (M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr)) = u₁ ∧
        toAddMap Φ (M 1 0 • (v ∘ Sum.inl) + M 1 1 • (v ∘ Sum.inr)) = u₂ := by
    intro v u₁ u₂ h
    rw [hxf] at h
    exact ⟨by funext j; exact congrFun h (Sum.inl j), by funext j; exact congrFun h (Sum.inr j)⟩
  have e1 : ∀ c : K, toAddMap Φ (M 0 0 • c • f) = c • f ∧ toAddMap Φ (M 1 0 • c • f) = 0 := by
    intro c
    have h := comp _ _ _ (h1 c)
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_zero, add_zero] using h
  have e2 : ∀ c : K, toAddMap Φ (M 0 1 • c • f) = 0 ∧ toAddMap Φ (M 1 1 • c • f) = c • f := by
    intro c
    have h := comp _ _ _ (h2 c)
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_zero, zero_add] using h
  have hzero : ∀ m : K, toAddMap Φ (m • (1 : K) • f) = 0 → m = 0 := by
    intro m hm
    rw [toAddMap_eq_zero_iff, one_smul] at hm
    exact (smul_eq_zero.mp hm).resolve_right hf
  have h10 : M 1 0 = 0 := hzero _ (e1 1).2
  have h01 : M 0 1 = 0 := hzero _ (e2 1).1
  have hdiag : M 0 0 = M 1 1 := by
    have h3 : toAddMap Φ (M 0 0 • (1 : K) • f) = toAddMap Φ (M 1 1 • (1 : K) • f) :=
      (e1 1).1.trans (e2 1).2.symm
    have h4 := congrArg (toAddMap Φ⁻¹) h3
    rw [toAddMap_apply_inv, toAddMap_apply_inv, one_smul, ← sub_eq_zero, ← sub_smul] at h4
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hf)
  have hσ : σ = RingEquiv.refl K := by
    refine RingEquiv.ext fun c => ?_
    have h3 := (e1 c).1
    rw [smul_comm, hΦ, (by simpa only [one_smul] using (e1 1).1 : toAddMap Φ (M 0 0 • f) = f)]
      at h3
    rw [← sub_eq_zero, ← sub_smul] at h3
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hf)
  subst hσ
  obtain ⟨A₀, rfl⟩ := exists_matAut_of_mem_linSub (show Φ ∈ linSub from hΦ)
  obtain ⟨g, hg⟩ := exists_dg_of_scalar (x := x) (A₀ := A₀) (β := M 0 0) fun v => by
    rw [hxf, h01, h10, ← hdiag, zero_smul, zero_smul, add_zero, zero_add]
    rfl
  rw [hg]
  exact matAut_dgHom_mem_dgSub g

theorem exists_fix_vec [Finite K] {n : ℕ} (hn : n ≠ 0) (hK : Nat.card K = 2 ^ n)
    {D : Subgroup (MulAut (W6 K))} (hD : D ≤ dgSub K) (h2 : ∀ x ∈ D, x ^ 2 = 1) :
    ∃ f : Fin 3 → K, f ≠ 0 ∧ ∀ x ∈ D, ∀ c : K,
      toAddMap x (vL (c • f)) = vL (c • f) ∧
        toAddMap x (vR (c • f)) = vR (c • f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥D := fun x => ⟨1, Subtype.ext (by simpa using h2 x.1 x.2)⟩
  have hmod := card_modEq_card_fixV hP
  rw [card_stdMod, card_I6, hK, ← pow_mul] at hmod
  have hev : 2 ∣ Nat.card ↥(fixV D) := by
    have h3 : 2 ∣ 2 ^ (n * 6) := dvd_pow_self 2 (by positivity)
    exact (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3)))
  have hne : fixV D ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hev
    exact absurd hev (by norm_num)
  obtain ⟨v, hv, hv1⟩ := (fixV D).bot_or_exists_ne_one.resolve_left hne
  have hcomp : Multiplicative.toAdd v ∘ Sum.inl ≠ 0 ∨ Multiplicative.toAdd v ∘ Sum.inr ≠ 0 := by
    by_contra h
    push Not at h
    apply hv1
    apply Multiplicative.toAdd.injective
    funext i
    rcases i with i | i
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hfixA : ∀ x ∈ D, ∃ A : GL (Fin 3) K, x = matAut (dgHom A) ∧
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (Multiplicative.toAdd v ∘ Sum.inl) =
        Multiplicative.toAdd v ∘ Sum.inl ∧
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (Multiplicative.toAdd v ∘ Sum.inr) =
        Multiplicative.toAdd v ∘ Sum.inr := by
    intro x hx
    obtain ⟨A, rfl⟩ := hD hx
    refine ⟨A, rfl, (dg_fix_iff A _).mp ?_⟩
    exact congrArg Multiplicative.toAdd (hv _ hx)
  have key : ∀ f : Fin 3 → K, (∀ x ∈ D, ∃ A : GL (Fin 3) K, x = matAut (dgHom A) ∧
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ f = f) → ∀ x ∈ D, ∀ c : K,
      toAddMap x (vL (c • f)) = vL (c • f) ∧
        toAddMap x (vR (c • f)) = vR (c • f) := by
    intro f hf x hx c
    obtain ⟨A, rfl, hA⟩ := hf x hx
    constructor
    · rw [dg_fix_iff, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_smul, hA,
        Matrix.mulVec_zero]
      exact ⟨rfl, rfl⟩
    · rw [dg_fix_iff, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_smul, hA,
        Matrix.mulVec_zero]
      exact ⟨rfl, rfl⟩
  rcases hcomp with h | h
  · refine ⟨_, h, key _ fun x hx => ?_⟩
    obtain ⟨A, hA, h1, -⟩ := hfixA x hx
    exact ⟨A, hA, h1⟩
  · refine ⟨_, h, key _ fun x hx => ?_⟩
    obtain ⟨A, hA, -, h2⟩ := hfixA x hx
    exact ⟨A, hA, h2⟩

theorem fixV_bot_eq : fixV (⊥ : Subgroup (MulAut (W6 K))) = ⊤ :=
  eq_top_iff.mpr fun v _ x hx => by rw [Subgroup.mem_bot.mp hx]; rfl

theorem eq_bot_of_fixV_eq_top {A : Subgroup (MulAut (W6 K))} (h : fixV A = ⊤) : A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun v => (h ▸ Subgroup.mem_top v : v ∈ fixV A) x hx

theorem offender_model [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {Y A : Subgroup (MulAut (W6 K))} (hY : Y ≤ normD K) (hA : A ∈ E3.aSet (2 * n) Y) :
    A ≤ dgSub K ∧ Nat.card A = Nat.card K ^ 2 := by
  obtain ⟨hAY, hA0, hAe, hAs⟩ := hA
  have hAN : A ≤ normD K := hAY.trans hY
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  have hP : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x.1 x.2)⟩
  set D₀ := A ⊓ dgSub K with hD₀
  have hEl : IsElemAbelian2 (A ⊓ linSub) :=
    ⟨fun a ha b hb => hAe.1 a ha.1 b hb.1, fun a ha => hAe.2 a ha.1⟩
  have h1 := card_le_two_mul_lin (by omega) hK hAN hAe.2
  have h2 := card_lin_le (by omega) hK (inf_le_left.trans hAN) inf_le_right hEl
  rw [inf_assoc, inf_eq_right.mpr dgSub_le_linSub] at h2
  have hrel := Subgroup.relIndex_mul_card (H := D₀) (K := A)
  rw [inf_eq_left.mpr (inf_le_left : D₀ ≤ A), E3.relIndex_eq_two_pow hP] at hrel
  have hm : E3.mQuot A D₀ < 2 * n := by
    have h3 : 2 ^ E3.mQuot A D₀ * Nat.card ↥D₀ ≤ 2 ^ (n + 1) * Nat.card ↥D₀ := by
      rw [hrel, pow_succ, ← hK, mul_comm (Nat.card K) 2, mul_assoc]
      exact h1.trans (Nat.mul_le_mul_left 2 h2)
    have h4 := Nat.le_of_mul_le_mul_right h3 Nat.card_pos
    have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
    omega
  have hfix : fixV D₀ = fixV A := hAs D₀ inf_le_left hm
  obtain ⟨f, hf, hfD⟩ := exists_fix_vec (by omega) hK (inf_le_right : D₀ ≤ dgSub K)
    fun x hx => hAe.2 x hx.1
  have hfA : ∀ x ∈ A, ∀ c : K, toAddMap x (vL (c • f)) = vL (c • f) ∧
      toAddMap x (vR (c • f)) = vR (c • f) := by
    intro x hx c
    have hv1 : Multiplicative.ofAdd (vL (c • f)) ∈ fixV D₀ := fun y hy =>
      congrArg Multiplicative.ofAdd (hfD y hy c).1
    have hv2 : Multiplicative.ofAdd (vR (c • f)) ∈ fixV D₀ := fun y hy =>
      congrArg Multiplicative.ofAdd (hfD y hy c).2
    rw [hfix] at hv1 hv2
    exact ⟨congrArg Multiplicative.toAdd (hv1 x hx), congrArg Multiplicative.toAdd (hv2 x hx)⟩
  have hAD : A ≤ dgSub K := fun x hx =>
    mem_dgSub_of_fix (hAN hx) hf (fun c => (hfA x hx c).1) (fun c => (hfA x hx c).2)
  refine ⟨hAD, le_antisymm ?_ ?_⟩
  · have := card_dg_le hAe
    rwa [inf_eq_left.mpr hAD] at this
  ·
    by_contra hlt
    push Not at hlt
    have hm0 : E3.mQuot A ⊥ < 2 * n := by
      have h3 := E3.relIndex_eq_two_pow hP ⊥
      rw [Subgroup.relIndex_bot_left] at h3
      rw [h3, hK, ← pow_mul] at hlt
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
      omega
    have h3 := hAs ⊥ bot_le hm0
    rw [fixV_bot_eq] at h3
    exact hA0 (eq_bot_of_fixV_eq_top h3.symm)

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
