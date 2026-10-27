module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

private theorem dotProduct_eq_zero_of_vecMulVec_involution {K : Type} [Field K] [CharP K 2]
    {m : ℕ} {u f : Fin m → K} (hu : u ≠ 0)
    (h : (1 + Matrix.vecMulVec u f) * (1 + Matrix.vecMulVec u f) = 1) :
    f ⬝ᵥ u = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (funext hcon)
  have hA2 : Matrix.vecMulVec u f + Matrix.vecMulVec u f = 0 := by
    ext i k
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  have hAA : Matrix.vecMulVec u f * Matrix.vecMulVec u f =
      (f ⬝ᵥ u) • Matrix.vecMulVec u f := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i k
    simp [Matrix.vecMulVec_apply, mul_left_comm]
  have hexp : (1 + Matrix.vecMulVec u f) * (1 + Matrix.vecMulVec u f) =
      1 + (Matrix.vecMulVec u f + Matrix.vecMulVec u f) +
        Matrix.vecMulVec u f * Matrix.vecMulVec u f := by
    rw [add_mul, mul_add, mul_add]
    simp only [one_mul, mul_one]
    abel
  have hz : (f ⬝ᵥ u) • Matrix.vecMulVec u f = 0 := by
    have h1 : 1 + (f ⬝ᵥ u) • Matrix.vecMulVec u f = 1 := by
      calc 1 + (f ⬝ᵥ u) • Matrix.vecMulVec u f =
          1 + (Matrix.vecMulVec u f + Matrix.vecMulVec u f) +
            Matrix.vecMulVec u f * Matrix.vecMulVec u f := by
            rw [hA2, hAA]; abel
        _ = (1 + Matrix.vecMulVec u f) * (1 + Matrix.vecMulVec u f) := hexp.symm
        _ = 1 := h
    have h2 : 1 + (f ⬝ᵥ u) • Matrix.vecMulVec u f = 1 + 0 := by simpa using h1
    exact add_left_cancel h2
  by_contra hne
  have hA0 : Matrix.vecMulVec u f = 0 := (smul_eq_zero.mp hz).resolve_left hne
  have hf0 : f = 0 := by
    ext k
    have h1 : Matrix.vecMulVec u f j k = 0 := by rw [hA0, Matrix.zero_apply]
    simp only [Matrix.vecMulVec_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left hj
  rw [hf0] at hne
  simpa using hne

theorem card_le_pow_of_elations {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {X : Subgroup (GL (Fin m) K)} {u : Fin m → K} (hu : u ≠ 0)
    (hX : ∀ g ∈ X, ∀ x, ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u)
    (hX2 : ∀ g ∈ X, g * g = 1) :
    Nat.card X ≤ Nat.card K ^ (m - 1) := by
  classical
  let f : X → Fin m → K := fun g => (exists_vecMulVec_of_sub_smul (hX g.1 g.2)).choose
  have hmat : ∀ g : X, (g.1 : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u (f g) :=
    fun g => (exists_vecMulVec_of_sub_smul (hX g.1 g.2)).choose_spec
  have hf : ∀ g : X, f g ⬝ᵥ u = 0 := by
    intro g
    have hgg : (g.1 : Matrix (Fin m) (Fin m) K) * (g.1 : Matrix (Fin m) (Fin m) K) = 1 := by
      simpa using congrArg (fun x : GL (Fin m) K => (x : Matrix (Fin m) (Fin m) K))
        (hX2 g.1 g.2)
    exact dotProduct_eq_zero_of_vecMulVec_involution hu (by rw [← hmat g]; exact hgg)
  have hF : Function.Injective
      (fun g : X => (⟨f g, hf g⟩ : {f : Fin m → K // f ⬝ᵥ u = 0})) := by
    intro g g' hgg
    have h1 : f g = f g' := congrArg Subtype.val hgg
    apply Subtype.ext
    apply Units.ext
    calc (g.1 : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u (f g) := hmat g
      _ = 1 + Matrix.vecMulVec u (f g') := by rw [h1]
      _ = (g'.1 : Matrix (Fin m) (Fin m) K) := (hmat g').symm
  have hle := Nat.card_le_card_of_injective
    (fun g : X => (⟨f g, hf g⟩ : {f : Fin m → K // f ⬝ᵥ u = 0})) hF
  rwa [card_dotProduct_ker hu] at hle

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.card_LB_le_mul_card_LB_inf_CN (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {m : ℕ}
    (hm : SLMNat hc t m) :
    Nat.card ↥(LB M Q B) ≤ Nat.card Z ^ (m - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  have h5 : Sec5Hyp hc n t := H.toSec5 ht.mem_LB ht.2.2.1
  obtain ⟨m₀, hm₀, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have hSL : SLNat hc t := SLMNat.toSLNat hsl hm₀
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t h5 hSL
  obtain ⟨K, fK, finK, hchar, hKcard, m', hm'2, φ, hker, hSA, -, -, ⟨u, hu, hel⟩, -⟩ :=
    stroth310SLTransv_of_34 h34 G M Q Z B hc n t h5 ht.2.2.2.2 hVQB
  have hm' : m' = m := by
    have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
    have hpow : Nat.card Z ^ (m' + 1) = Nat.card Z ^ (m + 1) :=
      (card_Vt_of_sectionAct (t := t) (φ := φ) hKcard hSA).symm.trans (SLMNat.card_Vt hm)
    have := Nat.pow_right_injective hq hpow
    omega
  have hXle : Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) ≤
      Nat.card K ^ (m' - 1) := by
    refine card_le_pow_of_elations
      (X := ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) (u := u) hu ?_ ?_
    · rintro g ⟨l, hl, rfl⟩ x
      exact hel l (Subgroup.mem_subgroupOf.mp hl) x
    · rintro g ⟨l, hl, rfl⟩
      have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
      have h2CN : (l : G) ^ 2 ∈ hc.CN t :=
        Ctx.Q_le_CN hc ht.mem_LB (hc.sq_mem_Q_of_mem_LB hlL)
      have hll : l * l ∈ φ.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using h2CN)
      show φ l * φ l = 1
      rw [← map_mul]
      exact hll
  rw [hKcard] at hXle
  have hmap := card_inf_mul_card_map (le_Rt (LB M Q B) ht.mem_LB) φ hker
  rw [← hmap, ← hm']
  calc Nat.card ↥(LB M Q B ⊓ hc.CN t) *
        Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ)
      ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (m' - 1) :=
        Nat.mul_le_mul_left _ hXle
    _ = Nat.card Z ^ (m' - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := mul_comm _ _

end CFSG.RankThree.GF2n.Stroth80
