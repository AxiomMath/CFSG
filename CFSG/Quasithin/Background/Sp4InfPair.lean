module

public import CFSG.Quasithin.Background.HSp4A
public import CFSG.Quasithin.Background.Sp4InfRank

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open CFSG.Assembly.LowTwoRank Matrix
open CFSG.Quasithin.H CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_pairMod_sp {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (8 * n) := by
  rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem card_fixV_le_of_involution {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (htN : t ∈ pairNormSp K) (ht : orderOf t = 2) :
    Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 2 ^ (5 * n) := by
  have h := le_rkIdx_fixV_of_involution hn hK htN ht
  rw [SL3Pair.card_eq_two_pow_sub_rkIdx (card_pairMod_sp hK)]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_fixV_le_of_nonlinear {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (htN : t ∈ pairNormSp K) (ht2 : t * t = 1)
    (h1 : (V₁ (Fin 2 ⊕ Fin 2) K).map t.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K)
    (hnl : t ∉ pairSp K) : Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 2 ^ (4 * n) := by
  obtain ⟨a, b, rfl⟩ := exists_pairAut htN h1
  obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp htN
  rw [pairAut_mul] at ht2
  obtain ⟨ha2, hb2⟩ := pairAut_injective (ht2.trans pairAut_one.symm)
  have hslof : ∀ (x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) (C : StatedSp 2 K) (D : K),
      (∀ v, toAddMap x v = D • (((C : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ fun i => σ (v i))) →
      IsSemilinear x σ := by
    intro x C D hxv c v
    rw [hxv, hxv]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
      smul_comm]
  have hsla := hslof a B D₁ ha
  have hslb := hslof b (tauSp B) D₂ hb
  have hσ : σ ≠ RingEquiv.refl K := by
    intro hσ
    subst hσ
    apply hnl
    obtain ⟨C, -, hCe⟩ := eq_pairHom_of_linear htN (by rw [pairAut_mul, ha2, hb2]; rfl) hsla
    rw [hCe]
    exact pairHom_mem_pairImg _ _ C
  have hsl2 : ∀ x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), IsSemilinear x σ → x * x = 1 →
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) K // x v = v} = 2 ^ (2 * n) := by
    intro x hx hx2
    obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two hn hK hx hσ (by rw [sq]; exact hx2)
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    have hW : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (4 * n) := by
      rw [card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul]
      congr 1
      ring
    rw [card_fix_eq_card_fixV, SL3Pair.card_eq_two_pow_sub_rkIdx hW]
    congr 1
    omega
  rw [card_fixV_pairAut, hsl2 a hsla ha2, hsl2 b hslb hb2, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_inf_pairSp_le {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hB2 : IsElemAbelian2 B) :
    Nat.card ↥(B ⊓ pairSp K) ≤ 2 ^ (3 * n) := by
  set f : StatedSp 2 K →* MulAut (PairMod (Fin 2 ⊕ Fin 2) K) :=
    pairHom (StatedSp 2 K) tauSp with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    rw [hf, pairHom_apply, pairHom_apply] at hxy
    exact natAut_injective (StatedSp 2 K) (pairAut_injective hxy).1
  set E : Subgroup (StatedSp 2 K) := (B ⊓ pairSp K).comap f with hE
  have hEmap : E.map f = B ⊓ pairSp K := by
    rw [hE, Subgroup.map_comap_eq]
    have hle : B ⊓ pairSp K ≤ f.range := inf_le_right
    exact inf_eq_right.2 hle
  have hcard : Nat.card ↥(B ⊓ pairSp K) = Nat.card E := by
    rw [← hEmap]
    exact Subgroup.card_map_of_injective hfinj
  have hEB : ∀ x ∈ E, f x ∈ B := fun x hx => (Subgroup.mem_comap.mp hx).1
  rw [hcard]
  have := card_le_pow_three_of_exponent_two (E := E)
    (fun x hx => by
      apply hfinj
      rw [map_mul, map_one, ← sq]
      exact hB2.2 _ (hEB x hx))
    (fun x hx y hy => by
      apply hfinj
      rw [map_mul, map_mul]
      exact hB2.1 _ (hEB x hx) _ (hEB y hy))
  rw [hK, ← pow_mul, mul_comm] at this
  exact this

theorem card_mul_fixV_le_pair {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hBN : B ≤ pairNormSp K)
    (hBs : B ≤ pairSub (Fin 2 ⊕ Fin 2) K) (hB2 : IsElemAbelian2 B) (hB1 : B ≠ ⊥) :
    Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) := by
  have hV := card_pairMod_sp hK
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← sq]; exact hB2.2 x hx
  have hV1 : ∀ x ∈ B, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp (hBs hx)
    exact map_V₁_pairAut a b
  have hfix : ∀ X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), X ≤ B →
      Nat.card ↥(fixV B) ≤ Nat.card ↥(fixV X) := fun X hX =>
    Subgroup.card_le_of_le (fun v hv x hx => hv x (hX hx))
  by_cases hlin : B ≤ pairSp K
  ·
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    have ht : orderOf (t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) = 2 := by
      refine orderOf_eq_prime ?_ (fun h => ht1 (Subtype.ext h))
      exact hB2.2 _ t.2
    have h1 := card_fixV_le_of_involution hn hK (hBN t.2) ht
    have h2 := hfix (Subgroup.zpowers (t : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)))
      (by rw [Subgroup.zpowers_le]; exact t.2)
    have h3 := card_inf_pairSp_le hK hB2
    rw [inf_eq_left.2 hlin] at h3
    rw [hV, show 8 * n = 3 * n + 5 * n by ring, pow_add]
    exact Nat.mul_le_mul h3 (h2.trans h1)
  ·
    obtain ⟨x₀, hx₀B, hx₀⟩ := IsConcreteLE.not_le_iff_exists.mp hlin
    have h1 := card_fixV_le_of_nonlinear hn hK (hBN hx₀B) (hsq x₀ hx₀B) (hV1 x₀ hx₀B) hx₀
    have h2 := hfix (Subgroup.zpowers x₀) (by rw [Subgroup.zpowers_le]; exact hx₀B)
    obtain ⟨c, hcB, hc1, -⟩ := exists_card_le hn hK hBN hsq hV1
    have h3 := card_inf_pairSp_le hK hB2
    have hc2 : c * 2 ^ n ≤ 2 ^ (2 * n - 1) := by rw [← hK]; exact hc1
    have hq : 2 ^ (2 * n - 1) * 2 = 2 ^ (2 * n) := by
      rw [← pow_succ]; congr 1; omega
    have hBle : 2 * Nat.card ↥B ≤ 2 ^ (4 * n) := by
      calc 2 * Nat.card ↥B ≤ 2 * (c * Nat.card ↥(B ⊓ pairSp K)) := Nat.mul_le_mul_left 2 hcB
        _ ≤ 2 * (c * 2 ^ (3 * n)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left c h3)
        _ = 2 * (c * 2 ^ n) * 2 ^ (2 * n) := by
            rw [show 3 * n = n + 2 * n by ring, pow_add]; ring
        _ ≤ 2 * 2 ^ (2 * n - 1) * 2 ^ (2 * n) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hc2)
        _ = 2 ^ (2 * n) * 2 ^ (2 * n) := by rw [mul_comm 2, hq]
        _ = 2 ^ (4 * n) := by rw [← pow_add]; congr 1; ring
    rw [hV]
    calc Nat.card ↥B * Nat.card ↥(fixV B)
        ≤ Nat.card ↥B * 2 ^ (4 * n) := Nat.mul_le_mul_left _ (h2.trans h1)
      _ ≤ 2 ^ (4 * n) * 2 ^ (4 * n) := by
          have : Nat.card ↥B ≤ 2 ^ (4 * n) := by omega
          exact Nat.mul_le_mul_right _ this
      _ = 2 ^ (8 * n) := by rw [← pow_add]; congr 1; ring

end Sp4Inf

end CFSG.Quasithin
