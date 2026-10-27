module

public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

section StdMod

open CFSG.Quasithin.H

variable {K : Type} [Field K] [Finite K]

theorem nl2w_card_natImage {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hinj : Function.Injective (natAut (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) :=
    fun _ _ h => Subtype.ext (matHom_injective h)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).symm.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]

variable [CharP K 2]

theorem nl2w_card_mul_card_fixV_le {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hEN : E ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (hE : IsElemAbelian2 E) :
    Nat.card E * Nat.card ↥(fixV E) ≤ Nat.card (StdMod (Fin 2) K) := by
  by_contra hlt
  push Not at hlt
  have hEim : E ≤ natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    B69.le_natImage_of_offender hn hK hEN (fun x hx => hE.2 x hx)
      (fun x hx y hy => hE.1 x hx y hy) hlt.le
  rcases eq_or_ne E ⊥ with rfl | hbot
  · rw [B1.card_bot_mul_card_fixV] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨⟨x, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨γ, hγ⟩ := hEim hxE
    have hM : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
      intro h
      apply hx1'
      rw [← hγ]
      refine toAddMap_injective fun v => ?_
      rw [toAddMap_natAut, toAddMap_one, h, Matrix.one_mulVec]
    have hfix : Nat.card ↥(fixV E) ≤ Nat.card K := by
      have hv : ∀ v : ↥(fixV E), ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (v : StdMod (Fin 2) K)) =
            Multiplicative.toAdd (v : StdMod (Fin 2) K) := fun v => by
        have h1 : x (v : StdMod (Fin 2) K) = v := v.2 x hxE
        rw [← hγ] at h1
        exact congrArg Multiplicative.toAdd h1
      let f : ↥(fixV E) → {w : Fin 2 → K //
          ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w = w} :=
        fun v => ⟨Multiplicative.toAdd (v : StdMod (Fin 2) K), hv v⟩
      have hf : Function.Injective f := by
        intro v w hvw
        have h1 := Subtype.ext_iff.mp hvw
        exact Subtype.ext (Multiplicative.toAdd.injective h1)
      exact (Nat.card_le_card_of_injective f hf).trans (B42L2.card_fixed_le _ hM)
    have hEc : Nat.card E ≤ 2 ^ n :=
      (B42L2.card_le_of_isPGroup hEim hE.isPGroup hn (nl2w_card_natImage hK)).1
    have hV : Nat.card (StdMod (Fin 2) K) = 2 ^ n * 2 ^ n := by
      rw [card_stdMod, Fintype.card_fin, hK, sq]
    have h2 : Nat.card E * Nat.card ↥(fixV E) ≤ 2 ^ n * 2 ^ n :=
      calc Nat.card E * Nat.card ↥(fixV E) ≤ 2 ^ n * Nat.card K := Nat.mul_le_mul hEc hfix
        _ = 2 ^ n * 2 ^ n := by rw [hK]
    rw [hV] at hlt
    exact absurd hlt (not_lt.2 h2)

end StdMod

variable {W : Type} [CommGroup W] [Finite W]

theorem natL2_weight {L E : Subgroup (MulAut W)} {n : ℕ} (hnat : BinaryNaturalSL L ⊤ ⊥ 2 n)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : IsElemAbelian2 E) :
    rk ↥E ≤ rkIdx (fixV E) := by
  obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hnat
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK] at h1
      norm_num at h1
    · exact h
  obtain ⟨e, he⟩ := H.exists_mulEquiv_of_realizesVia
    (CFSG.Assembly.LowTwoRank.StatedSL 2 K) hπ
  have hLe : L.map (H.congrHom e) = H.natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    H.map_congrHom_eq_natImage _ hπ.1 e he
  have hEN' : E.map (H.congrHom e) ≤ H.natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
    have h1 := Subgroup.map_mono (f := H.congrHom e) hEN
    rwa [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hLe] at h1
  have hV : ∀ v : W, v ^ 2 = 1 := by
    intro v
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact B69.ffVec_add_self _
  by_contra hlt
  push Not at hlt
  have h1 := (B1.card_lt_iff hV hE).2 hlt
  have h2 := nl2w_card_mul_card_fixV_le hn hK hEN' ((H.isElemAbelian2_map_congrHom e).2 hE)
  rw [H.card_map_congrHom, H.fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
    ← Nat.card_congr e.toEquiv] at h2
  exact absurd h1 (not_lt.2 h2)

end CFSG.Quasithin
