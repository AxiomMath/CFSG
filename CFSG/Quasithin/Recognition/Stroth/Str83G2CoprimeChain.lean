module

public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Vol2.Ch10SecACoprime
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_inf_eq_of_isElemAbelian {N L D : Subgroup G}
    (hLN : L ≤ N) (hNe : IsElemAbelian 2 N)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hDL : D ≤ Subgroup.normalizer (L : Set G))
    (hDodd : Odd (Nat.card D)) :
    ⁅N, D⁆ ⊓ L = ⁅L, D⁆ := by
  classical
  have hLe : ⁅L, D⁆ ≤ ⁅N, D⁆ ⊓ L :=
    le_inf (Subgroup.commutator_mono hLN le_rfl)
      (CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hDL)
  have hKe : IsElemAbelian 2 L := hNe.mono hLN
  have hcop : Nat.Coprime (Nat.card D) (Nat.card L) := by
    obtain ⟨k, hk⟩ := (hKe.isPGroup (p := 2)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Odd.coprime_two_right hDodd)
  letI : CommGroup ↥N := hNe.1.instCommGroup
  letI : CommGroup ↥L := hKe.1.instCommGroup
  have hcommL : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := fun a ha b hb => by
    simpa using (hKe.1.is_comm.comm (⟨a, ha⟩ : ↥L) (⟨b, hb⟩ : ↥L))
  have hCdisj : (⁅N, D⁆ ⊓ L) ⊓ (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    have hxND : x ∈ ⁅N, D⁆ := hx.1.1
    have hxC : x ∈ Subgroup.centralizer (D : Set G) := hx.2.2
    have hbot : ⁅N, D⁆ ⊓ Subgroup.centralizer (D : Set G) = ⊥ :=
      CFSG.Quasithin.Vol2.Ch10.SecA.commutator_inf_centralizer_eq_bot
        (W := N) (D := D) (h2 := hNe.2) hDodd hDN
    have : x ∈ ⁅N, D⁆ ⊓ Subgroup.centralizer (D : Set G) := ⟨hxND, hxC⟩
    rwa [hbot] at this
  obtain ⟨hsupL, hdisjL⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp L D hDL
      (fun x y => Subtype.ext (hcommL (x : G) x.2 (y : G) y.2)) hcop
  have hcardL : Nat.card ↥L = Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G)) *
      Nat.card ↥⁅L, D⁆ := by
    have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (L ⊓ Subgroup.centralizer (D : Set G)) ⁅L, D⁆ ?_
    · have hinf : (L ⊓ Subgroup.centralizer (D : Set G)) ⊓ ⁅L, D⁆ = ⊥ :=
        disjoint_iff.mp hdisjL
      have := hprod.1
      rw [hsupL, hinf, Subgroup.card_bot, mul_one] at this
      exact this
    · intro x hx y hy
      exact hcommL x hx.1 y (CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hDL hy)
  have hcard_inf : Nat.card ↥(⁅N, D⁆ ⊓ L) *
      Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G)) ≤ Nat.card ↥L := by
    have hsup_le : (⁅N, D⁆ ⊓ L) ⊔ (L ⊓ Subgroup.centralizer (D : Set G)) ≤ L :=
      sup_le inf_le_right inf_le_left
    have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (⁅N, D⁆ ⊓ L) (L ⊓ Subgroup.centralizer (D : Set G)) ?_
    · rw [hCdisj, Subgroup.card_bot, mul_one] at hprod
      rw [← hprod.1]
      exact Nat.card_le_card_of_injective (Subgroup.inclusion hsup_le)
        (Subgroup.inclusion_injective hsup_le)
    · intro x hx y hy
      exact hcommL x hx.2 y hy.1
  have hCpos : 0 < Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G)) := Nat.card_pos
  have hcard_le : Nat.card ↥(⁅N, D⁆ ⊓ L) ≤ Nat.card ↥⁅L, D⁆ := by
    apply Nat.le_of_mul_le_mul_right _ hCpos
    calc Nat.card ↥(⁅N, D⁆ ⊓ L) *
          Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G))
        ≤ Nat.card ↥L := hcard_inf
      _ = Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G)) * Nat.card ↥⁅L, D⁆ := hcardL
      _ = Nat.card ↥⁅L, D⁆ *
          Nat.card ↥(L ⊓ Subgroup.centralizer (D : Set G)) := by ring
  exact (Subgroup.eq_of_le_of_card_ge (H := ⁅L, D⁆) (K := ⁅N, D⁆ ⊓ L) hLe hcard_le).symm


theorem card_commutator_le_pow_of_chiefSeries {H X D : Subgroup G} {b : ℕ}
    (hXH : X ≤ H) (hXe : IsElemAbelian 2 X) (hDH : D ≤ H)
    (hDodd : Odd (Nat.card D))
    (hb : ∀ L N : Subgroup G, IsChiefStep H X L N → ¬ IsCentralStep H L N →
      Nat.card (N ⧸ L.subgroupOf N) ≤ b)
    {N : Subgroup G} {n : ℕ} (hser : IsChiefSeriesFrom H X N n) :
    Nat.card ↥⁅N, D⁆ ≤ b ^ n := by
  induction hser with
  | bot =>
      rw [Subgroup.commutator_bot_left, Subgroup.card_bot, pow_zero]
  | @central N L n hstep hc hs ih =>
      have hLN : L ≤ N := hstep.2.2.1.le
      have hNe : IsElemAbelian 2 N := hXe.mono hstep.1.1
      have hDN : D ≤ Subgroup.normalizer (N : Set G) :=
        hDH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.1)
      have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
        hDH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.2.1)
      have hcent : ⁅N, D⁆ ≤ L := by
        rw [Subgroup.commutator_le]
        intro x hx d hd
        have h : ⁅d, x⁆ ∈ L := hc d (hDH hd) x hx
        have e : ⁅x, d⁆ = (⁅d, x⁆)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [e]
        exact L.inv_mem h
      have hEq : ⁅N, D⁆ = ⁅L, D⁆ := by
        rw [← commutator_inf_eq_of_isElemAbelian hLN hNe hDN hDL hDodd,
          inf_eq_left.mpr hcent]
      rw [hEq]
      exact ih
  | @noncentral N L n hstep hnc hs ih =>
      have hLN : L ≤ N := hstep.2.2.1.le
      have hNe : IsElemAbelian 2 N := hXe.mono hstep.1.1
      have hNX : N ≤ X := hstep.1.1
      have hDN : D ≤ Subgroup.normalizer (N : Set G) :=
        hDH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.1)
      have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
        hDH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.2.1)
      have hinf : ⁅N, D⁆ ⊓ L = ⁅L, D⁆ :=
        commutator_inf_eq_of_isElemAbelian hLN hNe hDN hDL hDodd
      have hNDnorm : ⁅N, D⁆ ≤ Subgroup.normalizer (L : Set G) :=
        (CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hDN).trans
          ((hNX.trans hXH).trans
            (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.2.1))
      have hArel : (⁅N, D⁆ ⊓ L).relIndex ⁅N, D⁆ ≤
          Nat.card (N ⧸ L.subgroupOf N) := by
        rw [← (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
          (H := ⁅N, D⁆) (K := L) hNDnorm).2]
        rw [show Nat.card (N ⧸ L.subgroupOf N) = L.relIndex N from rfl]
        exact Subgroup.relIndex_le_of_le_right
          (sup_le (CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hDN) hLN)
          (D15Proof.relIndex_ne_zero _ _)
      have hstep_le : (⁅N, D⁆ ⊓ L).relIndex ⁅N, D⁆ ≤ b :=
        hArel.trans (hb L N hstep hnc)
      have hfN : Nat.card ↥⁅N, D⁆ =
          ⁅L, D⁆.relIndex ⁅N, D⁆ * Nat.card ↥⁅L, D⁆ := by
        have hcard := Subgroup.relIndex_mul_card (H := ⁅N, D⁆ ⊓ L) (K := ⁅N, D⁆)
        rw [hinf, inf_eq_left.mpr (Subgroup.commutator_mono hLN le_rfl)] at hcard
        exact hcard.symm
      rw [hfN, pow_succ, mul_comm (b ^ n) b]
      exact Nat.mul_le_mul (by simpa [hinf] using hstep_le) ih

end CFSG.Quasithin.Stroth

end
