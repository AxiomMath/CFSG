module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl28_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    have hx' : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 hx
    rw [mem_modNull] at hx'
    exact IntMod.val_injective (by simpa using hx')
  · rintro rfl
    exact map_one _

private theorem s16h_sl28_card_preTil_bot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil ⊥ V hV)) :
    Nat.card ↥(preTil ⊥ V hV S) = Nat.card ↥S := by
  unfold preTil
  rw [Subgroup.card_map_of_injective (f := valHom V hV)
    (K := S.comap (mkTil ⊥ V hV)) (fun x y h => IntMod.val_injective h)]
  rw [← Subgroup.card_map_of_injective (f := mkTil ⊥ V hV)
    (K := S.comap (mkTil ⊥ V hV)) (s16h_sl28_mkTil_bot_injective hV),
    Subgroup.map_comap_eq_self_of_surjective (mkTil_surjective ⊥ V hV) S]

theorem s16h_sl28_seven_z_card
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    8 ≤ Nat.card ↥(wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) := by
  have hcardZ : Nat.card ↥(wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        Subgroup.centralizer (L : Set G)) =
      Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
    rw [s16h_wSub_inf_centralizer_eq_preTil D h]
    exact s16h_sl28_card_preTil_bot h.hyp151.isElemAbelian _
  have hpow : Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) =
      2 ^ rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) :=
    CFSG.Quasithin.card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian) _
  have h2 : 2 ≤ rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
    have h4 := hZ4
    rw [hpow] at h4
    by_contra hlt
    have hle : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 1 := by omega
    have hpowle : 2 ^ rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2 := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle
    omega
  have hle3 := s16h_sl28_seven_zmod_rk_le_three D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7 hxM hxn hZ0
  have hne2 := s16h_sl28_seven_zmod_rk_ne_two D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
    hthin hZ hbad hrow hZ4 h7 hxM hxn hZ0
  have hrk : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = 3 := by omega
  rw [hcardZ, hpow, hrk]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
