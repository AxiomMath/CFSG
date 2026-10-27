module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem lt_gammaN_of_bar_of_lift {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ normalizer (V : Set G)) (hMV₀ : M ≤ normalizer (V₀ : Set G))
    {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p M)
    (hsmall : ∀ z ∈ V₀, z ≠ 1 →
      1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({z} : Set G)))
    (hlift : ∀ z (hz : z ∈ V), z ∉ V₀ → ∀ ψ ∈ Mbar M V₀ V hV, orderOf ψ = p →
      ψ (mkTil V₀ V hV (IntMod.mk hV ⟨z, hz⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨z, hz⟩) →
      1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({z} : Set G)))
    (n N : ℕ) (hgood : s16n9bGood (Mbar M V₀ V hV) p n N) : (N : ℕ∞) < gammaN n M V := by
  have hMs : M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  refine s16n9b_lt_gammaN_of_good (P := {p}) hV hMV ?_ n N ?_
  · intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨hp, hsp⟩
  · intro t htM ht2 hrank W hWV hWn hWt
    obtain ⟨w, hwW, hw1⟩ := s16n9b_exists_commutator_ne_one hWt
    have hwmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
    by_cases hw0 : w⁻¹ * t⁻¹ * w * t ∈ V₀
    · exact ⟨_, hwmem, hw1, p, Set.mem_singleton p, hsmall _ hw0 hw1⟩
    · let g : ↥(stabTil V₀ V) := ⟨t, hMs htM⟩
      have hφM : actTil V₀ V hV g⁻¹ ∈ Mbar M V₀ V hV :=
        actTil_mem_barSub V₀ V hV (M.inv_mem htM) ((stabTil V₀ V).inv_mem g.2)
      have hφ2 : ∃ a : ℕ, orderOf (actTil V₀ V hV g⁻¹) = 2 ^ a := by
        obtain ⟨a, ha⟩ := ht2
        have hdvd : orderOf (actTil V₀ V hV g⁻¹) ∣ 2 ^ a := by
          refine (orderOf_map_dvd (actTil V₀ V hV) g⁻¹).trans ?_
          rw [orderOf_inv, ← ha]
          exact (Subgroup.orderOf_coe g).symm.dvd
        obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨b, hb⟩
      have hrank' : rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))) ≤ N :=
        (s16n9b_rkIdx_fixV_le V₀ V hV g).trans hrank
      have hU : rkIdx (imgTil V₀ V hV W) ≤ n :=
        (s16n9b_rkIdx_imgTil_le V₀ V hV W).trans hWn
      have hUφ : ¬ imgTil V₀ V hV W ≤ fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹)) :=
        s16n9b_not_le_fixV_of_commutator V₀ V hV g hwW (hWV hwW) hw0
      obtain ⟨zt, hzt, hzt1, ψ, hψ, hord, hfix⟩ := hgood _ hφM hφ2 hrank' _ hU hUφ
      obtain ⟨x, hxmem, hxz⟩ :=
        (mem_imgTil V₀ V hV (commElt W t) zt).1 (s16n9b_commOn_le_imgTil V₀ V hV W g hzt)
      have hx1 : x.val ≠ 1 := by
        intro h1
        have hx1' : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact h1)
        apply hzt1
        rw [← hxz, hx1', map_one]
      have hxmk : IntMod.mk hV ⟨x.val, x.val_mem⟩ = x := IntMod.val_injective rfl
      refine ⟨x.val, hxmem, hx1, p, Set.mem_singleton p, ?_⟩
      by_cases hx0 : x.val ∈ V₀
      · exact hsmall x.val hx0 hx1
      · refine hlift x.val x.val_mem hx0 ψ hψ hord ?_
        rw [hxmk, hxz]
        exact hfix

theorem s19_one_le_pRank_of_mem_V0 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h3 : R19_3At D V₀ V p L K h) {z : G} (hz : z ∈ V₀)
    (hz1 : z ≠ 1) : 1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({z} : Set G)) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hLcent : L ≤ centralizer (V₀ : Set G) :=
    le_sup_left.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)
  have h5pi : 5 ∈ piSet L := h.p_eq ▸ h.hyp.hL.2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 5 h5pi.2
  have hbz : (x : G) * z = z * (x : G) :=
    (Subgroup.mem_centralizer_iff.1 (hLcent x.2) z hz).symm
  have hbo : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
  have hmem : (x : G) ∈ D.M ⊓ centralizer ({z} : Set G) :=
    ⟨hLM x.2, Subgroup.mem_centralizer_singleton_iff.2 hbz⟩
  refine CFSG.SectionRank.le_pRank (p := 5) (H := D.M ⊓ centralizer ({z} : Set G))
    (E := Subgroup.zpowers (x : G)) (by norm_num) (Subgroup.zpowers_le.2 hmem)
    (CFSG.Open.isElemAbelian_zpowers (p := 5) (by rw [← hbo]; exact pow_orderOf_eq_one _)) ?_
  rw [Nat.card_zpowers, hbo, pow_one]

theorem s19_one_le_pRank_of_fix (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h5 : R19_5At D V₀ V p L K h) {z : G} (hz : z ∈ V)
    (hz0 : z ∉ V₀) {ψ : MulAut (Vtil V₀ V h.hyp.isElemAbelian)}
    (hψ : ψ ∈ Mbar D.M V₀ V h.hyp.isElemAbelian) (hord : orderOf ψ = 5)
    (hfix : ψ (mkTil V₀ V h.hyp.isElemAbelian (IntMod.mk h.hyp.isElemAbelian ⟨z, hz⟩)) =
      mkTil V₀ V h.hyp.isElemAbelian (IntMod.mk h.hyp.isElemAbelian ⟨z, hz⟩)) :
    1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({z} : Set G)) := by
  have hdvd : 5 ∣ Nat.card (F11.CElt D.M V₀ z) :=
    Sixteen21.dvd_card_cElt_of_mem_mbar (M := D.M) (hV := h.hyp.isElemAbelian) hψ hord hz hfix
  have hHdvd : 5 ∣ Nat.card ↥(centModInM D V₀ z) := by
    rwa [← cElt_eq_centModInM D V₀ z]
  obtain ⟨Q, hQ⟩ := h5 z hz hz0
  have hQdvd : 5 ∣ Nat.card ↥Q := Q.pow_dvd_card_of_pow_dvd_card (n := 1) hHdvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 5 hQdvd
  let x : ↥(centModInM D V₀ z) := q.1
  have hxord : orderOf ((x : ↥(centModInM D V₀ z)) : G) = 5 := by
    rw [Subgroup.orderOf_coe x]
    exact (Subgroup.orderOf_coe q).trans hq
  have hxC : ((x : ↥(centModInM D V₀ z)) : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    hQ (Subgroup.mem_map_of_mem (centModInM D V₀ z).subtype q.2)
  have hxM : ((x : ↥(centModInM D V₀ z)) : G) ∈ D.M := x.2.1
  have hmem : ((x : ↥(centModInM D V₀ z)) : G) ∈
      D.M ⊓ centralizer ({z} : Set G) := ⟨hxM, hxC⟩
  refine CFSG.SectionRank.le_pRank (p := 5)
    (H := D.M ⊓ centralizer ({z} : Set G))
    (E := Subgroup.zpowers ((x : ↥(centModInM D V₀ z)) : G)) (by norm_num)
    (Subgroup.zpowers_le.2 hmem) (CFSG.Open.isElemAbelian_zpowers (p := 5) ?_) ?_
  · rw [← hxord]
    exact pow_orderOf_eq_one _
  · rw [Nat.card_zpowers, hxord, pow_one]

theorem s19_lt_gammaN (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hSg : UC6S846.SigmaStd D) (h3 : R19_3At D V₀ V p L K h)
    (h5 : R19_5At D V₀ V p L K h) (n N : ℕ)
    (hgood : s16n9bGood (Mbar D.M V₀ V h.hyp.isElemAbelian) 5 n N) :
    (N : ℕ∞) < gammaN n D.M V := by
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC h.hyp.hL.1
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg hns (h.p_eq ▸ h.hyp.hp)
  exact lt_gammaN_of_bar_of_lift h.hyp.isElemAbelian h.hyp.hyp125.pairFacts.le_normalizer
    h.hyp.hyp125.pairFacts.le_normalizer₀ (by norm_num) hsp
    (fun z hz hz1 => s19_one_le_pRank_of_mem_V0 D h h3 hz hz1)
    (fun z hz hz0 ψ hψ hord hfix => s19_one_le_pRank_of_fix D h h5 hz hz0 hψ hord hfix)
    n N hgood

theorem eight_le_gammaN_of_invFix (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hSg : UC6S846.SigmaStd D) (h3 : R19_3At D V₀ V p L K h)
    (h4 : R19_4At D V₀ V p L K h)
    (hinv : s16n9bInvFix (Mbar D.M V₀ V h.hyp.isElemAbelian) 5 7) : 8 ≤ gammaN 2 D.M V :=
  Order.add_one_le_of_lt
    (s19_lt_gammaN D h hSg h3 (nineteen_five D V₀ V p L K h h4) 2 7
      (s16n9bGood_of_invFix hinv))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
