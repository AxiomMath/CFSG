module

public import CFSG.Quasithin.Background.E3Bar
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Nlow

variable {G : Type u} [Group G] [Finite G] {V T : Subgroup G}

theorem inE_of_nParam_eq {H : Subgroup G} {j : ℕ} (h : E1.nParam H = j) : E1.InE j H := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact E1.inE_of_odd (E1.odd_of_nParam_le_zero (by simpa using h.le))
  · exact (E1.nParam_le_iff hj).1 h.le

theorem e3_35_one (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hT : HypE322 T V) {M H S : Subgroup G}
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hS : IsSylowIn 2 S H) (hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hQS : T ⊓ Subgroup.centralizer (V : Set G) ≤ S)
    (hn : E1.nParam H < min (wParam T V) (rParam V)) : H ≤ M := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hn)
  rw [← hj] at hn
  have hjw : (j : ℕ∞) < wParam T V := lt_of_lt_of_le hn (min_le_left _ _)
  have hjr : (j : ℕ∞) < rParam V := lt_of_lt_of_le hn (min_le_right _ _)
  have hw : 0 < wParam T V := lt_of_le_of_lt zero_le hjw
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hrk : 0 < rk ↥V := Nat.pos_of_ne_zero fun h0 => hV1 ((rk_eq_zero_iff_of_isPGroup hV2).1 h0)
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hWS : ∀ i ≤ j, wClos V i T ≤ S := fun i hi =>
    ((wClos_le_of_lt_wParam (lt_of_le_of_lt (Nat.cast_le.2 hi) hjw))).trans hQS
  have hWeq : ∀ i ≤ j, wClos V i T = wClos V i S := fun i hi =>
    e3_15 hT.sylow le_top hS2 (hWS i hi)
  have h34 := e3_34_two hV hT hM (i := 0) hrk (by simpa using hw)
  have hSM : S ≤ M := by
    have h1 := e3_15_normalizer hT.sylow (Y := S) le_top hS2 (hWS 0 (Nat.zero_le j))
    exact Subgroup.le_normalizer.trans (h1.trans h34.1)
  have hInE := inE_of_nParam_eq hj.symm
  have hEF := (E1.inE_iff_inEFor hS).1 hInE (gammaSet V 0 H) (isInvColl_gammaSet hV 0 H)
  rw [weakClosure_gammaSet hS.le, ← hWeq 0 (Nat.zero_le j)] at hEF
  have hN : H ⊓ Subgroup.normalizer (wClos V 0 T : Set G) ≤ M := inf_le_right.trans h34.1
  have hE : E1.eGen j H S (gammaSet V 0 H) ≤ M := by
    refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
    obtain ⟨-, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (mQuot_eq_zero_iff (isPGroup_conjSubgroup hV2 g) hAg).1 hm
    have hAel : IsElemAbelian 2 A := hAeq ▸ isElemAbelian_conjSubgroup hV g
    obtain ⟨hAK, hcardK⟩ := card_le_of_isE hS hAS hAel hK
    have hKH : K ≤ H := hK.1
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    have key : ∀ k ∈ K, conjSubgroup A k⁻¹ ≤ Subgroup.centralizer (V : Set G) := by
      intro k hk
      by_contra hnc'
      have hA' : conjSubgroup A k⁻¹ = conjSubgroup V (g * k⁻¹) := by
        rw [hAeq, conjSubgroup_conjSubgroup]
      have hVN : ¬ V ≤ Subgroup.normalizer (conjSubgroup V (g * k⁻¹) : Set G) := by
        intro h
        apply hnc'
        rw [hA']
        exact (e3_25_centralizer_iff (g * k⁻¹)).2
          ((e3_25_centralizer_iff_normalizer hV hT hw (g * k⁻¹)).2 h)
      have hkN : k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk)
      have hconjO : conjSubgroup (pCoreOf 2 K) k⁻¹ = pCoreOf 2 K :=
        conjSubgroup_eq_iff_mem_normalizer.2 hkN
      have hA'2 : IsPGroup 2 (conjSubgroup V (g * k⁻¹)) :=
        isPGroup_conjSubgroup hV2 (g * k⁻¹)
      have hcard' : Nat.card (conjSubgroup V (g * k⁻¹)) ≤
          2 ^ j * Nat.card ↥(conjSubgroup V (g * k⁻¹) ⊓ pCoreOf 2 K) := by
        rw [← hA', card_conjSubgroup]
        have e : Nat.card ↥(conjSubgroup A k⁻¹ ⊓ pCoreOf 2 K) = Nat.card ↥(A ⊓ pCoreOf 2 K) := by
          rw [← card_conjSubgroup (A ⊓ pCoreOf 2 K) k⁻¹, conjSubgroup_inf, hconjO]
        rw [e]
        exact hcardK
      set B' := conjSubgroup V (g * k⁻¹) ⊓ pCoreOf 2 K with hB'
      have hmB : mQuot (conjSubgroup V (g * k⁻¹)) B' ≤ j := by
        have e := card_eq_two_pow_mul hA'2 (inf_le_left : B' ≤ conjSubgroup V (g * k⁻¹))
        rw [e] at hcard'
        have := Nat.le_of_mul_le_mul_right hcard' Nat.card_pos
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
      have hB'S : B' ≤ S := inf_le_right.trans
        ((B6.pCoreOf_two_le_of_isSylowTwoOf hSK).trans inf_le_left)
      have hmem : B' ∈ gammaSet V (mQuot (conjSubgroup V (g * k⁻¹)) B') S :=
        ⟨hB'S, g * k⁻¹, inf_le_left, rfl⟩
      have hB'C : B' ≤ Subgroup.centralizer (V : Set G) := by
        have h1 := le_wClos hmem
        have h2 : wClos V (mQuot (conjSubgroup V (g * k⁻¹)) B') T =
            wClos V (mQuot (conjSubgroup V (g * k⁻¹)) B') S := hWeq _ hmB
        have h3 := wClos_le_of_lt_wParam (T := T) (V := V)
          (i := mQuot (conjSubgroup V (g * k⁻¹)) B')
          (lt_of_le_of_lt (Nat.cast_le.2 hmB) hjw)
        rw [← h2] at h1
        exact (h1.trans h3).trans inf_le_right
      have hmC : mQuot (conjSubgroup V (g * k⁻¹))
          (conjSubgroup V (g * k⁻¹) ⊓ Subgroup.centralizer (V : Set G)) ≤ j :=
        (mQuot_mono (le_inf inf_le_left hB'C)).trans hmB
      have h4 := e3_4_two hVN
      exact absurd (lt_of_lt_of_le hjr (h4.trans (Nat.cast_le.2 hmC))) (lt_irrefl _)
    have hConj : conjClosure A K ≤ M := by
      refine conjClosure_le fun k hk a ha => ?_
      have hkH : k ∈ H := hKH hk
      have haH : a ∈ H := hKH (hAK ha)
      have hmemA : k * a * k⁻¹ ∈ conjSubgroup A k⁻¹ := by
        rw [mem_conjSubgroup_iff, inv_inv]
        have e : k⁻¹ * (k * a * k⁻¹) * k = a := by group
        rw [e]
        exact ha
      exact hCH ⟨H.mul_mem (H.mul_mem hkH haH) (H.inv_mem hkH), key k hk hmemA⟩
    have hres : twoResidual K ≤ M := (E1.twoResidual_le_conjClosure hK.isEAny).trans hConj
    have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
    rw [hKeq]
    exact sup_le (inf_le_left.trans hSM) hres
  calc H = E1.eGen j H S (gammaSet V 0 H) ⊔
        (H ⊓ Subgroup.normalizer (wClos V 0 T : Set G)) := hEF.symm
    _ ≤ M := sup_le hE hN

theorem e3_35_one_solvable (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hT : HypE322 T V)
    {M H S : Subgroup G}
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hS : IsSylowIn 2 S H) (hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hQS : T ⊓ Subgroup.centralizer (V : Set G) ≤ S) (hH : Group.IsSolvable ↥H)
    (h1 : 1 < min (wParam T V) (rParam V)) : H ≤ M :=
  e3_35_one hV hV1 hT hM hS hCH hQS (lt_of_le_of_lt (E1.solvable_nParam_le_one hH) h1)

theorem e3_35_two (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hT : HypE322 T V) {M H S : Subgroup G}
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hS : IsSylowIn 2 S H) (hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ M)
    (hQS : T ⊓ Subgroup.centralizer (V : Set G) ≤ S) (has : aParam (autI hV ⊤) < sParam hV)
    (hrw : wParam T V ≤ rParam V) (hHM : ¬ H ≤ M) :
    wParam T V ≤ E1.nParam H ∧
      ((sParam hV - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ wParam T V ∧
      0 < sParam hV - aParam (autI hV ⊤) := by
  have h1 : ¬ E1.nParam H < min (wParam T V) (rParam V) := fun h =>
    hHM (e3_35_one hV hV1 hT hM hS hCH hQS h)
  rw [min_eq_left hrw] at h1
  exact ⟨not_lt.1 h1, e3_34_one hV hT has⟩

end Nlow

end E3

end CFSG.Quasithin
