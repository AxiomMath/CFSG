module

public import CFSG.Quasithin.Background.SimsE215KF1Defs
public import CFSG.Quasithin.Vol2.E2SevenPair
import CFSG.Quasithin.Background.SimsE215KF1Paired
import CFSG.Quasithin.Vol2.E2SevenKG4Two
import CFSG.Quasithin.Vol2.Ch3E213MOS2
import CFSG.GroupTheory.SylowCentralProduct
public import CFSG.Quasithin.Background.F9Basic

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

theorem le_centralizer_of_pair {X : Type*} [Group X]
    {T V K : Subgroup X} {t : X}
    (hVT : T ≤ Subgroup.normalizer (V : Set X))
    (hcomm : ⁅K, B6.conjSub t K⁆ = ⊥)
    (hdecomp : V = (V ⊓ K) ⊔ (V ⊓ B6.conjSub t K))
    (hcard : Nat.card ↥(V ⊓ K) = 2)
    (hcard' : Nat.card ↥(V ⊓ B6.conjSub t K) = 2)
    (hsplit : T ⊓ (K ⊔ B6.conjSub t K) = (T ⊓ K) ⊔ (T ⊓ B6.conjSub t K)) :
    V ≤ Subgroup.centralizer
      ((T ⊓ (K ⊔ B6.conjSub t K) : Subgroup X) : Set X) := by
  have hnormK : T ⊓ K ≤ Subgroup.normalizer ((V ⊓ K : Subgroup X) : Set X) :=
    (le_inf (inf_le_left.trans hVT) (inf_le_right.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hnormK' :
      T ⊓ B6.conjSub t K ≤
        Subgroup.normalizer ((V ⊓ B6.conjSub t K : Subgroup X) : Set X) :=
    (le_inf (inf_le_left.trans hVT) (inf_le_right.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKc : V ⊓ K ≤ Subgroup.centralizer ((T ⊓ K : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff,
      ← CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two hcard]
    exact hnormK
  have hKc' :
      V ⊓ B6.conjSub t K ≤
        Subgroup.centralizer ((T ⊓ B6.conjSub t K : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff,
      ← CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two hcard']
    exact hnormK'
  have hcomm' : ∀ a ∈ K, ∀ b ∈ B6.conjSub t K, a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hleft : V ⊓ K ≤ Subgroup.centralizer
      (((T ⊓ K) ⊔ (T ⊓ B6.conjSub t K) : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact hKc
    · rw [Subgroup.le_centralizer_iff]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm' x hx.2 y hy.2).symm
  have hright : V ⊓ B6.conjSub t K ≤ Subgroup.centralizer
      (((T ⊓ K) ⊔ (T ⊓ B6.conjSub t K) : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcomm' y hy.2 x hx.2
    · rw [Subgroup.le_centralizer_iff]
      exact hKc'
  rw [hsplit, hdecomp]
  exact sup_le hleft hright

theorem exists_normal_centralizer_of_kgL2OddTwo {X : Type} [Group X] [Finite X]
    {T V K : Subgroup X} {t : X}
    (hsyl : IsSylowTwoOf T ⊤) (ht : t ∈ T)
    (hVT : T ≤ Subgroup.normalizer (V : Set X))
    (hcomm : ⁅K, B6.conjSub t K⁆ = ⊥)
    (hinf : K ⊓ B6.conjSub t K = ⊥)
    (hnorm : (⊤ : Subgroup X) ≤
      Subgroup.normalizer ((K ⊔ B6.conjSub t K : Subgroup X) : Set X))
    (hdecomp : V = (V ⊓ K) ⊔ (V ⊓ B6.conjSub t K))
    (hcard : Nat.card ↥(V ⊓ K) = 2) :
    ∃ F0 : Subgroup X, F0.Normal ∧ V ≤ F0 ∧
      V ≤ Subgroup.centralizer ((T ⊓ F0 : Subgroup X) : Set X) := by
  let F0 : Subgroup X := K ⊔ B6.conjSub t K
  have hF0norm : F0.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
  have hVF0 : V ≤ F0 := by
    rw [hdecomp]
    exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
  have hcard' : Nat.card ↥(V ⊓ B6.conjSub t K) = 2 := by
    have hconj : B6.conjSub t (V ⊓ K) = V ⊓ B6.conjSub t K := by
      change (V ⊓ K).map (MulAut.conj t).toMonoidHom =
        V ⊓ K.map (MulAut.conj t).toMonoidHom
      rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
        show V.map (MulAut.conj t).toMonoidHom = V from
          B6.conjSub_eq_self (hVT ht)]
    rw [← hconj]
    change Nat.card ↥((V ⊓ K).map (MulAut.conj t).toMonoidHom) = 2
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (V ⊓ K)
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm).trans hcard
  have hsplit : T ⊓ F0 = (T ⊓ K) ⊔ (T ⊓ B6.conjSub t K) := by
    have hF0sylow : IsSylowTwoOf (T ⊓ F0) F0 :=
      A4.isSylowTwoOf_inf_normal hsyl le_top hnorm
    have hodd : Odd (Nat.card ↥(K ⊓ B6.conjSub t K)) := by
      rw [hinf]
      simp
    have hcomm' : ∀ a ∈ K, ∀ b ∈ B6.conjSub t K, a * b = b * a := by
      intro a ha b hb
      have h := Subgroup.commutator_mem_commutator ha hb
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have h := (CFSG.GroupTheory.isSylowTwoOf_sup_inf_of_odd_inf
      (L := K) (L' := B6.conjSub t K) (P := T ⊓ F0) hcomm' hodd hF0sylow).1
    have h2 : T ⊓ F0 ⊓ K = T ⊓ K := by
      have hFK : F0 ⊓ K = K := inf_eq_right.mpr le_sup_left
      rw [inf_assoc, hFK]
    have h3 : T ⊓ F0 ⊓ B6.conjSub t K = T ⊓ B6.conjSub t K := by
      have hFK : F0 ⊓ B6.conjSub t K = B6.conjSub t K := inf_eq_right.mpr le_sup_right
      rw [inf_assoc, hFK]
    rw [h, h2, h3]
  have hle := le_centralizer_of_pair hVT hcomm hdecomp hcard hcard' hsplit
  exact ⟨F0, hF0norm, hVF0, hle⟩

theorem kgL2OddTwo_star
    {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G} (hS : Setting H T M V K)
    {t : G} (htT : t ∈ T) (htH : t ∈ H)
    (hMdecomp : M = (M ⊓ K) ⊔ B6.conjSub t (M ⊓ K) ⊔ T) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hPSL : IsPSL 2 p 1 ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)))
    (haut : 8 < E2.autCard (E2.star M H T) (E2.star M H K))
    (hP : E2.PairCase (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H T)
      (E2.star M H K) (E2P.starMap M H ⟨t, htH⟩)) :
    E2.star M H V = (E2.star M H V ⊓ E2.star M H K) ⊔
      (E2.star M H V ⊓ B6.conjSub (E2P.starMap M H ⟨t, htH⟩) (E2.star M H K)) ∧
    Nat.card ↥(E2.star M H V ⊓ E2.star M H K) = 2 := by
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  let X := E2.StarQuot M H
  let Tstar : Subgroup X := E2.star M H T
  let Mstar : Subgroup X := E2.star M H M
  let Kstar : Subgroup X := E2.star M H K
  let Vstar : Subgroup X := E2.star M H V
  let tstar : X := E2P.starMap M H ⟨t, htH⟩
  have hY28 : E2.Hyp28 (⊤ : Subgroup X) Tstar Mstar Vstar :=
    hS.hyp.star (E2.sqtkGroup_top hS.sqtk)
  have hmpY : MinParabolic (⊤ : Subgroup X) Tstar Mstar := E2P.minParabolic_star hmp
  have hJY : kerIn Mstar ⊤ = ⊥ := E2P.kerIn_star M H
  have htstar : tstar ∈ Tstar := E2.starMap_mem_star htH htT
  have hHK : (⊤ : Subgroup X) = Kstar ⊔ Tstar := by
    rw [← E2P.star_top M H, ← E2.star_sup hKH hTH, ← hS.eq_sup]
  have hMdecompStar :
      Mstar = (Mstar ⊓ Kstar) ⊔ B6.conjSub tstar (Mstar ⊓ Kstar) ⊔ Tstar := by
    have hMKH : M ⊓ K ≤ H := inf_le_left.trans hMH
    have hCKH : B6.conjSub t (M ⊓ K) ≤ H := by
      rintro x ⟨y, hy, rfl⟩
      exact H.mul_mem (H.mul_mem (hTH htT) (hMKH hy)) (H.inv_mem (hTH htT))
    have h1 : Mstar = E2.star M H ((M ⊓ K) ⊔ B6.conjSub t (M ⊓ K) ⊔ T) := by
      change E2.star M H M = E2.star M H ((M ⊓ K) ⊔ B6.conjSub t (M ⊓ K) ⊔ T)
      exact congrArg (E2.star M H) hMdecomp
    conv_lhs =>
      rw [h1, E2.star_sup (sup_le hMKH hCKH) hTH, E2.star_sup hMKH hCKH,
        E2P.star_inf_M K, E2.star_conjSub (X := M ⊓ K) (M := M) (H := H) (hTH htT),
        E2P.star_inf_M K]
  have hMKstar : Mstar ⊓ Kstar = Kstar ⊓ Subgroup.centralizer
      ((Tstar ⊓ Kstar ⊓ Subgroup.centralizer ((Tstar ⊓ Kstar : Subgroup X) : Set X) :
        Subgroup X) : Set X) := by
    rw [← E2P.star_inf_M K, hMK, zStar,
      E2P.star_inf_T hmp.isSylow (subnormal_of_mem_cComp hS.mem_cComp) hKH]
  exact E2.kgL2OddTwo_holds (G := X) (X := ⊤) (T := Tstar) (M := Mstar) (K := Kstar)
    (V := Vstar) (t := tstar) (p := p) hmpY hJY htstar le_top hP.ne hP.norm
    (by simpa only [top_inf_eq] using hP.cent) hP.inf hP.comm hHK.symm hp hp8 hPSL
    hMdecompStar hMKstar haut
    (CFSG.Quasithin.Ch3E213M.OS.star_le_pCoreOf hMH hS.hyp.le_pCoreOf) hY28.elem
    hY28.normal_T (hS.four_le.trans (CFSG.Quasithin.Ch3E213M.OS.relIndex_le_card_star hS.hyp))

theorem pkgOddPairedKF1 :
    PkgOddPairedKF1 := by
  intro G _ _ H T M V K hS h1 p hp hp8 hPSL hMK haut
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  obtain ⟨t, htT, hne, hMdecomp⟩ := h1.2
  have htH : t ∈ H := hTH htT
  let X := E2.StarQuot M H
  let Tstar : Subgroup X := E2.star M H T
  let Mstar : Subgroup X := E2.star M H M
  let Kstar : Subgroup X := E2.star M H K
  let Vstar : Subgroup X := E2.star M H V
  let tstar : X := E2P.starMap M H ⟨t, htH⟩
  have hY28 : E2.Hyp28 (⊤ : Subgroup X) Tstar Mstar Vstar :=
    hS.hyp.star (E2.sqtkGroup_top hS.sqtk)
  have hmpY : MinParabolic (⊤ : Subgroup X) Tstar Mstar := E2P.minParabolic_star hmp
  have htstar : tstar ∈ Tstar := E2.starMap_mem_star htH htT
  have hs : IsSimpleGroup ↥(E2.star M H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hPSL).2
  have hP : E2.PairCase (⊤ : Subgroup X) Tstar Kstar tstar :=
    pairCase_star hS htT hne hs
  obtain ⟨hVdecomp, hVcard⟩ :=
    kgL2OddTwo_star hS htT htH hMdecomp hp hp8 hPSL hMK haut hP
  obtain ⟨F0, hF0norm, hVF0, hVcent⟩ :=
    exists_normal_centralizer_of_kgL2OddTwo hmpY.isSylow htstar hY28.normal_T hP.comm hP.inf
      hP.norm hVdecomp hVcard
  exact ⟨F0, hF0norm, hVF0, hVcent⟩

end CFSG.Quasithin.SimsE2.KF1
