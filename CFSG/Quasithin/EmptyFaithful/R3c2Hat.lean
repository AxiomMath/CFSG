module

public import CFSG.Quasithin.EmptyFaithful.R3c2Excl
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top)
open CFSG.Quasithin.H13.L34 (ListOrd pslOrd psuOrd slOrd suOrd pslOrd_listOrd psuOrd_not_listOrd
  slOrd_not_listOrd suOrd_listOrd card_of_isPSLEps3q card_of_isSLEps3)

theorem card_of_isHat_alt6 {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, card_alternatingGroup_six]

theorem card_quotient_hat {X Q : Type} [Group X] [Finite X] [Group Q]
    (h : IsHat X (alternatingGroup (Fin 6))) (π : X →* Q) (hπ : Function.Surjective π)
    (hQ : ¬ Subsingleton Q) : Nat.card Q = 1080 ∨ Nat.card Q = 360 := by
  have hX := card_of_isHat_alt6 h
  have hne : π.ker ≠ ⊤ := by
    intro ht
    refine hQ ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'), MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]
  have hle := le_center_of_normal_ne_top h.1 hne
  have hdvd : Nat.card π.ker ∣ 3 := by
    rw [← h.2.1]
    exact Subgroup.card_dvd_of_le hle
  have hprod : Nat.card Q * Nat.card π.ker = 1080 := by
    rw [← hX, Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · left
    rw [h1] at hprod
    omega
  · right
    rw [h3] at hprod
    omega

theorem not_case2_of_card_hat6 {Q : Type} [Group Q] (h : Nat.card Q = 1080 ∨ Nat.card Q = 360)
    (s : Bool) (q : ℕ) (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (hQ : IsPSLEps3q s q Q) :
    False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isPSLEps3q hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL h
    have h4 := pslOrd_listOrd hq2 hL
    subst h4
    simp [pslOrd] at h
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL
    have hq3 : q % 3 = 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      have := Int.emod_emod_of_dvd (q : ℤ) (dvd_refl (3 : ℤ))
      unfold Int.ModEq at hq
      omega
    exact psuOrd_not_listOrd hq2 hq3 hL

theorem not_isSLEps3_of_card_hat6 {Q : Type} [Group Q] (h : Nat.card Q = 1080 ∨ Nat.card Q = 360)
    (s : Bool) (q : ℕ) (hQ : IsSLEps3 s q Q) : False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isSLEps3 hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL
    exact slOrd_not_listOrd hq2 hL
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL h
    have h3 := suOrd_listOrd hq2 hL
    subst h3
    simp [suOrd] at h

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

theorem eq_thetaOf_of_star_hat (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hSQ : SQTKGroup ↥I) (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15325 T Mc M V₁ V₂ Yp I)
    (hLc : L ∈ cComp I) (hnorm : I ≤ Subgroup.normalizer (L : Set G))
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hHat : IsHat ↥(Star153 T I L) (alternatingGroup (Fin 6))) : L = thetaOf I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hXq : CFSG.IsQuasisimple ↥(Star153 T I L) := hHat.1
  have h3r : FFC.ThreeRank2 ↥(Star153 T I L) := FFC.threeRank2_hat hHat
  have hr : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [pRank_three_eq_star hI hF hLI]
    exact h3r.pRank_two_le
  obtain ⟨ψ, hψ, hψ1⟩ := exists_starSurj T I L hLI
  have hker3 : ∀ x ∈ ψ.ker, orderOf x ≠ 3 := fun x hx h3 =>
    orderOf_ne_three_of_mem_centralizer_UI hI hF (hLI x.2) ((hψ1 x).1 hx)
      (by rw [Subgroup.orderOf_coe]; exact h3)
  have hX3 : 3 ∣ Nat.card ↥(Star153 T I L) := by
    rw [card_of_isHat_alt6 hHat]
    norm_num
  have hgen : Subgroup.closure {y : ↥(Star153 T I L) | orderOf y = 3} = ⊤ := by
    by_contra hne
    have := normal_closure_orderOf_eq (X := ↥(Star153 T I L)) 3
    have hle := le_center_of_normal_ne_top hXq hne
    obtain ⟨x, y, hx1, hx3, hy3, -, hyx⟩ := h3r
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hxc : x ∈ Subgroup.center ↥(Star153 T I L) := hle (Subgroup.subset_closure hxo)
    have hyc : y ∈ Subgroup.center ↥(Star153 T I L) := hle (Subgroup.subset_closure hyo)
    have hz : Subgroup.zpowers x = Subgroup.center ↥(Star153 T I L) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxc)
        (by rw [hHat.2.1, Nat.card_zpowers, hxo])
    exact hyx (hz ▸ hyc)
  have hθ : L ≤ thetaOf I := le_thetaOf_of_surjection hLI hperf hQ ψ hψ hker3 hgen hX3
  obtain ⟨π, hπ⟩ := exists_surjection_star_starImage hI hF hLI hnorm
  have hcard := card_quotient_hat hHat π hπ (not_subsingleton_starImage hLI (by omega))
  have hn2 : ¬ A318Case2 (starImage 3 (L.subgroupOf I)) := by
    rintro ⟨s, q, hmod, hPSL, -⟩
    exact not_case2_of_card_hat6 hcard s q hmod hPSL
  have hn3 : ¬ A318Case3b (starImage 3 (L.subgroupOf I)) := by
    rintro ⟨s, q, x, hSL, -⟩
    exact not_isSLEps3_of_card_hat6 hcard s q hSL
  exact eq_thetaOf_of_a318_of_group hF318 h36 h38 hSQ hLc hQ hr hn2 (fun _ => hn3) hθ

end CFSG.Quasithin.R3c2
