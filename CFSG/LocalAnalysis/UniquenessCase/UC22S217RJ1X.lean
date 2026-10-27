module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VPair
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Quasithin.EmptyFaithful.S146D1
import CFSG.Quasithin.EmptyFaithful.S152Y22
import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217rj_le_opp {M L : Subgroup G} (hL : L ∈ calC M) (hs : IsSimpleGroup (Bar2 L))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrL : r ∣ Nat.card (Bar2 L)) : L ≤ Opp r M := by
  rw [← CFSG.RankThree.PartTwo.Sec20.closure_pow_eq_one_eq hL.2.1 hs hr hr2
    (hrL.trans (Subgroup.card_quotient_dvd_card _))]
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine Subgroup.closure_mono fun z hz => ⟨hL.1.le hz.1, ?_⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1
    (show orderOf z ∣ r ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hz.2)
  exact ⟨k, hk⟩

theorem uc22s217rj_eq_one_of_mem_centralizer {M X : Subgroup G} (hX : X ∈ calC M)
    (hZ : center (Bar2 X) = ⊥) {q : Bar2 M} (hq : q ∈ barImage M X)
    (hqc : q ∈ centralizer (barImage M X : Set (Bar2 M))) : q = 1 := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
  have h0 : e.symm ⟨q, hq⟩ ∈ center (Bar2 X) := by
    refine Subgroup.mem_center_iff.2 fun w => e.injective (Subtype.ext ?_)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_centralizer_iff.1 hqc _ (e w).2
  rw [hZ, mem_bot] at h0
  have h1 : (⟨q, hq⟩ : ↥(barImage M X)) = 1 := by
    rw [← e.apply_symm_apply ⟨q, hq⟩, h0, map_one]
  exact congrArg Subtype.val h1

theorem uc22s217rj_one_le_pRank {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q} {r : ℕ}
    (hr : r.Prime) (h : r ∣ Nat.card H) : 1 ≤ CFSG.Open.pRank r H := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) r h
  have hx' : orderOf (x : Q) = r := (Subgroup.orderOf_coe x).trans hx
  exact UC6S846.le_pRank' hr (zpowers_le.2 x.2)
    (CFSG.Open.isElemAbelian_zpowers (by rw [← hx']; exact pow_orderOf_eq_one _))
    (by rw [Nat.card_zpowers, hx', pow_one])

theorem uc22s217rj_exists_inner {M X : Subgroup G} (hX : X ∈ calC M) (hJ : IsJ1 (Bar2 X))
    {y : G} (hyM : y ∈ M) (hyX : y ∈ normalizer (X : Set G)) {n : ℕ} (hy : y ^ n = 1) :
    ∃ a ∈ barImage M X, a⁻¹ * uc22p21cPi M ⟨y, hyM⟩ ∈ centralizer (barImage M X : Set (Bar2 M)) ∧
      a ^ n = 1 := by
  obtain ⟨-, hsimple, hinn⟩ := kJ1_holds (Bar2 X) hJ
  haveI := hsimple
  have hZ : center (Bar2 X) = ⊥ := uc22p21k_center_eq_bot hX.2.2
  have hinj : Function.Injective (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hac : a ∈ center (Bar2 X) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz : a * z * a⁻¹ = z := by
        simpa [MulAut.conj_apply] using DFunLike.congr_fun ha z
      calc z * a = a * z * a⁻¹ * a := by rw [hz]
        _ = a * z := by group
    rw [hZ] at hac
    exact Subgroup.mem_bot.1 hac
  let m : ↥(normalizer (X : Set G)) := ⟨y, hyX⟩
  obtain ⟨ub, hub⟩ := hinn (UC6S846.rhoL X m)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ub
  have huM : (u : G) ∈ M := hX.1.le u.2
  have hN : (u : G)⁻¹ * y ∈ normalizer (X : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer u.2)) hyX
  have hρ : UC6S846.rhoL X ⟨(u : G)⁻¹ * y, hN⟩ = 1 := by
    have e : (⟨(u : G)⁻¹ * y, hN⟩ : ↥(normalizer (X : Set G))) =
        (⟨(u : G), Subgroup.le_normalizer u.2⟩)⁻¹ * m := rfl
    rw [e, map_mul, map_inv, UC6S846.rhoL_inner X u u.2, hub]
    exact inv_mul_cancel _
  have hcb : CentralizesBar ((u : G)⁻¹ * y) X :=
    ⟨hN, fun l hl => (UC6S846.rhoL_fix_iff X ⟨_, hN⟩ ⟨l, hl⟩).1 (by rw [hρ, MulAut.one_apply])⟩
  have hc := uc22s217v_mem_centralizer_barImage hX (mul_mem (inv_mem huM) hyM) hcb
  obtain ⟨e, he⟩ := uc22p22l_barImage_equiv hX
  have hu1 : (QuotientGroup.mk u : Bar2 X) ^ n = 1 := by
    have hmn : m ^ n = 1 := Subtype.ext (by simpa [m] using hy)
    apply hinj
    rw [map_pow, ← hub, ← map_pow, hmn, map_one, map_one]
  refine ⟨uc22p21cPi M ⟨u, huM⟩, uc22p21c_mem_barImage.2 ⟨⟨u, huM⟩, u.2, rfl⟩, ?_, ?_⟩
  · have e2 : uc22p21cPi M ⟨(u : G)⁻¹ * y, mul_mem (inv_mem huM) hyM⟩ =
        (uc22p21cPi M ⟨u, huM⟩)⁻¹ * uc22p21cPi M ⟨y, hyM⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [← e2]
    exact hc
  · have hπu : uc22p21cPi M ⟨u, huM⟩ =
        ((e (QuotientGroup.mk u) : ↥(barImage M X)) : Bar2 M) := (he u).symm
    rw [hπu, ← Subgroup.coe_pow, ← map_pow, hu1, map_one, Subgroup.coe_one]

theorem uc22s217rj_mk_mem_sup {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hLK : L ≠ K) (hJL : IsJ1 (Bar2 L)) (hJK : IsJ1 (Bar2 K))
    (h7 : CFSG.Open.pRank 7 M ≤ 2) {y : G} (hyM : y ∈ M) (hyL : y ∈ normalizer (L : Set G))
    (hyK : y ∈ normalizer (K : Set G)) {k : ℕ} (hy : y ^ 7 ^ k = 1) :
    uc22p21cPi M ⟨y, hyM⟩ ∈ barImage M L ⊔ barImage M K := by
  have hp7 : (7 : ℕ).Prime := by norm_num
  obtain ⟨a, ha, haC, ha7⟩ := uc22s217rj_exists_inner hL hJL hyM hyL hy
  obtain ⟨b, hb, hbC, hb7⟩ := uc22s217rj_exists_inner hK hJK hyM hyK hy
  obtain ⟨c, hc⟩ : ∃ c, c = uc22p21cPi M ⟨y, hyM⟩ := ⟨_, rfl⟩
  rw [← hc] at haC hbC ⊢
  have hcomm := uc22p22l_barImage_commute hL hK hLK
  have hab : a * b = b * a := hcomm a ha b hb
  have hac : a * c = c * a := by
    have h := mem_centralizer_iff.1 haC a ha
    rw [mul_inv_cancel_left] at h
    calc a * c = a * (a⁻¹ * c * a) := by rw [← h]
      _ = c * a := by group
  have hbc : b * c = c * b := by
    have h := mem_centralizer_iff.1 hbC b hb
    rw [mul_inv_cancel_left] at h
    calc b * c = b * (b⁻¹ * c * b) := by rw [← h]
      _ = c * b := by group
  have hc7 : c ^ 7 ^ k = 1 := by
    have hy' : (⟨y, hyM⟩ : ↥M) ^ 7 ^ k = 1 := Subtype.ext (by simpa using hy)
    rw [hc, ← map_pow, hy', map_one]
  have hbL : b ∈ centralizer (barImage M L : Set (Bar2 M)) :=
    mem_centralizer_iff.2 fun q hq => hcomm q hq b hb
  have haK : a ∈ centralizer (barImage M K : Set (Bar2 M)) :=
    mem_centralizer_iff.2 fun q hq => (hcomm a ha q hq).symm
  obtain ⟨z, hz⟩ : ∃ z, z = b⁻¹ * (a⁻¹ * c) := ⟨_, rfl⟩
  have hzL : z ∈ centralizer (barImage M L : Set (Bar2 M)) := hz ▸ mul_mem (inv_mem hbL) haC
  have hzK : z ∈ centralizer (barImage M K : Set (Bar2 M)) := by
    have hz' : z = a⁻¹ * (b⁻¹ * c) := by
      rw [hz, ← mul_assoc, ← mul_assoc, ← mul_inv_rev, ← mul_inv_rev, hab]
    exact hz' ▸ mul_mem (inv_mem haK) hbC
  have hz7 : z ^ 7 ^ k = 1 := by
    have h1 : Commute b⁻¹ (a⁻¹ * c) :=
      (((show Commute b a from hab.symm).inv_right).mul_right (show Commute b c from hbc)).inv_left
    rw [hz, h1.mul_pow, (show Commute a c from hac).inv_left.mul_pow, inv_pow, inv_pow, ha7, hb7,
      hc7, inv_one, one_mul, one_mul]
  by_cases hz1 : z = 1
  ·
    have h1 : a⁻¹ * c = b := (inv_mul_eq_one.1 (hz ▸ hz1)).symm
    rw [show c = a * b by rw [← h1, mul_inv_cancel_left]]
    exact mul_mem_sup ha hb
  exfalso
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp7).1 (orderOf_dvd_of_pow_eq_one hz7)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.1 (by rw [hj, pow_zero]))
  have hwo : orderOf (z ^ (orderOf z / 7)) = 7 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne' (by rw [hj]; exact dvd_pow_self 7 hj0)
  obtain ⟨w, hw⟩ : ∃ w, w = z ^ (orderOf z / 7) := ⟨_, rfl⟩
  rw [← hw] at hwo
  have hWL : zpowers w ≤ centralizer (barImage M L : Set (Bar2 M)) :=
    zpowers_le.2 (hw ▸ pow_mem hzL _)
  have hWK : zpowers w ≤ centralizer (barImage M K : Set (Bar2 M)) :=
    zpowers_le.2 (hw ▸ pow_mem hzK _)
  have hZL : center (Bar2 L) = ⊥ := by
    haveI := (kJ1_holds _ hJL).2.1
    exact uc22p21k_center_eq_bot hL.2.2
  have hZK : center (Bar2 K) = ⊥ := by
    haveI := (kJ1_holds _ hJK).2.1
    exact uc22p21k_center_eq_bot hK.2.2
  have hKW := CFSG.Quasithin.pRank_add_le_pRank_sup hp7 (A := barImage M K) (B := zpowers w)
    (fun x hx q hq => mem_centralizer_iff.1 (hWK hq) x hx)
    ((Subgroup.eq_bot_iff_forall _).2 fun q hq =>
      uc22s217rj_eq_one_of_mem_centralizer hK hZK (mem_inf.1 hq).1 (hWK (mem_inf.1 hq).2))
  have hKWL : barImage M K ⊔ zpowers w ≤ centralizer (barImage M L : Set (Bar2 M)) :=
    sup_le (fun q hq => mem_centralizer_iff.2 fun x hx => hcomm x hx q hq) hWL
  have hLKW := CFSG.Quasithin.pRank_add_le_pRank_sup hp7 (A := barImage M L)
    (B := barImage M K ⊔ zpowers w) (fun x hx q hq => mem_centralizer_iff.1 (hKWL hq) x hx)
    ((Subgroup.eq_bot_iff_forall _).2 fun q hq =>
      uc22s217rj_eq_one_of_mem_centralizer hL hZL (mem_inf.1 hq).1 (hKWL (mem_inf.1 hq).2))
  have hcard : ∀ X ∈ calC M, IsJ1 (Bar2 X) → 7 ∣ Nat.card (barImage M X) := by
    intro X hX hJX
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
    rw [← Nat.card_congr e.toEquiv, (kJ1_holds _ hJX).1]
    norm_num
  have hL1 := uc22s217rj_one_le_pRank hp7 (hcard L hL hJL)
  have hK1 := uc22s217rj_one_le_pRank hp7 (hcard K hK hJK)
  have hW1 := uc22s217rj_one_le_pRank hp7 (H := zpowers w) (by rw [Nat.card_zpowers, hwo])
  have htop := CFSG.SectionRank.pRank_mono hp7.one_lt
    (le_top : barImage M L ⊔ (barImage M K ⊔ zpowers w) ≤ ⊤)
  have hM := uc22s206c_pRank_le M hp7 (by norm_num)
  omega

theorem uc22s217rj_conjClosure_eq_opp {M L : Subgroup G} (hL : L ∈ calC M)
    (hc2 : (conjSetOf M L).ncard = 2) (hJ1 : IsJ1 (Bar2 L)) (h7 : CFSG.Open.pRank 7 M ≤ 2) :
    conjClosure M L = Opp 7 M := by
  obtain ⟨K, hK, hKL⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc2]; norm_num) L
  have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hJK := uc22s217v_isJ1_of_mem hJ1 hK
  have hcK : (conjSetOf M K).ncard = 2 := by rwa [uc22p2214_conjSetOf_eq hK]
  refine le_antisymm (iSup₂_le fun X hX => ?_) ?_
  · obtain ⟨hcard, hsimple, -⟩ := kJ1_holds (Bar2 X) (uc22s217v_isJ1_of_mem hJ1 hX)
    exact uc22s217rj_le_opp (uc22p2214_calC_of_mem_conjSetOf hL hX) hsimple (by norm_num)
      (by norm_num) (by rw [hcard]; norm_num)
  · unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyM, j, hj⟩
    have hodd : Odd (orderOf y) := by
      rw [hj]
      exact Odd.pow (by decide)
    have hy7 : y ^ 7 ^ j = 1 := by
      rw [← hj]
      exact pow_orderOf_eq_one y
    have h := uc22s217rj_mk_mem_sup hL hKC hKL.symm hJ1 hJK h7 hyM
      (uc22p2214_mem_normalizer_of_odd hc2 hyM hodd) (uc22p2214_mem_normalizer_of_odd hcK hyM hodd)
      hy7
    exact CFSG.Quasithin.S152Y.mem_of_mk_mem_of_odd (uc22p22v_le_normalizer_conjClosure M L) hyM
      hodd (sup_le (uc22p22u_barImage_mono (uc22p22v_le_conjClosure M L))
        (uc22p22u_barImage_mono
          (le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) K hK le_rfl)) h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
