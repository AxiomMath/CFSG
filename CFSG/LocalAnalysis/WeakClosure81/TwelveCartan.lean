module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

theorem rankOne_finite {Y : Type} [Group Y] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n Y ∨ CFSG.Quasithin.IsSz n Y) : Finite Y := by
  rcases h with h | h
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.toEquiv.symm
  · obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.toEquiv.symm

theorem le_sylow_of_le_normalizer {G : Type} [Group G] [Finite G] {S : Sylow 2 G}
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXN : X ≤ normalizer (S : Set G)) :
    X ≤ (S : Subgroup G) := by
  have hsup : IsPGroup 2 (((S : Subgroup G) ⊔ X : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup' hX hXN
  have htop : (((S : Subgroup G) ⊔ X : Subgroup G)) = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_left
  rw [← htop]
  exact le_sup_right

section RankOne

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem rankOne_borel_ne_top
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) :
    normalizer (S : Set G) ≠ ⊤ := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  intro htop
  have hborel : borel (S : Subgroup G) = ⊤ := by
    show normalizer (S : Set G) = ⊤
    exact htop
  have h1 : (borel (S : Subgroup G)).index = 1 := Subgroup.index_eq_one.mpr hborel
  rw [hc.index_eq] at h1
  have hq : 0 < (2 ^ n) ^ i := pow_pos (pow_pos (by norm_num) n) i
  omega

theorem rankOne_centralizer_eq_sylow
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S : Sylow 2 G} {z : G}
    (hz : z ∈ rootCenter (S : Subgroup G)) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) = (S : Subgroup G) := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  exact hc.centralizer_eq_of_e_one hz hz1

theorem rankOne_exists_swap_in_dihedral
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {S S' : Sylow 2 G}
    (hne : S ≠ S') {a b : G} (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S' : Subgroup G))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ w : G, w ∈ Subgroup.closure ({a, b} : Set G) ∧ w * w = 1 ∧ w * a * w⁻¹ = b := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  obtain ⟨i', t', hc'⟩ := rankOne_exists_benderCore hG S'
  have haR : a ∈ rootCenter (S : Subgroup G) := hc.mem_rootCenter_of_mul_self ha ha2
  have hbR : b ∈ rootCenter (S' : Subgroup G) := hc'.mem_rootCenter_of_mul_self hb hb2
  have hCa : centralizer ({a} : Set G) = (S : Subgroup G) := hc.centralizer_eq_of_e_one haR ha1
  have hCb : centralizer ({b} : Set G) = (S' : Subgroup G) := hc'.centralizer_eq_of_e_one hbR hb1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  let r : G := a * b
  have har : a * r * a = r⁻¹ := by
    have h1 : a * r * a = b * a := by
      simp only [r]
      rw [show a * (a * b) * a = (a * a) * (b * a) by group, ha2, one_mul]
    have h2 : r⁻¹ = b * a := by
      simp only [r, mul_inv_rev, hai, hbi]
    rw [h1, h2]
  have hbr : b * r * b = r⁻¹ := by
    have h1 : b * r * b = b * a := by
      simp only [r]
      rw [show b * (a * b) * b = (b * a) * (b * b) by group, hb2, mul_one]
    have h2 : r⁻¹ = b * a := by
      simp only [r, mul_inv_rev, hai, hbi]
    rw [h1, h2]
  have hOdd : Odd (orderOf r) := by
    by_contra hodd
    have hEven : Even (orderOf r) := Nat.not_odd_iff_even.mp hodd
    have hordne : orderOf r ≠ 0 := (orderOf_pos r).ne'
    have h2dvd : 2 ∣ orderOf r := hEven.two_dvd
    let c : G := r ^ (orderOf r / 2)
    have hcord : orderOf c = 2 := by
      show orderOf (r ^ (orderOf r / 2)) = 2
      exact orderOf_pow_orderOf_div hordne h2dvd
    have hc2 : c * c = 1 := by
      rw [← pow_two, ← hcord, pow_orderOf_eq_one]
    have hc1 : c ≠ 1 := by
      intro h
      rw [h] at hcord
      simp only [orderOf_one] at hcord
      omega
    have hconjpow : a * c * a = c⁻¹ := by
      show a * (r ^ (orderOf r / 2)) * a = (r ^ (orderOf r / 2))⁻¹
      have h := map_pow (MulAut.conj a) r (orderOf r / 2)
      simp only [MulAut.conj_apply, hai, har] at h
      rw [h, inv_pow]
    have hconjpowb : b * c * b = c⁻¹ := by
      show b * (r ^ (orderOf r / 2)) * b = (r ^ (orderOf r / 2))⁻¹
      have h := map_pow (MulAut.conj b) r (orderOf r / 2)
      simp only [MulAut.conj_apply, hbi, hbr] at h
      rw [h, inv_pow]
    have hac : a * c = c * a := by
      have hca : a * c * a = c := by
        rw [hconjpow]
        exact inv_eq_of_mul_eq_one_right hc2
      have hcong := congrArg (fun z : G => z * a) hca
      simpa [mul_assoc, ha2] using hcong
    have hbc : b * c = c * b := by
      have hcb : b * c * b = c := by
        rw [hconjpowb]
        exact inv_eq_of_mul_eq_one_right hc2
      have hcong := congrArg (fun z : G => z * b) hcb
      simpa [mul_assoc, hb2] using hcong
    have hcCa : c ∈ centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hac
    have hcCb : c ∈ centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hbc
    have hcS : c ∈ (S : Subgroup G) := hCa ▸ hcCa
    have hcS' : c ∈ (S' : Subgroup G) := hCb ▸ hcCb
    have hV : Subgroup.zpowers c ≠ ⊥ := by
      intro hbot
      exact hc1 (Subgroup.zpowers_eq_bot.mp hbot)
    have hVS : Subgroup.zpowers c ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hcS
    have hVS' : Subgroup.zpowers c ≤ (S' : Subgroup G) := Subgroup.zpowers_le.mpr hcS'
    exact hne (rankOne_sylow_eq_of_ne_bot hG hV hVS hVS').symm
  obtain ⟨k, hyy⟩ := exists_sq_eq_of_odd_orderOf hOdd
  let y : G := r ^ k
  let w : G := a * y
  have hyy' : y * y = r := hyy
  have hay : a * y * a = y⁻¹ := by
    show a * (r ^ k) * a = (r ^ k)⁻¹
    have h := map_pow (MulAut.conj a) r k
    simp only [MulAut.conj_apply, hai, har] at h
    rw [h, inv_pow]
  have hww : w * w = 1 := by
    show (a * y) * (a * y) = 1
    rw [show (a * y) * (a * y) = (a * y * a) * y by group, hay, inv_mul_cancel]
  have hwa : w * a * w⁻¹ = b := by
    rw [inv_eq_of_mul_eq_one_right hww]
    show (a * y) * a * (a * y) = b
    have h1 : (a * y) * a * (a * y) = (a * y) * (a * a) * y := by group
    rw [h1, ha2, mul_one]
    have h2 : (a * y) * y = a * (y * y) := by group
    rw [h2, hyy']
    have h3 : a * r = b := by
      simp only [r]
      rw [show a * (a * b) = (a * a) * b by group, ha2, one_mul]
    exact h3
  have hmem : w ∈ Subgroup.closure ({a, b} : Set G) := by
    have haC : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hbC : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hrC : r ∈ Subgroup.closure ({a, b} : Set G) := by
      simp only [r]
      exact Subgroup.mul_mem _ haC hbC
    have hyC : y ∈ Subgroup.closure ({a, b} : Set G) := by
      show r ^ k ∈ Subgroup.closure ({a, b} : Set G)
      exact Subgroup.pow_mem _ hrC k
    show a * y ∈ Subgroup.closure ({a, b} : Set G)
    exact Subgroup.mul_mem _ haC hyC
  exact ⟨w, hmem, hww, hwa⟩

theorem rankOne_exists_cartan
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) :
    ∃ (T : Subgroup G) (t : G), T ≤ normalizer (S : Set G) ∧ (S : Subgroup G) ⊓ T = ⊥ ∧
      (S : Subgroup G) ⊔ T = normalizer (S : Set G) ∧ IsCyclic T ∧ Nat.card T = 2 ^ n - 1 ∧
      t * t = 1 ∧ t ∉ normalizer (S : Set G) ∧ (∀ x ∈ T, t * x * t = x⁻¹) ∧
      ∀ x ∈ T, x ≠ 1 → ∀ s ∈ (S : Subgroup G), s * x = x * s → s = 1 := by
  obtain ⟨i, t, hc⟩ := rankOne_exists_benderCore hG S
  refine ⟨cartan (S : Subgroup G) t, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cartan_le_borel (S : Subgroup G) t
  · exact hc.inf_eq
  · exact hc.sup_eq
  · exact hc.isCyclic
  · simpa using hc.card_cartan
  · exact hc.sq_eq_one
  · exact hc.not_mem
  · intro x hx
    have hx' : x ∈ ⁅cartan (S : Subgroup G) t, Subgroup.zpowers t⁆ := by
      rw [← hc.cartan_eq_commutator rfl]
      exact hx
    exact (hc.mem_commutator_cartan_iff.mp hx').2
  · intro x hxT hx1 s hsS hsx
    by_contra hs1
    have hspos : orderOf s ≠ 0 := (orderOf_pos s).ne'
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_orderOf (p := 2) (G := ↥(S : Subgroup G))).mp S.isPGroup' ⟨s, hsS⟩
    have hk' : orderOf s = 2 ^ k := by simpa using hk
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hs1
      have h1 : orderOf s = 1 := by rw [hk', hk0]; norm_num
      exact orderOf_eq_one_iff.mp h1
    have h2dvd : 2 ∣ orderOf s := by
      rw [hk']
      exact dvd_pow_self 2 hk0
    have hzord : orderOf (s ^ (orderOf s / 2)) = 2 :=
      orderOf_pow_orderOf_div hspos h2dvd
    have hz2 : s ^ (orderOf s / 2) * s ^ (orderOf s / 2) = 1 := by
      have h : (s ^ (orderOf s / 2)) ^ orderOf (s ^ (orderOf s / 2)) = 1 :=
        pow_orderOf_eq_one _
      rw [hzord] at h
      simpa [pow_two] using h
    have hz1 : s ^ (orderOf s / 2) ≠ 1 := by
      intro h
      rw [h] at hzord
      simp only [orderOf_one] at hzord
      omega
    have hzS : s ^ (orderOf s / 2) ∈ (S : Subgroup G) := Subgroup.pow_mem _ hsS _
    have hzR : s ^ (orderOf s / 2) ∈ rootCenter (S : Subgroup G) :=
      hc.mem_rootCenter_of_mul_self hzS hz2
    have hCz : centralizer ({s ^ (orderOf s / 2)} : Set G) = (S : Subgroup G) :=
      hc.centralizer_eq_of_e_one hzR hz1
    have hcomm : Commute s x := hsx
    have hzx : s ^ (orderOf s / 2) * x = x * s ^ (orderOf s / 2) :=
      hcomm.pow_left (orderOf s / 2)
    have hxCz : x ∈ centralizer ({s ^ (orderOf s / 2)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hzx
    have hxS : x ∈ (S : Subgroup G) := hCz ▸ hxCz
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hc.inf_eq]
      exact ⟨hxS, hxT⟩
    exact hx1 (Subgroup.mem_bot.mp hxbot)

end RankOne

end CFSG.LocalAnalysis.WeakClosure81
