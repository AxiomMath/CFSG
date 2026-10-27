module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SExcl
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SLiftP
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SSyl
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSp)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf1422 {X : Type*} [Group X] [Finite X] (H N : Subgroup X)
    [N.Normal] : Nat.card (H ⊔ N : Subgroup X) * Nat.card (H ⊓ N : Subgroup X) =
      Nat.card H * Nat.card N := by
  have e := QuotientGroup.quotientInfEquivProdNormalQuotient H N
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h3 : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h3] at h1
  rw [h4, ← Nat.card_congr e.toEquiv] at h2
  rw [h2, h1]
  ring

theorem card_img148_of_injOn1422 {A Y : Subgroup G} [(ker148 A Y).Normal] {X : Subgroup G}
    (hX : X ≤ Y ⊔ A)
    (hinj : ∀ x ∈ X, ∀ y ∈ X, ∀ (hx : x ∈ Y ⊔ A) (hy : y ∈ Y ⊔ A),
      QuotientGroup.mk' (ker148 A Y) ⟨x, hx⟩ = QuotientGroup.mk' (ker148 A Y) ⟨y, hy⟩ → x = y) :
    Nat.card (img148 A Y X) = Nat.card X := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x : ↥X =>
    (⟨QuotientGroup.mk' (ker148 A Y) ⟨x, hX x.2⟩, mem_img148_iff.mpr ⟨x, hX x.2, x.2, rfl⟩⟩ :
      ↥(img148 A Y X))) ⟨fun x y hxy => ?_, ?_⟩)
  · exact Subtype.ext (hinj x x.2 y y.2 _ _ (congrArg Subtype.val hxy))
  · rintro ⟨z, hz⟩
    obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hz
    exact ⟨⟨g, hgX⟩, rfl⟩

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem not_innerOn_Sp48 (hKF : KF1422Sp48) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* projSp 2 (GaloisField 2 3)) :
    ¬ InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A) := by
  intro hin
  have hA : IsE27 A := h.pt.std.isE27
  have hne : Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) ≠ 360 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.PGLModel.card_projSp_two_eight]
    norm_num
  have hAJ' := img148_mono (A := A) (Y := Subgroup.normalizer (S : Set G))
    (h.le_J_of_innerOn hne hin)
  have hE := isE27_subgroupOf1422 hAJ' (img148_isE27 hA)
  exact hKF.1 _ ⟨ψ⟩ _ hE.1 hE.2

theorem card_J_inf_A (h : Cfg A c L R S J)
    (hnin : ¬ InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A)) :
    Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J ⊓
      img148 A (Subgroup.normalizer (S : Set G)) A : Subgroup _) = 9 := by
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  have hA : IsE27 A := h.pt.std.isE27
  obtain ⟨-, hB9, hBK⟩ := h.B_bar_facts
  have hBle : img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) ≤ J' ⊓ A' :=
    le_inf (hBK.trans (img148_mono h.K_le)) (img148_mono inf_le_left)
  have h9 : 9 ≤ Nat.card (J' ⊓ A' : Subgroup _) := hB9 ▸ Subgroup.card_le_of_le hBle
  have hA27 : Nat.card A' = 27 := (img148_isE27 (Y := Subgroup.normalizer (S : Set G)) hA).2
  have hdvd : Nat.card (J' ⊓ A' : Subgroup _) ∣ 27 := hA27 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hne : Nat.card (J' ⊓ A' : Subgroup _) ≠ 27 := by
    intro h27
    have heq : J' ⊓ A' = A' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h27, hA27])
    have hcJ : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ J' := by
      have h1 : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ A' :=
        alpha148_mem_img148 h.pt.mem_A
      rw [← heq] at h1
      exact h1.1
    exact hnin ⟨_, hcJ, fun y _ => rfl⟩
  have : Nat.card (J' ⊓ A' : Subgroup _) ∈ Nat.divisors 27 := by
    rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  have h27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [h27] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem card_sup_Sp48 (h : Cfg A c L R S J)
    (hnin : ¬ InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A)) :
    Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J ⊔
      img148 A (Subgroup.normalizer (S : Set G)) A : Subgroup _) =
      3 * Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) := by
  haveI := h.normal_J
  have hA : IsE27 A := h.pt.std.isE27
  have h1 := card_sup_mul_card_inf1422 (img148 A (Subgroup.normalizer (S : Set G)) A)
    (img148 A (Subgroup.normalizer (S : Set G)) J)
  rw [sup_comm (img148 A (Subgroup.normalizer (S : Set G)) A),
    inf_comm (img148 A (Subgroup.normalizer (S : Set G)) A), h.card_J_inf_A hnin,
    (img148_isE27 (Y := Subgroup.normalizer (S : Set G)) hA).2] at h1
  omega

theorem centralizer_eq_bot_Sp48 (h : Cfg A c L R S J)
    (hne : Nat.card (img148 A (Subgroup.normalizer (S : Set G)) J) ≠ 360)
    (hnin : ¬ InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A)) :
    (img148 A (Subgroup.normalizer (S : Set G)) J ⊔ img148 A (Subgroup.normalizer (S : Set G)) A)
      ⊓ Subgroup.centralizer (img148 A (Subgroup.normalizer (S : Set G)) J :
        Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
          ker148 A (Subgroup.normalizer (S : Set G)))) = ⊥ := by
  haveI := h.normal_J
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  set Z := (J' ⊔ A') ⊓ Subgroup.centralizer (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
    ker148 A (Subgroup.normalizer (S : Set G)))) with hZ
  obtain ⟨-, hcen⟩ := h.center_J_eq_bot hne
  have hZJ : Z ⊓ J' = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxZ, hxJ⟩
    have hx : (⟨x, hxJ⟩ : ↥J') ∈ Subgroup.center ↥J' := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxZ.2 y y.2)
    rw [hcen, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
  have h1 := card_sup_mul_card_inf1422 Z J'
  rw [hZJ, Subgroup.card_bot, mul_one] at h1
  have hle : Z ⊔ J' ≤ J' ⊔ A' := sup_le inf_le_left le_sup_left
  have h2 : Nat.card (Z ⊔ J' : Subgroup _) ∣ 3 * Nat.card J' :=
    h.card_sup_Sp48 hnin ▸ Subgroup.card_dvd_of_le hle
  rw [h1] at h2
  have hJpos : 0 < Nat.card J' := Nat.card_pos
  have hZ3 : Nat.card Z ∣ 3 := Nat.dvd_of_mul_dvd_mul_right hJpos h2
  rcases (Nat.dvd_prime Nat.prime_three).mp hZ3 with hZ1 | hZ3'
  · exact Subgroup.eq_bot_of_card_eq Z hZ1
  · exfalso
    apply hnin
    have heq : Z ⊔ J' = J' ⊔ A' := Subgroup.eq_of_le_of_card_ge hle (by
      rw [h1, hZ3', h.card_sup_Sp48 hnin])
    have hc : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ Z ⊔ J' :=
      heq ▸ Subgroup.mem_sup_right (alpha148_mem_img148 h.pt.mem_A)
    have hc' : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈
        ((Z : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
          ker148 A (Subgroup.normalizer (S : Set G)))) *
        (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
          ker148 A (Subgroup.normalizer (S : Set G))))) := by
      rw [← Subgroup.mul_normal Z J']
      exact hc
    obtain ⟨z, hz, j, hj, hzj⟩ := hc'
    refine ⟨j, hj, fun y hy => ?_⟩
    rw [← hzj]
    have hjy : j * y * j⁻¹ ∈ J' := J'.mul_mem (J'.mul_mem hj hy) (J'.inv_mem hj)
    have hzc := Subgroup.mem_centralizer_iff.mp hz.2 _ hjy
    calc z * j * y * (z * j)⁻¹ = z * (j * y * j⁻¹) * z⁻¹ := by group
      _ = (j * y * j⁻¹) * z * z⁻¹ := by rw [hzc]
      _ = j * y * j⁻¹ := by group

theorem exists_sylow_Sp48 (hKF : KF1422Sp48) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* projSp 2 (GaloisField 2 3)) :
    ∃ P : Subgroup (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))),
      img148 A (Subgroup.normalizer (S : Set G)) A ≤ P ∧ IsPGroup 3 P ∧ Nat.card P = 243 ∧
      P ≤ img148 A (Subgroup.normalizer (S : Set G)) J ⊔
        img148 A (Subgroup.normalizer (S : Set G)) A ∧
      (∀ x ∈ P ⊓ img148 A (Subgroup.normalizer (S : Set G)) J,
        ∀ y ∈ P ⊓ img148 A (Subgroup.normalizer (S : Set G)) J, x * y = y * x) ∧
      (∀ x ∈ P, x ^ 3 = 1 → x ∈ img148 A (Subgroup.normalizer (S : Set G)) A) ∧
      ∀ x ∈ img148 A (Subgroup.normalizer (S : Set G)) A,
        x ∉ img148 A (Subgroup.normalizer (S : Set G)) J →
        ∀ y ∈ img148 A (Subgroup.normalizer (S : Set G)) A,
          y ∉ img148 A (Subgroup.normalizer (S : Set G)) J →
          ∃ p ∈ P ⊓ img148 A (Subgroup.normalizer (S : Set G)) J,
            Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y := by
  haveI := h.normal_J
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  set C := J' ⊔ A' with hC
  have hA : IsE27 A := h.pt.std.isE27
  have hnin := h.not_innerOn_Sp48 hKF ψ
  have hne : Nat.card J' ≠ 360 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.PGLModel.card_projSp_two_eight]
    norm_num
  have hJC : J' ≤ C := le_sup_left
  have hAC : A' ≤ C := le_sup_right
  set J₀ := J'.subgroupOf C with hJ₀
  have hJ₀n : J₀.Normal := Subgroup.normal_subgroupOf
  have hJ₀ψ : Nonempty (↥J₀ ≃* projSp 2 (GaloisField 2 3)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hJC).trans ψ⟩
  have hcent : Subgroup.centralizer (J₀ : Set ↥C) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) ∈ C ⊓ Subgroup.centralizer (J' : Set _) := by
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hz ⟨y, hJC hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val this
    rw [h.centralizer_eq_bot_Sp48 hne hnin, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  have hcardC : Nat.card ↥C = 3 * Nat.card J₀ := by
    rw [h.card_sup_Sp48 hnin, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
  set E := A'.subgroupOf C with hE
  have hEe := isE27_subgroupOf1422 hAC (img148_isE27 hA)
  have hEJ : Nat.card (E ⊓ J₀ : Subgroup ↥C) = 9 := by
    have hmap : (E ⊓ J₀).map C.subtype = J' ⊓ A' := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.mp hy2, Subgroup.mem_subgroupOf.mp hy1⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hJC hx1⟩, ⟨hx2, hx1⟩, rfl⟩
    rw [← h.card_J_inf_A hnin, ← hmap, Subgroup.card_map_of_injective C.subtype_injective]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.1.2 x x.2)⟩
  obtain ⟨P₀, hEP₀⟩ := hE3.exists_le_sylow
  have hP243 : Nat.card (P₀ : Subgroup ↥C) = 243 := by
    have hidx := (P₀ : Subgroup ↥C).index_mul_card
    have hnd := P₀.not_dvd_index
    obtain ⟨k, hk⟩ := P₀.isPGroup'.exists_card_eq
    rw [hcardC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv, Nat.card_congr ψ.toEquiv,
      CFSG.PGLModel.card_projSp_two_eight, hk] at hidx
    have hk20 : k < 21 := by
      by_contra hk'
      have h1 : 3 ^ 21 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3 ^ k ≤ 3 * 1056706560 := by
        rw [← hidx]
        exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at hidx)
      omega
    rw [hk]
    interval_cases k <;> omega
  obtain ⟨hPab, hPΩ, hPtr⟩ := hKF.2.1 ↥C J₀ hJ₀n hJ₀ψ hcent hcardC E hEe.1 hEe.2 hEJ P₀
    P₀.isPGroup' hEP₀ hP243
  refine ⟨(P₀ : Subgroup ↥C).map C.subtype, ?_, P₀.isPGroup'.map _, ?_, Subgroup.map_subtype_le _,
    ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hAC hx⟩, hEP₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hP243]
  · rintro _ ⟨⟨x, hxP, rfl⟩, hxJ⟩ _ ⟨⟨y, hyP, rfl⟩, hyJ⟩
    have := hPab.is_comm.comm ⟨x, hxP, Subgroup.mem_subgroupOf.mpr hxJ⟩
      ⟨y, hyP, Subgroup.mem_subgroupOf.mpr hyJ⟩
    exact congrArg (fun z : ↥((P₀ : Subgroup ↥C) ⊓ J₀) => C.subtype (z : ↥C)) this
  · rintro _ ⟨x, hxP, rfl⟩ hx3
    have hx3' : x ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    exact Subgroup.mem_subgroupOf.mp (hPΩ x hxP hx3')
  · intro x hxA hxJ y hyA hyJ
    obtain ⟨p, ⟨hpP, hpJ⟩, hp⟩ := hPtr ⟨x, hAC hxA⟩ (Subgroup.mem_subgroupOf.mpr hxA)
      (fun h1 => hxJ (Subgroup.mem_subgroupOf.mp h1)) ⟨y, hAC hyA⟩
      (Subgroup.mem_subgroupOf.mpr hyA) (fun h1 => hyJ (Subgroup.mem_subgroupOf.mp h1))
    refine ⟨p, ⟨⟨p, hpP, rfl⟩, Subgroup.mem_subgroupOf.mp hpJ⟩, ?_⟩
    have := congrArg (Subgroup.map C.subtype) hp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    simpa using this

theorem card_P_inf_J_Sp48 (h : Cfg A c L R S J)
    (hnin : ¬ InnerOn148 (img148 A (Subgroup.normalizer (S : Set G)) J)
      (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A))
    {P' : Subgroup (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))}
    (hAP' : img148 A (Subgroup.normalizer (S : Set G)) A ≤ P') (hP'243 : Nat.card P' = 243)
    (hP'C : P' ≤ img148 A (Subgroup.normalizer (S : Set G)) J ⊔
      img148 A (Subgroup.normalizer (S : Set G)) A) :
    Nat.card (P' ⊓ img148 A (Subgroup.normalizer (S : Set G)) J : Subgroup _) = 81 := by
  haveI := h.normal_J
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  have h1 := card_sup_mul_card_inf1422 P' J'
  have hle : P' ⊔ J' ≤ J' ⊔ A' := sup_le hP'C le_sup_left
  have h2 : Nat.card (P' ⊔ J' : Subgroup _) ≤ 3 * Nat.card J' :=
    h.card_sup_Sp48 hnin ▸ Subgroup.card_le_of_le hle
  have hJpos : 0 < Nat.card J' := Nat.card_pos
  have h3 : Nat.card (P' ⊓ J' : Subgroup _) ∣ 3 ^ 5 := by
    rw [show (3 : ℕ) ^ 5 = 243 by norm_num, ← hP'243]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (P' ⊓ J' : Subgroup _) ≠ 243 := by
    intro h243
    have heq : P' ⊓ J' = P' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h243, hP'243])
    have hcJ : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ J' := by
      have h4 : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ P' :=
        hAP' (alpha148_mem_img148 h.pt.mem_A)
      rw [← heq] at h4
      exact h4.2
    exact hnin ⟨_, hcJ, fun y _ => rfl⟩
  have h81 : 81 ≤ Nat.card (P' ⊓ J' : Subgroup _) := by
    have h4 : 243 * Nat.card J' ≤ 3 * Nat.card J' * Nat.card (P' ⊓ J' : Subgroup _) := by
      rw [← hP'243, ← h1]
      exact Nat.mul_le_mul_right _ h2
    have h5 : 3 * Nat.card J' * 81 ≤ 3 * Nat.card J' * Nat.card (P' ⊓ J' : Subgroup _) := by
      calc 3 * Nat.card J' * 81 = 243 * Nat.card J' := by ring
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_left h5 (Nat.mul_pos (by norm_num) hJpos)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  rw [hk'] at hne h81 ⊢
  interval_cases k
  all_goals first | rfl | exact absurd rfl hne | (norm_num at h81)

theorem exists_fusion_data_Sp48 (hKF : KF1422Sp48) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* projSp 2 (GaloisField 2 3)) :
    ∃ P N : Subgroup G, A ≤ P ∧ IsPGroup 3 P ∧ N ≤ P ∧ (N.subgroupOf P).Normal ∧
      Nat.card P = 3 * Nat.card N ∧ c ∉ N ∧ A ⊓ L ≤ N ∧
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ 27 < Nat.card P ∧
      (∀ x ∈ P, x ^ 3 = 1 → x ∈ A) ∧
      ∀ x ∈ A, x ∉ A ⊓ L → ∀ y ∈ A, y ∉ A ⊓ L →
        ∃ p ∈ N, Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y := by
  haveI := h.normal_J
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  set B' := img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) with hB'
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hA3' : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
  have hnin := h.not_innerOn_Sp48 hKF ψ
  obtain ⟨P', hAP', hP'3, hP'243, hP'C, hP'ab, hP'Ω, hP'tr⟩ := h.exists_sylow_Sp48 hKF ψ
  obtain ⟨P, hAP, hPYA, hP3, hPP', hPcard, hPinj⟩ :=
    exists_lift_isPGroup_three148 hA3' h.A_le_NM hP'3 hAP'
  set π := QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) with hπ
  set JJ : Subgroup G := (J'.comap π).map (Subgroup.normalizer (S : Set G) ⊔ A).subtype
    with hJJ
  have hmemJJ : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (S : Set G) ⊔ A),
      x ∈ JJ ↔ π ⟨x, hx⟩ ∈ J' := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h1
      exact ⟨⟨x, hx⟩, h1, rfl⟩
  have hJJn : ∀ g ∈ Subgroup.normalizer (S : Set G) ⊔ A, ∀ x ∈ JJ, g * x * g⁻¹ ∈ JJ := by
    rintro g hg _ ⟨y, hy, rfl⟩
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    show π (⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹) ∈ J'
    rw [map_mul, map_mul, map_inv]
    exact h.normal_J.conj_mem _ hy _
  have hπP : ∀ x (hx : x ∈ P), π ⟨x, hPYA hx⟩ ∈ P' := by
    intro x hx
    rw [← hPP']
    exact mem_img148_iff.mpr ⟨x, hPYA hx, hx, rfl⟩
  have hP'P : ∀ z ∈ P', ∃ x, ∃ hx : x ∈ P, π ⟨x, hPYA hx⟩ = z := by
    intro z hz
    rw [← hPP'] at hz
    obtain ⟨x, hxYA, hxP, rfl⟩ := mem_img148_iff.mp hz
    exact ⟨x, hxP, rfl⟩
  have hinj : ∀ x (hx : x ∈ P) y (hy : y ∈ P), π ⟨x, hPYA hx⟩ = π ⟨y, hPYA hy⟩ → x = y :=
    fun x hx y hy hxy => hPinj x hx y hy _ _ hxy
  set N := P ⊓ JJ with hN
  have hNP : N ≤ P := inf_le_left
  have hNYA : N ≤ Subgroup.normalizer (S : Set G) ⊔ A := hNP.trans hPYA
  have hNn : (N.subgroupOf P).Normal := by
    constructor
    intro n hn p
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨P.mul_mem (P.mul_mem p.2 hn.1) (P.inv_mem p.2), ?_⟩
    simpa using hJJn p (hPYA p.2) n hn.2
  have hNimg : img148 A (Subgroup.normalizer (S : Set G)) N = P' ⊓ J' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, hxN, rfl⟩ := mem_img148_iff.mp hz
      exact ⟨hπP x hxN.1, (hmemJJ x hx).mp hxN.2⟩
    · rintro ⟨hzP, hzJ⟩
      obtain ⟨x, hxP, rfl⟩ := hP'P z hzP
      exact mem_img148_iff.mpr ⟨x, hPYA hxP, ⟨hxP, (hmemJJ x _).mpr hzJ⟩, rfl⟩
  have hNcard : Nat.card N = 81 := by
    rw [← card_img148_of_injOn1422 hNYA (fun x hx y hy hx' hy' hxy =>
      hPinj x hx.1 y hy.1 hx' hy' hxy), hNimg]
    exact h.card_P_inf_J_Sp48 hnin hAP' hP'243 hP'C
  have hPcard' : Nat.card P = 243 := by rw [hPcard, hP'243]
  have hidx : Nat.card P = 3 * Nat.card N := by rw [hPcard', hNcard]
  have hcN : c ∉ N := by
    intro hc
    have hcJ := (hmemJJ c (Subgroup.mem_sup_right h.pt.mem_A)).mp hc.2
    exact hnin ⟨_, hcJ, fun y _ => rfl⟩
  obtain ⟨-, hB9, hBK⟩ := h.B_bar_facts
  have hBJ : B' ≤ J' := hBK.trans (img148_mono h.K_le)
  have hBN : A ⊓ L ≤ N := by
    intro b hb
    refine ⟨hAP hb.1, (hmemJJ b (Subgroup.mem_sup_right hb.1)).mpr (hBJ ?_)⟩
    exact mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hb.1, hb, rfl⟩
  have hπmul : ∀ x (hx : x ∈ P) y (hy : y ∈ P),
      π ⟨x * y, hPYA (P.mul_mem hx hy)⟩ = π ⟨x, hPYA hx⟩ * π ⟨y, hPYA hy⟩ := by
    intro x hx y hy
    rw [← map_mul]
    rfl
  have hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    apply hinj (x * y) (P.mul_mem hx.1 hy.1) (y * x) (P.mul_mem hy.1 hx.1)
    rw [hπmul x hx.1 y hy.1, hπmul y hy.1 x hx.1]
    exact hP'ab _ ⟨hπP x hx.1, (hmemJJ x _).mp hx.2⟩ _ ⟨hπP y hy.1, (hmemJJ y _).mp hy.2⟩
  have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ A := by
    intro x hx hx3
    have h1 : π ⟨x, hPYA hx⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hPYA hx⟩ : ↥(Subgroup.normalizer (S : Set G) ⊔ A)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    obtain ⟨a, ha, haA, hax⟩ := mem_img148_iff.mp (hP'Ω _ (hπP x hx) h1)
    have := hinj a (hAP haA) x hx hax
    rw [← this]
    exact haA
  have hJA : B' = J' ⊓ A' :=
    Subgroup.eq_of_le_of_card_ge (le_inf hBJ (img148_mono inf_le_left))
      (le_of_eq (by rw [h.card_J_inf_A hnin, hB9]))
  have hout : ∀ x (hx : x ∈ A), x ∉ A ⊓ L → π ⟨x, Subgroup.mem_sup_right hx⟩ ∉ J' := by
    intro x hx hxB hxJ
    have h1 : π ⟨x, Subgroup.mem_sup_right hx⟩ ∈ B' := by
      rw [hJA]
      exact ⟨hxJ, mem_img148_iff.mpr ⟨x, Subgroup.mem_sup_right hx, hx, rfl⟩⟩
    obtain ⟨b, hb, hbB, hbx⟩ := mem_img148_iff.mp h1
    have := hinj b (hAP hbB.1) x (hAP hx) hbx
    exact hxB (this ▸ hbB)
  have hzp : ∀ (u : G) (hu : u ∈ P) (k : ℤ),
      π ⟨u ^ k, hPYA (P.zpow_mem hu k)⟩ = π ⟨u, hPYA hu⟩ ^ k := by
    intro u hu k
    rw [← map_zpow]
    rfl
  have htr : ∀ x ∈ A, x ∉ A ⊓ L → ∀ y ∈ A, y ∉ A ⊓ L →
      ∃ p ∈ N, Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y := by
    intro x hx hxB y hy hyB
    obtain ⟨p', ⟨hp'P, hp'J⟩, hp'⟩ := hP'tr _
      (mem_img148_iff.mpr ⟨x, Subgroup.mem_sup_right hx, hx, rfl⟩) (hout x hx hxB) _
      (mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_right hy, hy, rfl⟩) (hout y hy hyB)
    obtain ⟨p, hpP, rfl⟩ := hP'P p' hp'P
    refine ⟨p, ⟨hpP, (hmemJJ p _).mpr hp'J⟩, ?_⟩
    have hxP := hAP hx
    have hyP := hAP hy
    have hpxP : p * x * p⁻¹ ∈ P := P.mul_mem (P.mul_mem hpP hxP) (P.inv_mem hpP)
    have himg : π ⟨p * x * p⁻¹, hPYA hpxP⟩ =
        π ⟨p, hPYA hpP⟩ * π ⟨x, hPYA hxP⟩ * (π ⟨p, hPYA hpP⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have hp'' : Subgroup.zpowers (π ⟨p * x * p⁻¹, hPYA hpxP⟩) =
        Subgroup.zpowers (π ⟨y, hPYA hyP⟩) := by
      rw [himg]
      exact hp'
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      have h1 : π ⟨p * x * p⁻¹, hPYA hpxP⟩ ∈ Subgroup.zpowers (π ⟨y, hPYA hyP⟩) := by
        rw [← hp'']
        exact Subgroup.mem_zpowers _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have := hinj _ (P.zpow_mem hyP k) _ hpxP (by rw [hzp y hyP k, hk])
      rw [← this]
      exact zpow_mem (Subgroup.mem_zpowers y) k
    · rw [Subgroup.zpowers_le]
      have h1 : π ⟨y, hPYA hyP⟩ ∈ Subgroup.zpowers (π ⟨p * x * p⁻¹, hPYA hpxP⟩) := by
        rw [hp'']
        exact Subgroup.mem_zpowers _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have := hinj _ (P.zpow_mem hpxP k) _ hyP (by rw [hzp _ hpxP k, hk])
      rw [← this]
      exact zpow_mem (Subgroup.mem_zpowers _) k
  exact ⟨P, N, hAP, hP3, hNP, hNn, hidx, hcN, hBN, hNc, by rw [hPcard']; norm_num, hΩ, htr⟩

end Cfg

end KP4

section KP4Syl


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem false_of_inverting_Sp48 (hKF : KF1422Sp48) (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (ψ : ↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃* projSp 2 (GaloisField 2 3))
    {g : G} (hg : g * c * g⁻¹ = c⁻¹) : False := by
  haveI := h.normal_J
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨u, ⟨huA, huR⟩, huc⟩ := h.pt.exists_inverting hA6 h.R_mem hg
  have huc' : u ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show Subgroup.zpowers (u * c * u⁻¹) = Subgroup.zpowers c
    rw [huc, Subgroup.zpowers_inv]
  obtain ⟨v, ⟨⟨-, -⟩, hvS⟩, hv⟩ := h.S_mem.2.2.2 u ⟨⟨huc', huA⟩, huR⟩
  have hvc : v * c * v⁻¹ = c⁻¹ := by rw [← hv c h.pt.mem_A, huc]
  set cc := alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A with hcc
  set vv := QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))
    ⟨v, Subgroup.mem_sup_left hvS⟩ with hvv
  have hvcc : vv * cc * vv⁻¹ = cc⁻¹ := by
    have h1 : (⟨v, Subgroup.mem_sup_left hvS⟩ : ↥(Subgroup.normalizer (S : Set G) ⊔ A)) *
        ⟨c, Subgroup.mem_sup_right h.pt.mem_A⟩ * (⟨v, Subgroup.mem_sup_left hvS⟩)⁻¹ =
        (⟨c, Subgroup.mem_sup_right h.pt.mem_A⟩)⁻¹ := Subtype.ext hvc
    have h2 := congrArg (QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))) h1
    rw [hvv, hcc, alpha148_eq_mk']
    simpa only [map_mul, map_inv] using h2
  have hN : ∀ x, x ∈ Subgroup.normalizer (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)))) := by
    intro x
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_J]
    exact Subgroup.mem_top x
  set α := J'.normalizerMonoidHom ⟨cc, hN cc⟩ with hα
  set β := J'.normalizerMonoidHom ⟨vv, hN vv⟩ with hβ
  have hc3 : cc ^ 3 = 1 := by
    rw [hcc, ← alpha148_pow h.pt.mem_A 3]
    simp only [hA3 c h.pt.mem_A]
    rfl
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨cc, hN cc⟩ : ↥(Subgroup.normalizer (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G)))))) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hout : ∀ s : ↥J', α ≠ MulAut.conj s := by
    intro s hs
    refine h.not_innerOn_Sp48 hKF ψ ⟨s, s.2, fun y hy => ?_⟩
    have h1 := congrArg (fun τ : MulAut ↥J' => ((τ ⟨y, hy⟩ : ↥J') :
      ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸ ker148 A (Subgroup.normalizer (S : Set G)))) hs
    exact h1
  have hβα : β * α * β⁻¹ = α⁻¹ := by
    have h1 : (⟨vv, hN vv⟩ : ↥(Subgroup.normalizer (J' : Set (↥(Subgroup.normalizer (S : Set G) ⊔
        A) ⧸ ker148 A (Subgroup.normalizer (S : Set G)))))) * ⟨cc, hN cc⟩ * (⟨vv, hN vv⟩)⁻¹ =
        (⟨cc, hN cc⟩)⁻¹ := Subtype.ext hvcc
    have h2 := congrArg J'.normalizerMonoidHom h1
    simpa only [map_mul, map_inv] using h2
  exact hKF.2.2 ↥J' ⟨ψ⟩ α β hα3 hout hβα

end Cfg

end KP4Syl


end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
