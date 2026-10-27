module

public import CFSG.Monster.Schur.GmatStructureZ

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup

theorem le_of_normal_of_isPGroup {X : Type*} [Group X] {K S : Subgroup X} [K.Normal]
    (hsimple : IsSimpleGroup (X ⧸ K)) (hnp : ¬ IsPGroup 2 (X ⧸ K)) (hS : IsPGroup 2 S)
    (hSn : ∀ g : X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : S ≤ K := by
  have hSN : S.Normal := ⟨fun s hs g => hSn g s hs⟩
  have hMn : (S.map (QuotientGroup.mk' K)).Normal :=
    Subgroup.Normal.map hSN _ (QuotientGroup.mk'_surjective K)
  have hMp : IsPGroup 2 (S.map (QuotientGroup.mk' K)) := hS.map _
  rcases hsimple.eq_bot_or_eq_top_of_normal (S.map (QuotientGroup.mk' K)) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hnp
    intro x
    have hx : x ∈ S.map (QuotientGroup.mk' K) := h ▸ Subgroup.mem_top x
    obtain ⟨k, hk⟩ := hMp ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem natCard_imPhi_mul {S : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hS : S ≤ Gvis) :
    Nat.card (imPhi S) * Nat.card ↥(Qmat ⊓ S) = Nat.card S := by
  have h1 := Subgroup.relIndex_ker (S.subgroupOf Gvis) PhiV
  have h2 := Subgroup.relIndex_mul_card PhiV.ker (S.subgroupOf Gvis)
  rw [ker_PhiV] at h1 h2
  have hinf : rhoQvis ⊓ S.subgroupOf Gvis = (Qmat ⊓ S).subgroupOf Gvis := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [hinf] at h2
  have e1 : Nat.card ↥((Qmat ⊓ S).subgroupOf Gvis) = Nat.card ↥(Qmat ⊓ S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : Qmat ⊓ S ≤ S).trans hS)).toEquiv
  have e2 : Nat.card ↥(S.subgroupOf Gvis) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  rw [← e2, ← e1, ← h2, h1]
  rfl

theorem natCard_RMat : Nat.card RMat = 2 ^ 24 := by
  have := two_mul_natCard_RMat
  rw [natCard_QyMat] at this
  omega

instance finite_RMat : Finite RMat := Nat.finite_of_card_ne_zero (by rw [natCard_RMat]; norm_num)

theorem isPGroup_RMat : IsPGroup 2 RMat := IsPGroup.of_card natCard_RMat

theorem RMat_le_Gvis : RMat ≤ Gvis := RMat_le_CVMat.trans CVMat_le_Hmat

theorem Nvis_normalizes_imPhi_RMat :
    ∀ ν ∈ Nvis, ∀ a ∈ imPhi RMat, ν * a * ν⁻¹ ∈ imPhi RMat := by
  intro ν hν a ha
  obtain ⟨g, hg, hgR, rfl⟩ := mem_imPhi.1 ha
  rw [← imPhi_CV_eq_Nvis] at hν
  obtain ⟨c, hc, hcC, rfl⟩ := mem_imPhi.1 hν
  have hcgc : c * g * c⁻¹ ∈ RMat := by
    refine ⟨QyMat_normalized c hcC.2 g hgR.1, ?_⟩
    exact Hmat.mul_mem (Hmat.mul_mem hcC.1 hgR.2) (Hmat.inv_mem hcC.1)
  refine mem_imPhi.2 ⟨c * g * c⁻¹, Gvis.mul_mem (Gvis.mul_mem hc hg) (Gvis.inv_mem hc), hcgc, ?_⟩
  have : (⟨c * g * c⁻¹, Gvis.mul_mem (Gvis.mul_mem hc hg) (Gvis.inv_mem hc)⟩ : Gvis) =
      ⟨c, hc⟩ * ⟨g, hg⟩ * ⟨c, hc⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem imPhi_RMat_le_Nvis :
    imPhi RMat ≤ Nvis :=
  imPhi_CV_eq_Nvis ▸ imPhi_mono RMat_le_CVMat

theorem imPhi_RMat_le_Evis :
    imPhi RMat ≤ Evis := by
  have hsimple : IsSimpleGroup (Nvis ⧸ Evis.subgroupOf Nvis) := by
    have := CFSG.Monster.Code.AutPerm_isSimpleGroup
    exact NvisQuotEquiv.isSimpleGroup
  have hnp : ¬ IsPGroup 2 (Nvis ⧸ Evis.subgroupOf Nvis) := by
    intro h
    have h' : IsPGroup 2 CFSG.Monster.Code.AutPerm := h.of_equiv NvisQuotEquiv
    have : Finite CFSG.Monster.Code.AutPerm :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Monster.Code.card_AutPerm]; norm_num)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h'
    rw [CFSG.Monster.Code.card_AutPerm] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) (by norm_num)).1
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega
  have hRp : IsPGroup 2 (RMat.subgroupOf Gvis) :=
    IsPGroup.of_card (n := 24) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe RMat_le_Gvis).toEquiv, natCard_RMat])
  have hSp : IsPGroup 2 ((imPhi RMat).subgroupOf Nvis) :=
    (hRp.map PhiV : IsPGroup 2 (imPhi RMat)).of_equiv
      (Subgroup.subgroupOfEquivOfLe imPhi_RMat_le_Nvis).symm
  have hle := le_of_normal_of_isPGroup hsimple hnp hSp (fun g s hs =>
    Subgroup.mem_subgroupOf.2 (Nvis_normalizes_imPhi_RMat g.1 g.2 s.1
      (Subgroup.mem_subgroupOf.1 hs)))
  intro a ha
  exact Subgroup.mem_subgroupOf.1
    (hle (show (⟨a, imPhi_RMat_le_Nvis ha⟩ : Nvis) ∈ (imPhi RMat).subgroupOf Nvis from ha))

instance finite_Evis : Finite Evis := Nat.finite_of_card_ne_zero (by rw [natCard_Evis]; norm_num)

instance finite_ZMat : Finite ZMat :=
  Finite.of_injective (Subgroup.inclusion (inf_le_left : ZMat ≤ Qmat))
    (Subgroup.inclusion_injective _)

theorem ZMat_comm : ∀ a ∈ ZMat, ∀ b ∈ ZMat, a * b = b * a := by
  intro a ha b hb
  rcases isExtraspecialAmbient_Qmat.comm a ha.1 b hb.1 with h | h
  · exact h
  · rcases isExtraspecialAmbient_QyMat.comm a ha.2 b hb.2 with h' | h'
    · exact h'
    · exact absurd (mul_right_cancel (h.symm.trans h')) xmat_ne_xmatTau

theorem Qmat_inf_RMat : Qmat ⊓ RMat = ZMat := by
  ext g
  constructor
  · rintro ⟨hq, hr⟩
    exact ⟨hq, hr.1⟩
  · rintro ⟨hq, hy⟩
    exact ⟨hq, hy, Qmat_le_Hmat hq⟩

theorem two_pow_thirteen_le_natCard_ZMat :
    2 ^ 13 ≤ Nat.card ZMat := by
  have h1 := natCard_imPhi_mul RMat_le_Gvis
  rw [Qmat_inf_RMat, natCard_RMat] at h1
  have h2 : Nat.card (imPhi RMat) ≤ 2 ^ 11 :=
    (Subgroup.card_le_of_le imPhi_RMat_le_Evis).trans natCard_Evis.le
  by_contra hlt
  push Not at hlt
  have : Nat.card (imPhi RMat) * Nat.card ZMat < 2 ^ 11 * 2 ^ 13 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ h2) (Nat.mul_lt_mul_of_pos_left hlt (by norm_num))
  omega

theorem natCard_ZMat_sq_le :
    Nat.card ZMat * Nat.card ZMat ≤ 2 * Nat.card QyMat := by
  have hQy := isExtraspecialAmbient_QyMat
  have hZQy : ZMat ≤ QyMat := inf_le_right
  have h := hQy.card_inf_centralizer_mul_card hZQy xmatTau_mem_ZMat
  have hZC : ZMat ≤ QyMat ⊓ Subgroup.centralizer (ZMat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) :=
    fun a ha => ⟨hZQy ha, Subgroup.mem_centralizer_iff.2 fun b hb => ZMat_comm b hb a ha⟩
  have hfin : Finite ↥(QyMat ⊓ Subgroup.centralizer (ZMat : Set (SpaceB ≃ₗ[ℚ] SpaceB))) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have := Subgroup.card_le_of_le hZC
  calc Nat.card ZMat * Nat.card ZMat ≤
      Nat.card ↥(QyMat ⊓ Subgroup.centralizer (ZMat : Set (SpaceB ≃ₗ[ℚ] SpaceB))) *
        Nat.card ZMat := Nat.mul_le_mul_right _ this
    _ = 2 * Nat.card QyMat := h

theorem natCard_ZMat :
    Nat.card ZMat = 2 ^ 13 := by
  have h1 := two_pow_thirteen_le_natCard_ZMat
  have h2 := natCard_ZMat_sq_le
  rw [natCard_QyMat] at h2
  by_contra hne
  have hgt : 2 ^ 13 < Nat.card ZMat := lt_of_le_of_ne h1 (Ne.symm hne)
  have : 2 ^ 13 * 2 ^ 13 < Nat.card ZMat * Nat.card ZMat := Nat.mul_self_lt_mul_self hgt
  omega

theorem imPhi_RMat_eq_Evis :
    imPhi RMat = Evis := by
  have h1 := natCard_imPhi_mul RMat_le_Gvis
  rw [Qmat_inf_RMat, natCard_RMat, natCard_ZMat] at h1
  have h2 : Nat.card (imPhi RMat) = 2 ^ 11 := by
    have h3 : Nat.card (imPhi RMat) * 2 ^ 13 = 2 ^ 11 * 2 ^ 13 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  exact Subgroup.eq_of_le_of_card_ge imPhi_RMat_le_Evis (by rw [natCard_Evis, h2])

end CFSG.Monster.Schur
