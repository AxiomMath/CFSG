module

public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion

public section

namespace CFSG.LocalAnalysis.SteinbergBK

open Subgroup

variable {F : Type*} [Group F]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {a x : F} (ha : orderOf a = 2)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_of_sylow_map_le {p : ℕ} [Fact p.Prime] {H R T : Subgroup F} (S : Sylow p H)
    (hS : (S : Subgroup H).map H.subtype = T) (hR : IsPGroup p R) (hTR : T ≤ R) (hRH : R ≤ H) :
    R = T := by
  have h1 : IsPGroup p (R.subgroupOf H) := hR.comap_of_injective H.subtype H.subtype_injective
  have h2 : (S : Subgroup H) ≤ R.subgroupOf H := by
    intro x hx
    rw [mem_subgroupOf]
    exact hTR (hS ▸ mem_map_of_mem H.subtype hx)
  have h3 := S.is_maximal' h1 h2
  rw [← hS, ← h3, map_subgroupOf_eq_of_le hRH]

theorem map_conj_eq_self_of_mem_centralizer {J : Subgroup F} {k : F}
    (hk : k ∈ centralizer (J : Set F)) : J.map (MulAut.conj k).toMonoidHom = J := by
  have hfix : ∀ x ∈ J, MulAut.conj k x = x := by
    intro x hx
    rw [MulAut.conj_apply, ← mem_centralizer_iff.mp hk x hx, mul_inv_cancel_right]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change MulAut.conj k x ∈ J
    rw [hfix x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, hfix y hy⟩

theorem quasisimple_involution_centralizer_order_two_standard [Finite F] {J : Subgroup F}
    (hJ : CFSG.Assembly.IsQuasisimple J)
    (hE : ∃ E : Subgroup F, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4)
    {a : F} (haJ : a ∈ centralizer (J : Set F)) (ha : orderOf a = 2)
    (hcomp : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set F)))
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (J : Set F) ⊓ centralizer ({a} : Set F)),
      (S : Subgroup _).map (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).subtype =
        zpowers a) :
    (∃ S : Sylow 2 (centralizer (J : Set F)),
      (S : Subgroup _).map (centralizer (J : Set F)).subtype = zpowers a) ∧
    (∀ b ∈ centralizer (J : Set F), orderOf b = 2 →
      ∃ h ∈ centralizer (J : Set F), h⁻¹ * a * h = b) ∧
    CFSG.Assembly.ComponentType.IsStandardSubgroup J := by
  set B := centralizer (J : Set F) with hB
  obtain ⟨S, hS⟩ := hsyl
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hzp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have haCa : a ∈ centralizer ({a} : Set F) := mem_centralizer_singleton_iff.mpr rfl
  have hzB : zpowers a ≤ B := zpowers_le.mpr haJ
  have stepA : ∀ Q : Subgroup F, IsPGroup 2 Q → zpowers a ≤ Q → Q ≤ B → Q = zpowers a := by
    intro Q hQ haQ hQB
    have hR : Q ⊓ centralizer ({a} : Set F) = zpowers a :=
      eq_of_sylow_map_le S hS (hQ.to_le inf_le_left) (le_inf haQ (zpowers_le.mpr haCa))
        (inf_le_inf_right _ hQB)
    have haQ' : a ∈ Q := haQ (mem_zpowers a)
    have : Nontrivial Q := ⟨⟨⟨a, haQ'⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have := hQ.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : center Q)
    have hcomm : ∀ q ∈ Q, q * (z : F) = (z : F) * q := fun q hq =>
      congrArg Subtype.val (mem_center_iff.mp z.2 ⟨q, hq⟩)
    have hzR : ((z : Q) : F) ∈ zpowers a :=
      hR ▸ ⟨(z : Q).2, mem_centralizer_singleton_iff.mpr (hcomm a haQ').symm⟩
    have hza : ((z : Q) : F) = a := by
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha hzR with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hz
      · exact h
    have hQC : Q ≤ centralizer ({a} : Set F) := by
      intro q hq
      rw [mem_centralizer_singleton_iff, ← hza]
      exact hcomm q hq
    rw [← hR, inf_eq_left.mpr hQC]
  have hzB' : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hzp.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨Sa, hSa⟩ := hzB'.exists_le_sylow
  have hSaeq : (Sa : Subgroup B).map B.subtype = zpowers a := by
    apply stepA
    · exact Sa.isPGroup'.map B.subtype
    · intro x hx
      exact ⟨⟨x, hzB hx⟩, hSa (by rw [mem_subgroupOf]; exact hx), rfl⟩
    · exact map_subtype_le _
  have hcardSa : Nat.card (Sa : Subgroup B) = 2 := by
    rw [← card_map_of_injective B.subtype_injective, hSaeq, Nat.card_zpowers, ha]
  have hcardSyl : ∀ T : Sylow 2 B, Nat.card (T : Subgroup B) = 2 := by
    intro T
    rw [T.card_eq_multiplicity, ← Sa.card_eq_multiplicity, hcardSa]
  have stepC : ∀ Q : Subgroup F, IsPGroup 2 Q → Q ≤ B → Nat.card Q ≤ 2 := by
    intro Q hQ hQB
    obtain ⟨T, hT⟩ := (hQ.comap_of_injective B.subtype B.subtype_injective).exists_le_sylow
    calc Nat.card Q = Nat.card (Q.subgroupOf B) :=
          (Nat.card_congr (subgroupOfEquivOfLe hQB).toEquiv).symm
      _ ≤ Nat.card (T : Subgroup B) := card_le_of_le hT
      _ = 2 := hcardSyl T
  have stepD : ∀ b ∈ B, orderOf b = 2 → ∃ h ∈ B, h⁻¹ * a * h = b := by
    intro b hb hb2
    have hbp : IsPGroup 2 (zpowers b) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
    obtain ⟨Tb, hTb⟩ := (hbp.comap_of_injective B.subtype B.subtype_injective).exists_le_sylow
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq B Sa Tb
    have haSa : (⟨a, haJ⟩ : B) ∈ (Sa : Subgroup B) := by
      obtain ⟨y, hy, hya⟩ : a ∈ (Sa : Subgroup B).map B.subtype := hSaeq ▸ mem_zpowers a
      have : y = ⟨a, haJ⟩ := Subtype.ext hya
      rwa [← this]
    have hc : MulAut.conj h (⟨a, haJ⟩ : B) ∈ (Tb : Subgroup B) := by
      rw [← hh, Sylow.coe_subgroup_smul]
      exact smul_mem_pointwise_smul _ _ _ haSa
    have hTf2 : Nat.card ((Tb : Subgroup B).map B.subtype) = 2 := by
      rw [card_map_of_injective B.subtype_injective]
      exact hcardSyl Tb
    have hbTf : zpowers b ≤ (Tb : Subgroup B).map B.subtype := by
      intro x hx
      exact ⟨⟨x, (zpowers_le.mpr hb) hx⟩, hTb (by rw [mem_comap]; exact hx), rfl⟩
    have heq := eq_of_le_of_card_ge hbTf (by rw [hTf2, Nat.card_zpowers, hb2])
    have hcmem : (h : F) * a * (h : F)⁻¹ ∈ zpowers b := heq ▸ ⟨_, hc, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hb2 hcmem with h1 | h1
    · exfalso
      apply ha1
      have h2 : (h : F)⁻¹ * ((h : F) * a * (h : F)⁻¹) * (h : F) = a := by group
      rw [h1] at h2
      rw [← h2]
      group
    · exact ⟨(h : F)⁻¹, B.inv_mem h.2, by rw [inv_inv]; exact h1⟩
  have hLg : ∀ g : F, ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g hg
    obtain ⟨E, hEJ, -, hE4⟩ := hE
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hg
    have hEg : E.map (MulAut.conj g).toMonoidHom ≤ B := (map_mono hEJ).trans hg
    have hEp : IsPGroup 2 (E.map (MulAut.conj g).toMonoidHom) :=
      (IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)).map _
    have h4 := stepC _ hEp hEg
    rw [card_map_of_injective (MulAut.conj g).injective, hE4] at h4
    omega
  have heven : Even (Nat.card B) := by
    rw [even_iff_two_dvd, ← ha]
    have h1 := orderOf_dvd_natCard (⟨a, haJ⟩ : B)
    rwa [Subgroup.orderOf_mk] at h1
  have hcomp' : ∀ t ∈ B, orderOf t = 2 →
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set F)) := by
    intro t ht ht2
    obtain ⟨k, hk, hkt⟩ := stepD t ht ht2
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp k⁻¹
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, inv_inv, hkt,
      map_conj_eq_self_of_mem_centralizer (B.inv_mem hk)] at h1
    exact h1
  exact ⟨⟨Sa, hSaeq⟩, stepD,
    (CFSG.LocalAnalysis.ComponentInitial.involution_component_standard_criterion hJ heven
      hLg).mpr hcomp'⟩

end CFSG.LocalAnalysis.SteinbergBK
