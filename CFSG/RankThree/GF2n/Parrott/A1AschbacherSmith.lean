module

public import CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.GF2Type.AschbacherFSmith1977
import CFSG.RankThree.GF2n.Parrott.Section1
import CFSG.RankThree.GF2n.Parrott.Section4Lemma41
import CFSG.LargeExtraspecial.DWTim79.Bridge
import CFSG.Goldschmidt75.TheoremBcN1
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem z_ne_one_A1 (h : Tim79a.ParrottHypA1 z) : z ≠ 1 := by
  intro hz
  have h2 := orderOf_z_A1 h
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem isCharacteristicP_H_A1 (h : Tim79a.ParrottHypA1 z) :
    IsCharacteristicP 2 ↥(H z) := by
  show Subgroup.centralizer (pCore 2 ↥(H z) : Set ↥(H z)) ≤ pCore 2 ↥(H z)
  intro x hx
  rw [← J_subgroupOf_eq_pCore] at hx ⊢
  rw [Subgroup.mem_subgroupOf]
  refine h.centralizer_le (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hjx := Subgroup.mem_centralizer_iff.mp hx ⟨j, J_le_H hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
  exact congrArg Subtype.val hjx

theorem pPrimeCore_H_eq_bot_A1 (h : Tim79a.ParrottHypA1 z) : pPrimeCore 2 ↥(H z) = ⊥ :=
  CFSG.pPrimeCore_eq_bot_of_isCharacteristicP ↥(H z) 2 (isCharacteristicP_H_A1 h)

theorem generalizedFitting_H_eq_J_A1 (h : Tim79a.ParrottHypA1 z) :
    inSubgroup generalizedFitting (H z) = J z := by
  have hF := (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥(H z) 2).mp
    (isCharacteristicP_H_A1 h)
  show (generalizedFitting ↥(H z)).map (H z).subtype = (pCore 2 ↥(H z)).map (H z).subtype
  rw [hF]

theorem isExtraspecialPGroup_generalizedFitting_A1 (h : Tim79a.ParrottHypA1 z) :
    IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) := by
  rw [← H_eq_centralizer, generalizedFitting_H_eq_J_A1 h]
  exact (CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 (J z)).mpr
    h.extraspecial

theorem card_generalizedFitting_A1 (h : Tim79a.ParrottHypA1 z) :
    Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 4) := by
  rw [← H_eq_centralizer, generalizedFitting_H_eq_J_A1 h, card_J_A1 h]

theorem isSimpleGroup_quotient_A1 (h : Tim79a.ParrottHypA1 z) :
    IsSimpleGroup (↥(H z) ⧸ (J z).subgroupOf (H z)) := by
  obtain ⟨D⟩ := h.quotient
  have : IsSimpleGroup D.X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) D.lie
  exact MulEquiv.isSimpleGroup D.iso

theorem eq_H_of_normal_of_not_mem_J_A1 (h : Tim79a.ParrottHypA1 z) (hJH : ⁅J z, H z⁆ = J z)
    {C : Subgroup G} (hCH : C ≤ H z) (hCn : ∀ c ∈ C, ∀ x ∈ H z, x * c * x⁻¹ ∈ C)
    {y : G} (hyC : y ∈ C) (hyJ : y ∉ J z) : C = H z := by
  classical
  have := isSimpleGroup_quotient_A1 h
  have hCJ : ∀ x ∈ H z, ∃ c ∈ C, c⁻¹ * x ∈ J z := by
    have hCn' : (C.subgroupOf (H z)).Normal := by
      refine ⟨fun c hc g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      exact hCn c hc g g.2
    have hK : (C.subgroupOf (H z)).map (QuotientGroup.mk' ((J z).subgroupOf (H z))) = ⊤ := by
      have := hCn'.map (QuotientGroup.mk' ((J z).subgroupOf (H z)))
        (QuotientGroup.mk'_surjective _)
      refine (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left fun hbot => hyJ ?_
      have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' ((J z).subgroupOf (H z)))
        (Subgroup.mem_subgroupOf.mpr hyC : (⟨y, hCH hyC⟩ : ↥(H z)) ∈ C.subgroupOf (H z))
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hmem
      exact hmem
    intro x hx
    have hmem : QuotientGroup.mk' ((J z).subgroupOf (H z)) ⟨x, hx⟩ ∈
        (C.subgroupOf (H z)).map (QuotientGroup.mk' ((J z).subgroupOf (H z))) := by
      rw [hK]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hmem
    refine ⟨c, Subgroup.mem_subgroupOf.mp hc, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    exact Subgroup.mem_subgroupOf.mp hcx
  let K : Subgroup G :=
    { carrier := {a | a ∈ H z ∧ ∀ x ∈ H z, ⁅a, x⁆ ∈ C}
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨mul_mem haH hbH, fun x hx => ?_⟩
        have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (hCn _ (hb x hx) a haH) (ha x hx)
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [commutatorElement_one_left]
        exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨inv_mem haH, fun x hx => ?_⟩
        have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hCn _ (inv_mem (ha x hx)) a⁻¹ (inv_mem haH) }
  have hCK : C ≤ K := fun c hc => ⟨hCH hc, fun x hx => by
    have e : ⁅c, x⁆ = c * (x * c⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hc (hCn _ (inv_mem hc) x hx)⟩
  have hzK : z ∈ K := ⟨z_mem_H, fun x hx => by
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have e : ⁅z, x⁆ = 1 := by
      rw [commutatorElement_def, ← hxz]
      group
    rw [e]
    exact one_mem _⟩
  have hJzC : J z ≤ C ⊔ Subgroup.zpowers z := by
    rw [← hJH, Subgroup.commutator_le]
    intro j hj x hx
    obtain ⟨c, hc, hcx⟩ := hCJ x hx
    have e : ⁅j, x⁆ = (j * c * j⁻¹) * ⁅j, c⁻¹ * x⁆ * c⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hjj : ⁅j, c⁻¹ * x⁆ ∈ Subgroup.zpowers z := by
      rw [← h.commutator]
      exact Subgroup.commutator_mem_commutator hj hcx
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (hCn c hc j (J_le_H hj)))
      (Subgroup.mem_sup_right hjj)) (Subgroup.mem_sup_left (inv_mem hc))
  have hJC : J z ≤ C := by
    have hJK : J z ≤ K := hJzC.trans (sup_le hCK (Subgroup.zpowers_le.mpr hzK))
    rw [← hJH, Subgroup.commutator_le]
    intro j hj x hx
    exact (hJK hj).2 x hx
  refine le_antisymm hCH fun x hx => ?_
  obtain ⟨c, hc, hcx⟩ := hCJ x hx
  have hmem := mul_mem hc (hJC hcx)
  rwa [mul_inv_cancel_left] at hmem

theorem exists_conj_mem_H_not_mem_J_A1 (h : Tim79a.ParrottHypA1 z)
    (hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z) :
    ∃ g : G, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ∉ J z := by
  obtain ⟨y, ⟨g, rfl⟩, -, hyH, hyz⟩ := prop2_conj_centralizer (orderOf_z_A1 h) hne
  refine ⟨g, hyH, fun hyJ => hyz ?_⟩
  have h1 := hwc g⁻¹ (by rwa [inv_inv])
  rw [inv_inv] at h1
  rw [h1]
  exact Subgroup.mem_zpowers z

theorem centerIn_eq_zpowers_of_isSylowOf_A1 (h : Tim79a.ParrottHypA1 z) (T : Subgroup G)
    (hT : IsSylowOf 2 T (H z)) : centerIn T = Subgroup.zpowers z := by
  have hJT : J z ≤ T := J_le_of_isSylowOf T hT
  apply le_antisymm
  · intro x hx
    have hx' := Subgroup.mem_inf.mp (show x ∈ T ⊓ Subgroup.centralizer (T : Set G) from hx)
    rw [← centerIn_J_eq_zpowers_A1 h, ← centralizer_J_eq_centerIn_A1 h]
    refine Subgroup.mem_inf.mpr ⟨hT.le hx'.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp hx'.2 j (hJT hj)
  · exact Subgroup.zpowers_le.mpr
      ⟨hJT (z_mem_J_A1 h), Subgroup.centralizer_le hT.le (z_centralizes_H_A (z := z))⟩

theorem normalizer_le_H_of_isSylowOf_A1 (h : Tim79a.ParrottHypA1 z) (T : Subgroup G)
    (hT : IsSylowOf 2 T (H z)) : normalizer (T : Set G) ≤ H z := by
  have hzT : z ∈ T := J_le_of_isSylowOf T hT (z_mem_J_A1 h)
  intro n hn
  have hnz : n * z * n⁻¹ ∈ centerIn T := by
    show n * z * n⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set G)
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn z).mp hzT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : n⁻¹ * t * n ∈ T := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t).mp ht
      rwa [inv_inv] at h1
    have hc : (n⁻¹ * t * n) * z = z * (n⁻¹ * t * n) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT.le ht')
    calc t * (n * z * n⁻¹) = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by rw [hc]
      _ = n * z * n⁻¹ * t := by group
  rw [centerIn_eq_zpowers_of_isSylowOf_A1 h T hT] at hnz
  have hne : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply z_ne_one_A1 h
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two (orderOf_z_A1 h) hnz with h1 | h1
  · exact absurd h1 hne
  · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h1]

theorem isSylowOf_top_of_isSylowOf_H_A1 (h : Tim79a.ParrottHypA1 z) (T : Subgroup G)
    (hT : IsSylowOf 2 T (H z)) : IsSylowOf 2 T ⊤ := by
  have hT' : IsSylowOf 2 T (H z ⊓ ⊤) := by rwa [inf_top_eq]
  refine isSylowOf_of_normalizer_inf_le hT' ?_
  rw [inf_top_eq]
  exact normalizer_le_H_of_isSylowOf_A1 h T hT

theorem z_mem_of_normal_of_two_dvd_A1 (h : Tim79a.ParrottHypA1 z) {N : Subgroup G}
    (hN : N.Normal) (h2 : 2 ∣ Nat.card N) : z ∈ N := by
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
  have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H_A1 h T hT
  have hNTsylow : IsSylowOf 2 (N ⊓ T) N := by
    have h' := hTtop.inf_of_le_normalizer (N := N) le_top
      (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm)
    simpa [inf_comm] using h'
  have hQne : N ⊓ T ≠ ⊥ := by
    have hfacpos : 0 < (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have hcard : Nat.card (N ⊓ T : Subgroup G) = 2 ^ (Nat.card N).factorization 2 :=
      hNTsylow.card_eq
    have hgt : 1 < Nat.card (N ⊓ T : Subgroup G) := by
      rw [hcard]
      exact one_lt_pow' (by norm_num) (Nat.pos_iff_ne_zero.mp hfacpos)
    exact (Subgroup.nontrivial_iff_ne_bot (N ⊓ T)).mp (Finite.one_lt_card_iff_nontrivial.mp hgt)
  have hTN : T ≤ Subgroup.normalizer ((N ⊓ T : Subgroup G) : Set G) := by
    have : ((N ⊓ T).subgroupOf T).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hN.subgroupOf T
    exact Subgroup.le_normalizer_of_normal_subgroupOf inf_le_right
  have hcenterNe : (N ⊓ T) ⊓ centerIn T ≠ ⊥ := by
    have h' := CFSG.Goldschmidt75.inf_centralizer_ne_bot (p := 2) hTtop.isPGroup
      (inf_le_right : N ⊓ T ≤ T) hTN hQne
    rw [show centerIn T = T ⊓ Subgroup.centralizer (T : Set G) from rfl,
      ← inf_assoc, inf_eq_left.mpr inf_le_right]
    exact h'
  rw [centerIn_eq_zpowers_of_isSylowOf_A1 h T hT] at hcenterNe
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenterNe
  have hyN : (y : G) ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp y.2).1).1
  have hyz : (y : G) ∈ Subgroup.zpowers z := (Subgroup.mem_inf.mp y.2).2
  have hyne : (y : G) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two (orderOf_z_A1 h) hyz with h1 | h1
  · exact absurd h1 hyne
  · rwa [h1] at hyN

theorem card_H_A1 (h : Tim79a.ParrottHypA1 z) : Nat.card (H z) = 2 ^ 9 * 25920 := by
  obtain ⟨D⟩ := h.quotient
  have hX : Nat.card D.X = 25920 := by
    have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := D.X)
      (show (3 : ℕ) ≠ 2 by norm_num) (D.lie.statedClassicalModel_of_ne_zero (by norm_num))).2.2.1
      rfl
    rw [hc]
    decide +kernel
  have hQ : Nat.card (↥(H z) ⧸ (J z).subgroupOf (H z)) = 25920 := by
    rw [Nat.card_congr D.iso.toEquiv, hX]
  have hJ' : Nat.card ((J z).subgroupOf (H z)) = 2 ^ 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe J_le_H).toEquiv, card_J_A1 h]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((J z).subgroupOf (H z)), hQ, hJ',
    mul_comm]

theorem factorization_two_card_A1 (h : Tim79a.ParrottHypA1 z) :
    (Nat.card G).factorization 2 = 15 := by
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
  have h1 : Nat.card T = 2 ^ 15 := by
    rw [hT.card_eq, card_H_A1 h, show (2 ^ 9 * 25920 : ℕ) = 2 ^ 15 * 405 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have h2 := (isSylowOf_top_of_isSylowOf_H_A1 h T hT).card_eq
  rw [h1, Subgroup.card_top] at h2
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

theorem pPrimeCore_eq_bot_A1 (h : Tim79a.ParrottHypA1 z)
    (hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z) (hJH : ⁅J z, H z⁆ = J z) :
    pPrimeCore 2 G = ⊥ := by
  classical
  obtain ⟨g, hyH, hyJ⟩ := exists_conj_mem_H_not_mem_J_A1 h hne hwc
  set O := pPrimeCore 2 G
  have hOn : O.Normal := pPrimeCore_normal
  have hfix : ∀ o ∈ O, o * z = z * o → o = 1 := by
    intro o ho hoz
    have hoH : o ∈ H z := Subgroup.mem_centralizer_singleton_iff.mpr hoz
    have hKn : (O.subgroupOf (H z)).Normal := hOn.subgroupOf (H z)
    have hKcop : Nat.Coprime 2 (Nat.card (O.subgroupOf (H z))) := by
      have hdvd : Nat.card (O.subgroupOf (H z)) ∣ Nat.card O := by
        rw [← Subgroup.card_map_of_injective (H z).subtype_injective,
          Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    have hKbot := (pPrimeCore_eq_bot_iff.mp (pPrimeCore_H_eq_bot_A1 h)) _ hKn hKcop
    have hmem : (⟨o, hoH⟩ : ↥(H z)) ∈ O.subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr ho
    rw [hKbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hzz : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [orderOf_z_A1 h, sq] at h1
  have hinv : ∀ o ∈ O, z * o * z⁻¹ = o⁻¹ := by
    let φ : ↥O →* ↥O := (MulAut.conjNormal z : MulAut ↥O).toMonoidHom
    have hφ : ∀ o : ↥O, ((φ o : ↥O) : G) = z * o * z⁻¹ := fun o => MulAut.conjNormal_apply z o
    have hfpf : MonoidHom.FixedPointFree φ := by
      intro o ho
      apply Subtype.ext
      apply hfix o o.2
      have h1 := congrArg Subtype.val ho
      rw [hφ] at h1
      calc (o : G) * z = z * o * z⁻¹ * z := by rw [h1]
        _ = z * o := by group
    have hinvol : Function.Involutive φ := by
      intro o
      apply Subtype.ext
      rw [hφ, hφ]
      calc z * (z * (o : G) * z⁻¹) * z⁻¹ = (z * z) * o * (z * z)⁻¹ := by group
        _ = o := by rw [hzz]; group
    have heq := hfpf.coe_eq_inv_of_involutive hinvol
    intro o ho
    have h1 := congrArg Subtype.val (congrFun heq ⟨o, ho⟩)
    rw [hφ] at h1
    exact h1
  have hyinv : ∀ o ∈ O, (g * z * g⁻¹) * o * (g * z * g⁻¹)⁻¹ = o⁻¹ := by
    intro o ho
    have ho' : g⁻¹ * o * g ∈ O := by
      have h1 := hOn.conj_mem o ho g⁻¹
      rwa [inv_inv] at h1
    calc (g * z * g⁻¹) * o * (g * z * g⁻¹)⁻¹ = g * (z * (g⁻¹ * o * g) * z⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * o * g)⁻¹ * g⁻¹ := by rw [hinv _ ho']
      _ = o⁻¹ := by group
  have hCn : ∀ c ∈ H z ⊓ Subgroup.centralizer (O : Set G), ∀ x ∈ H z,
      x * c * x⁻¹ ∈ H z ⊓ Subgroup.centralizer (O : Set G) := by
    intro c hc x hx
    obtain ⟨hcH, hcO⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx hcH) (inv_mem hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : x⁻¹ * o * x ∈ O := by
      have h1 := hOn.conj_mem o ho x⁻¹
      rwa [inv_inv] at h1
    have hc' := Subgroup.mem_centralizer_iff.mp hcO _ ho'
    calc o * (x * c * x⁻¹) = x * ((x⁻¹ * o * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * o * x)) * x⁻¹ := by rw [hc']
      _ = x * c * x⁻¹ * o := by group
  have hzyC : z * (g * z * g⁻¹) ∈ H z ⊓ Subgroup.centralizer (O : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem z_mem_H hyH, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have key : z * (g * z * g⁻¹) * o * (z * (g * z * g⁻¹))⁻¹ = o := by
      calc z * (g * z * g⁻¹) * o * (z * (g * z * g⁻¹))⁻¹
          = z * ((g * z * g⁻¹) * o * (g * z * g⁻¹)⁻¹) * z⁻¹ := by group
        _ = z * o⁻¹ * z⁻¹ := by rw [hyinv o ho]
        _ = (z * o * z⁻¹)⁻¹ := by group
        _ = o := by rw [hinv o ho, inv_inv]
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  have hzyJ : z * (g * z * g⁻¹) ∉ J z := by
    intro hmem
    apply hyJ
    have h1 := mul_mem (inv_mem (z_mem_J_A1 h)) hmem
    rwa [inv_mul_cancel_left] at h1
  have hCH := eq_H_of_normal_of_not_mem_J_A1 h hJH inf_le_left hCn hzyC hzyJ
  have hzC : z ∈ H z ⊓ Subgroup.centralizer (O : Set G) := by
    rw [hCH]
    exact z_mem_H
  rw [eq_bot_iff]
  intro o ho
  rw [Subgroup.mem_bot]
  exact hfix o ho (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzC).2 o ho)

theorem isSimpleGroup_A1 (h : Tim79a.ParrottHypA1 z)
    (hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z) (hJH : ⁅J z, H z⁆ = J z) :
    IsSimpleGroup G := by
  classical
  have hO := pPrimeCore_eq_bot_A1 h hne hwc hJH
  obtain ⟨g, hyH, hyJ⟩ := exists_conj_mem_H_not_mem_J_A1 h hne hwc
  have : Nontrivial G := ⟨⟨z, 1, z_ne_one_A1 h⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    have h2dvd : 2 ∣ Nat.card N := by
      by_contra h2dvd
      have hcop : Nat.Coprime 2 (Nat.card N) :=
        (Nat.prime_two.coprime_iff_not_dvd).mpr h2dvd
      exact hNbot ((pPrimeCore_eq_bot_iff.mp hO) N hN hcop)
    have hzN : z ∈ N := z_mem_of_normal_of_two_dvd_A1 h hN h2dvd
    have hyN : g * z * g⁻¹ ∈ N := hN.conj_mem z hzN g
    have hHN : H z ≤ N := by
      have hCn : ∀ c ∈ N ⊓ H z, ∀ x ∈ H z, x * c * x⁻¹ ∈ N ⊓ H z := by
        intro c hc x hx
        obtain ⟨hcN, hcH⟩ := Subgroup.mem_inf.mp hc
        exact Subgroup.mem_inf.mpr ⟨hN.conj_mem c hcN x, mul_mem (mul_mem hx hcH) (inv_mem hx)⟩
      have hC : N ⊓ H z = H z :=
        eq_H_of_normal_of_not_mem_J_A1 h hJH inf_le_right hCn (Subgroup.mem_inf.mpr ⟨hyN, hyH⟩)
          hyJ
      rw [← hC]
      exact inf_le_left
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
    have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H_A1 h T hT
    have hTN : T ≤ N := le_trans hT.le hHN
    have hTsylowN : IsSylowOf 2 T N := by
      have hs := hTtop.inf_of_le_normalizer (N := N) le_top
        (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm)
      rwa [inf_eq_left.mpr hTN] at hs
    obtain ⟨Q, hQ⟩ := hTsylowN
    have hfrat : normalizer (T : Set G) ⊔ N = ⊤ := by
      have hs := Sylow.normalizer_sup_eq_top Q
      rwa [hQ] at hs
    rw [eq_top_iff, ← hfrat]
    exact sup_le (le_trans (normalizer_le_H_of_isSylowOf_A1 h T hT) hHN) le_rfl

theorem not_isSporadic_co2_A1 (h : Tim79a.ParrottHypA1 z) :
    ¬ CFSG.Blueprint.NativeSporadic.IsSporadic G .Co2 := by
  rintro ⟨e⟩
  have hc : Nat.card G = 42305421312000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co2.card_Co2
  have h2 := factorization_two_card_A1 h
  rw [hc, show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at h2
  omega

theorem lieModel_psu_six_of_aschbacherFSmith_A1
    (hAS : CFSG.GF2Type.AschbacherFSmith1977Statement) (h : Tim79a.ParrottHypA1 z)
    (hne : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ J z → g⁻¹ * z * g = z) (hJH : ⁅J z, H z⁆ = J z) :
    CFSG.Blueprint.LieModel G .PSU 6 2 1 := by
  have : IsSimpleGroup G := isSimpleGroup_A1 h hne hwc hJH
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    have hbot : ⁅J z, J z⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      by_contra hab
      exact hcon ⟨a, b, hab⟩
    have hz : z ∈ ⁅J z, J z⁆ := by
      rw [h.commutator]
      exact Subgroup.mem_zpowers z
    rw [hbot, Subgroup.mem_bot] at hz
    exact z_ne_one_A1 h hz
  have hwc' : ∀ g : G, g⁻¹ * z * g ∈
      inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)) → g⁻¹ * z * g = z := by
    intro g hg
    rw [← H_eq_centralizer, generalizedFitting_H_eq_J_A1 h] at hg
    exact hwc g hg
  rcases hAS G hnonab z (orderOf_z_A1 h) (isExtraspecialPGroup_generalizedFitting_A1 h) 4
      (card_generalizedFitting_A1 h) (by norm_num) hwc' with hU | ⟨-, hCo2⟩
  · simpa using hU
  · exact absurd hCo2 (not_isSporadic_co2_A1 h)

end CFSG.RankThree.GF2n.Parrott
