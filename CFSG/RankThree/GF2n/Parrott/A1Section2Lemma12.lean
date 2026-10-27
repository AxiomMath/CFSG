module

public import CFSG.RankThree.GF2n.Parrott.A1Section2CJ
public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
import CFSG.GroupTheory.CentralizerSylowFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem map_map_conj_eq {A B : Type*} [Group A] [Group B] (f : A →* B) (a : A)
    (K : Subgroup A) :
    (K.map (MulAut.conj a).toMonoidHom).map f = (K.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

omit [Finite G] in
private theorem map_conj_zpowers_eq_of_coe {a b : ↥(H z)} {k : G} (hk : k ∈ H z)
    (hab : (Subgroup.zpowers (a : G)).map (MulAut.conj k).toMonoidHom =
      Subgroup.zpowers (b : G)) :
    (Subgroup.zpowers a).map (MulAut.conj (⟨k, hk⟩ : ↥(H z))).toMonoidHom =
      Subgroup.zpowers b := by
  apply Subgroup.map_injective (H z).subtype_injective
  rw [map_map_conj_eq]
  simp only [MonoidHom.map_zpowers] at hab ⊢
  exact hab

omit [Finite G] in
private theorem map_conj_zpowers_coe_eq {a b k : ↥(H z)}
    (hab : (Subgroup.zpowers a).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers b) :
    (Subgroup.zpowers (a : G)).map (MulAut.conj (k : G)).toMonoidHom =
      Subgroup.zpowers (b : G) := by
  have h := congrArg (Subgroup.map (H z).subtype) hab
  rw [map_map_conj_eq] at h
  simp only [MonoidHom.map_zpowers] at h ⊢
  exact h

private theorem exists_map_conj_le_of_isSylowOf_two {K P W : Subgroup G}
    (hP : IsSylowOf 2 P K) (hWK : W ≤ K) (hW : IsPGroup 2 W) :
    ∃ c ∈ K, W.map (MulAut.conj c).toMonoidHom ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hWQ⟩ := (hW.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk, hkP⟩ := hP.exists_mem_conj (P' := (Q : Subgroup K).map K.subtype) ⟨Q, rfl⟩
  refine ⟨k⁻¹, K.inv_mem hk, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hwQ : w ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨w, hWK hw⟩, hWQ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  simpa [MulAut.conj_apply] using (hkP w).mp hwQ

private theorem exists_mem_H_map_conj_zpowers_eq
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    (hz : orderOf z = 2) {x y : G} {T U : Subgroup G}
    (hT : IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G))) (hTJ : ⁅T, T⁆ ≤ J z)
    (hU : U ≤ Subgroup.centralizer ({y} : Set G)) (hU2 : IsPGroup 2 U) (hzU : z ∈ ⁅U, U⁆)
    {g : G} (hg : (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x) :
    ∃ k ∈ H z, (Subgroup.zpowers y).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers x := by
  have hUg : U.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({x} : Set G) := by
    have h1 : U ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      rw [CFSG.GroupTheory.centralizer_zpowers_eq]
      exact hU
    have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
    rwa [← CFSG.GroupTheory.centralizer_map_conj, hg,
      CFSG.GroupTheory.centralizer_zpowers_eq] at h2
  obtain ⟨c, hc, hcle⟩ := exists_map_conj_le_of_isSylowOf_two hT hUg (hU2.map _)
  have hck : U.map (MulAut.conj (c * g)).toMonoidHom ≤ T := by
    rw [← CFSG.GroupTheory.map_conj_map_conj]
    exact hcle
  have hzJ : (c * g) * z * (c * g)⁻¹ ∈ J z := by
    apply hTJ
    have hmem : (MulAut.conj (c * g)) z ∈ (⁅U, U⁆).map (MulAut.conj (c * g)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzU
    rw [Subgroup.map_commutator] at hmem
    simpa only [MulAut.conj_apply] using Subgroup.commutator_mono hck hck hmem
  have hz2 : orderOf ((c * g) * z * (c * g)⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  have hfix : (c * g) * z * (c * g)⁻¹ = z := by
    by_contra hne
    exact hJ _ hzJ hz2 hne (c * g) rfl
  refine ⟨c * g, ?_, ?_⟩
  · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc (c * g) * z = ((c * g) * z * (c * g)⁻¹) * (c * g) := by group
      _ = z * (c * g) := by rw [hfix]
  · rw [← CFSG.GroupTheory.map_conj_map_conj, hg, CFSG.GroupTheory.map_conj_zpowers]
    congr 1
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group

private theorem CJ_le_of_isSylowOf (hJ2 : IsPGroup 2 (J z)) {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer ({x} : Set G))) : CJ z x ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hT
  have hle : CJ z x ≤ H z ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    ⟨J_le_H (mem_CJ.mp hy).2, (mem_CJ.mp hy).1⟩
  have hN : ((CJ z x).subgroupOf (H z ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnx, hnJ⟩ := mem_CJ.mp hn
    refine mem_CJ.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ k.2.2 hnx) (Subgroup.inv_mem _ k.2.2)
    · exact (Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A k.2.1) n).mp hnJ
  have hP : IsPGroup 2 ((CJ z x).subgroupOf (H z ⊓ Subgroup.centralizer ({x} : Set G))) :=
    (hJ2.to_le (inf_le_right : CJ z x ≤ J z)).comap_subtype
  intro y hy
  exact ⟨⟨y, hle hy⟩, hP.le_sylow_of_normal Q (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

omit [Finite G] in
private theorem commutator_le_J_of_not_four_dvd
    [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) {x : ↥(H z)}
    {T : Subgroup G} (hTH : T ≤ H z) (hTx : T ≤ Subgroup.centralizer ({(x : G)} : Set G))
    (hT2 : IsPGroup 2 T)
    (h4 : ¬ 4 ∣ Nat.card (Subgroup.centralizer ({qHP D x} : Set QP45.originalSubgroup))) :
    ⁅T, T⁆ ≤ J z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup QP45.originalSubgroup := (T.subgroupOf (H z)).map (qHP D) with hQ
  have hQC : Q ≤ Subgroup.centralizer ({qHP D x} : Set QP45.originalSubgroup) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hTx (Subgroup.mem_subgroupOf.mp ht)))
  have hQ2 : IsPGroup 2 Q := (hT2.comap_subtype (K := H z)).map _
  obtain ⟨n, hn⟩ := hQ2.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card (Subgroup.centralizer ({qHP D x} : Set _)) :=
    Subgroup.card_dvd_of_le hQC
  have hn1 : n ≤ 1 := by
    by_contra hlt
    apply h4
    refine (pow_dvd_pow 2 (by omega : 2 ≤ n)).trans ?_
    rwa [← hn]
  have hQ2' : Nat.card Q ∣ 2 := by
    rw [hn]
    simpa using pow_dvd_pow 2 hn1
  have hsq : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    have h1 : orderOf (⟨q, hq⟩ : ↥Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans hQ2')
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (hsq _ (Q.mul_mem ha hb))
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hsq b hb), inv_eq_of_mul_eq_one_right (hsq a ha)]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : qHP D ⁅(⟨a, hTH ha⟩ : ↥(H z)), ⟨b, hTH hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ ⟨_, Subgroup.mem_subgroupOf.mpr ha, rfl⟩ _
      ⟨_, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have h2 : ⁅(⟨a, hTH ha⟩ : ↥(H z)), ⟨b, hTH hb⟩⁆ ∈ (J z).subgroupOf (H z) := by
    rw [← ker_qHP D]
    exact MonoidHom.mem_ker.mpr h1
  have h3 := Subgroup.mem_subgroupOf.mp h2
  have h4 : ((⁅(⟨a, hTH ha⟩ : ↥(H z)), ⟨b, hTH hb⟩⁆ : ↥(H z)) : G) = ⁅a, b⁆ :=
    map_commutatorElement (H z).subtype _ _
  rwa [h4] at h3

omit [Finite G] in
private theorem not_isConj_of_noFusionJ
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j := by
  intro j hj hj2 hjz hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  exact hJ j hj hj2 (fun hjz' => hjz (hjz' ▸ Subgroup.mem_zpowers z)) c hc

private theorem isSylowOf_centralizer_of_mem_derived_J_A1 (h : Tim79a.ParrottHypA1 z)
    {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer ({x} : Set G)))
    (hzT : z ∈ ⁅T, T⁆) (hTJ : ⁅T, T⁆ ≤ J z)
    (hJ : ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j) :
    IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf z = 2 := orderOf_z_A1 h
  refine CFSG.GroupTheory.isSylowOf_of_forall_pElement_normalizer_le hT ?_
  intro g _ hgN _
  have hTmap : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hmap : (⁅T, T⁆).map (MulAut.conj g).toMonoidHom = ⁅T, T⁆ := by
    rw [Subgroup.map_commutator, hTmap]
  have hzTg : g * z * g⁻¹ ∈ ⁅T, T⁆ := by
    have hmem : (MulAut.conj g) z ∈ (⁅T, T⁆).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzT
    simpa [MulAut.conj_apply] using hmap ▸ hmem
  have hz2 : orderOf (g * z * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rwa [MulAut.conj_apply, hzo] at this
  have hz_eq : g * z * g⁻¹ = z := by
    by_contra hne
    have hnz : g * z * g⁻¹ ∉ Subgroup.zpowers z := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · have h1' : g * z * g⁻¹ = 1 := by
          rw [← hk, ← zpow_mod_orderOf z k, hzo, show k % ((2 : ℕ) : ℤ) = 0 from h0, zpow_zero]
        rw [h1', orderOf_one] at hz2
        norm_num at hz2
      · exact hne (by
          rw [← hk, ← zpow_mod_orderOf z k, hzo, show k % ((2 : ℕ) : ℤ) = 1 from h1, zpow_one])
    exact hJ _ (hTJ hzTg) hz2 hnz (isConj_iff.mpr ⟨g, rfl⟩)
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hz_eq]

omit [Finite G] in
private theorem map_conj_zpowers_qHP
    [hN : ((J z).subgroupOf (H z)).Normal] {D : QuotientDataPSp (z := z) hN}
    {a b k : ↥(H z)}
    (hab : (Subgroup.zpowers a).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers b) :
    (Subgroup.zpowers (qHP D a)).map (MulAut.conj (qHP D k)).toMonoidHom =
      Subgroup.zpowers (qHP D b) := by
  rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← map_map_conj_eq, hab]

private theorem exists_map_conj_zpowers_eq_of_qHP
    [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) (hJ2 : IsPGroup 2 (J z)) {a b : ↥(H z)}
    (ha : orderOf a = 3) (hb : orderOf b = 3) {c : QP45.originalSubgroup}
    (hc : (Subgroup.zpowers (qHP D a)).map (MulAut.conj c).toMonoidHom =
      Subgroup.zpowers (qHP D b)) :
    ∃ k : ↥(H z), (Subgroup.zpowers a).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c', rfl⟩ := qHP_surjective D c
  set a' : ↥(H z) := c' * a * c'⁻¹ with ha'
  have hza' : (Subgroup.zpowers a).map (MulAut.conj c').toMonoidHom = Subgroup.zpowers a' :=
    CFSG.GroupTheory.map_conj_zpowers c' a
  have ha'3 : orderOf a' = 3 := by
    rw [ha', ← MulAut.conj_apply, MulEquiv.orderOf_eq, ha]
  have hmem : qHP D a' ∈ Subgroup.zpowers (qHP D b) := by
    rw [← hc]
    refine ⟨qHP D a, Subgroup.mem_zpowers _, ?_⟩
    simp [ha', MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  set J' : Subgroup ↥(H z) := (J z).subgroupOf (H z) with hJ'
  set M : Subgroup ↥(H z) := J' ⊔ Subgroup.zpowers b with hM
  have hbM : Subgroup.zpowers b ≤ M := le_sup_right
  have ha'M : Subgroup.zpowers a' ≤ M := by
    rw [Subgroup.zpowers_le]
    have hj : (b ^ n)⁻¹ * a' ∈ J' := by
      rw [hJ', ← ker_qHP D, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
    have hsplit : a' = b ^ n * ((b ^ n)⁻¹ * a') := by group
    rw [hsplit]
    exact M.mul_mem (hbM (Subgroup.zpow_mem_zpowers b n)) (le_sup_left (a := J') hj)
  have hJ'2 : IsPGroup 2 J' := hJ2.comap_subtype
  obtain ⟨e, he⟩ := hJ'2.exists_card_eq
  have hcb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hrelb : (Subgroup.zpowers b).relIndex M ∣ 2 ^ e := by
    rw [hM, relIndex_sup_eq_relIndex_of_normal, ← he]
    exact Subgroup.relIndex_dvd_card _ _
  have hsyl : ∀ X : Subgroup ↥(H z), X ≤ M → Nat.card X = 3 → IsSylowOf 3 X M := by
    intro X hXM hX
    have h1 := Subgroup.relIndex_mul_card X M
    have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers b) M
    rw [inf_eq_left.mpr hXM, hX] at h1
    rw [inf_eq_left.mpr hbM, hcb] at h2
    have hrel : X.relIndex M = (Subgroup.zpowers b).relIndex M := by omega
    rw [isSylowOf_iff]
    refine ⟨hXM, IsPGroup.of_card (n := 1) (by rw [hX, pow_one]), ?_⟩
    rw [hrel]
    intro h3
    have h32 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hrelb))
    omega
  obtain ⟨m, -, hm⟩ := (hsyl _ hbM hcb).exists_mem_conj
    (hsyl _ ha'M (by rw [Nat.card_zpowers, ha'3]))
  refine ⟨m⁻¹ * c', ?_⟩
  rw [← CFSG.GroupTheory.map_conj_map_conj, hza']
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using (hm x).mp hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, Nat.card_zpowers,
      Nat.card_zpowers, ha'3, hb]

section Lemma12


private theorem exists_isSylowOf_centralizer_sHP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∃ T : Subgroup G,
      IsSylowOf 2 T (Subgroup.centralizer ({((sHP (quotientDataA1 h) : ↥(H z)) : G)} : Set G)) ∧
        ⁅T, T⁆ ≤ J z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := quotientDataA1 h
  obtain ⟨T, hT⟩ := exists_isSylowOf 2
    (H z ⊓ Subgroup.centralizer ({((sHP D : ↥(H z)) : G)} : Set G))
  have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card (card_J_A1 h)
  have hCJ : CJ z ((sHP D : ↥(H z)) : G) ≤ T := CJ_le_of_isSylowOf hJ2 hT
  have hJ0T : CJ z ((s1HP D : ↥(H z)) : G) ≤ T := (CJ_s1HP_le_CJ_sHP_A1 h heq).trans hCJ
  have hzT : z ∈ ⁅T, T⁆ :=
    Subgroup.commutator_mono hJ0T hJ0T (z_mem_commutator_CJ_s1HP_A1 h)
  have hTJ : ⁅T, T⁆ ≤ J z := by
    refine commutator_le_J_of_not_four_dvd D (x := sHP D) (hT.le.trans inf_le_left)
      (hT.le.trans inf_le_right) hT.isPGroup ?_
    rw [qHP_sHP]
    have h54 := qp45_card_centralizer_s1s2inv
    have hs : (⟨sigma1 * sigma2⁻¹, QP45.originalSubgroup.mul_mem sigma1_mem_Q
        (QP45.originalSubgroup.inv_mem sigma2_mem_Q)⟩ : QP45.originalSubgroup) =
        (⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup) * (⟨sigma2, sigma2_mem_Q⟩)⁻¹ := rfl
    rw [hs, h54]
    norm_num
  exact ⟨T, isSylowOf_centralizer_of_mem_derived_J_A1 h hT hzT hTJ
    (not_isConj_of_noFusionJ hJ), hTJ⟩

omit [Finite G] in
private theorem orderOf_eq_three_of_qHP [hN : ((J z).subgroupOf (H z)).Normal]
    {D : QuotientDataPSp (z := z) hN} {x : ↥(H z)} (hx3 : x ^ 3 = 1)
    (hq : orderOf (qHP D x) = 3) : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime hx3 fun h1 => ?_
  rw [h1, map_one, orderOf_one] at hq
  omega

theorem not_conj_zpowers_s1HP_sHP_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ g : G, (Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G)).map
        (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G) := by
  intro g hg
  set D := quotientDataA1 h
  obtain ⟨T, hT, hTJ⟩ := exists_isSylowOf_centralizer_sHP_A1 h heq hJ
  have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card (card_J_A1 h)
  obtain ⟨k, hk, hkg⟩ := exists_mem_H_map_conj_zpowers_eq hJ (orderOf_z_A1 h) hT hTJ
    (U := CJ z ((s1HP D : ↥(H z)) : G)) (fun y hy => (mem_CJ.mp hy).1)
    (hJ2.to_le (fun y hy => (mem_CJ.mp hy).2))
    (z_mem_commutator_CJ_s1HP_A1 h) hg
  have hP := map_conj_zpowers_qHP (D := D) (map_conj_zpowers_eq_of_coe hk hkg)
  rw [qHP_s1HP, qHP_sHP] at hP
  exact qp45_orderThree_subgroup_not_conj.2.1 ⟨_, hP⟩

theorem not_conj_zpowers_sHP_s1s2HP_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ g : G, (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)).map
        (MulAut.conj g).toMonoidHom ≠
      Subgroup.zpowers ((s1HP (quotientDataA1 h) * s2HP (quotientDataA1 h) : ↥(H z)) : G) := by
  intro g hg
  set D := quotientDataA1 h
  obtain ⟨T, hT, hTJ⟩ := exists_isSylowOf_centralizer_sHP_A1 h heq hJ
  have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card (card_J_A1 h)
  have hg' : (Subgroup.zpowers ((s1HP D * s2HP D : ↥(H z)) : G)).map
      (MulAut.conj g⁻¹).toMonoidHom = Subgroup.zpowers ((sHP D : ↥(H z)) : G) := by
    rw [← hg, CFSG.GroupTheory.map_conj_map_conj_inv]
  obtain ⟨k, hk, hkg⟩ := exists_mem_H_map_conj_zpowers_eq hJ (orderOf_z_A1 h) hT hTJ
    (U := CJ z ((s1HP D * s2HP D : ↥(H z)) : G)) (fun y hy => (mem_CJ.mp hy).1)
    (hJ2.to_le (fun y hy => (mem_CJ.mp hy).2))
    (Subgroup.commutator_mono (CJ_s1HP_le_CJ_s1HP_mul_s2HP_A1 h heq)
      (CJ_s1HP_le_CJ_s1HP_mul_s2HP_A1 h heq) (z_mem_commutator_CJ_s1HP_A1 h))
    hg'
  have hP := map_conj_zpowers_qHP (D := D) (map_conj_zpowers_eq_of_coe hk hkg)
  rw [map_mul, qHP_s1HP, qHP_s2HP, qHP_sHP] at hP
  exact qp45_orderThree_subgroup_not_conj.2.2 ⟨_, hP⟩

theorem conj_zpowers_sHP_star_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) :
    ∀ g : G, CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) g ≤ H z →
      ∃ k ∈ H z, CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) g =
        CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) k := by
  intro g hgH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := quotientDataA1 h
  have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card (card_J_A1 h)
  have hY : CFSG.conjugate (Subgroup.zpowers ((sHP D : ↥(H z)) : G)) g =
      Subgroup.zpowers (g⁻¹ * ((sHP D : ↥(H z)) : G) * g) := by
    rw [CFSG.conjugate, CFSG.GroupTheory.map_conj_zpowers, inv_inv]
  have hyH : g⁻¹ * ((sHP D : ↥(H z)) : G) * g ∈ H z := hgH (hY ▸ Subgroup.mem_zpowers _)
  set yH : ↥(H z) := ⟨_, hyH⟩ with hyHdef
  have hy3 : orderOf yH = 3 := by
    rw [hyHdef, Subgroup.orderOf_mk]
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) ((sHP D : ↥(H z)) : G)
    rw [MulAut.conj_apply, inv_inv, Subgroup.orderOf_coe, orderOf_sHP D] at this
    exact this
  have hyq3 : orderOf (qHP D yH) = 3 := by
    have h1 : orderOf (qHP D yH) ∣ 3 := hy3 ▸ orderOf_map_dvd (qHP D) yH
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exfalso
      have hyJ : (yH : G) ∈ J z := by
        have : yH ∈ (qHP D).ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
        rw [ker_qHP D] at this
        exact Subgroup.mem_subgroupOf.mp this
      obtain ⟨e, he⟩ := hJ2 ⟨yH, hyJ⟩
      have h2 : orderOf yH ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
        simpa using congrArg Subtype.val he))
      rw [hy3] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
    · exact h1
  have hcard : Nat.card (Subgroup.zpowers (qHP D yH)) = 3 := by rw [Nat.card_zpowers, hyq3]
  have hs1 : (⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup) = qHP D (s1HP D) :=
    (qHP_s1HP D).symm
  have hs12 : (⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup) * ⟨sigma2, sigma2_mem_Q⟩ =
      qHP D (s1HP D * s2HP D) := by
    rw [map_mul, qHP_s1HP, qHP_s2HP]
  have hs : (⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup) * (⟨sigma2, sigma2_mem_Q⟩)⁻¹ =
      qHP D (sHP D) := by
    rw [qHP_sHP]
    rfl
  rcases qp45_orderThree_subgroup_classes _ hcard with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exfalso
    rw [hs1] at hc
    obtain ⟨k, hk⟩ := exists_map_conj_zpowers_eq_of_qHP D hJ2 hy3 (orderOf_s1HP D) hc
    apply not_conj_zpowers_s1HP_sHP_A1 h heq hJ (g * ((k : ↥(H z)) : G)⁻¹)
    rw [← map_conj_zpowers_coe_eq hk, CFSG.GroupTheory.map_conj_map_conj,
      CFSG.GroupTheory.map_conj_zpowers]
    congr 1
    simp only [hyHdef]
    group
    rfl
  · exfalso
    rw [hs12] at hc
    have h12q : orderOf (qHP D (s1HP D * s2HP D)) = 3 := by
      rw [← Nat.card_zpowers, ← hc, Subgroup.card_map_of_injective (MulAut.conj c).injective,
        hcard]
    have h12c : (s1HP D * s2HP D) ^ 3 = 1 := by
      have h1 : s1HP D ^ 3 = 1 := by
        rw [← orderOf_s1HP D]
        exact pow_orderOf_eq_one _
      have h2 : s2HP D ^ 3 = 1 := by
        rw [← orderOf_s2HP D]
        exact pow_orderOf_eq_one _
      rw [(commute_s1HP_s2HP D).mul_pow, h1, h2, one_mul]
    obtain ⟨k, hk⟩ := exists_map_conj_zpowers_eq_of_qHP D hJ2 hy3
      (orderOf_eq_three_of_qHP h12c h12q) hc
    apply not_conj_zpowers_sHP_s1s2HP_A1 h heq hJ (((k : ↥(H z)) : G) * g⁻¹)
    rw [← map_conj_zpowers_coe_eq hk, ← CFSG.GroupTheory.map_conj_map_conj,
      CFSG.GroupTheory.map_conj_zpowers, CFSG.GroupTheory.map_conj_zpowers,
      CFSG.GroupTheory.map_conj_zpowers]
    congr 1
    simp only [hyHdef]
    group
    rfl
  · rw [hs] at hc
    obtain ⟨k, hk⟩ := exists_map_conj_zpowers_eq_of_qHP D hJ2 hy3 (orderOf_sHP D) hc
    refine ⟨((k : ↥(H z)) : G), k.2, ?_⟩
    rw [hY, CFSG.conjugate, ← map_conj_zpowers_coe_eq hk, CFSG.GroupTheory.map_conj_map_conj,
      inv_mul_cancel]
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy

end Lemma12

end CFSG.RankThree.GF2n.Parrott
