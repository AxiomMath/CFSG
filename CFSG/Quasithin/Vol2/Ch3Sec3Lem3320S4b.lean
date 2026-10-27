module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S4a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_mem_of_relIndex_two {K T : Subgroup G} (h2 : K.relIndex T = 2) {t t' : G}
    (ht : t ∈ T) (ht' : t' ∈ T) : ⁅t, t'⁆ ∈ K := by
  have hidx : (K.subgroupOf T).index = 2 := h2
  have hm : ((⟨t, ht⟩ : ↥T) * ⟨t', ht'⟩ * (⟨t, ht⟩ : ↥T)⁻¹ * (⟨t', ht'⟩ : ↥T)⁻¹) ∈
      K.subgroupOf T := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
    tauto
  exact Subgroup.mem_subgroupOf.mp hm

omit [Finite G] in
theorem eq_of_le_of_relIndex_eq {H K L : Subgroup G} (hHK : H ≤ K) (hKL : K ≤ L)
    (h : H.relIndex L = K.relIndex L) (h0 : K.relIndex L ≠ 0) : H = K := by
  have hmul := Subgroup.relIndex_mul_relIndex H K L hHK hKL
  rw [h] at hmul
  have h1 : H.relIndex K = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (hmul.trans (one_mul _).symm)
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.mp h1)

theorem inf_eq_of_isSylowTwoOf {Γ : Type*} [Group Γ] [Finite Γ] {Q N P : Subgroup Γ}
    (hQ : IsSylowTwoOf Q N) (hQP : Q ≤ P) (hP : IsPGroup 2 ↥P) : N ⊓ P = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQNP : Q ≤ N ⊓ P := le_inf hQ.1 hQP
  have hP2 : IsPGroup 2 ↥(N ⊓ P) := hP.to_le inf_le_right
  obtain ⟨n, hn⟩ := hP2.index (Q.subgroupOf (N ⊓ P))
  have hn' : Q.relIndex (N ⊓ P) = 2 ^ n := hn
  have hdvd : Q.relIndex (N ⊓ P) ∣ Q.relIndex N :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex Q (N ⊓ P) N hQNP inf_le_left)
  have h1 : Q.relIndex (N ⊓ P) = 1 := by
    rcases n with _ | n
    · simpa using hn'
    · exfalso
      apply hQ.2.2
      rw [hn'] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hQNP

theorem card_plus_eq {I T : Subgroup G} (hTI : IsSylowTwoOf T I)
    (hQ : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I)) :
    Nat.card ↥(plus I T) = (pCoreOf 2 I).relIndex T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 ↥(T.subgroupOf I) :=
    hTI.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTI.1).symm
  have hQT : Open.pCore 2 ↥I ≤ T.subgroupOf I := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTI
      (Subgroup.mem_map_of_mem I.subtype hx))
  have hNT : CFSG.pPrimeCore 3 ↥I ⊓ T.subgroupOf I = Open.pCore 2 ↥I :=
    inf_eq_of_isSylowTwoOf hQ hQT hT'
  show Nat.card ↥((T.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) = _
  rw [← Subgroup.relIndex_ker (K := T.subgroupOf I)
      (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)), QuotientGroup.ker_mk',
    ← Subgroup.inf_relIndex_right (H := CFSG.pPrimeCore 3 ↥I) (K := T.subgroupOf I), hNT,
    ← Subgroup.relIndex_map_map_of_injective (Open.pCore 2 ↥I) (T.subgroupOf I)
      I.subtype_injective, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTI.1]
  rfl

theorem card_of_caseTwo {Q : Type*} [Group Q] [Finite Q] (h : F6.IsF618CaseTwo Q) :
    Nat.card Q = 36 ∨ Nat.card Q = 108 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨φ, hφ, hker⟩
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    rfl
  · right
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker.2.1,
      Nat.card_prod] at h1
    rw [h1]
    simp [Nat.card_eq_fintype_card]

theorem card_le_four_of_caseTwo {Q : Type*} [Group Q] [Finite Q] (h : F6.IsF618CaseTwo Q)
    {P : Subgroup Q} (hP : IsPGroup 2 ↥P) : Nat.card ↥P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd := Subgroup.card_subgroup_dvd_card P
  rw [hk] at hdvd ⊢
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    rcases card_of_caseTwo h with hQ | hQ <;> rw [hQ] at hdvd <;>
      exact absurd (h8.trans hdvd) (by norm_num)
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem isSolvable_of_caseTwo {Q : Type*} [Group Q] [Finite Q] (h : F6.IsF618CaseTwo Q) :
    Group.IsSolvable Q := by
  rcases h with ⟨⟨e⟩⟩ | ⟨φ, hφ, hker⟩
  · have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : IsPGroup 3 ↥φ.ker := IsPGroup.of_card hker.2.1
    have : Group.IsNilpotent ↥φ.ker := h3.isNilpotent
    exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])

theorem isSolvable_of_caseTwo_triple {I G₁ G₂ : Subgroup G} (h : F6.IsGoldschmidtTripleIn I G₁ G₂)
    (h2 : F6.IsF618CaseTwo (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) : Group.IsSolvable ↥I := by
  have := h.isSolvable_pPrimeCore
  have := isSolvable_of_caseTwo h2
  exact Group.isSolvable_of_ker_le_range (CFSG.pPrimeCore 3 ↥I).subtype
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

theorem relIndex_R : (pCoreOf 2 (X ⊔ T)).relIndex T = 2 := by
  obtain ⟨e⟩ := H.hS3
  have h3 := Lem3320.relIndex_eq_three_of_iso H.isSylowTwoOf_XT e
  have h6 : (pCoreOf 2 (X ⊔ T)).relIndex (X ⊔ T) = 6 := by
    have hs : (pCoreOf 2 (X ⊔ T)).subgroupOf (X ⊔ T) = CFSG.pCore 2 ↥(X ⊔ T) := by
      exact Subgroup.comap_map_eq_self_of_injective (X ⊔ T).subtype_injective _
    rw [Subgroup.relIndex, hs, Subgroup.index_eq_card, Nat.card_congr e.toEquiv,
      Nat.card_perm, Nat.card_fin]
    rfl
  have h := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (X ⊔ T)) T (X ⊔ T) H.R_le_T le_sup_right
  rw [h3, h6] at h
  omega

theorem relIndex_conj_R {d : G} (hd : d ∈ D) :
    (conjByElt d (pCoreOf 2 (X ⊔ T))).relIndex T = 2 := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj d).toMonoidHom)
    (pCoreOf 2 (X ⊔ T)) T (MulAut.conj d).injective
  have hT : T.map (MulAut.conj d).toMonoidHom = T := H.conjByElt_T hd
  rw [hT, H.relIndex_R] at h
  exact h

theorem relIndex_inf_conj {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    (pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T))).relIndex T = 4 := by
  have hle := Subgroup.relIndex_inf_le (H := pCoreOf 2 (X ⊔ T))
    (K := conjByElt g (pCoreOf 2 (X ⊔ T))) (L := T)
  rw [H.relIndex_R, H.relIndex_conj_R hg] at hle
  have hmul := Subgroup.relIndex_mul_relIndex
    (pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T))) (pCoreOf 2 (X ⊔ T)) T
    inf_le_left H.R_le_T
  rw [H.relIndex_R] at hmul
  have hne : (pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T))).relIndex
      (pCoreOf 2 (X ⊔ T)) ≠ 1 := by
    intro h
    apply hgR
    have h3 : pCoreOf 2 (X ⊔ T) ≤ conjByElt g (pCoreOf 2 (X ⊔ T)) :=
      (Subgroup.relIndex_eq_one.mp h).trans inf_le_right
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (Subgroup.eq_of_le_of_card_ge h3 (card_conjByElt g _).le).symm
  have hpos : (pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T))).relIndex
      (pCoreOf 2 (X ⊔ T)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem pCoreOf_gZero_le {g : G} (hg : g ∈ D) :
    pCoreOf 2 (gZero X T g) ≤ pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 (gZero X T g) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (H.isSylowTwoOf_gZero g)
  have hON := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (gZero X T g)
  have hO2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (gZero X T g)
  refine le_inf ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      (le_sup_left.trans hON) hO2
  · rw [← pCoreOf_conj]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans (H.T_le_conj hg))
      (le_sup_right.trans hON) hO2

theorem plus_T_le {g : G} (hg : g ∈ D) :
    plus (gZero X T g) T ≤
      plus (gZero X T g) (X ⊔ T) ⊓ plus (gZero X T g) (conjByElt g (X ⊔ T)) :=
  le_inf (Subgroup.map_mono (Subgroup.comap_mono le_sup_right))
    (Subgroup.map_mono (Subgroup.comap_mono (H.T_le_conj hg)))

theorem isPGroup_plus_T (g : G) : IsPGroup 2 ↥(plus (gZero X T g) T) :=
  (H.h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (H.isSylowTwoOf_gZero g).1).symm).map _

theorem card_plus_T {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    Nat.card ↥(plus (gZero X T g) T) = (pCoreOf 2 (gZero X T g)).relIndex T :=
  card_plus_eq (H.isSylowTwoOf_gZero g)
    (H.isGoldschmidtTripleIn hg (H.not_mem_normalizer_X hg hgR)).isSylowTwoOf_pCore_pPrimeCore

theorem four_le_relIndex {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    4 ≤ (pCoreOf 2 (gZero X T g)).relIndex T := by
  have hdvd := Subgroup.relIndex_dvd_of_le_left (L := T) (H.pCoreOf_gZero_le hg)
  rw [H.relIndex_inf_conj hg hgR] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd

theorem not_caseOne {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    ¬ F6.IsF618CaseOne (plus (gZero X T g) (X ⊔ T)) (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∧
      ¬ F6.IsF618CaseOne (plus (gZero X T g) (conjByElt g (X ⊔ T)))
        (plus (gZero X T g) (X ⊔ T)) := by
  have h4 := H.four_le_relIndex hg hgR
  rw [← H.card_plus_T hg hgR] at h4
  have h2 := Subgroup.card_le_of_le (H.plus_T_le hg)
  have key : ∀ {A : Type} [Group A] [Finite A] (K : Subgroup A),
      Nonempty (↥K ≃* Multiplicative (ZMod 2)) → Nat.card ↥K = 2 := by
    intro A _ _ K ⟨e⟩
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  constructor
  · rintro ⟨he, -⟩
    have := key _ he
    omega
  · rintro ⟨he, -⟩
    rw [inf_comm] at he
    have := key _ he
    omega

theorem pCoreOf_eq_of_caseTwo {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G))
    (h2 : F6.IsF618CaseTwo (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))) :
    pCoreOf 2 (gZero X T g) = pCoreOf 2 (X ⊔ T) ⊓ conjByElt g (pCoreOf 2 (X ⊔ T)) := by
  have h4 := card_le_four_of_caseTwo h2 (H.isPGroup_plus_T g)
  rw [H.card_plus_T hg hgR] at h4
  have h4' := H.four_le_relIndex hg hgR
  refine eq_of_le_of_relIndex_eq (H.pCoreOf_gZero_le hg) (inf_le_left.trans H.R_le_T) ?_ ?_
  · rw [H.relIndex_inf_conj hg hgR]
    omega
  · rw [H.relIndex_inf_conj hg hgR]
    norm_num

theorem isSolvable_gZero_of_caseTwo {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G))
    (h2 : F6.IsF618CaseTwo (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))) :
    Group.IsSolvable ↥(gZero X T g) :=
  isSolvable_of_caseTwo_triple (H.isGoldschmidtTripleIn hg (H.not_mem_normalizer_X hg hgR)) h2

end Hyp3320

end S3320

end CFSG.Quasithin.H13
