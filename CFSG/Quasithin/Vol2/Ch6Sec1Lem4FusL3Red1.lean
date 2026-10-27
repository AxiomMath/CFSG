module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Red1

variable {Γ : Type} [Group Γ] [Finite Γ] {K T : Subgroup Γ}

@[expose] noncomputable def kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) : Subgroup Γ :=
  (piKT614 hTK).ker.map (K ⊔ T).subtype

theorem kerAct614_le_sup (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    kerAct614 hTK ≤ K ⊔ T :=
  Subgroup.map_subtype_le _

theorem mem_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {g : Γ} (hg : g ∈ K ⊔ T) :
    g ∈ kerAct614 hTK ↔ piKT614 hTK ⟨g, hg⟩ = 1 := by
  unfold kerAct614
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    have hx' : x = ⟨g, hg⟩ := Subtype.ext hxg
    rw [← hx']
    exact MonoidHom.mem_ker.mp hx
  · intro h
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩

private theorem conj_mem_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {g x : Γ}
    (hg : g ∈ K ⊔ T) (hx : x ∈ kerAct614 hTK) : g * x * g⁻¹ ∈ kerAct614 hTK := by
  have hxKT : x ∈ K ⊔ T := kerAct614_le_sup hTK hx
  have hgx : g * x * g⁻¹ ∈ K ⊔ T :=
    (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hg hxKT) ((K ⊔ T).inv_mem hg)
  rw [mem_kerAct614 hTK hgx]
  have hx1 : piKT614 hTK ⟨x, hxKT⟩ = 1 := (mem_kerAct614 hTK hxKT).mp hx
  have e : (⟨g * x * g⁻¹, hgx⟩ : ↥(K ⊔ T)) = ⟨g, hg⟩ * ⟨x, hxKT⟩ * (⟨g, hg⟩)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [e, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]

theorem kerAct614_normal (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    K ⊔ T ≤ Subgroup.normalizer (kerAct614 hTK : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_kerAct614 hTK hg
  · intro hx
    have h := conj_mem_kerAct614 hTK ((K ⊔ T).inv_mem hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem commutator_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {c k : Γ}
    (hc : c ∈ kerAct614 hTK) (hk : k ∈ K) : c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hXK : kerAct614 hTK ≤ Subgroup.normalizer (K : Set Γ) :=
    (kerAct614_le_sup hTK).trans (sup_le_normalizer614 hTK)
  have h := commutator_le_pCoreOf_of_actModO2_614 hXK
    (fun x hx => (mem_kerAct614 hTK (kerAct614_le_sup hTK hx)).mp hx)
  rw [← commutatorElement_def]
  exact h (Subgroup.commutator_mem_commutator hc hk)

theorem pCoreOf_le_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    pCoreOf 2 K ≤ kerAct614 hTK := by
  intro o ho
  have hok : o ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K ho
  apply (mem_kerAct614 hTK ((le_sup_left : K ≤ K ⊔ T) hok)).mpr
  rw [piKT614_of_mem hTK hok]
  have h1 : ((⟨o, hok⟩ : ↥K) : ModO2 K) = 1 :=
    (QuotientGroup.eq_one_iff (⟨o, hok⟩ : ↥K)).mpr
      (mem_pCore_of_mem_pCoreOf614 (k := ⟨o, hok⟩) ho)
  rw [h1, map_one]

theorem pCoreOf_le_of_sylow614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) : pCoreOf 2 K ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set Γ) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hT : T ≤ Subgroup.normalizer (pCoreOf 2 K : Set Γ) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hle : pCoreOf 2 K ≤ K ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle (sup_le hK hT)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs)

private theorem relIndex_eq_relIndex_sup614 {Q H : Subgroup Γ}
    (hHQ : H ≤ Subgroup.normalizer (Q : Set Γ)) : Q.relIndex H = Q.relIndex (H ⊔ Q) := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hHQ
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHQ
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H Q hHQ).toEquiv

private theorem relIndex_dvd_relIndex614 {N Y S : Subgroup Γ} (hNY : N ≤ Y) (hSY : S ≤ Y)
    (hSN : S ≤ Subgroup.normalizer (N : Set Γ)) : S.relIndex N ∣ S.relIndex Y := by
  have hNSY : S ⊔ N ≤ Y := sup_le hSY hNY
  have h1 : S.relIndex N * N.relIndex Y = (S ⊓ N).relIndex Y := by
    have h := Subgroup.relIndex_inf_mul_relIndex S N Y
    rwa [inf_eq_left.mpr hNY] at h
  have h2 : N.relIndex S * S.relIndex Y = (N ⊓ S).relIndex Y := by
    have h := Subgroup.relIndex_inf_mul_relIndex N S Y
    rwa [inf_eq_left.mpr hSY] at h
  have h3 : N.relIndex (S ⊔ N) * (S ⊔ N).relIndex Y = N.relIndex Y :=
    Subgroup.relIndex_mul_relIndex N (S ⊔ N) Y le_sup_right hNSY
  have h4 : N.relIndex S = N.relIndex (S ⊔ N) := relIndex_eq_relIndex_sup614 hSN
  have h5 : (S ⊓ N).relIndex Y = (N ⊓ S).relIndex Y := by rw [inf_comm]
  have hb : N.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  have key : N.relIndex S * (S.relIndex N * (S ⊔ N).relIndex Y) =
      N.relIndex S * S.relIndex Y := by
    calc N.relIndex S * (S.relIndex N * (S ⊔ N).relIndex Y)
        = S.relIndex N * (N.relIndex (S ⊔ N) * (S ⊔ N).relIndex Y) := by rw [h4]; ring
      _ = S.relIndex N * N.relIndex Y := by rw [h3]
      _ = (S ⊓ N).relIndex Y := h1
      _ = (N ⊓ S).relIndex Y := h5
      _ = N.relIndex S * S.relIndex Y := h2.symm
  exact ⟨(S ⊔ N).relIndex Y, (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb) key).symm⟩

private theorem odd_relIndex614 {N Y S : Subgroup Γ} (hS : IsSylowTwoOf S Y) (hNY : N ≤ Y)
    (hSN : S ≤ Subgroup.normalizer (N : Set Γ)) : ¬ 2 ∣ S.relIndex N :=
  fun h => hS.2.2 (h.trans (relIndex_dvd_relIndex614 hNY hS.1 hSN))

private theorem sup_le_normalizer_inf614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) :
    K ⊔ T ≤ Subgroup.normalizer ((kerAct614 hTK ⊓ K : Subgroup Γ) : Set Γ) := by
  have hn : ∀ y ∈ K ⊔ T, ∀ h ∈ kerAct614 hTK ⊓ K, y * h * y⁻¹ ∈ kerAct614 hTK ⊓ K := by
    intro y hy h hh
    have hC : y * h * y⁻¹ ∈ kerAct614 hTK :=
      (Subgroup.mem_normalizer_iff.mp (kerAct614_normal hTK hy) h).mp (Subgroup.mem_inf.mp hh).1
    have hK : y * h * y⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer614 hTK hy) h).mp
        (Subgroup.mem_inf.mp hh).2
    exact Subgroup.mem_inf.mpr ⟨hC, hK⟩
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hn y hy h
  · intro hh
    have h' := hn y⁻¹ ((K ⊔ T).inv_mem hy) _ hh
    have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rwa [e] at h'

private theorem relIndex_sup_dvd_two_pow614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) : ∃ n : ℕ, K.relIndex (K ⊔ T) ∣ 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hTs.2.1
  refine ⟨n, ?_⟩
  have h1 : K.relIndex (K ⊔ T) = K.relIndex T := by
    rw [sup_comm]
    exact (relIndex_eq_relIndex_sup614 hTK).symm
  have h2 : K.relIndex T ∣ Nat.card T := Subgroup.relIndex_dvd_card K T
  rw [hn] at h2
  rw [h1]
  exact h2

private theorem le_inf_sup_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) :
    kerAct614 hTK ≤ (kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T) := by
  have hCY : kerAct614 hTK ≤ K ⊔ T := kerAct614_le_sup hTK
  have hTC : T ≤ Subgroup.normalizer (kerAct614 hTK : Set Γ) :=
    le_sup_right.trans (kerAct614_normal hTK)
  have hCK : kerAct614 hTK ≤ Subgroup.normalizer (K : Set Γ) :=
    hCY.trans (sup_le_normalizer614 hTK)
  have hHC : (kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T) ≤ kerAct614 hTK :=
    sup_le inf_le_left inf_le_left
  have hBH : kerAct614 hTK ⊓ K ≤ (kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T) := le_sup_left
  have hAH : kerAct614 hTK ⊓ T ≤ (kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T) := le_sup_right
  have hd1 : ((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK) ∣
      T.relIndex (kerAct614 hTK) := by
    have h := Subgroup.relIndex_mul_relIndex (kerAct614 hTK ⊓ T) _ (kerAct614 hTK) hAH hHC
    rw [Subgroup.inf_relIndex_left] at h
    exact Dvd.intro_left _ h
  have hdT : ((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK) ∣
      T.relIndex (K ⊔ T) :=
    hd1.trans (relIndex_dvd_relIndex614 hCY le_sup_right hTC)
  have hodd : ¬ 2 ∣ ((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK) :=
    fun h => hTs.2.2 (h.trans hdT)
  have hd2 : ((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK) ∣
      K.relIndex (kerAct614 hTK) := by
    have h := Subgroup.relIndex_mul_relIndex (kerAct614 hTK ⊓ K) _ (kerAct614 hTK) hBH hHC
    rw [Subgroup.inf_relIndex_left] at h
    exact Dvd.intro_left _ h
  have hKC : K.relIndex (kerAct614 hTK) = K.relIndex (kerAct614 hTK ⊔ K) :=
    relIndex_eq_relIndex_sup614 hCK
  have hKCK : K.relIndex (kerAct614 hTK ⊔ K) ∣ K.relIndex (K ⊔ T) := by
    have h := Subgroup.relIndex_mul_relIndex K (kerAct614 hTK ⊔ K) (K ⊔ T) le_sup_right
      (sup_le hCY le_sup_left)
    exact Dvd.intro _ h
  obtain ⟨n, hn⟩ := relIndex_sup_dvd_two_pow614 hTK hTs
  have hdn : ((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK) ∣ 2 ^ n := by
    rw [hKC] at hd2
    exact hd2.trans (hKCK.trans hn)
  have hcop : Nat.Coprime
      (((kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T)).relIndex (kerAct614 hTK)) (2 ^ n) :=
    Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
  exact Subgroup.relIndex_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdn)

private theorem mem_of_pow_two_pow_mem_of_odd614 {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hodd : ¬ 2 ∣ N.index) {x : G} {m : ℕ} (hx : x ^ 2 ^ m ∈ N) : x ∈ N := by
  have h1 : orderOf (x : G ⧸ N) ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hx
  have h2 : orderOf (x : G ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ m) N.index :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h3 : orderOf (x : G ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_mul_of_mem_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {c : Γ} (hc : c ∈ kerAct614 hTK) :
    ∃ t ∈ kerAct614 hTK ⊓ T, ∃ z ∈ kerAct614 hTK ⊓ K, c = t * z := by
  have hTN : kerAct614 hTK ⊓ T ≤
      Subgroup.normalizer ((kerAct614 hTK ⊓ K : Subgroup Γ) : Set Γ) :=
    (inf_le_right.trans le_sup_right).trans (sup_le_normalizer_inf614 hTK)
  have hc' : c⁻¹ ∈ (kerAct614 hTK ⊓ K) ⊔ (kerAct614 hTK ⊓ T) :=
    le_inf_sup_kerAct614 hTK hTs ((kerAct614 hTK).inv_mem hc)
  have hmem : c⁻¹ ∈ ((kerAct614 hTK ⊓ K : Subgroup Γ) : Set Γ) *
      ((kerAct614 hTK ⊓ T : Subgroup Γ) : Set Γ) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN]
    exact hc'
  obtain ⟨z, hz, t, ht, hzt⟩ := Set.mem_mul.mp hmem
  refine ⟨t⁻¹, (kerAct614 hTK ⊓ T).inv_mem (SetLike.mem_coe.mp ht),
    z⁻¹, (kerAct614 hTK ⊓ K).inv_mem (SetLike.mem_coe.mp hz), ?_⟩
  calc c = (c⁻¹)⁻¹ := (inv_inv c).symm
    _ = (z * t)⁻¹ := by rw [hzt]
    _ = t⁻¹ * z⁻¹ := mul_inv_rev z t

private theorem conj_inf_T_mem614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {z p : Γ} (hz : z ∈ kerAct614 hTK ⊓ K)
    (hp : p ∈ kerAct614 hTK ⊓ T) : z * p * z⁻¹ ∈ kerAct614 hTK ⊓ T := by
  have h1 : p * z * p⁻¹ * z⁻¹ ∈ pCoreOf 2 K :=
    commutator_kerAct614 hTK (Subgroup.mem_inf.mp hp).1 (Subgroup.mem_inf.mp hz).2
  have h2 : z * p * z⁻¹ * p⁻¹ ∈ pCoreOf 2 K := by
    have h := (pCoreOf 2 K).inv_mem h1
    have e : (p * z * p⁻¹ * z⁻¹)⁻¹ = z * p * z⁻¹ * p⁻¹ := by group
    rwa [e] at h
  have h3 : z * p * z⁻¹ * p⁻¹ ∈ kerAct614 hTK ⊓ T :=
    Subgroup.mem_inf.mpr ⟨pCoreOf_le_kerAct614 hTK h2, pCoreOf_le_of_sylow614 hTK hTs h2⟩
  have e : z * p * z⁻¹ = (z * p * z⁻¹ * p⁻¹) * p := by group
  rw [e]
  exact (kerAct614 hTK ⊓ T).mul_mem h3 hp

private theorem conj_inf_T_mem_of_mem614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {c p : Γ} (hc : c ∈ kerAct614 hTK)
    (hp : p ∈ kerAct614 hTK ⊓ T) : c * p * c⁻¹ ∈ kerAct614 hTK ⊓ T := by
  obtain ⟨t, ht, z, hz, rfl⟩ := exists_mul_of_mem_kerAct614 hTK hTs hc
  have e : t * z * p * (t * z)⁻¹ = t * (z * p * z⁻¹) * t⁻¹ := by group
  rw [e]
  exact (kerAct614 hTK ⊓ T).mul_mem
    ((kerAct614 hTK ⊓ T).mul_mem ht (conj_inf_T_mem614 hTK hTs hz hp))
    ((kerAct614 hTK ⊓ T).inv_mem ht)

private theorem normal_inf_T_subgroupOf614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) :
    ((kerAct614 hTK ⊓ T).subgroupOf (kerAct614 hTK)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact conj_inf_T_mem_of_mem614 hTK hTs g.2 hn

private theorem mem_inf_T_of_pow_eq_one614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {c : Γ} (hc : c ∈ kerAct614 hTK) {m : ℕ}
    (hm : c ^ 2 ^ m = 1) : c ∈ kerAct614 hTK ⊓ T := by
  haveI := normal_inf_T_subgroupOf614 hTK hTs
  have hTC : T ≤ Subgroup.normalizer (kerAct614 hTK : Set Γ) :=
    le_sup_right.trans (kerAct614_normal hTK)
  have hodd : ¬ 2 ∣ (kerAct614 hTK ⊓ T).relIndex (kerAct614 hTK) := by
    rw [Subgroup.inf_relIndex_left]
    exact odd_relIndex614 hTs (kerAct614_le_sup hTK) hTC
  have hx1 : (⟨c, hc⟩ : ↥(kerAct614 hTK)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
  have hx2 : (⟨c, hc⟩ : ↥(kerAct614 hTK)) ^ 2 ^ m ∈
      (kerAct614 hTK ⊓ T).subgroupOf (kerAct614 hTK) := by
    rw [hx1]
    exact Subgroup.one_mem _
  have hx3 := mem_of_pow_two_pow_mem_of_odd614
    ((kerAct614 hTK ⊓ T).subgroupOf (kerAct614 hTK)) hodd hx2
  exact Subgroup.mem_subgroupOf.mp hx3

private theorem sup_le_normalizer_inf_T614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) :
    K ⊔ T ≤ Subgroup.normalizer ((kerAct614 hTK ⊓ T : Subgroup Γ) : Set Γ) := by
  have hconj : ∀ y ∈ K ⊔ T, ∀ p ∈ kerAct614 hTK ⊓ T, y * p * y⁻¹ ∈ kerAct614 hTK ⊓ T := by
    intro y hy p hp
    have hC : y * p * y⁻¹ ∈ kerAct614 hTK :=
      (Subgroup.mem_normalizer_iff.mp (kerAct614_normal hTK hy) p).mp (Subgroup.mem_inf.mp hp).1
    obtain ⟨k, hk⟩ := hTs.2.1 ⟨p, (Subgroup.mem_inf.mp hp).2⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hpow : (y * p * y⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow, hk', mul_one, mul_inv_cancel]
    exact mem_inf_T_of_pow_eq_one614 hTK hTs hC hpow
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact hconj y hy p
  · intro hp
    have h' := hconj y⁻¹ ((K ⊔ T).inv_mem hy) _ hp
    have e : y⁻¹ * (y * p * y⁻¹) * y⁻¹⁻¹ = p := by group
    rwa [e] at h'

theorem mem_pCoreOf_of_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {c : Γ} (hc : c ∈ kerAct614 hTK) {m : ℕ}
    (hm : c ^ 2 ^ m = 1) : c ∈ pCoreOf 2 (K ⊔ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : kerAct614 hTK ⊓ T ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans le_sup_right)
      (sup_le_normalizer_inf_T614 hTK hTs) (hTs.2.1.to_le inf_le_right)
  exact hle (mem_inf_T_of_pow_eq_one614 hTK hTs hc hm)

theorem conj_mem_inf_of_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {z t : Γ} (hz : z ∈ kerAct614 hTK ⊓ K) (ht : t ∈ T ⊓ K) :
    z * t * z⁻¹ ∈ T ⊓ K := by
  have h1 : z * t * z⁻¹ * t⁻¹ ∈ pCoreOf 2 K :=
    commutator_kerAct614 hTK (Subgroup.mem_inf.mp hz).1 (Subgroup.mem_inf.mp ht).2
  have h2 : z * t * z⁻¹ * t⁻¹ ∈ T := pCoreOf_le_of_sylow614 hTK hTs h1
  have e : z * t * z⁻¹ = (z * t * z⁻¹ * t⁻¹) * t := by group
  refine Subgroup.mem_inf.mpr ⟨?_, K.mul_mem (K.mul_mem (Subgroup.mem_inf.mp hz).2
    (Subgroup.mem_inf.mp ht).2) (K.inv_mem (Subgroup.mem_inf.mp hz).2)⟩
  rw [e]
  exact T.mul_mem h2 (Subgroup.mem_inf.mp ht).1

theorem mem_inf_of_two_elem_kerAct614 (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hTs : IsSylowTwoOf T (K ⊔ T)) {z t : Γ} (hz : z ∈ kerAct614 hTK ⊓ K) (ht : t ∈ T ⊓ K)
    {m : ℕ} (hm : (z * t) ^ 2 ^ m = 1) : z * t ∈ T ⊓ K := by
  have hBQ : kerAct614 hTK ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conj_mem_inf_of_kerAct614 hTK hTs hb hh
    · intro hh
      have h' := conj_mem_inf_of_kerAct614 hTK hTs ((kerAct614 hTK ⊓ K).inv_mem hb) hh
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [e] at h'
  have hRN : (T ⊓ K) ⊔ (kerAct614 hTK ⊓ K) ≤
      Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) :=
    sup_le Subgroup.le_normalizer hBQ
  haveI : ((T ⊓ K).subgroupOf ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRN
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)) := by
    have h1 : (T ⊓ K).relIndex ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)) =
        (T ⊓ K).relIndex (kerAct614 hTK ⊓ K) := by
      rw [sup_comm]
      exact (relIndex_eq_relIndex_sup614 hBQ).symm
    have e3 : (T ⊓ K) ⊓ (kerAct614 hTK ⊓ K) = T ⊓ (kerAct614 hTK ⊓ K) := by
      rw [inf_assoc, inf_eq_right.mpr (inf_le_right : kerAct614 hTK ⊓ K ≤ K)]
    have h2 : (T ⊓ K).relIndex (kerAct614 hTK ⊓ K) = T.relIndex (kerAct614 hTK ⊓ K) := by
      rw [← Subgroup.inf_relIndex_right (T ⊓ K) (kerAct614 hTK ⊓ K), e3,
        Subgroup.inf_relIndex_right]
    rw [h1, h2]
    exact odd_relIndex614 hTs (inf_le_right.trans le_sup_left)
      (le_sup_right.trans (sup_le_normalizer_inf614 hTK))
  have hzt : z * t ∈ (T ⊓ K) ⊔ (kerAct614 hTK ⊓ K) :=
    ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)).mul_mem
      ((le_sup_right : kerAct614 hTK ⊓ K ≤ (T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)) hz)
      ((le_sup_left : T ⊓ K ≤ (T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)) ht)
  have hx1 : (⟨z * t, hzt⟩ : ↥((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K))) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using hm)
  have hx2 : (⟨z * t, hzt⟩ : ↥((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K))) ^ 2 ^ m ∈
      (T ⊓ K).subgroupOf ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K)) := by
    rw [hx1]
    exact Subgroup.one_mem _
  have hx3 := mem_of_pow_two_pow_mem_of_odd614
    ((T ⊓ K).subgroupOf ((T ⊓ K) ⊔ (kerAct614 hTK ⊓ K))) hodd hx2
  exact Subgroup.mem_subgroupOf.mp hx3

end Red1

end CFSG.Quasithin.H13
