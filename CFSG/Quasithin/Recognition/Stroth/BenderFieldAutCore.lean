module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_two_eq_one_of_odd_relIndex {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQKn : K ≤ Subgroup.normalizer (Q : Set G)) (hodd : Odd (Q.relIndex K)) {c : G}
    (hcK : c ∈ K) (hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1) : c ∈ Q := by
  classical
  haveI : (Q.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hQKn
  obtain ⟨k, hk⟩ := hc2
  let π : ↥K →* ↥K ⧸ Q.subgroupOf K := QuotientGroup.mk' (Q.subgroupOf K)
  have hπpow : (π ⟨c, hcK⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow, show (⟨c, hcK⟩ : ↥K) ^ 2 ^ k = 1 from Subtype.ext hk, map_one]
  have hdvd1 : orderOf (π ⟨c, hcK⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hπpow
  have hcard : Nat.card (↥K ⧸ Q.subgroupOf K) = Q.relIndex K := by
    rw [← Subgroup.index_eq_card]
    rfl
  have hdvd2 : orderOf (π ⟨c, hcK⟩) ∣ Q.relIndex K := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Q.relIndex K) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hone : orderOf (π ⟨c, hcK⟩) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd1 hdvd2)
  have hq1 : π ⟨c, hcK⟩ = 1 := orderOf_eq_one_iff.mp hone
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)

theorem commutator_mem_of_series {P Q Z K : Subgroup G} (hZQ : Z ≤ Q)
    (hQ2 : IsPGroup 2 Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hKP : K ≤ P) (hQK : Q ≤ K)
    (hQKn : K ≤ Subgroup.normalizer (Q : Set G))
    (hKodd : Odd (Q.relIndex K)) (hC7 : K ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hKn : P ≤ Subgroup.normalizer (K : Set G)) {t x : G} (htP : t ∈ P) (hxK : x ∈ K)
    (htQ : ∀ q ∈ Q, t * q * t⁻¹ * q⁻¹ ∈ Z)
    (htZ : ∀ z ∈ Z, t * z * t⁻¹ = z) :
    t * x * t⁻¹ * x⁻¹ ∈ Q := by
  classical
  set c : G := t * x * t⁻¹ * x⁻¹ with hc
  have hxP : x ∈ P := hKP hxK
  have hcK : c ∈ K := by
    rw [hc]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn htP) x).mp hxK) (K.inv_mem hxK)
  let C₁ : Subgroup G := centralizerMod Z P Q
  have hC₁n : P ≤ Subgroup.normalizer (C₁ : Set G) :=
    le_normalizer_centralizerMod hPZ Subgroup.le_normalizer hPQ
  have htC₁ : t ∈ C₁ := by
    rw [mem_centralizerMod]
    exact ⟨htP, hPZ htP, htQ⟩
  have hxtC₁ : x * t * x⁻¹ ∈ C₁ :=
    (Subgroup.mem_normalizer_iff.mp (hC₁n hxP) t).mp htC₁
  have hcC₁ : c ∈ C₁ := by
    rw [hc]
    have h := C₁.mul_mem htC₁ (C₁.inv_mem hxtC₁)
    have heq : t * (x * t * x⁻¹)⁻¹ = t * x * t⁻¹ * x⁻¹ := by group
    rwa [heq] at h
  let C₂ : Subgroup G := Subgroup.centralizer (Z : Set G)
  have hC₂n : P ≤ Subgroup.normalizer (C₂ : Set G) :=
    hPZ.trans (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer (Z : Subgroup G))
  have htC₂ : t ∈ C₂ := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h' : t * z = z * t := by
      calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [htZ z hz]
    exact h'.symm
  have hxtC₂ : x * t * x⁻¹ ∈ C₂ :=
    (Subgroup.mem_normalizer_iff.mp (hC₂n hxP) t).mp htC₂
  have hcC₂ : c ∈ C₂ := by
    rw [hc]
    have h := C₂.mul_mem htC₂ (C₂.inv_mem hxtC₂)
    have heq : t * (x * t * x⁻¹)⁻¹ = t * x * t⁻¹ * x⁻¹ := by group
    rwa [heq] at h
  set b : G := TauCeti.pFreePart 2 c with hb
  have hbK : b ∈ K := Subgroup.zpowers_le.mpr hcK (TauCeti.pFreePart_mem_zpowers 2 c)
  have hbC₁ : b ∈ C₁ := Subgroup.zpowers_le.mpr hcC₁ (TauCeti.pFreePart_mem_zpowers 2 c)
  have hbC₂ : b ∈ C₂ := Subgroup.zpowers_le.mpr hcC₂ (TauCeti.pFreePart_mem_zpowers 2 c)
  have hbodd : Odd (orderOf b) := by
    refine Nat.not_even_iff_odd.mp fun hev => ?_
    exact (TauCeti.not_dvd_orderOf_pFreePart Nat.prime_two (orderOf_pos c).ne')
      (even_iff_two_dvd.mp hev)
  have hbQs : ∀ q ∈ Q, b * q * b⁻¹ * q⁻¹ ∈ Z := fun q hq => (mem_centralizerMod.mp hbC₁).2.2 q hq
  have hbZs : ∀ z ∈ Z, b * z * b⁻¹ = z := by
    intro z hz
    have hcomm : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hbC₂) z hz
    calc b * z * b⁻¹ = (z * b) * b⁻¹ := by rw [hcomm.symm]
      _ = z := by group
  have hbcent : ∀ q ∈ Q, b * q * b⁻¹ = q :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series hbodd hQ2 hZQ
      (fun q hq => (Subgroup.mem_normalizer_iff.mp (hPQ (hKP hbK)) q).mp hq) hbZs hbQs
  have hbQ : b ∈ Q := hC7 (Subgroup.mem_inf.mpr ⟨hbK,
    (Subgroup.mem_centralizer_iff.mpr fun q hq => by
      calc q * b = (b * q * b⁻¹) * b := by rw [hbcent q hq]
        _ = b * q := by group)⟩)
  have hb1 : b = 1 := by
    obtain ⟨k, hk⟩ := hQ2 ⟨b, hbQ⟩
    have hb2pow : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hb2pow
    have hodd : Odd (orderOf b) := hbodd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj] at hodd
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · exact absurd hodd (by simp [Nat.pow_succ])
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  have hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    have hcb : c = TauCeti.pPart 2 c * b := (TauCeti.pPart_mul_pFreePart 2 c).symm
    have hc_eq : c = TauCeti.pPart 2 c := by
      calc c = TauCeti.pPart 2 c * b := hcb
        _ = TauCeti.pPart 2 c := by rw [hb1, mul_one]
    refine ⟨(orderOf c).factorization 2, ?_⟩
    have hord : orderOf (TauCeti.pPart 2 c) = 2 ^ (orderOf c).factorization 2 :=
      TauCeti.orderOf_pPart Nat.prime_two (orderOf_pos c).ne' 
    rw [← hord]
    have hpow : c ^ orderOf (TauCeti.pPart 2 c) =
        (TauCeti.pPart 2 c) ^ orderOf (TauCeti.pPart 2 c) :=
      congrArg (fun z : G => z ^ orderOf (TauCeti.pPart 2 c)) hc_eq
    rw [hpow]
    exact pow_orderOf_eq_one _
  exact mem_of_pow_two_eq_one_of_odd_relIndex hQK hQKn hKodd hcK hc2

theorem commutator_inv_inv_mem {M : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (M : Set G)) (hb : b ∈ Subgroup.normalizer (M : Set G))
    (h : a * b * a⁻¹ * b⁻¹ ∈ M) : a⁻¹ * b⁻¹ * a * b ∈ M := by
  have hN : a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem ha)
      ((Subgroup.normalizer _).inv_mem hb)
  have hconj : (a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) * (a⁻¹ * b⁻¹)⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp h
  simpa [mul_assoc] using hconj

theorem commutator_of_inv_right_mem {M : Subgroup G} {a b : G}
    (hb : b ∈ Subgroup.normalizer (M : Set G))
    (h : a * b⁻¹ * a⁻¹ * b ∈ M) : a * b * a⁻¹ * b⁻¹ ∈ M := by
  have hconj : b * (a * b⁻¹ * a⁻¹ * b) * b⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp hb _).mp h
  have e : b * (a * b⁻¹ * a⁻¹ * b) * b⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  rw [e] at hconj
  simpa using M.inv_mem hconj

theorem isPGroup_quotient_sup_of_isPGroup {P P' S : Subgroup G} (hP : P = P' ⊔ S)
    (hSP' : S ≤ Subgroup.normalizer (P' : Set G)) (hS2 : IsPGroup 2 S)
    [hP'normal : (P'.subgroupOf P).Normal] :
    IsPGroup 2 (↥P ⧸ P'.subgroupOf P) := by
  classical
  have hSP : S ≤ P := by rw [hP]; exact le_sup_right
  have hP'P : P' ≤ P := by rw [hP]; exact le_sup_left
  let f : ↥S →* ↥P ⧸ P'.subgroupOf P :=
    (QuotientGroup.mk' (P'.subgroupOf P)).comp (Subgroup.inclusion hSP)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    have hp : (p : G) ∈ P' ⊔ S := by rw [← hP]; exact p.2
    obtain ⟨p', hp', s, hs, hp_eq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSP').mp hp
    refine ⟨⟨s, hs⟩, ?_⟩
    change QuotientGroup.mk (⟨s, hSP hs⟩ : ↥P) = QuotientGroup.mk p
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hconj : s⁻¹ * p' * s ∈ P' := by
      have hsinv : s⁻¹ ∈ Subgroup.normalizer (P' : Set G) :=
        (Subgroup.normalizer _).inv_mem (hSP' hs)
      have h2 := (Subgroup.mem_normalizer_iff.mp hsinv p').mp hp'
      simpa using h2
    have e : ((⟨s, hSP hs⟩ : ↥P)⁻¹ * p : ↥P) =
        ⟨s⁻¹ * p' * s, P.mul_mem (P.mul_mem (P.inv_mem (hSP hs)) (hP'P hp')) (hSP hs)⟩ := by
      apply Subtype.ext
      simp [hp_eq, mul_assoc]
    rw [e]
    simpa using hconj
  exact IsPGroup.of_surjective hS2 f hf

theorem isPGroup_quotient_inf_of_isPGroup_quotient {P N K P' : Subgroup G}
    (hNP : N ≤ P) (hKP' : K ≤ P') (hM : N ⊓ K = N ⊓ P')
    [hP'normal : (P'.subgroupOf P).Normal]
    [hNKnormal : ((N ⊓ K).subgroupOf N).Normal]
    (hquot : IsPGroup 2 (↥P ⧸ P'.subgroupOf P)) :
    IsPGroup 2 (↥N ⧸ (N ⊓ K).subgroupOf N) := by
  classical
  let f : ↥N →* ↥P ⧸ P'.subgroupOf P :=
    (QuotientGroup.mk' (P'.subgroupOf P)).comp (Subgroup.inclusion hNP)
  have hfker : f.ker = (N ⊓ P').subgroupOf N := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : (Subgroup.inclusion hNP x : ↥P) ∈ P'.subgroupOf P :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_subgroupOf.mpr
        ⟨x.2, Subgroup.mem_subgroupOf.mp hx'⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2)
  haveI : IsPGroup 2 (↥P ⧸ P'.subgroupOf P) := hquot
  have hrange : IsPGroup 2 f.range := IsPGroup.to_subgroup hquot f.range
  have hker : (N ⊓ K).subgroupOf N = f.ker := by rw [hfker, hM]
  exact IsPGroup.of_equiv hrange
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange f)).symm

theorem le_pCoreOf_of_nilpotent_quotient {P N Q T : Subgroup G}
    (hNP : N ≤ P) (hNn : P ≤ Subgroup.normalizer (N : Set G))
    (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q) (hQn : P ≤ Subgroup.normalizer (Q : Set G))
    (hTN : T ≤ N) (hT2 : IsPGroup 2 T)
    [hQNnormal : (Q.subgroupOf N).Normal]
    (hquotNil : Group.IsNilpotent (↥N ⧸ (Q.subgroupOf N))) :
    T ≤ pCoreOf 2 P := by
  classical
  let Y := ↥N ⧸ (Q.subgroupOf N)
  let π : ↥N →* Y := QuotientGroup.mk' (Q.subgroupOf N)
  let R : Subgroup ↥N := (pCore 2 Y).comap π
  let N₂ : Subgroup G := R.map N.subtype
  have hker2 : IsPGroup 2 π.ker := by
    rw [show π.ker = Q.subgroupOf N from QuotientGroup.ker_mk' _]
    exact hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hR2 : IsPGroup 2 R :=
    IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := Y)) π hker2
  have hN₂2 : IsPGroup 2 N₂ := hR2.map N.subtype
  have hN₂N : N₂ ≤ N := Subgroup.map_subtype_le R
  have hN₂P : N₂ ≤ P := hN₂N.trans hNP
  have hmem : ∀ x ∈ N, x ∈ N₂ ↔ ∃ k : ℕ, x ^ 2 ^ k ∈ Q := by
    intro x hxN
    constructor
    · intro hxN₂
      obtain ⟨y, hyR, hyx⟩ := Subgroup.mem_map.mp hxN₂
      have hyQ : π y ∈ pCore 2 Y := hyR
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)).exists_pow_pow_eq_one
        ⟨π y, hyQ⟩
      have hπk : (π y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hyQ' : y ^ 2 ^ k ∈ Q.subgroupOf N := by
        rw [← QuotientGroup.eq_one_iff]
        exact hπk
      have hyG : (y : G) = x := hyx
      exact ⟨k, by simpa [hyG] using Subgroup.mem_subgroupOf.mp hyQ'⟩
    · rintro ⟨k, hkQ⟩
      have hπk : (π ⟨x, hxN⟩) ^ 2 ^ k = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkQ)
      have hz : IsPGroup 2 (Subgroup.zpowers (π ⟨x, hxN⟩)) :=
        isPGroup_iff_orderOf_dvd_pow.2 fun g =>
          ⟨k, by
            simpa [Subgroup.orderOf_coe] using
              (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one hπk)⟩
      haveI : Group.IsNilpotent Y := hquotNil
      have hle : Subgroup.zpowers (π ⟨x, hxN⟩) ≤ pCore 2 Y :=
        CFSG.section12_pSubgroup_le_pCore_of_nilpotent_pre hz
      exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hle (Subgroup.mem_zpowers _), rfl⟩
  have hN₂n : P ≤ Subgroup.normalizer (N₂ : Set G) := by
    have forward : ∀ p ∈ P, ∀ y ∈ N₂, p * y * p⁻¹ ∈ N₂ := by
      intro p hp y hy
      have hyN : y ∈ N := hN₂N hy
      obtain ⟨k, hkQ⟩ := (hmem y hyN).mp hy
      have hpyN : p * y * p⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hNn hp) y).mp hyN
      refine (hmem (p * y * p⁻¹) hpyN).mpr ⟨k, ?_⟩
      have hconjQ : p * y ^ 2 ^ k * p⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQn hp) _).mp hkQ
      have hpow : (p * y * p⁻¹) ^ 2 ^ k = p * y ^ 2 ^ k * p⁻¹ := by
        simpa [mul_assoc] using (conj_pow (a := p) (b := y) (i := 2 ^ k))
      rw [hpow]
      exact hconjQ
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact forward p hp x
    · intro hx
      have h := forward p⁻¹ (P.inv_mem hp) (p * x * p⁻¹) hx
      simpa [mul_assoc] using h
  have hN₂Q : N₂ ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 hN₂P hN₂n hN₂2
  have hT'2 : IsPGroup 2 ((T.subgroupOf N).map π) := by
    have hTsub : IsPGroup 2 (T.subgroupOf N) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
    exact hTsub.map π
  haveI : Group.IsNilpotent Y := hquotNil
  have hT'le : (T.subgroupOf N).map π ≤ pCore 2 Y :=
    CFSG.section12_pSubgroup_le_pCore_of_nilpotent_pre hT'2
  intro t ht
  have htN : t ∈ N := hTN ht
  have ht' : π ⟨t, htN⟩ ∈ (T.subgroupOf N).map π :=
    Subgroup.mem_map.mpr ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  exact hN₂Q (Subgroup.mem_map.mpr ⟨⟨t, htN⟩, hT'le ht', rfl⟩)

end CFSG.Quasithin.Stroth
