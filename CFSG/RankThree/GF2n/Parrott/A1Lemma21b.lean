module

public import CFSG.RankThree.GF2n.Parrott.A1SL23Pair
public import CFSG.RankThree.GF2n.Parrott.A1Quotient
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
import CFSG.RankThree.GF2n.Parrott.A1CentralizerOrders
import CFSG.RankThree.GF2n.Parrott.Proposition6D8SquareOne
import CFSG.Quasithin.EmptyFaithful.S143UA
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma38
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.OddStandard.SmallF3.HarrisU33 (twoThreeCore)

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem centralizes_of_mul_centralizes {Q : Subgroup G}
    (hsq : ∀ q ∈ Q, ∀ b ∈ Q, q * q * b = b * (q * q)) {y q : G} (hy3 : y ^ 3 = 1) (hq : q ∈ Q)
    (hc : ∀ a ∈ Q, y * q * a * (y * q)⁻¹ = a) : ∀ b ∈ Q, y * b * y⁻¹ = b := by
  have hmem : ∀ b ∈ Q, q⁻¹ * b * q ∈ Q := fun b hb =>
    Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hb) hq
  have hconj : ∀ b ∈ Q, y * b * y⁻¹ = q⁻¹ * b * q := by
    intro b hb
    calc y * b * y⁻¹ = y * q * (q⁻¹ * b * q) * (y * q)⁻¹ := by group
      _ = q⁻¹ * b * q := hc _ (hmem b hb)
  intro b hb
  have h3 : y * (y * (y * b * y⁻¹) * y⁻¹) * y⁻¹ = q⁻¹ * (q⁻¹ * (q⁻¹ * b * q) * q) * q := by
    rw [hconj b hb, hconj _ (hmem b hb), hconj _ (hmem _ (hmem b hb))]
  have hy : y * (y * (y * b * y⁻¹) * y⁻¹) * y⁻¹ = b := by
    calc y * (y * (y * b * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * b * (y ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = b := by rw [hy3]; group
  have hqq : (q * q)⁻¹ * b * (q * q) = b := by
    rw [mul_assoc, ← hsq q hq b hb]
    group
  have hqb : q⁻¹ * (q⁻¹ * (q⁻¹ * b * q) * q) * q = q⁻¹ * b * q := by
    calc q⁻¹ * (q⁻¹ * (q⁻¹ * b * q) * q) * q = q⁻¹ * ((q * q)⁻¹ * b * (q * q)) * q := by group
      _ = q⁻¹ * b * q := by rw [hqq]
  rw [hy, hqb] at h3
  rw [hconj b hb]
  exact h3.symm

omit [Finite G] in
private theorem inf_zpowers_eq_bot_of_card_center {B : Subgroup G}
    (hZ : Nat.card (Subgroup.center B) = 2) {s : G} (hs : orderOf s = 3)
    (hsB : ∀ b ∈ B, s * b = b * s) : B ⊓ Subgroup.zpowers s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxB, hxs⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have hxZ : (⟨x, hxB⟩ : B) ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxs
    change (b : G) * x = x * b
    rw [← hk]
    exact ((Commute.zpow_left (hsB b b.2) k).eq).symm
  have h2 : orderOf x ∣ 2 := by
    have := orderOf_dvd_natCard (⟨⟨x, hxB⟩, hxZ⟩ : Subgroup.center B)
    rwa [hZ, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  have h3 : orderOf x ∣ 3 := hs ▸ orderOf_dvd_of_mem_zpowers hxs
  have hg : Nat.gcd 2 3 = 1 := by norm_num
  have h1 : orderOf x ∣ 1 := hg ▸ Nat.dvd_gcd h2 h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private theorem mul_self_commute_of_mem_J (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {q b : G} (hq : q ∈ J z) (hb : b ∈ H z) :
    q * q * b = b * (q * q) := by
  have hpi : QuotientV.pi z (⟨q, hq⟩ * ⟨q, hq⟩) = 1 := by
    rw [map_mul, ← pow_two]
    exact pow_two_eq_one_V hJ _
  have hk : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥(J z)) ∈ (QuotientV.pi z).ker := hpi
  rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf, centerIn_J_eq_zpowers hJ hcomm] at hk
  have hk' : q * q ∈ Subgroup.zpowers z := by simpa using hk
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hk'
  rw [show (H z : Subgroup G) = Subgroup.centralizer ({z} : Set G) from rfl,
    Subgroup.mem_centralizer_singleton_iff] at hb
  rw [← hk]
  exact ((Commute.zpow_right hb k).eq).symm

omit [Finite G] in
private theorem sup_commute_of_commute {A A' B B' : Subgroup G}
    (h1 : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ A, ∀ b ∈ B', a * b = b * a)
    (h3 : ∀ a ∈ A', ∀ b ∈ B, a * b = b * a) (h4 : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) :
    ∀ x ∈ A ⊔ A', ∀ y ∈ B ⊔ B', x * y = y * x := by
  have hle : B ⊔ B' ≤ Subgroup.centralizer ((A ⊔ A' : Subgroup G) : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le (fun b hb => ?_) (fun b hb => ?_) <;> rw [Subgroup.mem_centralizer_iff]
      · exact fun a ha => h1 a ha b hb
      · exact fun a ha => h2 a ha b hb
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le (fun b hb => ?_) (fun b hb => ?_) <;> rw [Subgroup.mem_centralizer_iff]
      · exact fun a ha => h3 a ha b hb
      · exact fun a ha => h4 a ha b hb
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx

omit [Finite G] in
private theorem inv_mul_mem_of_index_two {P T : Subgroup G} (hidx : (P.subgroupOf T).index = 2)
    {a b : G} (ha : a ∈ T) (hb : b ∈ T) (haP : a ∉ P) (hbP : b ∉ P) : a⁻¹ * b ∈ P := by
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥T)⁻¹)
    (b := ⟨b, hb⟩)).mpr ⟨fun h1 => absurd (by simpa using Subgroup.mem_subgroupOf.mp h1) haP,
      fun h1 => absurd (Subgroup.mem_subgroupOf.mp h1) hbP⟩
  simpa using Subgroup.mem_subgroupOf.mp h

section Quotient

variable {S : G}

omit [Finite G] in
private theorem nonempty_map_mk_mulEquiv {A : Subgroup G}
    (hAY : A ≤ Subgroup.centralizer ({S} : Set G)) (hA : A ⊓ Subgroup.zpowers S = ⊥) :
    Nonempty (↥((A.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
      (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
        (Subgroup.centralizer ({S} : Set G))))) ≃* ↥A) := by
  set Y := Subgroup.centralizer ({S} : Set G)
  set N := (Subgroup.zpowers S).subgroupOf Y
  let f : ↥(A.subgroupOf Y) →* ↥Y ⧸ N := (QuotientGroup.mk' N).comp (A.subgroupOf Y).subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : (x : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_subgroupOf] at hxN
    have h1 : ((x : ↥Y) : G) ∈ A ⊓ Subgroup.zpowers S :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp x.2, hxN⟩
    rw [hA, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hrange : f.range = (A.subgroupOf Y).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((MonoidHom.ofInjective hf).symm.trans (Subgroup.subgroupOfEquivOfLe hAY))⟩

omit [Finite G] in
private theorem map_mk_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ (A.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
          (Subgroup.centralizer ({S} : Set G)))),
      ∀ y ∈ (B.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
          (Subgroup.centralizer ({S} : Set G)))), x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))

omit [Finite G] in
private theorem mk_conj_mem_map {A : Subgroup G} {k : ↥(Subgroup.centralizer ({S} : Set G))}
    (hk : (k : G) ∈ Subgroup.normalizer (A : Set G))
    {x : ↥(Subgroup.centralizer ({S} : Set G)) ⧸
      (Subgroup.zpowers S).subgroupOf (Subgroup.centralizer ({S} : Set G))}
    (hx : x ∈ (A.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
      (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf (Subgroup.centralizer ({S} : Set G))))) :
    QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf (Subgroup.centralizer ({S} : Set G))) k *
        x * (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
          (Subgroup.centralizer ({S} : Set G))) k)⁻¹ ∈
      (A.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
          (Subgroup.centralizer ({S} : Set G)))) := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨k * a * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  simpa using (Subgroup.mem_normalizer_iff.mp hk _).mp ha

omit [Finite G] in
private theorem mk_mem_normalizer_map {A : Subgroup G} {k : ↥(Subgroup.centralizer ({S} : Set G))}
    (hk : (k : G) ∈ Subgroup.normalizer (A : Set G)) :
    QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf (Subgroup.centralizer ({S} : Set G))) k ∈
      Subgroup.normalizer (((A.subgroupOf (Subgroup.centralizer ({S} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers S).subgroupOf
          (Subgroup.centralizer ({S} : Set G))))) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => mk_conj_mem_map hk hx, fun hx => ?_⟩
  have hk' : ((k⁻¹ : ↥(Subgroup.centralizer ({S} : Set G))) : G) ∈
      Subgroup.normalizer (A : Set G) := by
    simpa using inv_mem hk
  have h := mk_conj_mem_map hk' hx
  rw [map_inv, inv_inv] at h
  convert h using 1
  group

end Quotient

section CaseOne


theorem lemma21_dichotomy
    (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = ⟨sigma1, sigma1_mem_A⟩) (hσ₂ : φ σ₂ = ⟨sigma2, sigma2_mem_A⟩)
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂)
    (hP6I : ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
      [_hO23 : ((CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
        (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).Normal] →
      (∃ L1 L2 : Subgroup G,
        L1 ≤ Subgroup.centralizer ({z} : Set G) ∧ L2 ≤ Subgroup.centralizer ({z} : Set G) ∧
        Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23) ∧
        (∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x) ∧
        L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
        L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype ∧
        L1 ⊔ L2 = CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
          (Subgroup.centralizer ({z} : Set G)) ∧
        ¬ (L1.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        ¬ (L2.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
        Nat.card (↥(Subgroup.centralizer ({z} : Set G)) ⧸
            (CFSG.OddStandard.SmallF3.HarrisU33.twoThreeCore
              (Subgroup.centralizer ({z} : Set G))).subgroupOf
              (Subgroup.centralizer ({z} : Set G))) = 2) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
        CFSG.Blueprint.LieModel G .PSp 2 3 1)
    [hNs : ((Subgroup.zpowers ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)).subgroupOf
      (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G))).Normal] :
    CFSG.Blueprint.LieModel
        (↥(Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ⧸
          (Subgroup.zpowers ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)).subgroupOf
            (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) .PSp 2 3 1 ∨
      Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G) =
        (H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ⊔
          (pPrimeCore 2 ↥(Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G))).map
            (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)).subtype := by
  classical
  obtain ⟨y, hy9, hyσ⟩ := hy
  obtain ⟨u, hu⟩ := hu
  have hQP := hrange.ge
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy9]; norm_num), hy9]
  obtain ⟨hs3, h32⟩ :=
    card_CJ_sigma1_mul_sigma2_inv_eq hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy9 hyσ hu
  have hz2 := orderOf_z hJ hcomm
  have hcardK := card_H_inf_centralizer_sigma1_mul_sigma2_inv hJ hcard hcomm hCHJ φ hker hrange
    hσ₁ hσ₂ h3₂ hc hy9 hyσ
  obtain ⟨Q₁, Q₂, hQ, hQi, hQc, hQ₁, hQ₂, -, -⟩ :=
    exists_quaternion_pair_CJ_sigma1_mul_sigma2_inv_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂
      hc hne hy9 hyσ hu
  obtain ⟨t₀, ht₀, hct₁, hct₂⟩ := exists_lift_t_commute_of hcard φ hker hQP hσ₁ hσ₂ h3₁ h3₂ hc
  have hτ₁ : Q₁.map (MulAut.conj (t₀ : G)).toMonoidHom = Q₂ :=
    map_conj_t_quaternion_pair_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy9 hyσ hu ht₀
      hQ hQi hQc hQ₁ hQ₂
  have hτ₂ : Q₂.map (MulAut.conj (t₀ : G)).toMonoidHom = Q₁ :=
    map_conj_t_quaternion_pair_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy9 hyσ hu ht₀
      (by rw [sup_comm]; exact hQ) (by rw [inf_comm]; exact hQi)
      (fun a ha b hb => (hQc b hb a ha).symm) hQ₂ hQ₁
  obtain ⟨y₁, y₂, hy₁3, hy₂3, hy₁₂, h1y₁, h2y₁, h1y₂, h2y₂, hy₁N₁, hy₁N₂, hy₂N₁, hy₂N₂, hy₁c,
    hy₂c, ⟨a₁, ha₁, ha₁m⟩, ⟨b₂, hb₂, hb₂m⟩⟩ :=
    exists_sl23_pair_generators hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ h3₂ hc hne hy9 hyσ hu hQ
      hQi hQc hQ₁ hQ₂
  set s : ↥(H z) := σ₁ * σ₂⁻¹ with hs_def
  set S : G := (s : G) with hS_def
  set P := CJ z S with hP_def
  set Y := Subgroup.centralizer ({S} : Set G) with hY_def
  have hS3 : orderOf S = 3 := by rw [hS_def, Subgroup.orderOf_coe, hs3]
  have hzY : z ∈ Y :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp s.2).symm
  have hmemY : ∀ g : ↥(H z), Commute σ₁ g → Commute σ₂ g → (g : G) ∈ Y := fun g h1 h2 =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((h1.mul_left h2.inv_left).eq.symm))
  have hPY : P ≤ Y := inf_le_left
  have hPJ : P ≤ J z := inf_le_right
  have hPH : P ≤ H z := hPJ.trans J_le_H
  have hQ₁P : Q₁ ≤ P := hQ ▸ le_sup_left
  have hQ₂P : Q₂ ≤ P := hQ ▸ le_sup_right
  have hzQ₁ : z ∈ Q₁ := (hQi ▸ inf_le_left : Subgroup.zpowers z ≤ Q₁) (Subgroup.mem_zpowers z)
  have hzQ₂ : z ∈ Q₂ := (hQi ▸ inf_le_right : Subgroup.zpowers z ≤ Q₂) (Subgroup.mem_zpowers z)
  have hy₁Y := hmemY y₁ h1y₁ h2y₁
  have hy₂Y := hmemY y₂ h1y₂ h2y₂
  have ht₀Y := hmemY t₀ hct₁.symm hct₂.symm
  set B₁ := Q₁ ⊔ Subgroup.zpowers (y₁ : G) with hB₁_def
  set B₂ := Q₂ ⊔ Subgroup.zpowers (y₂ : G) with hB₂_def
  have hB₁Y : B₁ ≤ Y := sup_le (hQ₁P.trans hPY) (Subgroup.zpowers_le_of_mem hy₁Y)
  have hB₂Y : B₂ ≤ Y := sup_le (hQ₂P.trans hPY) (Subgroup.zpowers_le_of_mem hy₂Y)
  have hB₁H : B₁ ≤ H z := sup_le (hQ₁P.trans hPH) (Subgroup.zpowers_le_of_mem y₁.2)
  have hB₂H : B₂ ≤ H z := sup_le (hQ₂P.trans hPH) (Subgroup.zpowers_le_of_mem y₂.2)
  obtain ⟨e₁⟩ : Nonempty (↥B₁ ≃* CFSG.OddStandard.Solomon75.SL23) :=
    CFSG.Quasithin.S143.SL23.nonempty_mulEquiv_sl23 hQ₁ (by rw [Subgroup.orderOf_coe, hy₁3])
      (fun b hb => (Subgroup.mem_normalizer_iff.mp hy₁N₁ b).mp hb) ⟨a₁, ha₁, ha₁m⟩
  obtain ⟨e₂⟩ : Nonempty (↥B₂ ≃* CFSG.OddStandard.Solomon75.SL23) :=
    CFSG.Quasithin.S143.SL23.nonempty_mulEquiv_sl23 hQ₂ (by rw [Subgroup.orderOf_coe, hy₂3])
      (fun b hb => (Subgroup.mem_normalizer_iff.mp hy₂N₂ b).mp hb) ⟨b₂, hb₂, hb₂m⟩
  have hZB : ∀ {B : Subgroup G}, (↥B ≃* CFSG.OddStandard.Solomon75.SL23) →
      Nat.card (Subgroup.center B) = 2 := fun e =>
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6
  have hSB : ∀ {B : Subgroup G}, B ≤ Y → ∀ b ∈ B, S * b = b * S := fun hBY b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hBY hb)).symm
  have hB₁S : B₁ ⊓ Subgroup.zpowers S = ⊥ :=
    inf_zpowers_eq_bot_of_card_center (hZB e₁) hS3 (hSB hB₁Y)
  have hB₂S : B₂ ⊓ Subgroup.zpowers S = ⊥ :=
    inf_zpowers_eq_bot_of_card_center (hZB e₂) hS3 (hSB hB₂Y)
  have hBc : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a := by
    refine sup_commute_of_commute hQc (fun a ha b hb => ?_) (fun a ha b hb => ?_)
      (fun a ha b hb => ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_right (show Commute a (y₂ : G) from (hy₂c a ha).symm) k)).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ((Commute.zpow_left (show Commute (y₁ : G) b from hy₁c b hb) k)).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_zpow (congrArg Subtype.val hy₁₂.eq : (y₁ : G) * y₂ = y₂ * y₁) k
        l)).eq
  have hcts : Commute s t₀ := hct₁.symm.mul_left hct₂.symm.inv_left
  have hτN : (t₀ : G) ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_CJ_of_commute hcts
  have hτJ : (t₀ : G) ∉ J z := by
    intro h
    have hk : t₀ ∈ φ.ker := by rw [hker, Subgroup.mem_subgroupOf]; exact h
    rw [MonoidHom.mem_ker, ht₀] at hk
    exact t_ne_one (congrArg Subtype.val hk)
  have hτP : (t₀ : G) ∉ P := fun h => hτJ (hPJ h)
  have hτ2 : (t₀ : G) * t₀ ∈ P := by
    have hk : t₀ * t₀ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, ht₀]
      apply Subtype.ext
      simp [t_sq]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    refine mem_CJ.mpr ⟨?_, hk⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((hcts.mul_right hcts).eq.symm)
  set T₂ := P ⊔ Subgroup.zpowers (t₀ : G) with hT₂_def
  have hT64 : Nat.card T₂ = 64 := card_eq_sixtyFour hQ₁ hQ₂ hQc hz2 hQi hQ hτN hτ2 hτP rfl
  have hT₂Y : T₂ ≤ Y := sup_le hPY (Subgroup.zpowers_le_of_mem ht₀Y)
  have hPT : P ≤ T₂ := le_sup_left
  have hidxT : (P.subgroupOf T₂).index = 2 := by
    have h := Subgroup.card_mul_index (P.subgroupOf T₂)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv, h32, hT64] at h
    omega
  have hτT : (t₀ : G) ∈ T₂ := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hPconj : ∀ p ∈ P, ∀ a ∈ Q₁, p * a * p⁻¹ ∈ Q₁ := by
    intro p hp a ha
    rw [← hQ, CFSG.mem_sup_of_commute (fun a ha b hb => hQc a ha b hb)] at hp
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := hp
    have h : q₁ * q₂ * a * (q₁ * q₂)⁻¹ = q₁ * a * q₁⁻¹ := by
      calc q₁ * q₂ * a * (q₁ * q₂)⁻¹ = q₁ * (q₂ * a) * q₂⁻¹ * q₁⁻¹ := by group
        _ = q₁ * a * q₁⁻¹ := by rw [← hQc a ha q₂ hq₂]; group
    rw [h]
    exact Q₁.mul_mem (Q₁.mul_mem hq₁ ha) (Q₁.inv_mem hq₁)
  have hswap : ∀ x ∈ T₂, x ∉ P → ∀ a ∈ Q₁, x * a * x⁻¹ ∈ Q₂ := by
    intro x hx hxP a ha
    have hp₀ := inv_mul_mem_of_index_two hidxT hτT hx hτP hxP
    have h1 := hPconj _ hp₀ a ha
    have h2 : (t₀ : G) * ((t₀ : G)⁻¹ * x * a * ((t₀ : G)⁻¹ * x)⁻¹) * (t₀ : G)⁻¹ ∈ Q₂ := by
      rw [← hτ₁]
      exact ⟨_, h1, rfl⟩
    convert h2 using 1
    group
  set N := (Subgroup.zpowers S).subgroupOf Y with hN_def
  set π := QuotientGroup.mk' N with hπ_def
  set zb := π ⟨z, hzY⟩ with hzb_def
  set C := Subgroup.centralizer ({zb} : Set (↥Y ⧸ N)) with hC_def
  have hzb2 : orderOf zb = 2 := orderOf_mk_eq_two hS3 hzY hz2
  have hCmap : C = ((Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y).map π :=
    centralizer_mk_eq_map hS3 hzY hz2
  have hmemC : ∀ k : ↥Y, (k : G) ∈ H z → π k ∈ C := fun k hk => by
    rw [hCmap]
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hk, k.2⟩, rfl⟩
  have hliftC : ∀ c ∈ C, ∃ k : ↥Y, (k : G) ∈ H z ∧ π k = c := by
    intro c hc
    rw [hCmap] at hc
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
    exact ⟨k, (Subgroup.mem_subgroupOf.mp hk).1, rfl⟩
  have hC576 : Nat.card C = 576 := by
    have h : Nat.card C * 3 = Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Y) :=
      card_centralizer_mk_mul_three hS3 hzY hz2
    have h' : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Y) = 2 ^ 6 * 27 := hcardK
    rw [h'] at h
    norm_num at h
    omega
  set L1 := (B₁.subgroupOf Y).map π with hL1_def
  set L2 := (B₂.subgroupOf Y).map π with hL2_def
  set Pb := (P.subgroupOf Y).map π with hPb_def
  set Tb := (T₂.subgroupOf Y).map π with hTb_def
  have hmapC : ∀ {A : Subgroup G}, A ≤ Y → A ≤ H z → (A.subgroupOf Y).map π ≤ C := by
    intro A _ hAH
    rintro _ ⟨a, ha, rfl⟩
    exact hmemC a (hAH (Subgroup.mem_subgroupOf.mp ha))
  have hT₂H : T₂ ≤ H z := sup_le hPH (Subgroup.zpowers_le_of_mem t₀.2)
  have hL1C : L1 ≤ C := hmapC hB₁Y hB₁H
  have hL2C : L2 ≤ C := hmapC hB₂Y hB₂H
  have hPbC : Pb ≤ C := hmapC hPY hPH
  have hTbC : Tb ≤ C := hmapC hT₂Y hT₂H
  have hiso : ∀ {A : Subgroup G}, A ≤ Y → A ⊓ Subgroup.zpowers S = ⊥ →
      Nat.card ((A.subgroupOf Y).map π) = Nat.card A := by
    intro A hAY hA
    obtain ⟨e⟩ := nonempty_map_mk_mulEquiv hAY hA
    exact Nat.card_congr e.toEquiv
  have h2bot : ∀ {A : Subgroup G}, IsPGroup 2 A → A ⊓ Subgroup.zpowers S = ⊥ := by
    intro A hA
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxS⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn⟩ := hA ⟨x, hxA⟩
    have h2 : orderOf x ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    have h3 : orderOf x ∣ 3 := hS3 ▸ orderOf_dvd_of_mem_zpowers hxS
    have hg := Nat.dvd_gcd h2 h3
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hg
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 5) (by rw [h32]; norm_num)
  have hT2 : IsPGroup 2 T₂ := IsPGroup.of_card (n := 6) (by rw [hT64]; norm_num)
  have hPb32 : Nat.card Pb = 32 := (hiso hPY (h2bot hP2)).trans h32
  have hTb64 : Nat.card Tb = 64 := (hiso hT₂Y (h2bot hT2)).trans hT64
  obtain ⟨f₁⟩ := nonempty_map_mk_mulEquiv hB₁Y hB₁S
  obtain ⟨f₂⟩ := nonempty_map_mk_mulEquiv hB₂Y hB₂S
  have eL1 : ↥L1 ≃* CFSG.OddStandard.Solomon75.SL23 := f₁.trans e₁
  have eL2 : ↥L2 ≃* CFSG.OddStandard.Solomon75.SL23 := f₂.trans e₂
  have hL124 : Nat.card L1 = 24 := (Nat.card_congr eL1.toEquiv).trans card_sl23_p6
  have hL224 : Nat.card L2 = 24 := (Nat.card_congr eL2.toEquiv).trans card_sl23_p6
  have hcommL : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x := map_mk_commute hBc
  have hzbL1 : zb ∈ L1 :=
    ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hzQ₁), rfl⟩
  have hzbL2 : zb ∈ L2 :=
    ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hzQ₂), rfl⟩
  have hZL : ∀ {L : Subgroup (↥Y ⧸ N)}, (↥L ≃* CFSG.OddStandard.Solomon75.SL23) →
      Nat.card ((Subgroup.center L).map L.subtype) = 2 := fun {L} e => by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6
  have hcenter : ∀ {L L' : Subgroup (↥Y ⧸ N)}, (↥L ≃* CFSG.OddStandard.Solomon75.SL23) →
      L ≤ C → zb ∈ L → zb ∈ L' → (∀ x ∈ L', ∀ y ∈ L, x * y = y * x) →
      L ⊓ L' = (Subgroup.center L).map L.subtype := by
    intro L L' e hLC hzL hzL' hc
    have hzZ : zb ∈ (Subgroup.center L).map L.subtype := by
      rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center]
      refine Subgroup.mem_inf.mpr ⟨hzL, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLC hh)
    have hZeq : (Subgroup.center L).map L.subtype = Subgroup.zpowers zb :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hzZ)
        (by rw [hZL e, Nat.card_zpowers, hzb2])).symm
    apply le_antisymm
    · rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center]
      refine le_inf inf_le_left fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact (hc x (Subgroup.mem_inf.mp hx).2 h hh).symm
    · rw [hZeq]
      exact Subgroup.zpowers_le_of_mem (Subgroup.mem_inf.mpr ⟨hzL, hzL'⟩)
  have hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype :=
    hcenter eL1 hL1C hzbL1 hzbL2 fun x hx y hy => (hcommL y hy x hx).symm
  have hinf2 : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype := by
    rw [inf_comm]
    exact hcenter eL2 hL2C hzbL2 hzbL1 hcommL
  have hinfcard : Nat.card ↥(L1 ⊓ L2) = 2 := by rw [hinf1]; exact hZL eL1
  have hR288 : Nat.card ↥(L1 ⊔ L2) = 288 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L1 L2 hcommL).1
    rw [hinfcard, hL124, hL224] at h
    omega
  have hRC : L1 ⊔ L2 ≤ C := sup_le hL1C hL2C
  have hidxR : ((L1 ⊔ L2).subgroupOf C).index = 2 := by
    have h := Subgroup.card_mul_index ((L1 ⊔ L2).subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hR288, hC576] at h
    omega
  have hOR : Pb ≤ L1 ⊔ L2 := by
    rintro _ ⟨p, hp, rfl⟩
    have hpP := Subgroup.mem_subgroupOf.mp hp
    rw [← hQ, CFSG.mem_sup_of_commute (fun a ha b hb => hQc a ha b hb)] at hpP
    obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := hpP
    have hpe : p = ⟨q₁, hPY (hQ₁P hq₁)⟩ * ⟨q₂, hPY (hQ₂P hq₂)⟩ := Subtype.ext hq.symm
    rw [hpe, map_mul]
    exact mul_mem
      (Subgroup.mem_sup_left ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hq₁), rfl⟩)
      (Subgroup.mem_sup_right ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hq₂), rfl⟩)
  have hON : (Pb.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPbC]
    intro c hc
    obtain ⟨k, hkH, rfl⟩ := hliftC c hc
    apply mk_mem_normalizer_map
    have hck : Commute s ⟨(k : G), hkH⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2).symm
    exact mem_normalizer_CJ_of_commute hck
  have hO : IsPGroup 2 Pb := IsPGroup.of_card (n := 5) (by rw [hPb32]; norm_num)
  have hsqQ₁ : ∀ q ∈ Q₁, ∀ b ∈ Q₁, q * q * b = b * (q * q) := fun q hq b hb =>
    mul_self_commute_of_mem_J hJ hcomm (hPJ (hQ₁P hq)) (hPH (hQ₁P hb))
  have hy₁3' : (y₁ : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hy₁3, pow_orderOf_eq_one, Subgroup.coe_one]
  have hnc : ∀ n ∈ Subgroup.zpowers S, ∀ c ∈ Y, n * c = c * n := by
    intro n hn c hcY
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hcY).symm k)).eq
  have ha₁Q₂ : a₁ ∉ Q₂ := fun h => ha₁m (by rw [hy₁c a₁ h]; group)
  have hOmax : ∀ W : Subgroup (↥Y ⧸ N), W ≤ C → (W.subgroupOf C).Normal → IsPGroup 2 W →
      W ≤ Pb := by
    intro W hWC hWn hW2
    have hCN : C ≤ Subgroup.normalizer (W : Set (↥Y ⧸ N)) :=
      Subgroup.le_normalizer_of_normal_subgroupOf (hK := hWn) hWC
    have hTb2 : IsPGroup 2 Tb := IsPGroup.of_card (n := 6) (by rw [hTb64]; norm_num)
    have hWT : W ≤ Tb := by
      have h2 : IsPGroup 2 ↥(W ⊔ Tb) :=
        IsPGroup.to_sup_of_normal_left' hW2 hTb2 (hTbC.trans hCN)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      have hdvd : Nat.card ↥(W ⊔ Tb) ∣ Nat.card C := Subgroup.card_dvd_of_le (sup_le hWC hTbC)
      rw [hn, hC576] at hdvd
      have hn6 : n ≤ 6 := by
        by_contra hlt
        push Not at hlt
        have h7 : 2 ^ 7 ∣ 576 := (pow_dvd_pow 2 hlt).trans hdvd
        norm_num at h7
      have heq : Tb = W ⊔ Tb := Subgroup.eq_of_le_of_card_ge le_sup_right (by
        rw [hn, hTb64]
        calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
          _ = 64 := by norm_num)
      rw [heq]
      exact le_sup_left
    intro w hw
    have hy₁C : π ⟨(y₁ : G), hy₁Y⟩ ∈ C := hmemC _ y₁.2
    have hw' : (π ⟨(y₁ : G), hy₁Y⟩)⁻¹ * w * π ⟨(y₁ : G), hy₁Y⟩ ∈ W := by
      have h := (Subgroup.mem_normalizer_iff.mp (hCN (inv_mem hy₁C)) w).mp hw
      rwa [inv_inv] at h
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hWT hw)
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp (hWT hw')
    rw [Subgroup.mem_subgroupOf] at hx hx'
    by_cases hxP : (x : G) ∈ P
    · exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    exfalso
    have hrel : π ((⟨(y₁ : G), hy₁Y⟩ : ↥Y)⁻¹ * x * ⟨(y₁ : G), hy₁Y⟩) = π x' := by
      rw [hxx', map_mul, map_mul, map_inv]
    obtain ⟨n, hnN, hn⟩ := (QuotientGroup.mk'_eq_mk' N).mp hrel
    rw [Subgroup.mem_subgroupOf] at hnN
    have hn' : (y₁ : G)⁻¹ * x * y₁ * n = x' := by
      have := congrArg Subtype.val hn
      simpa using this
    have hxeq : (x : G) = y₁ * x' * (n : G)⁻¹ * (y₁ : G)⁻¹ := by
      rw [← hn']
      group
    have hx'P : (x' : G) ∉ P := by
      intro hx'P
      have h1 : (y₁ : G)⁻¹ * a₁ * y₁ ∈ Q₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy₁N₁) a₁).mp ha₁
        rwa [inv_inv] at this
      have h2 : (n : G)⁻¹ * ((y₁ : G)⁻¹ * a₁ * y₁) * n = (y₁ : G)⁻¹ * a₁ * y₁ := by
        rw [mul_assoc, ← hnc _ hnN _ (hPY (hQ₁P h1))]
        group
      have h3 : (x : G) * a₁ * (x : G)⁻¹ ∈ Q₁ := by
        have h4 := hPconj _ hx'P _ h1
        have h5 : (y₁ : G) * ((x' : G) * ((y₁ : G)⁻¹ * a₁ * y₁) * (x' : G)⁻¹) * (y₁ : G)⁻¹ ∈ Q₁ :=
          (Subgroup.mem_normalizer_iff.mp hy₁N₁ _).mp h4
        convert h5 using 1
        rw [hxeq]
        calc (y₁ : G) * x' * (n : G)⁻¹ * (y₁ : G)⁻¹ * a₁ * ((y₁ : G) * x' * (n : G)⁻¹ * (y₁ : G)⁻¹)⁻¹
            = (y₁ : G) * ((x' : G) * ((n : G)⁻¹ * ((y₁ : G)⁻¹ * a₁ * y₁) * n) * (x' : G)⁻¹) *
                (y₁ : G)⁻¹ := by group
          _ = _ := by rw [h2]
      have h6 : (x : G) * a₁ * (x : G)⁻¹ ∈ Q₁ ⊓ Q₂ :=
        Subgroup.mem_inf.mpr ⟨h3, hswap _ hx hxP a₁ ha₁⟩
      rw [hQi] at h6
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h6
      have hxz : (x : G) * z = z * x := by
        have := hT₂H hx
        rw [show (H z : Subgroup G) = Subgroup.centralizer ({z} : Set G) from rfl,
          Subgroup.mem_centralizer_singleton_iff] at this
        exact this
      have ha₁z : a₁ = z ^ k := by
        have hxzk : (x : G)⁻¹ * z ^ k * x = z ^ k := by
          rw [mul_assoc, ← (Commute.zpow_right hxz k).eq]
          group
        rw [← hxzk, hk]
        group
      exact ha₁Q₂ (by rw [ha₁z]; exact Q₂.zpow_mem hzQ₂ k)
    have hp := inv_mul_mem_of_index_two hidxT hx hx' hxP hx'P
    set p : G := (x : G)⁻¹ * x' with hp_def
    have hconj : (x : G)⁻¹ * y₁ * x = (y₁ : G) * (n : G) * p⁻¹ := by
      rw [hp_def, ← hn']
      group
    have hcent : ∀ a ∈ Q₁, ((y₁ : G) * (n : G) * p⁻¹) * a * ((y₁ : G) * (n : G) * p⁻¹)⁻¹ = a := by
      intro a ha
      rw [← hconj]
      have hb := hswap _ hx hxP a ha
      have h1 : (y₁ : G) * ((x : G) * a * (x : G)⁻¹) * (y₁ : G)⁻¹ = (x : G) * a * (x : G)⁻¹ := by
        rw [hy₁c _ hb]
        group
      calc (x : G)⁻¹ * y₁ * x * a * ((x : G)⁻¹ * y₁ * x)⁻¹ =
          (x : G)⁻¹ * ((y₁ : G) * ((x : G) * a * (x : G)⁻¹) * (y₁ : G)⁻¹) * x := by group
        _ = a := by rw [h1]; group
    have hpinv : p⁻¹ ∈ P := inv_mem hp
    rw [← hQ, CFSG.mem_sup_of_commute (fun a ha b hb => hQc a ha b hb)] at hpinv
    obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := hpinv
    have hcent' : ∀ a ∈ Q₁, ((y₁ : G) * q₁) * a * ((y₁ : G) * q₁)⁻¹ = a := by
      intro a ha
      have h1 := hcent a ha
      rw [← hq] at h1
      have hq₂a : q₂ * a = a * q₂ := (hQc a ha q₂ hq₂).symm
      have hm : q₁ * a * q₁⁻¹ ∈ Y := hPY (hQ₁P (hPconj q₁ (hQ₁P hq₁) a ha))
      have hn1 := hnc _ hnN _ hm
      calc ((y₁ : G) * q₁) * a * ((y₁ : G) * q₁)⁻¹ =
          (y₁ : G) * (n : G)⁻¹ * ((n : G) * (q₁ * a * q₁⁻¹)) * (y₁ : G)⁻¹ := by group
        _ = (y₁ : G) * (n : G)⁻¹ * ((q₁ * a * q₁⁻¹) * n) * (y₁ : G)⁻¹ := by rw [hn1]
        _ = ((y₁ : G) * (n : G) * (q₁ * q₂)) * a * ((y₁ : G) * (n : G) * (q₁ * q₂))⁻¹ := by
          rw [show ((y₁ : G) * (n : G) * (q₁ * q₂)) * a * ((y₁ : G) * (n : G) * (q₁ * q₂))⁻¹ =
            ((y₁ : G) * (n : G)) * q₁ * (q₂ * a) * q₂⁻¹ * q₁⁻¹ * ((y₁ : G) * (n : G))⁻¹ by group, hq₂a]
          have hnq : (n : G) * (q₁ * a * q₁⁻¹) = (q₁ * a * q₁⁻¹) * n := hn1
          calc (y₁ : G) * (n : G)⁻¹ * ((q₁ * a * q₁⁻¹) * n) * (y₁ : G)⁻¹ =
              (y₁ : G) * (n : G)⁻¹ * ((n : G) * (q₁ * a * q₁⁻¹)) * (y₁ : G)⁻¹ := by rw [hnq]
            _ = ((y₁ : G) * (n : G)) * q₁ * (a * q₂) * q₂⁻¹ * q₁⁻¹ * ((y₁ : G) * (n : G))⁻¹ := by
              rw [show (y₁ : G) * (n : G)⁻¹ * ((n : G) * (q₁ * a * q₁⁻¹)) * (y₁ : G)⁻¹ =
                (y₁ : G) * (q₁ * a * q₁⁻¹) * (y₁ : G)⁻¹ by group]
              rw [show ((y₁ : G) * (n : G)) * q₁ * (a * q₂) * q₂⁻¹ * q₁⁻¹ * ((y₁ : G) * (n : G))⁻¹ =
                (y₁ : G) * ((n : G) * (q₁ * a * q₁⁻¹)) * (n : G)⁻¹ * (y₁ : G)⁻¹ by group, hnq]
              group
        _ = a := h1
    exact ha₁m (centralizes_of_mul_centralizes hsqQ₁ hy₁3' hq₁ hcent' a₁ ha₁)
  have hRN : ((L1 ⊔ L2).subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidxR
  have hsup : L1 ⊔ L2 = twoThreeCore C :=
    (twoThreeCore_eq_of_card hRC hOR hON hRN hO hOmax (k := 2) (m := 1)
      (by rw [hR288, hPb32]; norm_num) (by rw [hC576, hR288]; norm_num)).symm
  have hquot : Nat.card (↥C ⧸ (twoThreeCore C).subgroupOf C) = 2 := by
    rw [← hsup, ← Subgroup.index_eq_card]
    exact hidxR
  have hQ₁Y : Q₁ ≤ Y := hQ₁P.trans hPY
  have hQ₂Y : Q₂ ≤ Y := hQ₂P.trans hPY
  have hQ8 : ∀ {Q : Subgroup G}, Nonempty (↥Q ≃* QuaternionGroup 2) → Nat.card Q = 8 :=
    fun {Q} h => by
      obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQbar8 : ∀ {Q : Subgroup G}, Nonempty (↥Q ≃* QuaternionGroup 2) → Q ≤ Y →
      Nat.card ((Q.subgroupOf Y).map π) = 8 := fun {Q} hQq hQY =>
    (hiso hQY (h2bot (IsPGroup.of_card (n := 3) (by rw [hQ8 hQq]; norm_num)))).trans (hQ8 hQq)
  have ht₀C : π ⟨(t₀ : G), ht₀Y⟩ ∈ C := hmemC _ t₀.2
  have hconjL : ∀ {Qa Qb Ba : Subgroup G}, Qa ≤ Y → Qa ≤ Ba →
      Qa.map (MulAut.conj (t₀ : G)).toMonoidHom = Qb → (Ba.subgroupOf Y).map π ≤ C →
      (((Ba.subgroupOf Y).map π).subgroupOf C).Normal →
      (Qb.subgroupOf Y).map π ≤ (Ba.subgroupOf Y).map π := by
    intro Qa Qb Ba hQaY hQaB hτ hBC hn
    have hN := Subgroup.le_normalizer_of_normal_subgroupOf (hK := hn) hBC
    rintro _ ⟨q, hq, rfl⟩
    have hqQb := Subgroup.mem_subgroupOf.mp hq
    rw [← hτ] at hqQb
    obtain ⟨q', hq', hqq'⟩ := hqQb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqq'
    have hqe : q = ⟨(t₀ : G), ht₀Y⟩ * ⟨q', hQaY hq'⟩ * (⟨(t₀ : G), ht₀Y⟩ : ↥Y)⁻¹ :=
      Subtype.ext (by rw [← hqq']; rfl)
    rw [hqe, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN ht₀C) _).mp
      ⟨⟨q', hQaY hq'⟩, Subgroup.mem_subgroupOf.mpr (hQaB hq'), rfl⟩
  have hnn1 : ¬ (L1.subgroupOf C).Normal := by
    intro hn
    have hle : (Q₂.subgroupOf Y).map π ≤ L1 ⊓ L2 :=
      le_inf (hconjL hQ₁Y le_sup_left hτ₁ hL1C hn)
        (Subgroup.map_mono fun q hq => Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hq)))
    have h1 := Subgroup.card_le_of_le hle
    rw [hQbar8 hQ₂ hQ₂Y, hinfcard] at h1
    norm_num at h1
  have hnn2 : ¬ (L2.subgroupOf C).Normal := by
    intro hn
    have hle : (Q₁.subgroupOf Y).map π ≤ L1 ⊓ L2 :=
      le_inf (Subgroup.map_mono fun q hq => Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hq)))
        (hconjL hQ₂Y le_sup_left hτ₂ hL2C hn)
    have h1 := Subgroup.card_le_of_le hle
    rw [hQbar8 hQ₁ hQ₁Y, hinfcard] at h1
    norm_num at h1
  rcases hP6I (↥Y ⧸ N) zb hzb2 ⟨L1, L2, hL1C, hL2C, ⟨eL1⟩, ⟨eL2⟩, hcommL, hinf1, hinf2, hsup,
      hnn1, hnn2, hquot⟩ with h | h
  · exact Or.inr (eq_centralizer_sup_pPrimeCore hS3 hzY hz2 h)
  · exact Or.inl h

end CaseOne

end CFSG.RankThree.GF2n.Parrott.Remarks
