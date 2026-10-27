module

public import CFSG.RankThree.GF2n.Parrott.CentralizerImage

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private noncomputable def qHT₁ {T₁ : Subgroup G} (hH : T₁ ≤ H z) : ↥T₁ →* QA45.originalSubgroup :=
  (qH D).comp (Subgroup.inclusion hH)

omit [Finite G]
  in
private theorem range_qHT₁ {T₁ : Subgroup G} (hH : T₁ ≤ H z) :
    (qHT₁ D hH).range = (T₁.subgroupOf (H z)).map (qH D) := by
  classical
  ext y
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : G), hH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩

private theorem ker_qHT₁ {T₁ : Subgroup G} (hH : T₁ ≤ H z) :
    (qHT₁ D hH).ker = (J z).subgroupOf T₁ := by
  ext x
  show qH D (Subgroup.inclusion hH x) = 1 ↔ (x : G) ∈ J z
  constructor
  · intro hx
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D (Subgroup.inclusion hH x)).mpr hx)
  · intro hx
    exact (J_mem_iff D (Subgroup.inclusion hH x)).mp (Subgroup.mem_subgroupOf.mpr hx)

private theorem map_subgroupOf_qH_le_centralizer {T₁ : Subgroup G}
    (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    (T₁.subgroupOf (H z)).map (qH D) ≤
      Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup) := by
  rw [← map_centralizer_sigma1Nine_eq (D := D) h]
  refine Subgroup.map_mono ?_
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hT₁.le hy).2)

omit [Finite G]
  hN in
private theorem inf_centralizer_eq_map_centralizer_subtype (y : H z) :
    H z ⊓ Subgroup.centralizer ({(y : G)} : Set G) =
      (Subgroup.centralizer ({y} : Set ↥(H z))).map (H z).subtype := by
  ext g
  constructor
  · rintro ⟨hgH, hgC⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    simpa using Subgroup.mem_centralizer_singleton_iff.mp hgC
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))⟩

private theorem card_sylow_sigma1Nine {T₁ : Subgroup G}
    (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card T₁ = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card ↥(H z ⊓ centralizer
      ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) = 10368 := by
    rw [inf_centralizer_eq_map_centralizer_subtype (sigma1Nine (z := z) D),
      Subgroup.card_map_of_injective (H z).subtype_injective]
    exact card_centralizer_sigma1Nine (D := D) h
  have hfac : Nat.factorization 10368 2 = 7 := by
    have h10368 : 10368 = 2 ^ 7 * 81 := by norm_num
    rw [h10368, Nat.factorization_mul (a := (2 : ℕ) ^ 7) (b := 81) (by norm_num) (by norm_num)]
    rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (81 : ℕ)), add_zero]
  have hcard := hT₁.card_eq
  rw [hK, hfac] at hcard
  simpa using hcard

private theorem card_subgroupOf_J_le_sixteen {T₁ : Subgroup G}
    (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card ↥((J z).subgroupOf T₁) ≤ 16 := by
  classical
  have hinf : (J z) ⊓ T₁ ≤
      Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
    fun x hx => (hT₁.le (Subgroup.mem_inf.mp hx).2).2
  have hsub : ((J z) ⊓ Subgroup.centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)).subgroupOf (J z) =
      centralizerJ (sigma1Nine (z := z) D) := by
    rw [inf_comm]
    rfl
  calc Nat.card ↥((J z).subgroupOf T₁)
      = Nat.card ↥((J z) ⊓ T₁) := by
        rw [← Subgroup.inf_subgroupOf_right (J z) T₁]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_right : (J z) ⊓ T₁ ≤ T₁)).toEquiv
    _ ≤ Nat.card ↥((J z) ⊓
          Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) := by
        refine Nat.card_le_card_of_injective
          (fun x : ↥((J z) ⊓ T₁) =>
            (⟨x.1, Subgroup.mem_inf.mpr
              ⟨(Subgroup.mem_inf.mp x.2).1, hinf x.2⟩⟩ :
              ↥((J z) ⊓ Subgroup.centralizer
                ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))) ?_
        intro a b hab
        have hab' : (a : G) = (b : G) := congrArg (fun t : ↥((J z) ⊓
          Subgroup.centralizer
            ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) => (t : G)) hab
        exact Subtype.ext hab'
    _ = Nat.card (centralizerJ (sigma1Nine (z := z) D)) := by
        have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : (J z) ⊓ Subgroup.centralizer
            ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) ≤ J z)).toEquiv
        rw [← hsub]
        exact hcard.symm
    _ = 16 := card_centralizerJ_sigma1Nine h D

private theorem card_map_subgroupOf_qH_le_eight {T₁ : Subgroup G}
    (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card ((T₁.subgroupOf (H z)).map (qH D)) ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : T₁ ≤ H z := fun x hx => (hT₁.le hx).1
  have hA2 : IsPGroup 2 ↥((T₁.subgroupOf (H z)).map (qH D)) :=
    (hT₁.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hH).symm).map (qH D)
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hle : (T₁.subgroupOf (H z)).map (qH D) ≤
      Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup) :=
    map_subgroupOf_qH_le_centralizer (D := D) h hT₁
  have hdvd : 2 ^ k ∣ 648 := by
    rw [← hk]
    have h := Subgroup.card_subgroup_dvd_card
      (s := ((T₁.subgroupOf (H z)).map (qH D)).subgroupOf
        (Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup)))
    rw [card_centralizer_sigma1_QA45] at h
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  have hcop : (2 ^ k).Coprime 81 := Nat.Coprime.pow_left k (by norm_num)
  have hk3 : k ≤ 3 := by
    have h81 : (648 : ℕ) = 81 * 2 ^ 3 := by norm_num
    rw [h81] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
  calc Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) = 2 ^ k := hk
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

private theorem card_map_subgroupOf_qH_eq_eight {T₁ : Subgroup G}
    (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card ((T₁.subgroupOf (H z)).map (qH D)) = 8 := by
  classical
  have hH : T₁ ≤ H z := fun x hx => (hT₁.le hx).1
  have hmul := Subgroup.card_ker_mul_card_range (qHT₁ D hH)
  rw [ker_qHT₁ (D := D) hH, range_qHT₁ (D := D) hH] at hmul
  have hT1 : Nat.card ↥T₁ = 128 := card_sylow_sigma1Nine (D := D) h hT₁
  rw [hT1] at hmul
  have hkerle : Nat.card ↥((J z).subgroupOf T₁) ≤ 16 :=
    card_subgroupOf_J_le_sixteen (D := D) h hT₁
  have hrangele : Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) ≤ 8 :=
    card_map_subgroupOf_qH_le_eight (D := D) h hT₁
  have hge : 8 ≤ Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) := by
    have h16 : 128 ≤ 16 * Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) := by
      calc (128 : ℕ)
          = Nat.card ↥((J z).subgroupOf T₁) *
              Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) := hmul.symm
        _ ≤ 16 * Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) :=
            Nat.mul_le_mul_right _ hkerle
    omega
  omega

theorem map_qH_le_centralizer_and_card_eq_eight_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    (T₁.subgroupOf (H z)).map (qH D) ≤
        Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup) ∧
      Nat.card ((T₁.subgroupOf (H z)).map (qH D)) = 8 :=
  ⟨map_subgroupOf_qH_le_centralizer (D := D) h hT₁,
    card_map_subgroupOf_qH_eq_eight (D := D) h hT₁⟩

theorem exists_surjective_ker_eq_of_isSylowOf_centralizer_sigma1Nine {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    {Q : Type*} [Group Q] (e : ↥((T₁.subgroupOf (H z)).map (qH D)) ≃* Q) :
    ∃ π : ↥T₁ →* Q, Function.Surjective π ∧ π.ker = (J z).subgroupOf T₁ := by
  classical
  have hH : T₁ ≤ H z := fun x hx => (hT₁.le hx).1
  have hmem : ∀ x : ↥T₁, qHT₁ D hH x ∈ (T₁.subgroupOf (H z)).map (qH D) := by
    intro x
    rw [← range_qHT₁ (D := D) hH]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let f' : ↥T₁ →* ↥((T₁.subgroupOf (H z)).map (qH D)) :=
    MonoidHom.codRestrict (qHT₁ D hH) ((T₁.subgroupOf (H z)).map (qH D)) hmem
  have hf'_surj : Function.Surjective f' := by
    intro y
    have hy : (y : QA45.originalSubgroup) ∈ (qHT₁ D hH).range := by
      rw [range_qHT₁ (D := D) hH]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨e.toMonoidHom.comp f', ?_, ?_⟩
  · simpa using e.surjective.comp hf'_surj
  · rw [MonoidHom.ker_comp_of_injective f' e.toMonoidHom e.injective]
    have hker' : f'.ker = (qHT₁ D hH).ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    rw [hker', ker_qHT₁ (D := D) hH]

theorem exists_lift_normalizes_of_isSylowOf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z)
    {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    {r : QA45.originalSubgroup}
    (hr : r ∈ Subgroup.centralizer ({⟨sigma1, sigma1_mem_A⟩} : Set QA45.originalSubgroup))
    (hr3 : r ^ 3 = 1)
    (hrA : ∀ x ∈ (T₁.subgroupOf (H z)).map (qH D),
      r * x * r⁻¹ ∈ (T₁.subgroupOf (H z)).map (qH D))
    (hrx : ∃ x ∈ (T₁.subgroupOf (H z)).map (qH D), r * x * r⁻¹ ≠ x) :
    ∃ ρ : G, ρ ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) ∧
      (∀ g ∈ T₁, ρ * g * ρ⁻¹ ∈ T₁) ∧ ρ ^ 3 ∈ J z ∧
        ∃ g ∈ T₁, ρ * g * ρ⁻¹ * g⁻¹ ∉ J z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardA' : Nat.card ↥((T₁.subgroupOf (H z)).map (qH D)) = 8 :=
    card_map_subgroupOf_qH_eq_eight (D := D) h hT₁
  have hr' : r ∈ (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (qH D) := by
    rw [map_centralizer_sigma1Nine_eq (D := D) h]
    exact hr
  obtain ⟨ρ₀, hρ₀, hqρ⟩ := Subgroup.mem_map.mp hr'
  have hρ₀C : (ρ₀ : G) ∈
      Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hρ₀)
  let M : Subgroup G :=
    (((T₁.subgroupOf (H z)).map (qH D)).comap (qH D) ⊓
      Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (H z).subtype
  have hTM : T₁ ≤ M := by
    intro g hg
    have hgH : g ∈ H z := (hT₁.le hg).1
    have hgC : g ∈ Subgroup.centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := (hT₁.le hg).2
    refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  have hMK : M ≤ H z ⊓
      Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
  have hM2 : IsPGroup 2 ↥M := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨hyA, -⟩ := Subgroup.mem_inf.mp hy
    have hqA : qH D y ∈ (T₁.subgroupOf (H z)).map (qH D) := Subgroup.mem_comap.mp hyA
    have h8 : (qH D y) ^ 8 = 1 := by
      have h := pow_card_eq_one'
        (x := (⟨qH D y, hqA⟩ : ↥((T₁.subgroupOf (H z)).map (qH D))))
      rw [hcardA'] at h
      simpa using congrArg Subtype.val h
    have hx8J : (x : G) ^ 8 ∈ J z := by
      have hy8 : y ^ 8 ∈ (J z).subgroupOf (H z) := by
        rw [J_mem_iff D, map_pow, h8]
      have hcoe : ((y ^ 8 : ↥(H z)) : G) = (x : G) ^ 8 := by
        rw [Subgroup.coe_pow]
        exact congrArg (fun t : G => t ^ 8) hyx
      rw [← hcoe]
      exact Subgroup.mem_subgroupOf.mp hy8
    obtain ⟨k, hk⟩ := isPGroup_J h (⟨(x : G) ^ 8, hx8J⟩ : ↥(J z))
    have hk' : ((x : G) ^ 8) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hexp : (2 : ℕ) ^ (k + 3) = 8 * 2 ^ k := by
      rw [pow_add]
      norm_num
      ring
    refine ⟨k + 3, Subtype.ext ?_⟩
    have hmain : (x : G) ^ 2 ^ (k + 3) = 1 := by
      rw [hexp, pow_mul]
      exact hk'
    simpa using hmain
  have hMT : M = T₁ := hT₁.eq_of_le hTM hMK hM2
  refine ⟨(ρ₀ : G), ⟨ρ₀.2, hρ₀C⟩, ?_, ?_, ?_⟩
  · intro g hg
    have hgH : g ∈ H z := (hT₁.le hg).1
    have hgC : g ∈ Subgroup.centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := (hT₁.le hg).2
    have hconjH : (ρ₀ : G) * g * (ρ₀ : G)⁻¹ ∈ H z :=
      (H z).mul_mem ((H z).mul_mem ρ₀.2 hgH) ((H z).inv_mem ρ₀.2)
    have hconjC : (ρ₀ : G) * g * (ρ₀ : G)⁻¹ ∈
        Subgroup.centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
      (Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).mul_mem hρ₀C hgC) ((Subgroup.centralizer _).inv_mem hρ₀C)
    have hmemM : (ρ₀ : G) * g * (ρ₀ : G)⁻¹ ∈ M := by
      refine Subgroup.mem_map.mpr ⟨⟨_, hconjH⟩, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hqg : qH D ⟨g, hgH⟩ ∈ (T₁.subgroupOf (H z)).map (qH D) :=
          Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
        have hq : qH D (⟨(ρ₀ : G) * g * (ρ₀ : G)⁻¹, hconjH⟩ : ↥(H z)) =
            r * qH D ⟨g, hgH⟩ * r⁻¹ := by
          rw [show (⟨(ρ₀ : G) * g * (ρ₀ : G)⁻¹, hconjH⟩ : ↥(H z)) =
              ρ₀ * ⟨g, hgH⟩ * ρ₀⁻¹ from Subtype.ext rfl,
            map_mul, map_mul, map_inv, hqρ]
        rw [hq]
        exact hrA _ hqg
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hconjC)
    rw [← hMT]
    exact hmemM
  · have hq3 : qH D (ρ₀ ^ 3) = 1 := by
      rw [map_pow, hqρ, hr3]
    have hmem : ρ₀ ^ 3 ∈ (J z).subgroupOf (H z) := (J_mem_iff D (ρ₀ ^ 3)).mpr hq3
    simpa using Subgroup.mem_subgroupOf.mp hmem
  · obtain ⟨x, hxA, hxne⟩ := hrx
    obtain ⟨y, hy, hqy⟩ := Subgroup.mem_map.mp hxA
    have hyT : (y : G) ∈ T₁ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨(y : G), hyT, ?_⟩
    intro hmem
    have hyH : (y : G) ∈ H z := (hT₁.le hyT).1
    have hHprod : (ρ₀ : G) * (y : G) * (ρ₀ : G)⁻¹ * (y : G)⁻¹ ∈ H z :=
      (H z).mul_mem
        ((H z).mul_mem ((H z).mul_mem ρ₀.2 hyH) ((H z).inv_mem ρ₀.2)) ((H z).inv_mem hyH)
    let w : ↥(H z) := ⟨(ρ₀ : G) * (y : G) * (ρ₀ : G)⁻¹ * (y : G)⁻¹, hHprod⟩
    have hq1 : qH D w = 1 :=
      (J_mem_iff D w).mp (Subgroup.mem_subgroupOf.mpr (by simpa using hmem))
    have hqeq : qH D w = (r * x * r⁻¹) * x⁻¹ := by
      have hw : w = ρ₀ * y * ρ₀⁻¹ * y⁻¹ := Subtype.ext rfl
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, hqρ, hqy]
    have hx1 : (r * x * r⁻¹) * x⁻¹ = 1 := by
      rw [← hqeq]
      exact hq1
    have hrx' : r * x * r⁻¹ = x := by
      have h := congrArg (fun t => t * x) hx1
      simpa [mul_assoc] using h
    exact hxne hrx'

end CFSG.RankThree.GF2n.Parrott
