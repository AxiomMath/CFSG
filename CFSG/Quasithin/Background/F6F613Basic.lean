module

public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.CharacterTheory.Burnside
import CFSG.Foundations.KCoreClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

section Normalizer

variable {D : Type*} [Group D]

theorem mem_normalizer_centralizer_of_mem_normalizer {A : Subgroup D} {g : D}
    (hA : g ∈ Subgroup.normalizer (A : Set D)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set D) : Set D) := by
  have hA' : g⁻¹ ∈ Subgroup.normalizer (A : Set D) := Subgroup.inv_mem _ hA
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx a ha
    have hga : g⁻¹ * a * g ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp hA' a).mp ha
    have h1 := hx _ hga
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * a := by group
  · intro hx a ha
    have h1 := hx (g * a * g⁻¹) ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
    calc a * x = g⁻¹ * ((g * a * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h1]
      _ = x * a := by group

end Normalizer

section NormalizerFinite

variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem mem_normalizer_zpowers_of_commute {s g : D} (h : g * s = s * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers s : Set D) := by
  have hc : g * s * g⁻¹ = s := by rw [h, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hc

theorem mem_normalizer_of_conj_mem {H : Subgroup D} {g : D} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set D) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact hg a ha
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end NormalizerFinite

section Generic

variable {D : Type*} [Group D] [Finite D]

theorem exists_involution_mem_centerOf {P N : Subgroup D} (hP : IsPGroup 2 P) (hNP : N ≤ P)
    (hPN : P ≤ Subgroup.normalizer (N : Set D)) (hN : N ≠ ⊥) :
    ∃ x ∈ N, x ∈ centerOf P ∧ x ≠ 1 ∧ x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have : (N.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hne : N.subgroupOf P ≠ ⊥ := by
    intro h0
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hNP hx⟩ : ↥P) ∈ N.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
    rw [h0, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  set M := N.subgroupOf P ⊓ Subgroup.center ↥P
  have hM1 : M ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨k, hk⟩ := (hP.to_subgroup M).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hM1 (Subgroup.eq_bot_of_card_eq M (by simpa using hk))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hyN : ((y : ↥P) : D) ∈ N := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp y.2).1
  have hyZ : (y : ↥P) ∈ Subgroup.center ↥P := (Subgroup.mem_inf.mp y.2).2
  have hord : orderOf ((y : ↥P) : D) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  refine ⟨_, hyN, Subgroup.mem_inf.mpr ⟨(y : ↥P).2, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hyZ ⟨g, hg⟩
    exact congrArg Subtype.val this
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · rw [← hord]
    exact pow_orderOf_eq_one _

theorem card_le_two_mul_of_inv_mul_mem {H K : Subgroup D}
    (h2 : ∀ x ∈ K, ∀ y ∈ K, x ∉ H → y ∉ H → x⁻¹ * y ∈ H) :
    Nat.card K ≤ 2 * Nat.card H := by
  classical
  by_cases hex : ∃ t ∈ K, t ∉ H
  · obtain ⟨t, htK, htH⟩ := hex
    let f : ↥K → ↥H ⊕ ↥H := fun x =>
      if hx : (x : D) ∈ H then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨t⁻¹ * x, h2 t htK x x.2 htH hx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : D) ∈ H <;> by_cases hy : (y : D) ∈ H <;>
        simp only [f, hx, hy, dite_true, dite_false, reduceCtorEq, Sum.inl.injEq,
          Sum.inr.injEq, Subtype.mk.injEq, mul_right_inj] at hxy
      · exact Subtype.ext hxy
      · exact Subtype.ext hxy
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega
  · push Not at hex
    have := Subgroup.card_le_of_le (show K ≤ H from hex)
    omega

omit [Finite D] in
theorem conj_mul_conj_comm {x y : D} (g : D) (hxy : x * y = y * x) :
    (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) := by
  calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hxy]
    _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group

theorem eq_one_or_eq_of_commute_of_card_eq_four {P V : Subgroup D} (hV : Nat.card V = 4)
    (hself : ∀ y ∈ P, (∀ v ∈ V, y * v = v * y) → y ∈ V) {z : D} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hzc : ∀ y ∈ P, y * z = z * y) {x : D} (hxP : x ∈ P) (hxV : x ∉ V) {v : D} (hvV : v ∈ V)
    (hxv : x * v = v * x) : v = 1 ∨ v = z := by
  by_contra hne
  push Not at hne
  apply hxV
  refine hself x hxP fun w hw => ?_
  set C := V ⊓ Subgroup.centralizer ({x} : Set D)
  have hzC : z ∈ C :=
    Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hxP).symm⟩
  have hvC : v ∈ C :=
    Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_singleton_iff.mpr hxv.symm⟩
  have hCV : C ≤ V := inf_le_left
  have hdvd : Nat.card C ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV]
    exact Subgroup.card_dvd_of_le hCV
  obtain ⟨m, hm, hmC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hC4 : Nat.card C = 4 := by
    interval_cases m
    · exfalso
      have h0 := Subgroup.eq_bot_of_card_eq C (by simpa using hmC)
      rw [h0, Subgroup.mem_bot] at hzC
      exact hz1 hzC
    · exact absurd (eq_of_card_eq_two (by simpa using hmC) hvC hzC hne.1 hz1) hne.2
    · simpa using hmC
  have hCeq : C = V := Subgroup.eq_of_le_of_card_ge hCV (by rw [hV, hC4])
  have hwC : w ∈ C := hCeq ▸ hw
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwC).2).symm

theorem mem_normalizer_of_card_eq_eight {P V : Subgroup D} (hVP : V ≤ P) (hP : Nat.card P = 8)
    (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVc : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u)
    (hself : ∀ y ∈ P, (∀ v ∈ V, y * v = v * y) → y ∈ V) {d : D}
    (hdP : d ∈ Subgroup.normalizer (P : Set D)) (hd3 : d ^ 3 = 1) :
    d ∈ Subgroup.normalizer (V : Set D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have : Nontrivial ↥P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP]
    norm_num
  have := hP2.center_nontrivial
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  set z : D := (z₀ : D)
  have hzc : ∀ y ∈ P, y * z = z * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨y, hy⟩)
  have hz1 : z ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
  have hzV : z ∈ V := hself z z₀.2 fun v hv => (hzc v (hVP hv)).symm
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set D), ∀ y ∈ P, g * y * g⁻¹ ∈ P :=
    fun g hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hdP' : d⁻¹ ∈ Subgroup.normalizer (P : Set D) := Subgroup.inv_mem _ hdP
  have hidx : (V.subgroupOf P).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card V P
    rw [inf_eq_left.mpr hVP, hV, hP] at h1
    change V.relIndex P = 2
    omega
  have key : ∀ a ∈ V, d * a * d⁻¹ ∈ V := by
    intro a ha
    by_cases hac : ∀ y ∈ P, y * a = a * y
    · refine hself _ (hconj d hdP a (hVP ha)) fun v hv => ?_
      have h1 := hac (d⁻¹ * v * d⁻¹⁻¹) (hconj d⁻¹ hdP' v (hVP hv))
      rw [inv_inv] at h1
      calc d * a * d⁻¹ * v = d * (a * (d⁻¹ * v * d)) * d⁻¹ := by group
        _ = d * ((d⁻¹ * v * d) * a) * d⁻¹ := by rw [h1]
        _ = v * (d * a * d⁻¹) := by group
    · push Not at hac
      obtain ⟨y₀, hy₀P, hy₀⟩ := hac
      have ha1 : a ≠ 1 := by
        rintro rfl
        simp at hy₀
      have haz : a ≠ z := by
        rintro rfl
        exact hy₀ (hzc y₀ hy₀P)
      set b := d * a * d⁻¹ with hb
      set e := d * b * d⁻¹ with he
      have hda : d⁻¹ * b * d⁻¹⁻¹ = a := by rw [hb]; group
      have hdb : d⁻¹ * e * d⁻¹⁻¹ = b := by rw [he]; group
      have hea : d * e * d⁻¹ = a := by
        rw [he, hb]
        calc d * (d * (d * a * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * a * (d * d * d)⁻¹ := by group
          _ = a := by rw [← pow_three', hd3]; group
      by_contra hbV
      have hbP : b ∈ P := hconj d hdP a (hVP ha)
      have heP : e ∈ P := hconj d hdP b hbP
      have h1 : ¬ b * a = a * b := fun h => by
        rcases eq_one_or_eq_of_commute_of_card_eq_four hV hself hzV hz1 hzc hbP hbV ha h with
          h' | h'
        · exact ha1 h'
        · exact haz h'
      have h2 : ¬ e * b = b * e := fun h => h1 (by
        have := conj_mul_conj_comm d⁻¹ h
        rwa [hda, hdb] at this)
      have heV : e ∉ V := fun heV => h1 (by
        have := conj_mul_conj_comm d (hVc a ha e heV)
        rwa [hea, ← hb] at this)
      have hb2 : b ^ 2 = 1 := by rw [hb, conj_pow, hV2 a ha]; group
      have he2 : e ^ 2 = 1 := by rw [he, conj_pow, hb2]; group
      have hu : b⁻¹ * e ∈ V := by
        have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨b⁻¹, P.inv_mem hbP⟩)
          (b := ⟨e, heP⟩)).mpr ⟨fun h => absurd (by
            have := V.inv_mem (Subgroup.mem_subgroupOf.mp h)
            simpa using this) hbV,
            fun h => absurd (Subgroup.mem_subgroupOf.mp h) heV⟩
        simpa using Subgroup.mem_subgroupOf.mp hm
      set u := b⁻¹ * e with hudef
      have he' : e = b * u := by rw [hudef]; group
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
      have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 u hu)
      have hbu : b * u = u * b := by
        have h3 : (b * u) * (b * u) = 1 := by rw [← pow_two, ← he']; exact he2
        calc b * u = (b * u)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
          _ = u * b := by rw [mul_inv_rev, hbinv, huinv]
      exact h2 (by rw [he', mul_assoc, ← hbu, ← mul_assoc])
  exact mem_normalizer_of_conj_mem key

end Generic

section SQTK

theorem isSolvable_of_card_eq_two_pow_mul_three {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (h : Nat.card Y = 2 ^ n * 3) : Group.IsSolvable Y := by
  let _ : Fintype Y := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := n) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h, pow_one])

theorem isKGroupCat_of_isSolvable {Y : Type} [Group Y] [Finite Y] (hY : Group.IsSolvable Y) :
    CFSG.SectionRank.IsKGroupCat Y :=
  CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple hY

theorem stronglyQuasithin_of_card_eq_two_pow_mul_three {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : Nat.card Y = 2 ^ n * 3) : SQTKTauCeti.StronglyQuasithin Y := by
  rw [sqt_iff]
  intro p hp hp2
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup Y)
  have hdvd : p ^ Open.pRank p (⊤ : Subgroup Y) ∣ 2 ^ n * 3 := by
    rw [← hE, ← h]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (p ^ Open.pRank p (⊤ : Subgroup Y)) (2 ^ n) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h3 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_left hdvd)
  have := Nat.lt_pow_self (n := Open.pRank p (⊤ : Subgroup Y)) hp.one_lt
  omega

theorem isSQTKIn_of_card_eq_two_pow_mul_three {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {n : ℕ} (h : Nat.card Y = 2 ^ n * 3) : IsSQTKIn Y :=
  ⟨stronglyQuasithin_of_card_eq_two_pow_mul_three h,
    isKGroupCat_of_isSolvable (isSolvable_of_card_eq_two_pow_mul_three h)⟩

end SQTK

section Block

variable {G : Type} [Group G]

theorem isAltType_three_of_isChi0Block_of_isSolvable {X L : Subgroup G} (hL : IsChi0Block X L)
    (hX : Group.IsSolvable ↥X) : IsAltType L 3 := by
  have hLX : L ≤ X := hL.1.2.1
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX)
  have hcard := C1Pack.natCard_pCore_quotient_eq_three_of_isShort2 hL.1.1 inferInstance
  rcases hL.2 with ⟨n, hn, F, hFf, hFfin, hcardF, α, hα, hker, -⟩ | h3 | ⟨α, hα, hker, -⟩
  · exfalso
    let _ := hFf
    let _ := hFfin
    have hchar : (2 : F) = 0 := by
      have h2 : ringChar F = 2 := by
        refine FiniteField.even_card_iff_char_two.mpr ?_
        rw [hcardF]
        exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have : CharP F 2 := ringChar.eq_iff.mp h2
      simpa using CharP.cast_eq_zero F 2
    let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hg1 : g ≠ 1 := by
      intro h
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [g] at this
    have hgg : g * g = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
      rw [one_add_one_eq_two]
      exact hchar
    exact C1Pack.false_of_surjective_of_involution α hα hker hcard hg1 hgg
  · exact h3
  · exfalso
    have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have h1 : Nat.card (alternatingGroup (Fin 5)) = 3 := by
      rw [← Nat.card_congr e.toEquiv]
      exact hcard
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h1
    have h5 : Nat.factorial 5 = 120 := by decide
    omega

end Block

end F6

end CFSG.Quasithin
