module

public import CFSG.RankThree.PartTwo.Sec10.HWNormalizes
public import CFSG.RankThree.PartTwo.Sec9.Item97
public import CFSG.RankThree.PartTwo.KFacts.K72Invert
public import CFSG.RankThree.PartTwo.Sec11.LStar

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter

@[expose] def LStarInverting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹

@[expose] def LStarInvertingL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      (∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)) →
      ∀ d : G, A ⊓ L = Subgroup.zpowers d →
        ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹

theorem lStarInverting_of (h97 : Sec9.Item97) (hI3 : LStarInvertingL3) : LStarInverting := by
  intro G _ _ A c L a R Y h d hdL
  have key : ∀ {K : Type} [Field K] [Finite K], (3 : K) ≠ 0 →
      (L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
    intro K _ _ h3K e
    have hAe := h.mem_partTwoF.1
    obtain ⟨h3, hcl⟩ := h97 G A c L a R h.toHyp91
    have hA' := hcl d hdL
    have hdAL : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    have hd3 : orderOf d = 3 := by rw [← Nat.card_zpowers, ← hdL, h3]
    have hd1 : d ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hd3
      exact absurd hd3 (by norm_num)
    have hout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
    have ha := KFacts.inducesKind_field_of_pow_three L (hAe.2 a h.a_mem) hout e
    have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      rw [h.sectionCentralizer_eq]
      exact Subgroup.mem_zpowers c
    exact KFacts.exists_inverting_of_inducesKindPSL2 h3K hAe h.mem_A h.a_mem hdAL.1 hA' hsc.2
      hdAL.2 hd1 e ha
  rcases h.isList1016 with ⟨p, e, _, hp, -, ⟨eq⟩⟩ | ⟨n, -, ⟨eq⟩⟩ | hL
  · exact key (KFacts.three_ne_zero_galoisField (by omega) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · exact key (KFacts.three_ne_zero_galoisField (by norm_num) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · exact hI3 G A c L a R Y h hL d hdL

section Points

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_map_subtype {H X : Subgroup G} {B : Subgroup X}
    (hB : ∀ φ ∈ Sec4.autIn H X, B.map φ.toMonoidHom = B) :
    H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer ((B.map X.subtype : Subgroup G) :
      Set G) := by
  rintro g ⟨hgH, hgN⟩
  set φ := X.normalizerMonoidHom ⟨g, hgN⟩ with hφ
  have hφ' : φ ∈ Sec4.autIn H X := Sec4.mem_autIn_iff.mpr ⟨g, hgN, hgH, rfl⟩
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hcomp : (MulAut.conj g).toMonoidHom.comp X.subtype = X.subtype.comp φ.toMonoidHom := by
    ext x
    exact (Sec4.normalizerMonoidHom_apply_coe hgN x).symm
  show (B.map X.subtype).map (MulAut.conj g).toMonoidHom = B.map X.subtype
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hB φ hφ']

omit [Finite G] in
theorem mul_mul_mul_inv_of_commute {x y : G} (h : x * y = y * x) :
    x * y * (x * y⁻¹) = x ^ 2 ∧ x * y * (x * y⁻¹)⁻¹ = y ^ 2 := by
  constructor
  · calc x * y * (x * y⁻¹) = x * (y * x) * y⁻¹ := by group
      _ = x * (x * y) * y⁻¹ := by rw [← h]
      _ = x ^ 2 := by rw [pow_two]; group
  · calc x * y * (x * y⁻¹)⁻¹ = (x * y) * y * x⁻¹ := by group
      _ = (y * x) * y * x⁻¹ := by rw [h]
      _ = y * (x * y) * x⁻¹ := by group
      _ = y * (y * x) * x⁻¹ := by rw [h]
      _ = y ^ 2 := by rw [pow_two]; group

theorem eq_zpowers_or_eq_zpowers_of_le_normalizer (h97 : Sec9.Item97)
    (hT : LStarTransvection) (hI : LStarInverting) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {D : Subgroup G} (hDA : D ≤ A) (hD3 : Nat.card D = 3)
    (hDN : L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    D = Subgroup.zpowers c ∨ D = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hcA := h.mem_A
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hdA := hdAL.1
  have hd3 : orderOf d = 3 := by rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hA := (h97 G A c L a R h.toHyp91).2 d hdL
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
    rw [h.card_eq] at h1
    omega
  obtain ⟨l₀, ⟨hl₀L, hl₀W⟩, ⟨k, hk⟩, x₀, hx₀A, hx₀⟩ := hT G A c L a R Y h
  have hl₀c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₀L hl₀W
  have hl₀d : l₀ * d = d * l₀ := by
    refine Sec12.commute_of_conj_mem_zpowers hd3 ?_ hk
    rw [← hdL]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hl₀W d).mp hdA,
      L.mul_mem (L.mul_mem hl₀L hdAL.2) (L.inv_mem hl₀L)⟩
  set C := A ⊓ Subgroup.centralizer ({l₀} : Set G) with hC
  have hcdC : Subgroup.closure ({c, d} : Set G) ≤ C := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    · refine ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc c * l₀ = l₀ * c * l₀⁻¹ * l₀ := by rw [hl₀c]
        _ = l₀ * c := by group
    · exact ⟨hdA, Subgroup.mem_centralizer_singleton_iff.mpr hl₀d.symm⟩
  have hCA : C ≠ A := by
    intro hCA
    apply hx₀
    have h1 : x₀ ∈ C := by rw [hCA]; exact hx₀A
    rw [← Subgroup.mem_centralizer_singleton_iff.mp h1.2, mul_inv_cancel_right]
  have h9 : 9 ≤ Nat.card (Subgroup.closure ({c, d} : Set G)) := by
    have hcd : Subgroup.zpowers c ≤ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := hcdC.trans inf_le_left
    have h1 := Sec9.three_mul_card_le_of_le_of_ne hA3 hcdA hcd (fun h1 => hdc (by
      rw [h1]
      exact Subgroup.subset_closure (by simp)))
    rw [Nat.card_zpowers, hc3] at h1
    omega
  have hC9 : Nat.card C ≤ 9 := by
    have h1 : 3 * Nat.card C ≤ Nat.card A :=
      Sec9.three_mul_card_le_of_le_of_ne hA3 le_rfl inf_le_left hCA
    rw [h.card_eq] at h1
    omega
  have hCeq : Subgroup.closure ({c, d} : Set G) = C :=
    Subgroup.eq_of_le_of_card_ge hcdC (by omega)
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hD3]; norm_num)
  obtain ⟨⟨z, hzD⟩, hz1⟩ := exists_ne (1 : D)
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hz3 : orderOf z = 3 := orderOf_eq_prime (hexp z (hDA hzD)) hz1'
  have hDz : D = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzD)
      (by rw [hD3, Nat.card_zpowers, hz3])).symm
  have hzl₀ : l₀ * z = z * l₀ := by
    refine Sec12.commute_of_conj_mem_zpowers hz3 ?_ hk
    rw [← hDz]
    exact (Subgroup.mem_normalizer_iff.mp (hDN ⟨hl₀L, hl₀W⟩) z).mp hzD
  have hzcd : z ∈ Subgroup.closure ({c, d} : Set G) := by
    rw [hCeq]
    exact ⟨hDA hzD, Subgroup.mem_centralizer_singleton_iff.mpr hzl₀.symm⟩
  obtain ⟨i, j, hi, hj, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
    (hcomm c hcA d hdA) (hexp c hcA) (hexp d hdA) hzcd
  obtain ⟨l₁, ⟨hl₁L, hl₁W⟩, hl₁d⟩ := hI G A c L a R Y h d hdL
  have hl₁c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₁L hl₁W
  have hl₁z : l₁ * (c ^ i * d ^ j) * l₁⁻¹ = c ^ i * d⁻¹ ^ j := by
    have e1 : l₁ * (c ^ i * d ^ j) * l₁⁻¹ = (l₁ * c * l₁⁻¹) ^ i * (l₁ * d * l₁⁻¹) ^ j := by
      rw [conj_pow, conj_pow]
      group
    rw [e1, hl₁c, hl₁d]
  have hlz : c ^ i * (d ^ j)⁻¹ ∈ D := by
    rw [← inv_pow, ← hl₁z]
    exact (Subgroup.mem_normalizer_iff.mp (hDN ⟨hl₁L, hl₁W⟩) _).mp hzD
  obtain ⟨e1, e2⟩ := mul_mul_mul_inv_of_commute ((Commute.pow_pow (hcomm c hcA d hdA) i j).eq)
  have hw : (c ^ i) ^ 2 ∈ D := by
    rw [← e1]
    exact D.mul_mem hzD hlz
  have hw' : (d ^ j) ^ 2 ∈ D := by
    rw [← e2]
    exact D.mul_mem hzD (D.inv_mem hlz)
  have hD_of : ∀ x ∈ D, x ≠ 1 → D = Subgroup.zpowers x := fun x hx hx1 =>
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [hD3, Nat.card_zpowers, orderOf_eq_prime (hexp x (hDA hx)) hx1])).symm
  have hgen : ∀ {u : G}, u ∈ A → orderOf u = 3 → ∀ x ∈ Subgroup.zpowers u, x ∈ A → x ≠ 1 →
      Subgroup.zpowers x = Subgroup.zpowers u := fun {u} _ hu3 x hx hxA hx1 =>
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hu3, orderOf_eq_prime (hexp x hxA) hx1])
  have hsq : ∀ x ∈ A, x ^ 2 = 1 → x = 1 := fun x hx hx2 => by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hexp x hx, hx2]; group
  by_cases h1 : (c ^ i) ^ 2 = 1
  · by_cases h2 : (d ^ j) ^ 2 = 1
    · exfalso
      apply hz1'
      rw [hsq _ (A.pow_mem hcA i) h1, hsq _ (A.pow_mem hdA j) h2, one_mul]
    · right
      rw [hD_of _ hw' h2]
      exact hgen hdA hd3 _ (Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j) 2)
        (A.pow_mem (A.pow_mem hdA j) 2) h2
  · left
    rw [hD_of _ hw h1]
    exact hgen hcA hc3 _ (Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i) 2)
      (A.pow_mem (A.pow_mem hcA i) 2) h1

theorem exists_normal_three_of (h115 : Item115) (h116 : Item116) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card D = 3 ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have h27 := h.card_eq
  have hred := h115 G A c L a R Y h
  simp only [Sec21.IsIrreducibleOn, not_forall, not_or, exists_prop] at hred
  obtain ⟨B, hBinv, hB1, hBtop⟩ := hred
  set B' := B.map A.subtype with hB'
  have hB'A : B' ≤ A := Subgroup.map_subtype_le B
  have hB'N : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B' : Set G) :=
    fun g hg => le_normalizer_map_subtype hBinv ⟨hg, hg⟩
  have hcardB' : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective A.subtype_injective
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hA3.to_le hB'A)
  have hm3 : m ≤ 3 := by
    have h1 := Subgroup.card_dvd_of_le hB'A
    rw [hm, h27, show (27 : ℕ) = 3 ^ 3 by norm_num] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hB1
    rw [← Subgroup.card_eq_one, ← hcardB', hm, pow_zero]
  have hm3' : m ≠ 3 := by
    rintro rfl
    apply hBtop
    rw [← Subgroup.card_eq_iff_eq_top, ← hcardB', hm, h27]
    norm_num
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  ·
    exact ⟨B', hB'A, by rw [hm]; norm_num, hB'N⟩
  ·
    have hred' := h116 G A c L a R Y h B' hB'A (by rw [h27, hm]; norm_num)
    have hirr : ¬ Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) B') :=
      fun hirr => hred' ⟨hB'N, hirr⟩
    simp only [Sec21.IsIrreducibleOn, not_forall, not_or, exists_prop] at hirr
    obtain ⟨C, hCinv, hC1, hCtop⟩ := hirr
    set C' := C.map B'.subtype with hC'
    have hC'B' : C' ≤ B' := Subgroup.map_subtype_le C
    have hcardC' : Nat.card C' = Nat.card C := Subgroup.card_map_of_injective B'.subtype_injective
    obtain ⟨m', hm'⟩ := IsPGroup.iff_card.mp (hA3.to_le (hC'B'.trans hB'A))
    have hm'2 : m' ≤ 2 := by
      have h1 := Subgroup.card_dvd_of_le hC'B'
      rw [hm', hm] at h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h1
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      apply hC1
      rw [← Subgroup.card_eq_one, ← hcardC', hm', pow_zero]
    have hm'2' : m' ≠ 2 := by
      rintro rfl
      apply hCtop
      rw [← Subgroup.card_eq_iff_eq_top, ← hcardC', hm', hm]
    refine ⟨C', hC'B'.trans hB'A, ?_, fun g hg => le_normalizer_map_subtype hCinv ⟨hg, hB'N hg⟩⟩
    rw [hm', show m' = 1 by omega, pow_one]

theorem item117_of (h97 : Sec9.Item97) (h112 : Item112) (h114 : Item114) (h115 : Item115)
    (h116 : Item116) (hT : LStarTransvection) (hI : LStarInverting) : Item117 := by
  intro G _ _ A c L a R Y h d hdL D hDA hD3
  have hpts : ∀ D' : Subgroup G, D' ≤ A → Nat.card D' = 3 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D' : Set G) →
      D' = Subgroup.zpowers c ∨ D' = Subgroup.zpowers d := fun D' hD'A hD'3 hD'N =>
    eq_zpowers_or_eq_zpowers_of_le_normalizer h97 hT hI h hdL hD'A hD'3 (inf_le_right.trans hD'N)
  have hc : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro hcN
    obtain ⟨g, hgle, hgne⟩ := h112 G A c L a R Y h d hdL
    have hdA : d ∈ A := by
      have : d ∈ A ⊓ L := by
        rw [hdL]
        exact Subgroup.mem_zpowers d
      exact this.1
    have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact h.mem_A
      · exact hdA
    obtain ⟨w, hw, hgw⟩ := h114 G A c L a R Y h g (hgle.trans hcdA)
    apply hgne
    rw [hgw]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hcN hw)
  obtain ⟨D₀, hD₀A, hD₀3, hD₀N⟩ := exists_normal_three_of h115 h116 h
  have hdN : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rcases hpts D₀ hD₀A hD₀3 hD₀N with h1 | h1
    · rw [h1] at hD₀N
      exact absurd hD₀N hc
    · rwa [h1] at hD₀N
  constructor
  · intro hDN
    rcases hpts D hDA hD3 hDN with h1 | h1
    · rw [h1] at hDN
      exact absurd hDN hc
    · exact h1
  · rintro rfl
    exact hdN

end Points

end CFSG.RankThree.PartTwo.Sec11
