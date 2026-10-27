module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.RankThreeEven (projSL)

section SL2

variable {F : Type} [Field F]

theorem eq_one_of_mulVec_eq_of_det_ne189 {t : Matrix (Fin 2) (Fin 2) F} {v w : Fin 2 → F}
    (hv : t *ᵥ v = v) (hw : t *ᵥ w = w) (hd : v 0 * w 1 - v 1 * w 0 ≠ 0) : t = 1 := by
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv0 hv1 hw0 hw1
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, one_apply_eq]
    exact mul_right_cancel₀ hd (by linear_combination w 1 * hv0 - v 1 * hw0)
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      one_apply_ne]
    exact (mul_eq_zero.mp (by linear_combination v 0 * hw0 - w 0 * hv0 :
      t 0 1 * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hd
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, ne_eq, one_ne_zero, not_false_eq_true,
      one_apply_ne]
    exact (mul_eq_zero.mp (by linear_combination w 1 * hv1 - v 1 * hw1 :
      t 1 0 * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hd
  · simp only [Fin.mk_one, Fin.isValue, one_apply_eq]
    exact mul_right_cancel₀ hd (by linear_combination v 0 * hw1 - w 0 * hv1)

theorem exists_eq_smul_of_det_eq_zero189 {v w : Fin 2 → F} (hv : v ≠ 0)
    (hd : v 0 * w 1 - v 1 * w 0 = 0) : ∃ l : F, w = l • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨w 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_left h1
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨w 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hd

theorem mul_self_eq_one_of_mulVec_eq189 [CharP F 2] {g : SL₂ F} {v : Fin 2 → F} (hv0 : v ≠ 0)
    (hv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g * g = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.property
    rwa [Matrix.det_fin_two] at this
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  set E := (g 0 0 - 1) * (g 1 1 - 1) - g 0 1 * g 1 0 with hEdef
  have hE0 : E * v 0 = 0 := by
    rw [hEdef]
    linear_combination (g 1 1 - 1) * e0 - g 0 1 * e1
  have hE1 : E * v 1 = 0 := by
    rw [hEdef]
    linear_combination (g 0 0 - 1) * e1 - g 1 0 * e0
  have hE : E = 0 := by
    by_contra hne
    apply hv0
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp hE0).resolve_left hne
    · exact (mul_eq_zero.mp hE1).resolve_left hne
  have htr : g 0 0 + g 1 1 = 0 := by
    rw [hEdef] at hE
    linear_combination hdet - hE + h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination g 0 0 * htr - hdet - h2
  · linear_combination g 0 1 * htr
  · linear_combination g 1 0 * htr
  · linear_combination g 1 1 * htr - hdet - h2

theorem exists_fixed_ne_zero189 [CharP F 2] [Finite F] {T : Subgroup (SL₂ F)}
    (hT : IsPGroup 2 T) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ t ∈ T, (t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hT.card_modEq_card_fixedPoints (Fin 2 → F)
  have hF : 2 ∣ Nat.card F := by
    have := Fintype.ofFinite F
    obtain ⟨k, hp, hk⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self 2 k.ne_zero
  have hV : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_pi, Fin.prod_const]
    exact hF.trans (dvd_pow_self _ two_ne_zero)
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints T (Fin 2 → F)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hV))
  have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints T (Fin 2 → F) := fun t => by
    change (t : Matrix (Fin 2) (Fin 2) F) *ᵥ 0 = 0
    exact Matrix.mulVec_zero _
  have hpos : 0 < Nat.card (MulAction.fixedPoints T (Fin 2 → F)) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
  have hlt : 1 < Nat.card (MulAction.fixedPoints T (Fin 2 → F)) := by
    obtain ⟨k, hk⟩ := hfix
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨⟨v, hv⟩, hne⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints T (Fin 2 → F))
  exact ⟨v, fun h => hne (Subtype.ext h), fun t ht => hv ⟨t, ht⟩⟩

theorem eq_one_of_pow_three189 [Finite F] (h3 : ¬ 3 ∣ Nat.card F - 1) {l : F}
    (hl : l ^ 3 = 1) : l = 1 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h3
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hq := FiniteField.pow_card_sub_one_eq_one l hl0
  have hg : Nat.gcd 3 (Fintype.card F - 1) = 1 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)).symm
  have := (pow_gcd_eq_one (a := l) (m := 3) (n := Fintype.card F - 1)).mpr ⟨hl, hq⟩
  rwa [hg, pow_one] at this

theorem eq_one_of_mem_normalizer_sl2189 [CharP F 2] [Finite F] (h3 : ¬ 3 ∣ Nat.card F - 1)
    {T : Subgroup (SL₂ F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) {g : SL₂ F}
    (hg : g ∈ Subgroup.normalizer (T : Set (SL₂ F))) (hg3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨v, hv0, hvT⟩ := exists_fixed_ne_zero189 hT
  set w := (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v with hwdef
  have hwT : ∀ t ∈ T, (t : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w := by
    intro t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * t * g)).mpr ?_
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e]
      exact ht
    have h1 := hvT _ ht'
    have h2 := congrArg (fun u => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] at h2
    rw [hwdef, Matrix.mulVec_mulVec]
    have e : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : SL₂ F) * (t : Matrix (Fin 2) (Fin 2) F) *
        g) = (t : Matrix (Fin 2) (Fin 2) F) * g := by
      have e' : g * (g⁻¹ * t * g) = t * g := by group
      have := congrArg (fun x : SL₂ F => (x : Matrix (Fin 2) (Fin 2) F)) e'
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
    rw [← e]
    exact h2
  have hd : v 0 * w 1 - v 1 * w 0 = 0 := by
    by_contra hd
    apply hT1
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mulVec_eq_of_det_ne189 (hvT t ht) (hwT t ht) hd)
  obtain ⟨l, hl⟩ := exists_eq_smul_of_det_eq_zero189 hv0 hd
  have hg3v : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, ← pow_three', hg3]
    simp
  have hl' : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = l • v := hl
  rw [hl', Matrix.mulVec_smul, hl', smul_smul, Matrix.mulVec_smul, hl', smul_smul] at hg3v
  have hl3 : l ^ 3 = 1 := by
    have h : (l * l * l - 1) • v = 0 := by rw [sub_smul, one_smul, hg3v, sub_self]
    have := (smul_eq_zero.mp h).resolve_right hv0
    rw [sub_eq_zero] at this
    rw [← this]
    ring
  have hl1 := eq_one_of_pow_three189 h3 hl3
  rw [hl1, one_smul] at hl
  have hgg := mul_self_eq_one_of_mulVec_eq189 hv0 hl
  calc g = g ^ 3 * (g * g)⁻¹ := by group
    _ = 1 := by rw [hg3, hgg]; group

theorem eq_one_of_mem_normalizer_of_equiv189 {Y : Type*} [Group Y] [CharP F 2] [Finite F]
    (h3 : ¬ 3 ∣ Nat.card F - 1) (φ : Y ≃* SL₂ F) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) {g : Y} (hg : g ∈ Subgroup.normalizer (T : Set Y)) (hg3 : g ^ 3 = 1) :
    g = 1 := by
  have hT' : T.map φ.toMonoidHom ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective T φ.injective).mp h)
  have hg' : φ g ∈ Subgroup.normalizer ((T.map φ.toMonoidHom : Subgroup (SL₂ F)) :
      Set (SL₂ F)) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hg
  have h := eq_one_of_mem_normalizer_sl2189 h3 (hT.map φ.toMonoidHom) hT' hg'
    (by rw [← map_pow, hg3, map_one])
  exact φ.injective (h.trans (map_one φ).symm)

theorem mem_inner_of_pow_two_pow189 [CharP F 2] [Finite F] {n : ℕ} (hn : Odd n)
    (hK : Nat.card F = 2 ^ n) {ψ : MulAut (SL₂ F)} {k : ℕ} (hψ : ψ ^ (2 ^ k) = 1) :
    ψ ∈ inner (SL₂ F) := by
  have hcard := natCard_out_sl2 (K := F) hn.pos hK
  have h1 : (QuotientGroup.mk ψ : Outer (SL₂ F)) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hψ, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk ψ : Outer (SL₂ F)) ^ n = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hg : Nat.gcd (2 ^ k) n = 1 := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)
  have h := (pow_gcd_eq_one (a := (QuotientGroup.mk ψ : Outer (SL₂ F)))).mpr ⟨h1, h2⟩
  rw [hg, pow_one] at h
  exact (QuotientGroup.eq_one_iff ψ).mp h

theorem exists_conj_of_pow_two_pow189 {Y : Type*} [Group Y] [CharP F 2] [Finite F] {n : ℕ}
    (hn : Odd n) (hK : Nat.card F = 2 ^ n) (φ : Y ≃* SL₂ F) {ψ : MulAut Y} {k : ℕ}
    (hψ : ψ ^ (2 ^ k) = 1) : ∃ y : Y, ψ = MulAut.conj y := by
  have h : MulAut.congr φ ψ ^ (2 ^ k) = 1 := by rw [← map_pow, hψ, map_one]
  obtain ⟨M, hM⟩ := mem_inner_of_pow_two_pow189 hn hK h
  refine ⟨φ.symm M, ?_⟩
  apply (MulAut.congr φ).injective
  rw [congr_conj, MulEquiv.apply_symm_apply]
  exact hM.symm

end SL2

section Abstract

variable {X : Type*} [Group X] [Finite X] {Kb Sb : Subgroup X} [Kb.Normal]

theorem centralizer_eq_bot_of_sup189 (hsup : Kb ⊔ Sb = ⊤) (hS : IsPGroup 2 Sb)
    (hθ : aschbacherSolvableCore 3 X = ⊥) (hZ : Subgroup.center Kb = ⊥) :
    Subgroup.centralizer (Kb : Set X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (Kb : Set X) with hCdef
  have hCK : ∀ x ∈ C, x ∈ Kb → x = 1 := by
    intro x hxC hxK
    have hz : (⟨x, hxK⟩ : Kb) ∈ Subgroup.center Kb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hQ : IsPGroup 2 (X ⧸ Kb) := by
    refine hS.of_surjective ((QuotientGroup.mk' Kb).comp Sb.subtype) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Kb q
    have hx : x ∈ ((Kb ⊔ Sb : Subgroup X) : Set X) := by rw [hsup]; trivial
    rw [Subgroup.normal_mul] at hx
    obtain ⟨k, hk, s, hs, rfl⟩ := hx
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have := (inferInstance : Kb.Normal).conj_mem k hk s⁻¹
    simpa [mul_assoc] using this
  have hC : IsPGroup 2 C := by
    refine hQ.of_injective ((QuotientGroup.mk' Kb).comp C.subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (hCK x x.2 hx))
  have hCs : Group.IsSolvable C := by
    have := hC.isNilpotent
    infer_instance
  have hC3 : ¬ 3 ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := hC.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hle := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.1
    C inferInstance hCs hC3
  rw [hθ] at hle
  exact le_bot_iff.mp hle

omit [Finite X] in
theorem le_of_forall_inner189 (hC : Subgroup.centralizer (Kb : Set X) = ⊥) (hS : IsPGroup 2 Sb)
    (hinner : ∀ ψ : MulAut Kb, ∀ k : ℕ, ψ ^ (2 ^ k) = 1 → ∃ y : Kb, ψ = MulAut.conj y) :
    Sb ≤ Kb := by
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hψ : (MulAut.conjNormal s : MulAut Kb) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hsk, map_one]
  obtain ⟨y, hy⟩ := hinner _ k hψ
  have hmem : (y : X)⁻¹ * s ∈ Subgroup.centralizer (Kb : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut Kb => ((φ ⟨x, hx⟩ : Kb) : X)) hy
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((y : X)⁻¹ * s) = (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * s := by group
      _ = (y : X)⁻¹ * (s * x * s⁻¹) * s := by rw [h1]
      _ = ((y : X)⁻¹ * s) * x := by group
  rw [hC, Subgroup.mem_bot] at hmem
  have : s = y := by
    calc s = (y : X) * ((y : X)⁻¹ * s) := by group
      _ = y := by rw [hmem, mul_one]
  rw [this]
  exact y.2

end Abstract

section Alpha

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kAlpha189_normal (M H : Subgroup G) (c : G) : (kAlpha189 M H c).Normal := by
  have hn : ((normalClosureIn M c).subgroupOf (sk189 M H c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sk189_le_normalizer_k M H c)
  exact hn.map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem kAlpha189_sup_sAlpha189 (M H : Subgroup G) (c : G) :
    kAlpha189 M H c ⊔ sAlpha189 M H c = ⊤ := by
  rw [kAlpha189, sAlpha189, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (le_sup_right : normalClosureIn M c ≤ sk189 M H c) le_sup_left,
    show normalClosureIn M c ⊔ s189 M H = sk189 M H c from sup_comm _ _,
    Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem isPGroup_sAlpha189 (M H : Subgroup G) (c : G) : IsPGroup 2 (sAlpha189 M H c) :=
  ((isPGroup_s189 M H).comap_subtype).map _

theorem aschbacherSolvableCore_sKAlpha189 (M H : Subgroup G) (c : G) :
    aschbacherSolvableCore 3 (SKAlpha189 M H c) = ⊥ := by
  obtain ⟨hθs, -, hθp, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥(sk189 M H c)) Nat.prime_three
  exact (solvable_prime_complement_core_quotient_centralizers (G := ↥(sk189 M H c))
    Nat.prime_three (aschbacherSolvableCore 3 ↥(sk189 M H c)) hθs hθp).2.2.1

omit [Finite G] in
theorem mem_normalizer_subgroupOf189 {M H : Subgroup G} {c : G} {X : Subgroup G}
    {x : ↥(sk189 M H c)} (hx : (x : G) ∈ Subgroup.normalizer (X : Set G)) :
    x ∈ Subgroup.normalizer ((X.subgroupOf (sk189 M H c) : Subgroup _) : Set (sk189 M H c)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hx y

end Alpha

theorem not_three_dvd_two_pow_sub_one189 {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  rw [pow_succ, pow_mul]
  norm_num
  omega

theorem step189OddL2 : Step189OddL2 := by
  intro G _ _ A M H c hset n hn ⟨e⟩
  have h := hset.toSec18H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := kAlpha189_normal M H c
  let φ : ↥(kAlpha189 M H c) ≃* SL₂ (GaloisField 2 n) :=
    (e.trans (Sec4.projSLEquivPSL (GaloisField 2 n))).trans (slEquivPSL (GaloisField 2 n)).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have h3 : ¬ 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [hcard]
    exact not_three_dvd_two_pow_sub_one189 hn
  have hZ : Subgroup.center ↥(kAlpha189 M H c) = ⊥ := by
    have hmap := center_map_equiv φ
    rw [sl2_center_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hC := centralizer_eq_bot_of_sup189 (kAlpha189_sup_sAlpha189 M H c)
    (isPGroup_sAlpha189 M H c) (aschbacherSolvableCore_sKAlpha189 M H c) hZ
  have hSK : sAlpha189 M H c ≤ kAlpha189 M H c :=
    le_of_forall_inner189 hC (isPGroup_sAlpha189 M H c) fun ψ k hψ =>
      exists_conj_of_pow_two_pow189 hn hcard φ hψ
  have hcK : c ∈ normalClosureIn M c := Sec20.self_mem_normalClosureIn M c
  have hcSK : c ∈ sk189 M H c := (le_sup_right : normalClosureIn M c ≤ sk189 M H c) hcK
  set cb := alpha189 M H c ⟨c, hcSK⟩ with hcbdef
  have hcbK : cb ∈ kAlpha189 M H c :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcK)
  have hc3 := pow_three_of_sec18H189 h
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hset.pRank_eq
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcbdef, ← map_pow]
    have : (⟨c, hcSK⟩ : ↥(sk189 M H c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    rw [hcbdef, alpha189, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := orderOf_dvd_natCard
      (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c))
    rw [hord] at hdvd
    exact (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
      Nat.prime_three).2.2.1 hdvd
  have hcbN : cb ∈ Subgroup.normalizer (sAlpha189 M H c : Set (SKAlpha189 M H c)) := by
    have hcS : c ∈ Subgroup.normalizer (s189 M H : Set G) :=
      le_normalizer_s189 h (mem_of_sec18H189 h)
    exact Subgroup.le_normalizer_map _
      (Subgroup.mem_map_of_mem _ (mem_normalizer_subgroupOf189 hcS))
  have hT : IsPGroup 2 ((sAlpha189 M H c).subgroupOf (kAlpha189 M H c)) :=
    (isPGroup_sAlpha189 M H c).comap_subtype
  have hT1 : (sAlpha189 M H c).subgroupOf (kAlpha189 M H c) ≠ ⊥ := by
    intro hbot
    apply hset.sAlpha_ne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hSK hx⟩ : ↥(kAlpha189 M H c)) ∈
        (sAlpha189 M H c).subgroupOf (kAlpha189 M H c) := Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  have hgN : (⟨cb, hcbK⟩ : ↥(kAlpha189 M H c)) ∈ Subgroup.normalizer
      (((sAlpha189 M H c).subgroupOf (kAlpha189 M H c) : Subgroup _) :
        Set ↥(kAlpha189 M H c)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hcbN y
  have hg3 : (⟨cb, hcbK⟩ : ↥(kAlpha189 M H c)) ^ 3 = 1 := Subtype.ext (by simpa using hcb3)
  have hg1 := eq_one_of_mem_normalizer_of_equiv189 h3 φ hT hT1 hgN hg3
  exact hcb1 (congrArg Subtype.val hg1)

end CFSG.RankThree.PartTwo.Sec18
