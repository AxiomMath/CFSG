module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3EvenTools
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LieType.Universal.Unitary.Roots.Levels

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
open scoped Pointwise

section Group

variable {Y : Type*} [Group Y]

theorem mem_normalizer_zpowers_of_conj_mem189 {a g : Y} (h1 : g * a * g⁻¹ ∈ Subgroup.zpowers a)
    (h2 : g⁻¹ * a * g ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 m
  · intro hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    have he : z = (g⁻¹ * a * g⁻¹⁻¹) ^ m := by
      rw [conj_zpow, hm]
      group
    rw [he, inv_inv]
    exact Subgroup.zpow_mem _ h2 m

variable [Finite Y]

theorem exists_pow_two_pow_eq_one189 (T : Sylow 2 Y) {z : Y} (hz : z ∈ (T : Subgroup Y)) :
    ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨z, hz⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem not_mem_sylow_two189 (T : Sylow 2 Y) {y : Y} (hy3 : orderOf y = 3) :
    y ∉ (T : Subgroup Y) := by
  intro hy
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one189 T hy
  have h := orderOf_dvd_of_pow_eq_one hk
  rw [hy3] at h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem isSylowOf_three189 {A P : Subgroup Y} (hAP : A ≤ P) (hA : Nat.card A = 3) {a : ℕ}
    (hP : Nat.card P = 3 * 2 ^ a) : CFSG.ABGLocalTools.IsSylowOf 3 A P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hAP, IsPGroup.of_card (n := 1) (by rw [hA, pow_one]), fun h3 => ?_⟩
  have h := Subgroup.relIndex_mul_card A P
  rw [inf_eq_left.mpr hAP, hA, hP, mul_comm] at h
  have hr : A.relIndex P = 2 ^ a := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h
  rw [hr] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem card_sup_zpowers189 (T : Sylow 2 Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hy3 : orderOf y = 3) :
    Nat.card ((T : Subgroup Y) ⊔ Subgroup.zpowers y : Subgroup Y) =
      3 * 2 ^ (Nat.card Y).factorization 2 := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
    Subgroup.zpowers_le.2 hy
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (T : Subgroup Y)
    (Subgroup.zpowers y) hle
  have hT := Sylow.card_eq_multiplicity T
  set a := (Nat.card Y).factorization 2
  have h1 : Nat.card ((T : Subgroup Y) ⊔ Subgroup.zpowers y : Subgroup Y) ≤ 2 ^ a * 3 := by
    have e : Nat.card ((T : Subgroup Y) ⊔ Subgroup.zpowers y : Subgroup Y) =
        Nat.card (((T : Subgroup Y) : Set Y) * (Subgroup.zpowers y : Set Y)) := by
      rw [← hset]
      rfl
    rw [e, ← hT, ← hy3, ← Nat.card_zpowers]
    exact Set.natCard_mul_le
  have h2 : 2 ^ a ∣ Nat.card ((T : Subgroup Y) ⊔ Subgroup.zpowers y : Subgroup Y) :=
    hT ▸ Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card ((T : Subgroup Y) ⊔ Subgroup.zpowers y : Subgroup Y) := by
    have := Subgroup.card_dvd_of_le
      (le_sup_right : Subgroup.zpowers y ≤ (T : Subgroup Y) ⊔ Subgroup.zpowers y)
    rwa [Nat.card_zpowers, hy3] at this
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have h4 := Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h3 h2)
  exact le_antisymm (h1.trans (le_of_eq (mul_comm _ _))) h4

end Group

section Quotient

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_conj_borelQuotient189 (h : BorelQuotient D n H π M) (T : Sylow 2 Y) :
    ∃ π' : K →* Y, BorelQuotient D n H π' M ∧ π'.ker = π.ker ∧
      (T : Subgroup Y) = (posUnipotent D).map π' ∧
      Subgroup.normalizer ((T : Subgroup Y) : Set Y) = (borel D H).map π' := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  exact ⟨π', hQ, hker, hT, by rw [hT, hQ.normalizer_map_posUnipotent]⟩

theorem exists_conj_mem_torus189 (h : BorelQuotient D n H π M) (T : Sylow 2 Y) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hy3 : orderOf y = 3) :
    ∃ π' : K →* Y, BorelQuotient D n H π' M ∧ π'.ker = π.ker ∧
      (T : Subgroup Y) = (posUnipotent D).map π' ∧
      ∃ k ∈ (T : Subgroup Y) ⊔ Subgroup.zpowers y, ∃ t ∈ ⨆ i, H i, k * y * k⁻¹ = π' t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π', hQ, hker, hT, hN⟩ := exists_conj_borelQuotient189 h T
  refine ⟨π', hQ, hker, hT, ?_⟩
  have hyB : y ∈ (borel D H).map π' := hN ▸ hy
  obtain ⟨b, hb, hby⟩ := hyB
  have hb' : b ∈ posUnipotent D ⊔ ⨆ i, H i := by rwa [CFSG.LieType.Steinberg.borel, sup_comm] at hb
  have hTn := CFSG.ClassicalInvolution.WeakCT.torus_le_normalizer_posUnipotent h.ct
  obtain ⟨u, hu, t, ht, rfl⟩ :=
    (CFSG.ClassicalInvolution.ModelFacts.OddCover.mem_sup_iff_of_normalizes
      (Q := posUnipotent D) (A := ⨆ i, H i)
      fun a ha q hq => (Subgroup.mem_normalizer_iff.1 (hTn ha) q).1 hq).1 hb'
  have hsT : π' u ∈ (T : Subgroup Y) := by
    rw [hT]
    exact Subgroup.mem_map_of_mem π' hu
  have hds : π' t = (π' u)⁻¹ * y := by rw [← hby, map_mul, inv_mul_cancel_left]
  have hy3' : y * y * y = 1 := by rw [← pow_three', ← hy3, pow_orderOf_eq_one]
  have hd3T : π' t ^ 3 ∈ (T : Subgroup Y) := by
    have hconj : ∀ g ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y),
        g * (π' u)⁻¹ * g⁻¹ ∈ (T : Subgroup Y) :=
      fun g hg => (Subgroup.mem_normalizer_iff.1 hg _).1 (inv_mem hsT)
    have e : π' t ^ 3 = (π' u)⁻¹ * (y * (π' u)⁻¹ * y⁻¹) *
        ((y * y) * (π' u)⁻¹ * (y * y)⁻¹) * (y * y * y) := by
      rw [hds, pow_three']
      group
    rw [e, hy3', mul_one]
    exact mul_mem (mul_mem (inv_mem hsT) (hconj y hy)) (hconj (y * y) (mul_mem hy hy))
  have hdM : π' t ^ M = 1 := by
    rw [← map_pow, CFSG.ClassicalInvolution.WeakCT.pow_eq_one_of_mem_torus h.extras h.torus_pow ht,
      map_one]
  have hd3 : π' t ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one189 T hd3T
    have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
    have h2 : (π' t ^ 3) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hdM, one_pow]
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
      (orderOf_dvd_of_pow_eq_one h2))
  have hd1 : π' t ≠ 1 := by
    intro hd
    apply not_mem_sylow_two189 T hy3
    rw [← hby, map_mul, hd, mul_one]
    exact hsT
  have hdo : orderOf (π' t) = 3 := orderOf_eq_prime hd3 hd1
  have hP := card_sup_zpowers189 T hy hy3
  have hdP : π' t ∈ (T : Subgroup Y) ⊔ Subgroup.zpowers y := by
    rw [hds]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hsT))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hSy := isSylowOf_three189 (le_sup_right : Subgroup.zpowers y ≤ _)
    (by rw [Nat.card_zpowers, hy3]) hP
  have hSd := isSylowOf_three189 (Subgroup.zpowers_le.2 hdP) (by rw [Nat.card_zpowers, hdo]) hP
  obtain ⟨k, hk, hconj⟩ := hSd.exists_mem_conj hSy
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 ((hconj y).1 (Subgroup.mem_zpowers y))
  refine ⟨k⁻¹, inv_mem hk, t ^ m, zpow_mem ht m, ?_⟩
  rw [inv_inv, map_zpow, hm]

theorem normalizer_le_of_conj_mem_torus189 (h : BorelQuotient D n H π M) (T : Sylow 2 Y)
    (hT : (T : Subgroup Y) = (posUnipotent D).map π) {y k : Y} {t : K} (ht : t ∈ ⨆ i, H i)
    (hkt : k * y * k⁻¹ = π t) {J : Subgroup Y} (hTJ : (T : Subgroup Y) ≤ J) (hkJ : k ∈ J)
    (hJ : ∀ c : Y, c * y = y * c → c ∈ J) :
    Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J := by
  rw [hT, h.normalizer_map_posUnipotent, CFSG.LieType.Steinberg.borel, Subgroup.map_sup]
  refine sup_le ?_ (hT ▸ hTJ)
  rintro _ ⟨t', ht', rfl⟩
  have hc : π t' * π t = π t * π t' := by
    rw [← map_mul, ← map_mul, (CFSG.ClassicalInvolution.WeakCT.commute_of_mem_torus h.extras ht'
      ht).eq]
  have hy : y = k⁻¹ * π t * k := by rw [← hkt]; group
  have hcy : (k⁻¹ * π t' * k) * y = y * (k⁻¹ * π t' * k) := by
    rw [hy]
    calc k⁻¹ * π t' * k * (k⁻¹ * π t * k) = k⁻¹ * (π t' * π t) * k := by group
      _ = k⁻¹ * (π t * π t') * k := by rw [hc]
      _ = k⁻¹ * π t * k * (k⁻¹ * π t' * k) := by group
  have e : π t' = k * (k⁻¹ * π t' * k) * k⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hkJ (hJ _ hcy)) (inv_mem hkJ)

theorem not_mem_normalizer_of_inv189 (h : BorelQuotient D n H π M) (T : Sylow 2 Y) {y w : Y}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hy3 : orderOf y = 3)
    (hw : w * w = 1) (hwy : w * y * w⁻¹ = y⁻¹) :
    w ∉ Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
  intro hwN
  obtain ⟨π', hQ, -, hT, hN⟩ := exists_conj_borelQuotient189 h T
  have hwB : w ∈ (borel D H).map π' := hN ▸ hwN
  obtain ⟨b, hb, rfl⟩ := hwB
  have hwT : π' b ∈ (T : Subgroup Y) := by
    obtain ⟨m, hm⟩ := h.odd
    have e : π' b = π' (b ^ M) := by
      rw [map_pow, hm, pow_succ, pow_mul, sq, hw, one_pow, one_mul]
    rw [e, hT]
    exact Subgroup.mem_map_of_mem π' (pow_mem_posUnipotent189 hQ.ct hQ.extras hQ.torus_pow hb)
  apply not_mem_sylow_two189 T hy3
  have hy3' : y * y * y = 1 := by rw [← pow_three', ← hy3, pow_orderOf_eq_one]
  have e : y = π' b * (y * (π' b)⁻¹ * y⁻¹) := by
    calc y = y⁻¹ * y⁻¹ * (y * y * y) := by group
      _ = (π' b * y * (π' b)⁻¹) * y⁻¹ := by rw [hy3', mul_one, hwy]
      _ = π' b * (y * (π' b)⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem hwT ((Subgroup.mem_normalizer_iff.1 hy _).1 (inv_mem hwT))

end Quotient

section Unitary

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem pow_two_pow_eq_self189 (hf : 2 ^ f % 3 = 1) {c : F} (hc : c ^ 3 = 1) : c ^ 2 ^ f = c := by
  rw [← Nat.div_add_mod (2 ^ f) 3, hf, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]

theorem eq_one_of_mem_statedScalars189 (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ^ f % 3 = 1)
    {g : GL (Fin 3) F} (hg : g ∈ StatedSU 3 (2 ^ f) F) (hs : g ∈ StatedScalars (Fin 3) F) :
    g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, rfl⟩ := hs
  rw [← SUid_eq_statedSU hF 3, mem_SUid, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply] at hg
  obtain ⟨hdet, hiso⟩ := hg
  have hc3 : (c : F) ^ 3 = 1 := by simpa [det_diagonal] using hdet
  have h1 : conjTr (unitaryInvolution F 2 f) (diagonal fun _ : Fin 3 => (c : F)) =
      diagonal fun _ => unitaryInvolution F 2 f (c : F) := by
    rw [conjTr, diagonal_map (map_zero _), diagonal_transpose]
  rw [h1, diagonal_mul_diagonal] at hiso
  have h2 := congrFun (congrFun hiso 0) 0
  rw [diagonal_apply_eq, one_apply_eq, unitaryInvolution_apply, pow_two_pow_eq_self189 hf hc3]
    at h2
  have hc1 : (c : F) = 1 := by
    calc (c : F) = c * (c * c) := by rw [h2, mul_one]
      _ = c ^ 3 := by ring
      _ = 1 := hc3
  rw [show c = 1 from Units.ext hc1, map_one]

theorem eq_one_of_borelQuotient_su_eq_one189 (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ^ f % 3 = 1) {Y : Type} [Group Y] (e : Y ≃* StatedProj (StatedSU 3 (2 ^ f) F))
    {z : SU (unitaryInvolution F 2 f) 3}
    (hz : (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp
      (equivStatedSU hF 3).toMonoidHom)) z = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
  have h1 : equivStatedSU hF 3 z = 1 :=
    Subtype.ext (eq_one_of_mem_statedScalars189 hF hf (equivStatedSU hF 3 z).2 hz)
  exact (MulEquiv.map_eq_one_iff _).1 h1

omit [Finite F] [CharP F 2] in
theorem antidiag_mul_diagonal_mul_antidiag189 {m : ℕ} (d : Fin m → F) :
    antidiag m * diagonal d * antidiag m = diagonal fun s => d (Fin.rev s) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · rw [mul_diagonal]
    by_cases hab : a = b
    · subst hab
      simp [antidiag]
    · have h1 : ¬ b = Fin.rev (Fin.rev a) := by rw [Fin.rev_rev]; exact Ne.symm hab
      simp [antidiag, h1, diagonal_apply_ne _ hab, Ne.symm hab]
  · intro k _ hk
    rw [mul_diagonal]
    simp [antidiag, hk]
  · simp

theorem exists_inv_diag_su_three189 (hf : 2 ^ f % 3 = 1) :
    ∃ w : SU (unitaryInvolution F 2 f) 3, w * w = 1 ∧
      ∀ t ∈ diagSubgroup (unitaryInvolution F 2 f) 3, t ^ 3 = 1 → w * t * w⁻¹ = t⁻¹ := by
  have h2 : (-1 : F) = 1 := CharTwo.neg_eq 1
  have hdet : (antidiag 3 : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Matrix.det_fin_three]
    simp [antidiag, Fin.rev, h2]
  have hconj : conjTr (unitaryInvolution F 2 f) (antidiag 3 : Matrix (Fin 3) (Fin 3) F) =
      antidiag 3 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [conjTr, antidiag, Fin.rev]
  have hiso : conjTr (unitaryInvolution F 2 f) (antidiag 3 : Matrix (Fin 3) (Fin 3) F) *
      antidiag 3 * antidiag 3 = antidiag 3 := by
    rw [hconj, antidiag_mul_self, Matrix.one_mul]
  let w : SU (unitaryInvolution F 2 f) 3 :=
    ⟨⟨antidiag 3, antidiag 3, antidiag_mul_self 3, antidiag_mul_self 3⟩, hdet, hiso⟩
  have hwm : ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = antidiag 3 := rfl
  have hw : w * w = 1 := Subtype.ext (Units.ext (antidiag_mul_self 3))
  refine ⟨w, hw, fun t ht ht3 => ?_⟩
  obtain ⟨d, hd⟩ := ht
  have hd3 : ∀ s, d s ^ 3 = 1 := by
    have h := congrArg (fun g : SU (unitaryInvolution F 2 f) 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ht3
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hd, diagonal_pow, OneMemClass.coe_one,
      Units.val_one] at h
    intro s
    have := congrFun (congrFun h s) s
    simpa [diagonal_apply_eq] using this
  rw [inv_eq_of_mul_eq_one_right hw]
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one, hwm, hd]
  rw [antidiag_mul_diagonal_mul_antidiag189, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  have h1 := unitary_of_coe_eq_diagonal hd s
  rw [unitaryInvolution_apply, pow_two_pow_eq_self189 hf (hd3 s)] at h1
  rw [mul_comm]
  exact h1

end Unitary

end CFSG.RankThree.PartTwo.Sec18
