module

public import CFSG.RankThree.PartTwo.Census.OddClassical.Main
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThreePlanes
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Census

namespace UnitaryFourThree

open Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {F : Type} [Field F]

local notation "M⟦" x "⟧" => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

theorem det_eq_one (x : StatedSU 4 3 F) (h : UnitaryFieldData 3 1 F) : (M⟦x⟧).det = 1 :=
  ((mem_S43 h).mp x.2).1

theorem mk_eq_one_iff (h : UnitaryFieldData 3 1 F) {x : StatedSU 4 3 F} :
    (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) = 1 ↔ ∃ a : F, M⟦x⟧ = a • 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := det_eq_one x h
      rw [ha, zero_smul, Matrix.det_zero] at this
      exact zero_ne_one this
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, ha]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem pow_four_eq_one_of_eq_smul (h : UnitaryFieldData 3 1 F) {x : StatedSU 4 3 F} {a : F}
    (ha : M⟦x⟧ = a • 1) : a ^ 4 = 1 := by
  have := det_eq_one x h
  rw [ha, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
  exact this

theorem exists_mul_eq_smul (h : UnitaryFieldData 3 1 F) {x y : StatedSU 4 3 F}
    (hxy : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x) :
    ∃ d : F, d ^ 4 = 1 ∧ M⟦x⟧ * M⟦y⟧ = d • (M⟦y⟧ * M⟦x⟧) := by
  set z := x * y * x⁻¹ * y⁻¹
  have hz : (QuotientGroup.mk z : StatedProj (StatedSU 4 3 F)) = 1 := by
    simp only [z, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxy, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨d, hd⟩ := (mk_eq_one_iff h).mp hz
  refine ⟨d, pow_four_eq_one_of_eq_smul h hd, ?_⟩
  have hzz : x * y = z * (y * x) := by simp [z, mul_assoc]
  have := congrArg (fun g : StatedSU 4 3 F => M⟦g⟧) hzz
  simp only [Subgroup.coe_mul, Units.val_mul] at this
  rw [this, hd, Matrix.smul_mul, Matrix.one_mul]

theorem matrix_ne_zero (h : UnitaryFieldData 3 1 F) (x : StatedSU 4 3 F) : M⟦x⟧ ≠ 0 := by
  intro h0
  have := det_eq_one x h
  rw [h0, Matrix.det_zero] at this
  exact zero_ne_one this

theorem mat_comm_of_mem {A g : GL (Fin 4) F} (hg : g ∈ Subgroup.centralizer {A}) :
    (g : Matrix (Fin 4) (Fin 4) F) * A = A * g := by
  have := congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simpa only [Units.val_mul] using this

theorem inv_mulVec_of_mulVec {x : StatedSU 4 3 F} {a : F} (ha : a ≠ 0) {v : Fin 4 → F}
    (hv : M⟦x⟧ *ᵥ v = a • v) : M⟦x⁻¹⟧ *ᵥ v = a⁻¹ • v := by
  have h1 : M⟦x⁻¹⟧ * M⟦x⟧ = 1 := Units.inv_mul (x : GL (Fin 4) F)
  have h2 := congrArg (fun w => M⟦x⁻¹⟧ *ᵥ w) hv
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul] at h2
  calc M⟦x⁻¹⟧ *ᵥ v = a⁻¹ • (a • (M⟦x⁻¹⟧ *ᵥ v)) := by
        rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • v := by rw [← h2]

theorem commute_of_pow_odd (h : UnitaryFieldData 3 1 F) {x A : StatedSU 4 3 F} {c : F}
    (hA : M⟦A⟧ * M⟦A⟧ = c • 1)
    (hxA : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) * QuotientGroup.mk A =
      QuotientGroup.mk A * QuotientGroup.mk x) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    M⟦x⟧ * M⟦A⟧ = M⟦A⟧ * M⟦x⟧ := by
  obtain ⟨d, -, hd⟩ := exists_mul_eq_smul h hxA
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg Matrix.det hA
    rw [Matrix.det_mul, det_eq_one A h, zero_smul, Matrix.det_zero, mul_one] at this
    exact one_ne_zero this
  have hd2 := sq_eq_one_of_mul_eq_smul hA hc0 (matrix_ne_zero h x) hd
  have hdm := pow_mul_eq_smul hd m
  have hxm' : M⟦x⟧ ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hxm, Subgroup.coe_one, Units.val_one]
  rw [hxm', Matrix.one_mul, Matrix.mul_one] at hdm
  have hdm1 : d ^ m = 1 := by
    have h2 : (d ^ m - 1) • M⟦A⟧ = 0 := by rw [sub_smul, ← hdm, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (matrix_ne_zero h A))
  obtain ⟨k, rfl⟩ := hm
  have hd1 : d = 1 := by
    rw [pow_succ, pow_mul, hd2, one_pow, one_mul] at hdm1
    exact hdm1
  rw [hd, hd1, one_smul]

theorem exists_planes_of_orderOf (h : UnitaryFieldData 3 1 F) {A : StatedSU 4 3 F}
    (hA : orderOf (QuotientGroup.mk A : StatedProj (StatedSU 4 3 F)) = 2) :
    ∃ c : F, M⟦A⟧ * M⟦A⟧ = c • 1 ∧
    ∃ Vp Vm : Submodule F (Fin 4 → F), IsCompl Vp Vm ∧ finrank F Vp = 2 ∧ finrank F Vm = 2 ∧
      (∀ v ∈ Vp, ∀ w ∈ Vm, stdHermForm h 4 v w = 0) ∧
      (∀ X : Matrix (Fin 4) (Fin 4) F, X * M⟦A⟧ = M⟦A⟧ * X →
        (∀ v ∈ Vp, X *ᵥ v ∈ Vp) ∧ (∀ v ∈ Vm, X *ᵥ v ∈ Vm)) ∧
      (∀ X : Matrix (Fin 4) (Fin 4) F, X * M⟦A⟧ = -(M⟦A⟧ * X) →
        (∀ v ∈ Vp, X *ᵥ v ∈ Vm) ∧ (∀ v ∈ Vm, X *ᵥ v ∈ Vp)) := by
  have hsq : (QuotientGroup.mk (A * A) : StatedProj (StatedSU 4 3 F)) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (mk_eq_one_iff h).mp hsq
  simp only [Subgroup.coe_mul, Units.val_mul] at hc
  refine ⟨c, hc, exists_planes h (det_eq_one A h) ((mem_S43 h).mp A.2).2 hc fun d hd => ?_⟩
  have h1 : (QuotientGroup.mk A : StatedProj (StatedSU 4 3 F)) = 1 :=
    (mk_eq_one_iff h).mpr ⟨d, hd⟩
  rw [h1, orderOf_one] at hA
  exact absurd hA (by norm_num)

theorem pow_two_pow_eq_one (h : UnitaryFieldData 3 1 F) {x : StatedSU 4 3 F} {k : ℕ}
    (hx : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) ^ (2 ^ k) = 1) :
    (x : GL (Fin 4) F) ^ (2 ^ (k + 2)) = 1 := by
  rw [← QuotientGroup.mk_pow] at hx
  obtain ⟨e, he⟩ := (mk_eq_one_iff h).mp hx
  have he4 := pow_four_eq_one_of_eq_smul h he
  refine Units.ext ?_
  rw [pow_add, pow_mul, Units.val_pow_eq_pow_val, show (2 : ℕ) ^ 2 = 4 by norm_num,
    ← Subgroup.coe_pow, he, smul_pow, he4, one_pow, one_smul, Units.val_one]

theorem not_dvd_card_of_le_centralizer (h : UnitaryFieldData 3 1 F)
    {s : StatedProj (StatedSU 4 3 F)} (hs : orderOf s = 2)
    {R : Subgroup (StatedProj (StatedSU 4 3 F))} (hR : R ≤ Subgroup.centralizer {s}) :
    ¬ 27 ∣ Nat.card R := by
  intro h27
  have := h.finite
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨c, hAc, Vp, Vm, hc, hp2, hm2, horth, hcomm, -⟩ := exists_planes_of_orderOf h hs
  set π := QuotientGroup.mk' ((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 3 F))
  set Rh := R.comap π
  have h27' : 3 ^ 3 ∣ Nat.card Rh := by
    have := Subgroup.card_map_dvd Rh π
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at this
    exact h27.trans this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Rh) 3 h27'
  set K' : Subgroup (GL (Fin 4) F) := (K.map Rh.subtype).map (StatedSU 4 3 F).subtype
  have hK' : Nat.card K' = 27 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num
  have hK'C : K' ≤ StatedSU 4 3 F ⊓ Subgroup.centralizer {(A : GL (Fin 4) F)} := by
    rintro g ⟨g1, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(k : StatedSU 4 3 F).2, ?_⟩
    show ((k : StatedSU 4 3 F) : GL (Fin 4) F) ∈ Subgroup.centralizer {(A : GL (Fin 4) F)}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk27 : (k : StatedSU 4 3 F) ^ 27 = 1 := by
      have h1 : (⟨k, hk⟩ : K) ^ 27 = 1 := by
        rw [show (27 : ℕ) = Nat.card K by rw [hK]; norm_num]
        exact pow_card_eq_one'
      have h2 := congrArg (fun y : K => ((y : Rh) : StatedSU 4 3 F)) h1
      simpa using h2
    have hxA : (QuotientGroup.mk (k : StatedSU 4 3 F) : StatedProj (StatedSU 4 3 F)) *
        QuotientGroup.mk A = QuotientGroup.mk A * QuotientGroup.mk (k : StatedSU 4 3 F) := by
      have := hR k.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    exact Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact commute_of_pow_odd h hAc hxA (by decide) hk27)
  have hdvd := card_dvd_of_planes h
    (StatedSU 4 3 F ⊓ Subgroup.centralizer {(A : GL (Fin 4) F)}) inf_le_left hc hp2 hm2 horth
    (fun g hg v hv => ((hcomm _ (mat_comm_of_mem hg.2)).1 v hv))
    (fun g hg v hv => ((hcomm _ (mat_comm_of_mem hg.2)).2 v hv))
  have := (Subgroup.card_dvd_of_le hK'C).trans hdvd
  rw [hK'] at this
  norm_num at this

theorem card_le_two_of_le_centralizer (h : UnitaryFieldData 3 1 F)
    {K : Subgroup (StatedProj (StatedSU 4 3 F))} (hK : 9 ∣ Nat.card K)
    {Q : Subgroup (StatedProj (StatedSU 4 3 F))} (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ Subgroup.centralizer K) : Nat.card Q ≤ 2 := by
  have := h.finite
  have : CharP F 3 := h.charP
  suffices huniq : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ ≠ 1 → q₂ ≠ 1 → q₁ = q₂ by
    classical
    have hinj : Function.Injective
        fun q : Q => decide ((q : StatedProj (StatedSU 4 3 F)) = 1) := by
      intro a b hab
      by_cases ha : (a : StatedProj (StatedSU 4 3 F)) = 1
      · have hb : (b : StatedProj (StatedSU 4 3 F)) = 1 := by simpa [ha] using hab
        exact Subtype.ext (ha.trans hb.symm)
      · have hb : (b : StatedProj (StatedSU 4 3 F)) ≠ 1 := by simpa [ha] using hab
        exact Subtype.ext (huniq a a.2 b b.2 ha hb)
    simpa using Nat.card_le_card_of_injective _ hinj
  intro q₁ hq₁ q₂ hq₂ hq₁1 hq₂1
  have hQne : Q ≠ ⊥ := fun h0 => hq₁1 (by rw [h0] at hq₁; exact Subgroup.mem_bot.mp hq₁)
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : 2 ∣ Nat.card (Subgroup.center Q) := by
    have hZp : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
    have := hQ.center_nontrivial
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd hk Finite.one_lt_card.ne'
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  set s : StatedProj (StatedSU 4 3 F) :=
    (((z : Subgroup.center Q) : Q) : StatedProj (StatedSU 4 3 F))
  have hsQ : s ∈ Q := ((z : Subgroup.center Q) : Q).2
  have hs2 : orderOf s = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hsc : ∀ q ∈ Q, q * s = s * q := fun q hq =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩)
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective s
  rw [← hA] at hs2
  obtain ⟨c, hAc, Vp, Vm, hc, hp2, hm2, horth, hcomm, hanti⟩ := exists_planes_of_orderOf h hs2
  have hsp := separatingLeft_domRestrict_of_orth (stdHermForm_separatingLeft h 4) hc horth
  have hsm := separatingLeft_domRestrict_of_orth (stdHermForm_separatingLeft h 4) hc.symm
    (fun v hv w hw => by rw [← (stdHermForm_isSymm h 4).eq, horth w hw v hv, map_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg Matrix.det hAc
    rw [Matrix.det_mul, det_eq_one A h, zero_smul, Matrix.det_zero, mul_one] at this
    exact one_ne_zero this
  set C : Subgroup (GL (Fin 4) F) :=
    StatedSU 4 3 F ⊓ Subgroup.centralizer {(A : GL (Fin 4) F)}
  have hWp : ∀ g ∈ C, ∀ v ∈ Vp, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ Vp :=
    fun g hg v hv => (hcomm _ (mat_comm_of_mem hg.2)).1 v hv
  have hWm : ∀ g ∈ C, ∀ v ∈ Vm, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ Vm :=
    fun g hg v hv => (hcomm _ (mat_comm_of_mem hg.2)).2 v hv
  set π := QuotientGroup.mk' ((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 3 F))
  set Kh := K.comap π
  have h9 : 3 ^ 2 ∣ Nat.card Kh := by
    have := Subgroup.card_map_dvd Kh π
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at this
    exact hK.trans this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H9, hH9⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kh) 3 h9
  set H' : Subgroup (GL (Fin 4) F) := (H9.map Kh.subtype).map (StatedSU 4 3 F).subtype
  have hH' : Nat.card H' = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH9]
    norm_num
  have hH'S : H' ≤ StatedSU 4 3 F := by
    rintro g ⟨g1, -, rfl⟩
    exact g1.2
  have hH'lift : ∀ g ∈ H', ∃ y : StatedSU 4 3 F, (y : GL (Fin 4) F) = g ∧
      (QuotientGroup.mk y : StatedProj (StatedSU 4 3 F)) ∈ K := by
    rintro g ⟨g1, ⟨k, -, rfl⟩, rfl⟩
    exact ⟨(k : StatedSU 4 3 F), rfl, k.2⟩
  have hKs : ∀ k ∈ K, k * s = s * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hQK hsQ) k hk)
  have hH'C : H' ≤ C := by
    rintro g ⟨g1, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(k : StatedSU 4 3 F).2, ?_⟩
    show ((k : StatedSU 4 3 F) : GL (Fin 4) F) ∈ Subgroup.centralizer {(A : GL (Fin 4) F)}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk9 : (k : StatedSU 4 3 F) ^ 9 = 1 := by
      have h1 : (⟨k, hk⟩ : H9) ^ 9 = 1 := by
        rw [show (9 : ℕ) = Nat.card H9 by rw [hH9]; norm_num]
        exact pow_card_eq_one'
      have h2 := congrArg (fun y : H9 => ((y : Kh) : StatedSU 4 3 F)) h1
      simpa using h2
    have hxA : (QuotientGroup.mk (k : StatedSU 4 3 F) : StatedProj (StatedSU 4 3 F)) *
        QuotientGroup.mk A = QuotientGroup.mk A * QuotientGroup.mk (k : StatedSU 4 3 F) := by
      rw [hA]
      exact hKs _ k.2
    exact Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact commute_of_pow_odd h hAc hxA (by decide) hk9)
  obtain ⟨gp, hgpH, hgp3, hgpm, hgpp⟩ := exists_trivial_on h hH'S hH' hc hm2 hsm
    (fun g hg v hv => hWm g (hH'C hg) v hv)
  obtain ⟨gm, hgmH, hgm3, -, hgmm⟩ := exists_trivial_on h hH'S hH' hc.symm hp2 hsp
    (fun g hg v hv => hWp g (hH'C hg) v hv)
  obtain ⟨yp, hyp, hypK⟩ := hH'lift gp hgpH
  obtain ⟨ym, hym, hymK⟩ := hH'lift gm hgmH
  have hact : ∀ q ∈ Q, q ≠ 1 → ∀ x : StatedSU 4 3 F,
      (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) = q →
      ∃ a : F, a ≠ 0 ∧ (∀ v ∈ Vp, M⟦x⟧ *ᵥ v = a • v) ∧ (∀ v ∈ Vm, M⟦x⟧ *ᵥ v = (-a) • v) := by
    intro q hq hq1 x hx
    have hcommK : ∀ y : StatedSU 4 3 F, (QuotientGroup.mk y : StatedProj (StatedSU 4 3 F)) ∈ K →
        (y : GL (Fin 4) F) ^ 3 = 1 → M⟦x⟧ * M⟦y⟧ = M⟦y⟧ * M⟦x⟧ := by
      intro y hyK hy3
      have hxy : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) * QuotientGroup.mk y =
          QuotientGroup.mk y * QuotientGroup.mk x := by
        rw [hx]
        exact (Subgroup.mem_centralizer_iff.mp (hQK hq) _ hyK).symm
      obtain ⟨d, hd4, hd⟩ := exists_mul_eq_smul h hxy
      refine commute_of_pow_three_eq_one hd4 ?_ (matrix_ne_zero h x) hd
      rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
    have hxp := hcommK yp hypK (by rw [hyp]; exact hgp3)
    have hxm := hcommK ym hymK (by rw [hym]; exact hgm3)
    have hxA0 : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) * QuotientGroup.mk A =
        QuotientGroup.mk A * QuotientGroup.mk x := by
      rw [hx, hA]
      exact hsc q hq
    obtain ⟨d, -, hd⟩ := exists_mul_eq_smul h hxA0
    have hd2 := sq_eq_one_of_mul_eq_smul hAc hc0 (matrix_ne_zero h x) hd
    have hXXi : M⟦x⟧ * M⟦x⁻¹⟧ = 1 := Units.mul_inv (x : GL (Fin 4) F)
    have hXiX : M⟦x⁻¹⟧ * M⟦x⟧ = 1 := Units.inv_mul (x : GL (Fin 4) F)
    have hxA : M⟦x⟧ * M⟦A⟧ = M⟦A⟧ * M⟦x⟧ := by
      rcases mul_self_eq_one_iff.mp (show d * d = 1 by rw [← pow_two]; exact hd2) with hd1 | hd1
      · rw [hd, hd1, one_smul]
      · exfalso
        have hAX : M⟦A⟧ * M⟦x⟧ = -(M⟦x⟧ * M⟦A⟧) := by rw [hd, hd1, neg_one_smul, neg_neg]
        have hXi : M⟦x⁻¹⟧ * M⟦A⟧ = -(M⟦A⟧ * M⟦x⁻¹⟧) := by
          calc M⟦x⁻¹⟧ * M⟦A⟧ = M⟦x⁻¹⟧ * (M⟦A⟧ * M⟦x⟧) * M⟦x⁻¹⟧ := by
                rw [← Matrix.mul_assoc, Matrix.mul_assoc _ M⟦x⟧, hXXi, Matrix.mul_one]
            _ = -(M⟦A⟧ * M⟦x⁻¹⟧) := by
                rw [hAX, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, hXiX,
                  Matrix.one_mul]
        obtain ⟨v, hvp, hne⟩ := hgpp
        apply hne
        have hw : M⟦x⁻¹⟧ *ᵥ v ∈ Vm := (hanti _ hXi).1 v hvp
        have hvw : v = M⟦x⟧ *ᵥ (M⟦x⁻¹⟧ *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, hXXi, Matrix.one_mulVec]
        have hg : (gp : Matrix (Fin 4) (Fin 4) F) = M⟦yp⟧ := by rw [hyp]
        rw [hvw, Matrix.mulVec_mulVec, hg, ← hxp, ← Matrix.mulVec_mulVec, ← hg,
          hgpm _ hw]
    have hxC : (x : GL (Fin 4) F) ∈ C := ⟨x.2, by
      show (x : GL (Fin 4) F) ∈ Subgroup.centralizer {(A : GL (Fin 4) F)}
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxA)⟩
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    have hk' : (QuotientGroup.mk x : StatedProj (StatedSU 4 3 F)) ^ (2 ^ k) = 1 := by
      rw [hx]
      exact congrArg Subtype.val hk
    have hxn := pow_two_pow_eq_one h hk'
    obtain ⟨ap, hap⟩ := exists_smul_of_commute hp2 hWp hxC (hH'C hgpH) hgp3 hgpp
      (Units.ext (by rw [Units.val_mul, Units.val_mul, ← hyp]; exact hxp)) hxn
    obtain ⟨am, ham⟩ := exists_smul_of_commute hm2 hWm hxC (hH'C hgmH) hgm3 hgmm
      (Units.ext (by rw [Units.val_mul, Units.val_mul, ← hym]; exact hxm)) hxn
    have hap4 := pow_four_eq_one_of_smul h hp2 hsp hap
    have ham4 := pow_four_eq_one_of_smul h hm2 hsm ham
    have hdet : ap ^ 2 * am ^ 2 = 1 := by
      have := det_eq_pow_mul_pow_of_isCompl hc (f := Matrix.toLin' M⟦x⟧)
        (fun v hv => by rw [Matrix.toLin'_apply]; exact hap v hv)
        (fun v hv => by rw [Matrix.toLin'_apply]; exact ham v hv)
      rw [LinearMap.det_toLin', det_eq_one x h, hp2, hm2] at this
      exact this.symm
    have hsq : am ^ 2 = ap ^ 2 := by
      calc am ^ 2 = (ap ^ 2 * am ^ 2) * ap ^ 2 := by
            rw [mul_comm (ap ^ 2), mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl, hap4,
              mul_one]
        _ = ap ^ 2 := by rw [hdet, one_mul]
    have hap0 : ap ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hap4
      exact zero_ne_one hap4
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exfalso
      apply hq1
      rw [← hx]
      refine (mk_eq_one_iff h).mpr ⟨ap, eq_of_mulVec_eq hc (fun v hv => ?_) (fun v hv => ?_)⟩
      · rw [hap v hv, Matrix.smul_mulVec, Matrix.one_mulVec]
      · rw [ham v hv, heq, Matrix.smul_mulVec, Matrix.one_mulVec]
    · exact ⟨ap, hap0, hap, fun v hv => by rw [ham v hv, heq]⟩
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨x₂, hx₂⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨a₁, ha₁0, ha₁p, ha₁m⟩ := hact q₁ hq₁ hq₁1 x₁ hx₁
  obtain ⟨a₂, -, ha₂p, ha₂m⟩ := hact q₂ hq₂ hq₂1 x₂ hx₂
  have hy : (QuotientGroup.mk (x₁⁻¹ * x₂) : StatedProj (StatedSU 4 3 F)) = 1 := by
    refine (mk_eq_one_iff h).mpr ⟨a₁⁻¹ * a₂, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    refine eq_of_mulVec_eq hc (fun v hv => ?_) (fun v hv => ?_)
    · rw [← Matrix.mulVec_mulVec, ha₂p v hv, Matrix.mulVec_smul,
        inv_mulVec_of_mulVec ha₁0 (ha₁p v hv), smul_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, mul_comm]
    · rw [← Matrix.mulVec_mulVec, ha₂m v hv, Matrix.mulVec_smul,
        inv_mulVec_of_mulVec (neg_ne_zero.mpr ha₁0) (ha₁m v hv), smul_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, inv_neg, neg_mul_neg, mul_comm]
  rw [← hx₁, ← hx₂]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_mul_eq_one] at hy
  exact hy

theorem localRank_three_le_two_of {H : Type} [Group H] [Finite H]
    (hB : ∀ s : H, orderOf s = 2 → ∀ R : Subgroup H, R ≤ Subgroup.centralizer {s} →
      ¬ 27 ∣ Nat.card R)
    (hC : ∀ K : Subgroup H, 9 ∣ Nat.card K → ∀ Q : Subgroup H, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer K → Nat.card Q ≤ 2) :
    localRank 3 H ≤ 2 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three H (by change 0 < localRank 3 H; omega)
  change CFSG.Assembly.pRank 3 L = localRank 3 H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ : ∃ E : Subgroup H, E ≤ L ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ CFSG.Assembly.pRank 3 L :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three L
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  have hcomp : Nat.Coprime 3 (Nat.card P) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hr : 3 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set H)) := by omega
  have hVk : 3 ^ (2 + 1) ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨Hs, hHE, hHc, hW⟩ : ∃ Hs : Subgroup H, Hs ≤ E ∧ Nat.card Hs = 3 ^ 2 ∧
      P ⊓ Subgroup.centralizer (Hs : Set H) ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hP
    exact le_bot_iff.mp (CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_sub_le
      (M := ⊥) Nat.prime_three hE hVk hEL hcomp fun Hs hHs hc => (hno Hs hHs hc).le)
  set W := P ⊓ Subgroup.centralizer (Hs : Set H)
  have hW2 : IsPGroup 2 W := hP2.to_le inf_le_left
  have hWc : Nat.card W ≤ 2 := hC Hs (by rw [hHc]; norm_num) W hW2 inf_le_right
  have hWc2 : Nat.card W = 2 := by
    have h1 : Nat.card W ≠ 1 := fun h1 => hW (Subgroup.eq_bot_of_card_eq W h1)
    have h0 : 0 < Nat.card W := Nat.card_pos
    omega
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hW ((Subgroup.eq_bot_iff_forall W).mpr hno)
  have huniq : ∀ y ∈ W, y ≠ 1 → y = w := by
    intro y hy hy1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hWc2
    have e1 := hu ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
    have e2 := hu ⟨w, hwW⟩ (fun h => hw1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hw2 : orderOf w = 2 := by
    have hdvd : orderOf w ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard W hwW
      rwa [hWc2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h1
  have hEw : E ≤ Subgroup.centralizer {w} := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : e * w * e⁻¹ ∈ W := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hEL he) w).mp hwW.1, ?_⟩
      show e * w * e⁻¹ ∈ Subgroup.centralizer (Hs : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hke : k * e = e * k :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨k, hHE hk⟩ ⟨e, he⟩)
      have hkw : k * w = w * k := Subgroup.mem_centralizer_iff.mp hwW.2 k hk
      exact (((show Commute k e from hke).mul_right (show Commute k w from hkw)).mul_right
        (show Commute k e from hke).inv_right).eq
    have hne : e * w * e⁻¹ ≠ 1 := fun h1 => hw1 (by
      rw [mul_inv_eq_one, mul_eq_left] at h1
      exact h1)
    have heq := huniq _ hconj hne
    calc e * w = e * w * e⁻¹ * e := by rw [inv_mul_cancel_right]
      _ = w * e := by rw [heq]
  exact hB w hw2 E hEw (by rw [hEc]; exact pow_dvd_pow 3 hr)

end UnitaryFourThree

open UnitaryFourThree CFSG.LocalAnalysis.ComponentInitial in
theorem localRankThreeU43 : LocalRankThreeU43 := by
  intro F _ _ hF
  have h : UnitaryFieldData 3 1 F := ⟨Nat.prime_three, le_rfl, by rw [hF]; norm_num⟩
  exact localRank_three_le_two_of (fun s hs R hR => not_dvd_card_of_le_centralizer h hs hR)
    (fun K hK Q hQ hQK => card_le_two_of_le_centralizer h hK hQ hQK)

theorem excluded433_twistedA_three_three_of (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.p = 3) (hf : q.exponent = 1) :
    Excluded433 (.lie ⟨.twistedA 3 q, hv⟩) :=
  excluded433_twistedA_three_three localRankThreeU43 q hv hq hf

theorem item433Case_twistedA_of_odd (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p ≠ 2) :
    Item433Case (.lie ⟨.twistedA r q, hv⟩) :=
  item433Case_twistedA_odd localRankThreeU43 r q hv hq

end CFSG.RankThree.PartTwo.Census
