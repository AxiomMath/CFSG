module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUNormal
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUDict
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoClassical.URigid

private theorem nine3_isUnitaryTransvectionIn_conj {m n : ℕ} {F : Type} [Field F]
    {x : StatedProj (StatedSU m (2 ^ n) F)} (hx : IsUnitaryTransvectionIn m n x)
    (y : StatedProj (StatedSU m (2 ^ n) F)) :
    IsUnitaryTransvectionIn m n (y * x * y⁻¹) := by
  obtain ⟨g, hg, hr⟩ := hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨h * g * h⁻¹, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg]
  · have hcoe : (((h * g * h⁻¹ : StatedSU m (2 ^ n) F) : GL (Fin m) F) :
        Matrix (Fin m) (Fin m) F) =
        ((h : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv]
    rw [hcoe]
    have hdet : IsUnit (((h : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (h : GL (Fin m) F).isUnit
    have hdet' : IsUnit (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (h⁻¹ : GL (Fin m) F).isUnit
    have hmul : ((h : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hsub : ((h : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) *
          (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) =
        ((h : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
            ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
            (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) - 1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hmul]
    rw [← hsub, Matrix.mul_assoc,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet,
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet']
    exact hr

private theorem nine3_isUnitaryTransvectionIn_of_conj {m n : ℕ} {F : Type} [Field F]
    {c x : StatedProj (StatedSU m (2 ^ n) F)} (hc : IsUnitaryTransvectionIn m n c)
    (hcx : IsConj c x) : IsUnitaryTransvectionIn m n x := by
  obtain ⟨y, hy⟩ := isConj_iff.mp hcx
  rw [← hy]
  exact nine3_isUnitaryTransvectionIn_conj hc y

private theorem nine3_isotropize {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {a y : Fin m → F} (ha : hform h.bar a a = 0)
    (hay : hform h.bar a y = 1) :
    ∃ c : F, hform h.bar (y + c • a) (y + c • a) = 0 := by
  have hfix : h.bar (-hform h.bar y y) = -hform h.bar y y := by
    rw [map_neg, (hform_comm h.bar_bar y y).symm]
  obtain ⟨z, hz⟩ := h.traceLin_surjective ⟨-hform h.bar y y, h.mem_fixedField.mpr hfix⟩
  have hz' : z + h.bar z = -hform h.bar y y := congrArg Subtype.val hz
  refine ⟨z, ?_⟩
  have hya : hform h.bar y a = 1 := by rw [hform_comm h.bar_bar a y, hay, map_one]
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, ha, hay, hya,
    mul_zero, mul_one, add_zero]
  linear_combination hz'

private theorem nine3_exists_partner {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {a : Fin m → F} (ha0 : a ≠ 0)
    (ha : hform h.bar a a = 0) :
    ∃ f, hform h.bar f f = 0 ∧ hform h.bar a f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, hform h.bar a y ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact ha0 (eq_zero_of_hform_right (σ := h.bar) h.bar_bar hcon)
  have hy1 : hform h.bar a ((hform h.bar a y)⁻¹ • y) = 1 := by
    rw [hform_smul_right, inv_mul_cancel₀ hy]
  obtain ⟨c, hc⟩ := nine3_isotropize h ha hy1
  exact ⟨(hform h.bar a y)⁻¹ • y + c • a, hc, by
    rw [hform_add_right, hy1, hform_smul_right, ha, mul_zero, add_zero]⟩

private theorem nine3_sq_one {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {u : Fin m → F} (huu : hform h.bar u u = 0)
    {b : F} {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) : N * N = 1 := by
  apply mul_self_eq_one_of_val hN
  haveI := h.charP
  have hW2 : vecMulVec u (h.bar ∘ u) * vecMulVec u (h.bar ∘ u) = 0 :=
    vecMulVec_mul_self h huu
  have hbW2 : (b • vecMulVec u (h.bar ∘ u)) * (b • vecMulVec u (h.bar ∘ u)) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hW2, smul_zero, smul_zero]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hbW2, add_zero,
    add_assoc, ← two_smul F (b • vecMulVec u (h.bar ∘ u)), CharTwo.two_eq_zero, zero_smul,
    add_zero]

private theorem nine3_vecMulVec_mul_eq {m n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) (u v : Fin m → F) :
    vecMulVec u (h.bar ∘ u) * vecMulVec v (h.bar ∘ v) =
      hform h.bar u v • vecMulVec u (h.bar ∘ v) := by
  rw [vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  rfl

private theorem nine3_one_add_mulVec {m n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) {u v : Fin m → F} (b : F) :
    (1 + b • vecMulVec u (h.bar ∘ u)) *ᵥ v = v + (b * hform h.bar u v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec', smul_smul]
  rfl

private theorem nine3_transvection_comm_of_orth {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {u v : Fin m → F} (huv : hform h.bar u v = 0) (b c : F)
    {Nu Nv : StatedSU m (2 ^ n) F}
    (hNu : (Nu : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u))
    (hNv : (Nv : GL (Fin m) F).val = 1 + c • vecMulVec v (h.bar ∘ v)) :
    Nu * Nv = Nv * Nu := by
  apply Subtype.ext
  apply Units.ext
  change (Nu : GL (Fin m) F).val * (Nv : GL (Fin m) F).val =
    (Nv : GL (Fin m) F).val * (Nu : GL (Fin m) F).val
  rw [hNu, hNv]
  have huv' : hform h.bar v u = 0 := by rw [hform_comm h.bar_bar u v, huv, map_zero]
  have hWuv : vecMulVec u (h.bar ∘ u) * vecMulVec v (h.bar ∘ v) = 0 := by
    rw [nine3_vecMulVec_mul_eq h u v, huv, zero_smul]
  have hWvu : vecMulVec v (h.bar ∘ v) * vecMulVec u (h.bar ∘ u) = 0 := by
    rw [nine3_vecMulVec_mul_eq h v u, huv', zero_smul]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, hWuv, hWvu, smul_zero, add_zero]
  abel

private theorem nine3_exists_iso_orth {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {p q s : Fin m → F}
    (hp : hform h.bar p p = 0) (hq : hform h.bar q q = 0) (hs : hform h.bar s s = 0)
    (hpq : hform h.bar p q ≠ 0) (hsp : hform h.bar s p = 0) (hsq : hform h.bar s q = 0)
    (hs0 : s ≠ 0) :
    ∃ s', hform h.bar s' s' = 0 ∧ hform h.bar p s' = 0 ∧ hform h.bar q s' = 0 ∧
      hform h.bar s s' = 1 := by
  obtain ⟨f, hff, hsf⟩ := nine3_exists_partner h hs0 hs
  have hqp : hform h.bar q p ≠ 0 := by
    intro h0
    have h0' : h.bar (hform h.bar p q) = 0 := by
      rw [← hform_comm h.bar_bar p q]
      exact h0
    exact hpq (h.bar_eq_zero_iff.mp h0')
  set α : F := hform h.bar q f / hform h.bar q p with hα
  set β : F := hform h.bar p f / hform h.bar p q with hβ
  set w : Fin m → F := f - α • p - β • q with hw
  have hps : hform h.bar p s = 0 := by rw [hform_comm h.bar_bar s p, hsp, map_zero]
  have hqs : hform h.bar q s = 0 := by rw [hform_comm h.bar_bar s q, hsq, map_zero]
  have hpw : hform h.bar p w = 0 := by
    rw [hw, hform_sub_right, hform_sub_right, hform_smul_right, hform_smul_right, hp, hβ]
    field_simp
    ring
  have hqw : hform h.bar q w = 0 := by
    rw [hw, hform_sub_right, hform_sub_right, hform_smul_right, hform_smul_right, hq, hα]
    field_simp
    ring
  have hsw : hform h.bar s w = 1 := by
    rw [hw, hform_sub_right, hform_sub_right, hform_smul_right, hform_smul_right, hsp, hsq,
      mul_zero, mul_zero, sub_zero, sub_zero]
    exact hsf
  obtain ⟨γ, hγ⟩ := nine3_isotropize h hs hsw
  refine ⟨w + γ • s, hγ, ?_, ?_, ?_⟩
  · rw [hform_add_right, hpw, hform_smul_right, hps, mul_zero, add_zero]
  · rw [hform_add_right, hqw, hform_smul_right, hqs, mul_zero, add_zero]
  · rw [hform_add_right, hsw, hform_smul_right, hs, mul_zero, add_zero]

private theorem nine3_three_le_of_centres {m n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {p q s : Fin m → F}
    (hp : hform h.bar p p = 0) (hq : hform h.bar q q = 0) (hs : hform h.bar s s = 0)
    (hpq : hform h.bar p q ≠ 0) (hsp : hform h.bar s p = 0) (hsq : hform h.bar s q = 0)
    (hs0 : s ≠ 0) : 3 ≤ m := by
  have hqp : hform h.bar q p ≠ 0 := by
    intro h0
    exact hpq (h.bar_eq_zero_iff.mp (by rw [← hform_comm h.bar_bar p q]; exact h0))
  have hli : LinearIndependent F ![p, q, s] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_three] at hg
    have hg0 : g 0 = 0 := by
      have h1 := congrArg (fun w => hform h.bar w q) hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, hform_add_left, hform_smul_left, hform_zero_left,
        hq, hsq, mul_zero, add_zero] at h1
      exact h.bar_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_right hpq)
    have hg1 : g 1 = 0 := by
      have h1 := congrArg (fun w => hform h.bar w p) hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, hform_add_left, hform_smul_left, hform_zero_left,
        hp, hsp, mul_zero, zero_add, add_zero] at h1
      exact h.bar_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_right hqp)
    have hg2 : g 2 = 0 := by
      have h1 : g 2 • s = 0 := by simpa [hg0, hg1] using hg
      exact (smul_eq_zero.mp h1).resolve_right hs0
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hcard := hli.fintype_card_le_finrank
  simpa using hcard

theorem nine3_prop710_unitary_geom {m n : ℕ} {F : Type} [Field F] [Finite F]
    (hU : UnitaryFieldData 2 n F)
    {c a e a' v : StatedProj (StatedSU m (2 ^ n) F)} (hc : IsUnitaryTransvectionIn m n c)
    (hcfg : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  haveI := hU.charP
  obtain ⟨a₀, c₀, N₀, ha₀0, ha₀iso, hc₀0, hc₀bar, hN₀, hmk₀⟩ :=
    borel86_un_exists_eq_mk hU hc
  obtain ⟨p, bp, Na, hp0, hpiso, hbp0, _hbpbar, hNa, hmka⟩ :=
    borel86_un_exists_eq_mk hU (nine3_isUnitaryTransvectionIn_of_conj hc hcfg.conj_a)
  obtain ⟨q, be, Ne, hq0, hqiso, hbe0, _hbebar, hNe, hmke⟩ :=
    borel86_un_exists_eq_mk hU (nine3_isUnitaryTransvectionIn_of_conj hc hcfg.conj_e)
  obtain ⟨s, bv, Nv, hs0, hsiso, hbv0, _hbvbar, hNv, hmkv⟩ :=
    borel86_un_exists_eq_mk hU (nine3_isUnitaryTransvectionIn_of_conj hc hcfg.conj_v)
  have hpq : hform hU.bar p q ≠ 0 := by
    intro h0
    refine hcfg.not_comm_ae ?_
    have hcomm := nine3_transvection_comm_of_orth hU h0 bp be hNa hNe
    have h1 : (QuotientGroup.mk (Na * Ne) : StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk (Ne * Na) := congrArg QuotientGroup.mk hcomm
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hmka, hmke] at h1
    exact h1
  have hNv2 : Nv * Nv = 1 := nine3_sq_one hU hsiso hNv
  have hsp : hform hU.bar s p = 0 := by
    have hcomm : (QuotientGroup.mk Nv * QuotientGroup.mk Na :
        StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk Na * QuotientGroup.mk Nv := by
      rw [hmkv, hmka]
      exact hcfg.comm_va
    have hact := (borel86_ud_commute_iff hU hNv2 hp0 hpiso hbp0 hNa).mp hcomm
    have h2 := nine3_one_add_mulVec hU (u := s) (v := p) bv
    rw [hNv, h2] at hact
    have hzero : (bv * hform hU.bar s p) • s = 0 := by
      exact add_left_cancel (by rw [hact, add_zero])
    rcases smul_eq_zero.mp hzero with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hbv0
      · exact h4
    · exact absurd h3 hs0
  have hsq : hform hU.bar s q = 0 := by
    have hcomm : (QuotientGroup.mk Nv * QuotientGroup.mk Ne :
        StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk Ne * QuotientGroup.mk Nv := by
      rw [hmkv, hmke]
      exact hcfg.comm_ve
    have hact := (borel86_ud_commute_iff hU hNv2 hq0 hqiso hbe0 hNe).mp hcomm
    have h2 := nine3_one_add_mulVec hU (u := s) (v := q) bv
    rw [hNv, h2] at hact
    have hzero : (bv * hform hU.bar s q) • s = 0 := by
      exact add_left_cancel (by rw [hact, add_zero])
    rcases smul_eq_zero.mp hzero with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hbv0
      · exact h4
    · exact absurd h3 hs0
  have hm : 3 ≤ m := nine3_three_le_of_centres hU hpiso hqiso hsiso hpq hsp hsq hs0
  obtain ⟨s', hs'iso, hps', hqs', hss'⟩ :=
    nine3_exists_iso_orth hU hpiso hqiso hsiso hpq hsp hsq hs0
  have hs'p : hform hU.bar s' p = 0 := by
    rw [hform_comm hU.bar_bar p s', hps', map_zero]
  have hs'q : hform hU.bar s' q = 0 := by
    rw [hform_comm hU.bar_bar q s', hqs', map_zero]
  have hs's : hform hU.bar s' s = 1 := by
    rw [hform_comm hU.bar_bar s s', hss', map_one]
  have hs'0 : s' ≠ 0 := by
    intro h0
    rw [h0, hform_zero_right] at hss'
    exact one_ne_zero hss'.symm
  obtain ⟨Nd, hNd⟩ := exists_one_add_mem hU hs'iso hc₀bar
  have hNd2 : Nd * Nd = 1 := nine3_sq_one hU hs'iso hNd
  have hNd_p : (Nd : GL (Fin m) F).val *ᵥ p = p := by
    rw [hNd, nine3_one_add_mulVec hU (u := s') (v := p) c₀, hs'p, mul_zero, zero_smul, add_zero]
  have hNd_q : (Nd : GL (Fin m) F).val *ᵥ q = q := by
    rw [hNd, nine3_one_add_mulVec hU (u := s') (v := q) c₀, hs'q, mul_zero, zero_smul, add_zero]
  have hNd_s : (Nd : GL (Fin m) F).val *ᵥ s ≠ s := by
    rw [hNd, nine3_one_add_mulVec hU (u := s') (v := s) c₀, hs's, mul_one]
    intro h0
    have : c₀ • s' = 0 := by
      have := congrArg (fun v => v - s) h0
      simpa using this
    exact hs'0 ((smul_eq_zero.mp this).resolve_left hc₀0)
  refine ⟨QuotientGroup.mk Nd, ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := borel86_un_exists_conj hU hm ha₀0 ha₀iso hs'0 hs'iso hc₀0 hc₀bar
      hc₀0 hc₀bar hN₀ hNd
    refine isConj_iff.mpr ⟨QuotientGroup.mk S, ?_⟩
    rw [← hmk₀, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hS]
  · intro hEq
    have hcomm : (QuotientGroup.mk Nd * QuotientGroup.mk Nv :
        StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk Nv * QuotientGroup.mk Nd := by
      rw [hEq, hmkv]
    have hact := (borel86_ud_commute_iff hU hNd2 hs0 hsiso hbv0 hNv).mp hcomm
    exact hNd_s hact
  · have hcomm : (QuotientGroup.mk Nd * QuotientGroup.mk Na :
        StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk Na * QuotientGroup.mk Nd :=
      (borel86_ud_commute_iff hU hNd2 hp0 hpiso hbp0 hNa).mpr hNd_p
    rw [← hmka]
    exact hcomm
  · have hcomm : (QuotientGroup.mk Nd * QuotientGroup.mk Ne :
        StatedProj (StatedSU m (2 ^ n) F)) =
        QuotientGroup.mk Ne * QuotientGroup.mk Nd :=
      (borel86_ud_commute_iff hU hNd2 hq0 hqiso hbe0 hNe).mpr hNd_q
    rw [← hmke]
    exact hcomm

end CFSG.LocalAnalysis.WeakClosure81
