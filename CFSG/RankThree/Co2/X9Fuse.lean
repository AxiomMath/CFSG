module

public import CFSG.RankThree.Co2.Dist
public import CFSG.RankThree.Co2.X9FuseCert
public import CFSG.RankThree.Co2.Fusion2

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem inA_iff {c : ℕ} : inA c = true ↔ c ∈ ({0, 2, 7} : Finset ℕ) := by
  simp only [inA, Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton, or_assoc]

theorem inB_iff {c : ℕ} : inB c = true ↔ c ∈ ({1, 3, 5} : Finset ℕ) := by
  simp only [inB, Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton, or_assoc]

theorem inC_iff {c : ℕ} : inC c = true ↔ c ∈ ({4, 6, 8} : Finset ℕ) := by
  simp only [inC, Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton, or_assoc]

theorem pWords3_letters : ∀ k < pWords3.size, ∀ l ∈ pWords3[k]!, l < 42 := by
  decide +kernel

theorem mem_matGrp3_iff {m : Matrix (Fin 22) (Fin 22) (ZMod 2)} :
    m ∈ matGrp pWords3 ↔ ∃ y ∈ subW pWords3, crMat y = m := by
  constructor
  · intro hm
    obtain ⟨y, hy, e⟩ := Submonoid.mem_map.1 (matGrp_le_map pWords3_letters hm)
    exact ⟨y, hy, e⟩
  · rintro ⟨y, hy, rfl⟩
    exact map_subW_le pWords3_letters (Submonoid.mem_map.2 ⟨y, hy, rfl⟩)

theorem isConj_conj_right {G : Type} [Group G] (a x y : G) :
    IsConj a (y * x * y⁻¹) ↔ IsConj a x := by
  have hx : IsConj x (y * x * y⁻¹) := isConj_iff.2 ⟨y, rfl⟩
  exact ⟨fun h' => h'.trans hx.symm, fun h' => h'.trans hx⟩

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem rG_ne_one {c : ℕ} (hc : c < 10) : h.rG c ≠ 1 := by
  intro e
  apply rep_ne_one hc
  have : h.φ.symm (rep c) = 1 := Subtype.ext e
  exact (MulEquiv.map_eq_one_iff h.φ.symm).1 this

theorem isConj_rG_self {c : ℕ} : IsConj (h.φ (h.φ.symm (rep c))) (rep c) := by
  rw [MulEquiv.apply_symm_apply]

theorem isConj_z_rG_iff {c : ℕ} (hc : c < 10) : IsConj h.z (h.rG c) ↔ inA c = true := by
  constructor
  · intro hz
    by_contra hA
    have hbad : BadClass c ∨ c = 9 := by
      simp only [inA, Bool.or_eq_true, beq_iff_eq, not_or] at hA
      unfold BadClass
      omega
    rcases hbad with hb | rfl
    · exact h.not_isConj_rep_of_bad hz hb h.isConj_rG_self
    · exact h.not_isConj_rep_nine hz h.isConj_rG_self
  · intro hA
    have h27 := h.fusesTwo_and_fusesSeven
    simp only [inA, Bool.or_eq_true, beq_iff_eq] at hA
    rcases hA with (rfl | rfl) | rfl
    · exact (congrArg (IsConj h.z) h.rG_zero).mpr (IsConj.refl _)
    · exact h27.1
    · exact h27.2

theorem isConj_rG_of_inB {c : ℕ} (hB : inB c = true) : IsConj (h.rG 1) (h.rG c) := by
  have h135 := h.fuse_one_three_five
  simp only [inB, Bool.or_eq_true, beq_iff_eq] at hB
  rcases hB with (rfl | rfl) | rfl
  · exact IsConj.refl _
  · exact h135.1
  · exact h135.2

theorem isConj_rG_of_inC {c : ℕ} (hC : inC c = true) : IsConj (h.rG 8) (h.rG c) := by
  have h468 := h.fuse_eight_four_six
  simp only [inC, Bool.or_eq_true, beq_iff_eq] at hC
  rcases hC with (rfl | rfl) | rfl
  · exact h468.1
  · exact h468.2
  · exact IsConj.refl _

theorem not_isConj_z_one : ¬ IsConj h.z (h.rG 1) := by
  rw [h.isConj_z_rG_iff (by norm_num)]
  decide

theorem not_isConj_z_eight : ¬ IsConj h.z (h.rG 8) := by
  rw [h.isConj_z_rG_iff (by norm_num)]
  decide

theorem not_isConj_one_eight : ¬ IsConj (h.rG 1) (h.rG 8) := fun h18 =>
  h.not_isConj_one_four (h18.trans (h.isConj_rG_of_inC (c := 4) (by decide)))

theorem classes_cover {c : ℕ} (hc : c < 10) (hc9 : c ≠ 9) :
    inA c = true ∨ inB c = true ∨ inC c = true := by
  simp only [inA, inB, inC, Bool.or_eq_true, beq_iff_eq]
  omega

theorem isConj_rG_one_iff {c : ℕ} (hc : c < 10) (hc9 : c ≠ 9) :
    IsConj (h.rG 1) (h.rG c) ↔ inB c = true := by
  refine ⟨fun h1 => ?_, h.isConj_rG_of_inB⟩
  rcases classes_cover hc hc9 with hA | hB | hC
  · exact absurd ((h.isConj_z_rG_iff hc).2 hA |>.trans h1.symm) h.not_isConj_z_one
  · exact hB
  · exact absurd (h1.trans (h.isConj_rG_of_inC hC).symm) h.not_isConj_one_eight

theorem isConj_rG_eight_iff {c : ℕ} (hc : c < 10) (hc9 : c ≠ 9) :
    IsConj (h.rG 8) (h.rG c) ↔ inC c = true := by
  refine ⟨fun h8 => ?_, h.isConj_rG_of_inC⟩
  rcases classes_cover hc hc9 with hA | hB | hC
  · exact absurd ((h.isConj_z_rG_iff hc).2 hA |>.trans h8.symm) h.not_isConj_z_eight
  · exact absurd ((h.isConj_rG_of_inB hB).trans h8.symm) h.not_isConj_one_eight
  · exact hC

@[expose] def ClassPred (L : G → Prop) (S : Finset ℕ) : Prop :=
  (∀ a b : G, IsConj a b → (L a ↔ L b)) ∧ (∀ c < 10, (L (h.rG c) ↔ c ∈ S)) ∧
    (∀ g, L g → g * g = 1 ∧ g ≠ 1) ∧ ∀ c ∈ S, c < 10

theorem classPred_isConj {a : G} {S : Finset ℕ} (ha2 : a * a = 1) (ha : a ≠ 1)
    (hS : ∀ c < 10, (IsConj a (h.rG c) ↔ c ∈ S)) (hS10 : ∀ c ∈ S, c < 10) :
    h.ClassPred (IsConj a) S := by
  refine ⟨fun _ _ hbc => ⟨fun h' => h'.trans hbc, fun h' => h'.trans hbc.symm⟩, hS,
    fun g hg => ⟨?_, fun e => ha (isConj_one_left.1 (e ▸ hg))⟩, hS10⟩
  obtain ⟨c, rfl⟩ := isConj_iff.1 hg
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [ha2]; group

theorem rG_mul_self {c : ℕ} (hc : c < 10) :
    h.rG c * h.rG c = 1 := by
  have e : h.φ.symm (rep c) * h.φ.symm (rep c) = 1 := by
    rw [← map_mul, rep_mul_self hc, map_one]
  exact congrArg Subtype.val e

theorem classPred_iff {L : G → Prop} {S : Finset ℕ} (hL : h.ClassPred L S) (y : Cr) :
    L ((h.φ.symm y : h.H) : G) ↔ InCls S (crMat y) := by
  constructor
  · intro hy
    obtain ⟨hsq, hne⟩ := hL.2.2.1 _ hy
    have e2 : y * y = 1 := by
      apply h.φ.symm.injective
      apply Subtype.ext
      rw [map_mul, map_one]
      exact hsq
    have e1 : y ≠ 1 := by
      intro e
      apply hne
      rw [e, map_one]
      rfl
    obtain ⟨c, hc, hyc⟩ := exists_isConj_rep y e2 e1
    have hcy : IsConj (h.rG c) ((h.φ.symm y : h.H) : G) := h.isConj_φ_symm hyc.symm
    exact ⟨c, (hL.2.1 c hc).1 ((hL.1 _ _ hcy).2 hy), (isConj_iff_crConj hc).1 hyc.symm⟩
  · rintro ⟨c, hcS, hc⟩
    have hc10 := hL.2.2.2 c hcS
    exact (hL.1 _ _ (h.isConj_φ_symm ((isConj_iff_crConj hc10).2 hc))).1 ((hL.2.1 c hc10).2 hcS)

@[expose] def liftEquiv (S : Subgroup Cr) : S ≃ h.liftG S where
  toFun y := ⟨(h.φ.symm y : G), h.φ_symm_mem_liftG y.2⟩
  invFun x := ⟨h.φ ⟨x, (h.mem_liftG.1 x.2).1⟩, (h.mem_liftG.1 x.2).2⟩
  left_inv y := Subtype.ext (h.φ.apply_symm_apply _)
  right_inv x := by
    apply Subtype.ext
    change ((h.φ.symm (h.φ ⟨x, (h.mem_liftG.1 x.2).1⟩) : h.H) : G) = x
    rw [MulEquiv.symm_apply_apply]

theorem card_triple {L₁ L₂ L₃ : G → Prop} {S₁ S₂ S₃ : Finset ℕ} (h₁ : h.ClassPred L₁ S₁)
    (h₂ : h.ClassPred L₂ S₂) (h₃ : h.ClassPred L₃ S₃) :
    Nat.card {x : h.liftG (subW pWords3) // L₁ x ∧ L₂ (x * h.z) ∧ L₃ (x * h.rG 2)} =
      fuseN S₁ S₂ S₃ := by
  have e : Nat.card {x : h.liftG (subW pWords3) // L₁ x ∧ L₂ (x * h.z) ∧ L₃ (x * h.rG 2)} =
      Nat.card {y : subW pWords3 // L₁ (h.φ.symm y : G) ∧ L₂ ((h.φ.symm y : G) * h.z) ∧
        L₃ ((h.φ.symm y : G) * h.rG 2)} :=
    (Nat.card_congr ((h.liftEquiv _).subtypeEquiv fun _ => Iff.rfl)).symm
  have key : ∀ y : Cr, (L₁ ((h.φ.symm y : h.H) : G) ∧ L₂ (((h.φ.symm y : h.H) : G) * h.z) ∧
      L₃ (((h.φ.symm y : h.H) : G) * h.rG 2)) ↔
      (InCls S₁ (crMat y) ∧ InCls S₂ (crMat y * repMat 0) ∧ InCls S₃ (crMat y * repMat 2)) := by
    intro y
    have ez : ((h.φ.symm y : h.H) : G) * h.z = ((h.φ.symm (y * rCr) : h.H) : G) := by
      rw [map_mul, h.φ_symm_rCr]
      rfl
    have e2 : ((h.φ.symm y : h.H) : G) * h.rG 2 = ((h.φ.symm (y * rep 2) : h.H) : G) := by
      rw [map_mul]
      rfl
    have mz : crMat y * repMat 0 = crMat (y * rCr) := by
      rw [map_mul, ← rep_zero, crMat_rep (i := 0) (by norm_num)]
    have m2 : crMat y * repMat 2 = crMat (y * rep 2) := by
      rw [map_mul, crMat_rep (i := 2) (by norm_num)]
    rw [ez, e2, mz, m2, h.classPred_iff h₁, h.classPred_iff h₂, h.classPred_iff h₃]
  rw [e]
  unfold fuseN
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨crMat y.1.1, mem_matGrp3_iff.2 ⟨y.1.1, y.1.2, rfl⟩, (key y.1.1).1 y.2⟩) ⟨?_, ?_⟩)
  · intro a b e
    exact Subtype.ext (Subtype.ext (crMat_injective (congrArg Subtype.val e)))
  · rintro ⟨x, hx, hP⟩
    have hx' : ∃ y ∈ subW pWords3, crMat y = x := mem_matGrp3_iff.1 hx
    obtain ⟨y, hy, e⟩ := hx'
    refine ⟨⟨⟨y, hy⟩, (key y).2 ?_⟩, Subtype.ext e⟩
    rw [e]
    exact hP

theorem card_triple' {L₁ L₂ L₃ : G → Prop} {S₁ S₂ S₃ : Finset ℕ} (h₁ : h.ClassPred L₁ S₁)
    (h₂ : h.ClassPred L₂ S₂) (h₃ : h.ClassPred L₃ S₃) :
    Nat.card {x : h.liftG (subW pWords3) // L₁ x ∧ L₂ (x * h.rG 2) ∧ L₃ (x * h.z)} =
      fuseN S₁ S₃ S₂ :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩)).trans
    (h.card_triple h₁ h₃ h₂)

theorem exists_swap : ∃ y : G, y * h.z * y⁻¹ = h.rG 2 ∧ y * h.rG 2 * y⁻¹ = h.z := by
  have ht : IsConj h.z (h.rG 2) := h.fusesTwo_and_fusesSeven.1
  have htz : h.φ.symm (rep 2) ≠ h.zG := by
    intro e
    have e' := congrArg h.φ e
    rw [MulEquiv.apply_symm_apply, h.φ_zG] at e'
    exact not_isConj_rCr_rep (i := 2) (by norm_num) (by decide) (by rw [e'])
  obtain ⟨s, hs, -, Ψ, h1, h2, c, hc1, hc2, -⟩ := h.exists_partner ht htz
  obtain ⟨hs2, hs1⟩ := h.φ_invol hs
  obtain ⟨j, hj, hsj⟩ := exists_isConj_rep (h.φ s) hs2 hs1
  have hp : PartnerPair 2 j :=
    PartnerElts.of_conj ⟨Ψ, h1, h2⟩ (by rw [MulEquiv.apply_symm_apply]) hsj
  obtain rfl : j = 2 := by
    have := classSizes_eq_of_partnerPair (by norm_num) hj hp
    have hj23 : j = 2 ∨ j = 3 := by
      interval_cases j <;> first | (left; rfl) | (right; rfl) | (simp [classSizes] at this)
    rcases hj23 with h' | rfl
    · exact h'
    · exact absurd (PartnerElts.symm hp) (not_partnerPair (Or.inr (Or.inl rfl)) (by norm_num))
  obtain ⟨g, hg⟩ := isConj_iff.1 hsj.symm
  have hs' : (s : G) = (h.φ.symm g : G) * h.rG 2 * (h.φ.symm g : G)⁻¹ := by
    have : s = h.φ.symm g * h.φ.symm (rep 2) * (h.φ.symm g)⁻¹ := by
      apply h.φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hg]
    rw [this]
    rfl
  have hhz : (h.φ.symm g : G) * h.z = h.z * (h.φ.symm g : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm g).2
  refine ⟨(h.φ.symm g : G)⁻¹ * c⁻¹, ?_, ?_⟩
  · calc (h.φ.symm g : G)⁻¹ * c⁻¹ * h.z * ((h.φ.symm g : G)⁻¹ * c⁻¹)⁻¹ =
        (h.φ.symm g : G)⁻¹ * (c⁻¹ * h.z * c) * (h.φ.symm g : G) := by group
      _ = (h.φ.symm g : G)⁻¹ * ((h.φ.symm g : G) * h.rG 2 * (h.φ.symm g : G)⁻¹) *
          (h.φ.symm g : G) := by rw [← hc2, hs']
      _ = h.rG 2 := by group
  · have hct : c⁻¹ * h.rG 2 * c = h.z := by
      rw [show h.rG 2 = c * h.z * c⁻¹ from hc1.symm]
      group
    calc (h.φ.symm g : G)⁻¹ * c⁻¹ * h.rG 2 * ((h.φ.symm g : G)⁻¹ * c⁻¹)⁻¹ =
        (h.φ.symm g : G)⁻¹ * (c⁻¹ * h.rG 2 * c) * (h.φ.symm g : G) := by group
      _ = (h.φ.symm g : G)⁻¹ * (h.z * (h.φ.symm g : G)) := by rw [hct, mul_assoc]
      _ = h.z := by rw [← hhz]; group

theorem le_inf_C2 :
    h.liftG (subW pWords3) ≤ Subgroup.centralizer {h.z} ⊓ Subgroup.centralizer {h.rG 2} := by
  rw [h.inf_centralizer (rep 2)]
  intro g hg
  obtain ⟨hgH, hgS⟩ := h.mem_liftG.1 hg
  exact h.mem_liftG.2 ⟨hgH, sylLe3 (by simp) hgS⟩

theorem card_inf_C2 :
    Nat.card ↥(Subgroup.centralizer {h.z} ⊓ Subgroup.centralizer {h.rG 2}) = 589824 := by
  rw [h.inf_centralizer (rep 2), card_liftG]
  exact card_C 2 (by norm_num) (m := 589824) (by decide) (classSizes_pos (by norm_num))

theorem exists_swap_Q : ∃ y : G, y * h.z * y⁻¹ = h.rG 2 ∧ y * h.rG 2 * y⁻¹ = h.z ∧
    (h.liftG (subW pWords3)).map (MulAut.conj y).toMonoidHom = h.liftG (subW pWords3) := by
  haveI := h.finite
  obtain ⟨y, hy1, hy2⟩ := h.exists_swap
  refine exists_swap_normalizing (p := 2) hy1 hy2 h.le_inf_C2 ?_
  rw [h.card_inf_C2, factorization_two_eq (by norm_num : 589824 = 2 ^ 16 * 9) (by decide),
    card_liftG, sylCard3]

theorem isConj_eight_nine : IsConj (h.rG 8) (h.rG 9) := by
  haveI := h.finite
  obtain ⟨y, hy1, hy2, hyQ⟩ := h.exists_swap_Q
  have hA : h.ClassPred (IsConj h.z) {0, 2, 7} :=
    h.classPred_isConj (h.sq_eq_one_of_isConj_z (IsConj.refl _))
      (h.ne_one_of_isConj_z (IsConj.refl _))
      (fun c hc => (h.isConj_z_rG_iff hc).trans inA_iff) (by decide)
  by_contra h89
  have hC : h.ClassPred (IsConj (h.rG 8)) {4, 6, 8} := by
    refine h.classPred_isConj (h.rG_mul_self (by norm_num)) (h.rG_ne_one (by norm_num))
      (fun c hc => ?_) (by decide)
    by_cases hc9 : c = 9
    · subst hc9
      exact iff_of_false h89 (by decide)
    · exact (h.isConj_rG_eight_iff hc hc9).trans inC_iff
  by_cases h19 : IsConj (h.rG 1) (h.rG 9)
  · have hB : h.ClassPred (IsConj (h.rG 1)) {1, 3, 5, 9} := by
      refine h.classPred_isConj (h.rG_mul_self (by norm_num)) (h.rG_ne_one (by norm_num))
        (fun c hc => ?_) (by decide)
      by_cases hc9 : c = 9
      · subst hc9
        exact iff_of_true h19 (by decide)
      · rw [h.isConj_rG_one_iff hc hc9, inB_iff]
        simp [hc9]
    have hs := card_swap_eq hy1 hy2 hyQ (IsConj h.z) (IsConj (h.rG 8)) (IsConj (h.rG 1))
      (isConj_conj_right _ · y) (isConj_conj_right _ · y) (isConj_conj_right _ · y)
    have h68 := (h.card_triple hA hC hB).symm.trans (hs.trans (h.card_triple' hA hC hB))
    exact absurd (fuseCounts_cert.2.2.1.symm.trans (h68.trans fuseCounts_cert.2.2.2))
      (by norm_num)
  · have h9 : h.ClassPred (IsConj (h.rG 9)) {9} := by
      refine h.classPred_isConj (h.rG_mul_self (by norm_num)) (h.rG_ne_one (by norm_num))
        (fun c hc => ?_) (by decide)
      by_cases hc9 : c = 9
      · subst hc9
        exact iff_of_true (IsConj.refl _) (by decide)
      · refine iff_of_false (fun h9c => ?_) (by simpa using hc9)
        rcases classes_cover hc hc9 with hA' | hB | hC'
        · exact absurd (((h.isConj_z_rG_iff hc).2 hA').trans h9c.symm)
            (by rw [h.isConj_z_rG_iff (by norm_num)]; decide)
        · exact h19 ((h.isConj_rG_of_inB hB).trans h9c.symm)
        · exact h89 ((h.isConj_rG_of_inC hC').trans h9c.symm)
    have hs := card_swap_eq hy1 hy2 hyQ (IsConj h.z) (IsConj (h.rG 8)) (IsConj (h.rG 9))
      (isConj_conj_right _ · y) (isConj_conj_right _ · y) (isConj_conj_right _ · y)
    have h32 := (h.card_triple hA hC h9).symm.trans (hs.trans (h.card_triple' hA hC h9))
    exact absurd (fuseCounts_cert.1.symm.trans (h32.trans fuseCounts_cert.2.1)) (by norm_num)

end Co2CentHyp

end CFSG.RankThree.Co2
