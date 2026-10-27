module

public import Certificates.Kernel.Co2Census.S0
public import Certificates.Kernel.Co2Census.S0CK

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.KC.Co2InvS CFSG.KC.Co2Census

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev centS0 (s : K) : Set K := {y | y ∈ S0 ∧ y * s = s * y}

theorem ncard_centS0_mul
    {s : K} (hs : s ∈ S0) :
    (centS0 s).ncard * {y | ∃ w ∈ S0, y = w * s * w⁻¹}.ncard = 1451520 := by
  classical
  have h1 : Nat.card (Subgroup.centralizer {(⟨s, hs⟩ : S0)}) *
      (Subgroup.centralizer {(⟨s, hs⟩ : S0)}).index = 1451520 := by
    rw [Subgroup.card_mul_index, card_S0]
  have hidx : (Subgroup.centralizer {(⟨s, hs⟩ : S0)}).index =
      (MulAction.orbit (ConjAct S0) (⟨s, hs⟩ : S0)).ncard := by
    have hsurj : Function.Surjective (ConjAct.toConjAct (G := S0)).toMonoidHom :=
      fun x => ⟨ConjAct.ofConjAct x, rfl⟩
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact (Subgroup.index_comap_of_surjective _ hsurj).trans
      (MulAction.index_stabilizer (ConjAct S0) _)
  have horb : Subtype.val '' (MulAction.orbit (ConjAct S0) (⟨s, hs⟩ : S0)) =
      {y | ∃ w ∈ S0, y = w * s * w⁻¹} := by
    ext y
    constructor
    · rintro ⟨t, ⟨c, rfl⟩, rfl⟩
      refine ⟨((ConjAct.ofConjAct c : S0) : K), (ConjAct.ofConjAct c).2, ?_⟩
      change ((c • (⟨s, hs⟩ : S0) : S0) : K) = _
      rw [ConjAct.smul_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨ConjAct.toConjAct (⟨w, hw⟩ : S0) • (⟨s, hs⟩ : S0), ⟨_, rfl⟩, ?_⟩
      rw [ConjAct.toConjAct_smul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hC : Subtype.val '' ((Subgroup.centralizer {(⟨s, hs⟩ : S0)} : Subgroup S0) : Set S0) =
      centS0 s := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ht
      have e := congrArg Subtype.val ht
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at e
      exact ⟨t.2, e⟩
    · rintro ⟨hy, e⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact e
  rw [← hC, ← horb, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, ← hidx, ← Nat.card_coe_set_eq]
  exact h1

theorem cent_pts
    {nr NC ng j : ℕ} {CP CX CG CGR : ℕ → ℕ} (hj0 : j ≠ 0) (hj5 : j < 5)
    (hnr : s0Reps.getD (j - 1) 0 = nr)
    (htree : ∀ i < NC, treeK (rmStep CGR) ng NC CP CX i = true)
    (hclos : ∀ i < NC, closK (rmStep CGR) ng NC CP CX i = true)
    (hroot : ∀ i < NC, Nat.beq (rtOf CX i) 0 = true) (hmisc : centMisc CP CG CGR ng nr = true)
    (hNC : NC * s0Sizes.getD j 0 = 1451520) (hpos : 0 < NC) :
    {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr) := by
  simp only [centMisc, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hmisc
  obtain ⟨h0, hg⟩ := hmisc
  let g : ℕ → K := fun l => sElt (CG l)
  have hsteps : MulSteps repK (rmStep CGR) ng g := by
    intro l hl x M hx
    have e : rmStep CGR l M = mulV M (SK (CG l)) := by
      rw [rmStep, (hg l hl).1]
    rw [e]
    exact repK_mul hx (repK_sElt _)
  have h1 : repK 1 (CP 0) := by
    rw [h0]
    exact repK_one
  have hpts := mul_record (rep := repK) (fun _ _ _ h h' => repK_fun h h') hsteps htree hclos hpos
    (fun i hi => Nat.eq_of_beq_eq_true (hroot i hi)) h1
  have hcomm : ∀ l < ng, g l * sElt nr = sElt nr * g l := by
    intro l hl
    have hl' := (hg l hl)
    have ha : repK (g l) (CGR l) := by
      have := repK_sElt (CG l)
      rw [← hl'.1] at this
      exact this
    have hm := repK_mul ha (repK_sElt nr)
    rw [hl'.2] at hm
    exact repK_fun hm (repK_mul (repK_sElt nr) ha)
  have hsub : (gensSub g ng : Set K) ⊆ centS0 (sElt nr) := by
    have hle : gensSub g ng ≤ S0 ⊓ Subgroup.centralizer {sElt nr} := by
      rw [gensSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      exact Subgroup.mem_inf.2 ⟨sElt_mem_S0 _,
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm l hl)⟩
    intro y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 (hle hy)
    exact ⟨h1, Subgroup.mem_centralizer_singleton_iff.1 h2⟩
  have tf := treeK_sound htree
  have hcard : {y | ∃ i < NC, repK y (CP i)}.ncard = NC := by
    refine pts_ncard (fun _ _ _ h h' => repK_fun h h') (fun _ _ _ h h' => repK_unique h h')
      (fun i hi => ?_) tf.2
    obtain ⟨-, -, hr⟩ := tf.1 i hi
    rw [Nat.eq_of_beq_eq_true (hroot i hi)] at hr
    obtain ⟨w, -, hw⟩ := reach_mul hsteps hr h1
    exact ⟨_, hw⟩
  have hcls := (s0_class hj5).2
  rw [(s0_class hj5).1] at hcls
  have hrep : s0Rep j = sElt nr := by
    rw [s0Rep, if_neg hj0, hnr]
  rw [hrep] at hcls
  have hcent := ncard_centS0_mul (sElt_mem_S0 nr)
  rw [hcls] at hcent
  have hpos' : 0 < s0Sizes.getD j 0 := by
    interval_cases j <;> simp [s0Sizes]
  have hCN : (centS0 (sElt nr)).ncard = NC := by
    have := hNC.trans hcent.symm
    exact (Nat.eq_of_mul_eq_mul_right hpos' this).symm
  rw [hpts]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ ?_
  · rw [hCN, ← hcard, hpts]
  · exact (Set.toFinite _)

theorem cent_2331 :
    {y | ∃ i < 4608, repK y (C2331Pt i)} = centS0 (sElt 2331) :=
  cent_pts (j := 2) (by norm_num) (by norm_num) rfl C2331_tree C2331_clos C2331_root C2331_misc
    (by decide) (by norm_num)

theorem cent_144 :
    {y | ∃ i < 384, repK y (C144Pt i)} = centS0 (sElt 144) :=
  cent_pts (j := 4) (by norm_num) (by norm_num) rfl C144_tree C144_clos C144_root C144_misc
    (by decide) (by norm_num)

theorem cent_1082 :
    {y | ∃ i < 1536, repK y (C1082Pt i)} = centS0 (sElt 1082) :=
  cent_pts (j := 3) (by norm_num) (by norm_num) rfl C1082_tree C1082_clos C1082_root C1082_misc
    (by decide) (by norm_num)

end CertificateChecks.KernelCo2Census

end
