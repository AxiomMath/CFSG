module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleD
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCThmB
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.ClassicalInvolution.RouteD.Entries

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggWAutD_refl_isReflLin {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • ggBCDot c, ?_, rfl⟩
  rw [LinearMap.smul_apply, ggQ2x_ggBCDot_apply, smul_eq_mul]
  field_simp

private lemma ggWAutD_isReflLin_sq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {r : V ≃ₗ[ZMod 3] V} (hr : IsReflLin r) : r ^ 2 = 1 := by
  obtain ⟨c, φ, h, rfl⟩ := hr
  rw [pow_two, ← Module.reflection_inv h]
  exact mul_inv_cancel _

private lemma ggWAutD_isReflLin_ne_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {r : V ≃ₗ[ZMod 3] V} (hr : IsReflLin r) : r ≠ 1 := by
  obtain ⟨c, φ, h, rfl⟩ := hr
  intro h1
  have hthis : (Module.reflection h) c = c := by
    have := congrArg (fun f : V ≃ₗ[ZMod 3] V => f c) h1
    change (Module.reflection h) c = c at this
    exact this
  have h2 : c - φ c • c = c := by
    rw [Module.reflection_apply] at hthis
    exact hthis
  have h3 : φ c • c = 0 := sub_eq_self.mp h2
  rw [h] at h3
  have hc0 : c = 0 := (smul_eq_zero.mp h3).resolve_left (by decide)
  rw [hc0] at h
  exact (by decide : (0 : ZMod 3) ≠ 2) (by simpa using h)

private lemma ggWAutD_isReflLin_form {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {r : V ≃ₗ[ZMod 3] V} (hr : IsReflLin r) :
    ∃ (v : V) (f : Module.Dual (ZMod 3) V), ∀ w, r w = w - f w • v := by
  obtain ⟨c, φ, h, rfl⟩ := hr
  exact ⟨c, φ, fun w => Module.reflection_apply w h⟩

private lemma ggWAutD_B_apply {n : ℕ} (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i : ℕ) = n - 1 ∧ (j : ℕ) = n - 2) ∨
          ((j : ℕ) = n - 1 ∧ (i : ℕ) = n - 2) then 4
        else if ((j : ℕ) + 1 = (i : ℕ)) ∨ ((i : ℕ) + 1 = (j : ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]

private lemma ggWAutD_B_zero_one {n : ℕ} (hn : 3 ≤ n) {a0 b0 : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hb0 : (b0 : ℕ) = 1) : (CoxeterMatrix.B n) a0 b0 = 3 := by
  rw [ggWAutD_B_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

private lemma ggWAutD_B_zero_other {n : ℕ} (hn : 3 ≤ n) {a0 c : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hc0 : (c : ℕ) ≠ 0) (hc1 : (c : ℕ) ≠ 1) :
    (CoxeterMatrix.B n) a0 c = 2 := by
  rw [ggWAutD_B_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

private lemma ggWAutD_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma ggWAutD_dot_single {n : ℕ} (a : Fin n) (x : ZMod 3) (v : GGBCV n) :
    (Pi.single a x) ⬝ᵥ v = x * v a := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma ggWAutD_hc_single {n : ℕ} (a : Fin n) :
    (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ (Pi.single a (1 : ZMod 3)) ≠ 0 := by
  rw [ggWAutD_dot_single]
  simp

private lemma ggWAutD_smul_hc {n : ℕ} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) : (l • c) ⬝ᵥ (l • c) ≠ 0 := by
  rw [smul_dotProduct, dotProduct_smul]
  exact mul_ne_zero hl (mul_ne_zero hl hc)

private lemma ggWAutD_neg_hc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    (-c) ⬝ᵥ (-c) ≠ 0 := by
  rw [ggQ2_DW_neg_dot_self]; exact hc

private lemma ggWAutD_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + p * d * q + q * d * (p + p * d * d) = r := by decide

private lemma ggWAutD_refl_isometry {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (x y : GGBCV n) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV n) x, dotProduct_comm (c : GGBCV n) y]
  rw [ggWAutD_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggWAutD_refl_smul {n : ℕ} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hlc : (l • c) ⬝ᵥ (l • c) ≠ 0) :
    ggBCRefl (l • c) hlc = ggBCRefl c hc := by
  rcases ggQ2_DW_eq_one_or_neg_one l hl with rfl | rfl
  · exact ggQ2_DW_refl_congr (one_smul (ZMod 3) c) hlc hc
  · exact (ggQ2_DW_refl_congr (neg_one_smul (ZMod 3) c) hlc (ggWAutD_neg_hc c hc)).trans
      (ggQ2_DW_refl_neg c hc (ggWAutD_neg_hc c hc))

private noncomputable def ggWAutD_negLin {n : ℕ} (a : Fin n) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (Pi.single a (1 : ZMod 3)) (ggWAutD_hc_single a)

private lemma ggWAutD_negLin_isometry {n : ℕ} (a : Fin n) (u v : GGBCV n) :
    ggWAutD_negLin a u ⬝ᵥ ggWAutD_negLin a v = u ⬝ᵥ v := by
  rw [ggWAutD_negLin]
  exact ggWAutD_refl_isometry _ _ u v

private lemma ggWAutD_negLin_apply {n : ℕ} (a : Fin n) (v : GGBCV n) (i : Fin n) :
    ggWAutD_negLin a v i = if i = a then -v i else v i := by
  rw [ggWAutD_negLin, ggQ2_DW_bc_apply']
  have hcv : (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ v = v a := by
    rw [ggWAutD_dot_single]; ring
  have hcc : (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ (Pi.single a (1 : ZMod 3)) = 1 := by
    rw [ggWAutD_dot_single, Pi.single_eq_same]; ring
  rw [hcv, hcc]
  by_cases hia : i = a
  · subst hia
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact (by decide : ∀ x : ZMod 3, x + x = -x) (v i)
  · rw [if_neg hia]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hia, smul_eq_mul, mul_zero,
      add_zero]

private lemma ggWAutD_coroot_chain {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n)
    (ε : ZMod 3) :
    ggBCCoroot n ε i =
      (Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single ⟨(i : ℕ) + 1, h⟩ (1 : ZMod 3) := by
  have hne1 : i ≠ (⟨(i : ℕ) + 1, h⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp at this
  have hne2 : (⟨(i : ℕ) + 1, h⟩ : Fin n) ≠ i := hne1.symm
  funext j
  rw [ggBCCoroot, if_pos h, Pi.sub_apply]
  by_cases hji : (j : ℕ) = (i : ℕ)
  · rw [if_pos hji]
    have hji' : j = i := Fin.ext hji
    subst hji'
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne1]
    decide +kernel
  · rw [if_neg hji]
    by_cases hj : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos hj]
      have hj' : j = (⟨(i : ℕ) + 1, h⟩ : Fin n) := Fin.ext hj
      subst hj'
      rw [Pi.single_eq_of_ne hne2, Pi.single_eq_same]
      decide +kernel
    · rw [if_neg hj]
      rw [Pi.single_eq_of_ne (fun hh => hji (by rw [hh])),
        Pi.single_eq_of_ne (fun hh => hj (by rw [hh]))]
      simp

private lemma ggWAutD_Wt_eq_one {n : ℕ} {v : GGBCV n} (h : ggBCWt v = 1) :
    ∃ a : Fin n, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • Pi.single a 1 := by
  unfold ggBCWt at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  refine ⟨a, v a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
    simpa using hm
  · funext i
    by_cases hia : i = a
    · subst hia; simp
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, hvi]

private lemma ggWAutD_ggDSimple_eq_coroot {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ggDSimple 3 n i = ggBCCoroot n 1 i := by
  rw [ggWAutD_coroot_chain i hi 1]
  funext j
  rw [ggDSimple]
  simp only [hi, if_true]
  rw [Pi.sub_apply]
  by_cases h1 : (j : ℕ) = i
  · have hj : j = i := Fin.ext h1
    subst j
    have hne : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h; have := congrArg Fin.val h; simp at this
    rw [if_pos rfl, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    decide +kernel
  · rw [if_neg h1]
    by_cases h2 : (j : ℕ) = (i : ℕ) + 1
    · have hj : j = (⟨(i : ℕ) + 1, hi⟩ : Fin n) := Fin.ext h2
      subst j
      have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := by
        intro h; have := congrArg Fin.val h; simp at this
      rw [if_pos rfl, Pi.single_eq_of_ne hne, Pi.single_eq_same]
      decide +kernel
    · rw [if_neg h2, Pi.single_eq_of_ne (fun hh => h1 (by rw [hh])),
        Pi.single_eq_of_ne (fun hh => h2 (by rw [hh]))]
      simp

private lemma ggWAutD_ggDSimple_last {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (ha : (a : ℕ) + 2 = n) (hb : (b : ℕ) + 1 = n) :
    ggDSimple 3 n b = (Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1 := by
  have hbn : ¬ ((b : ℕ) + 1 < n) := by omega
  funext j
  rw [ggDSimple]
  simp only [hbn, if_false]
  rw [Pi.add_apply]
  by_cases hja : (j : ℕ) = (a : ℕ)
  · have hj : j = a := Fin.ext hja
    subst j
    have h1 : (a : ℕ) + 2 = n ∨ (a : ℕ) + 1 = n := Or.inl ha
    rw [if_pos h1, Pi.single_eq_same, Pi.single_eq_of_ne hab]
    simp
  · by_cases hjb : (j : ℕ) = (b : ℕ)
    · have hj : j = b := Fin.ext hjb
      subst j
      have h1 : (b : ℕ) + 2 = n ∨ (b : ℕ) + 1 = n := Or.inr hb
      rw [if_pos h1, Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same]
      simp
    · have h1 : ¬ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) := by
        rintro (h | h)
        · exact hja (by omega)
        · exact hjb (by omega)
      rw [if_neg h1, Pi.single_eq_of_ne (fun hh => hja (by rw [hh])),
        Pi.single_eq_of_ne (fun hh => hjb (by rw [hh]))]
      simp

private lemma ggWAutD_map_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Bijective f) (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    f g ∈ Subgroup.normalizer ((K.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : f (g * y * g⁻¹) ∈ K.map f := Subgroup.mem_map_of_mem f ((hg y).mp hy)
    rwa [map_mul, map_mul, map_inv] at hmem
  · intro hx
    obtain ⟨y, rfl⟩ := hf.2 x
    have hmem : f (g * y * g⁻¹) ∈ K.map f := by
      rw [map_mul, map_mul, map_inv]; exact hx
    obtain ⟨z, hz, hfz⟩ := Subgroup.mem_map.mp hmem
    have hzy : z = g * y * g⁻¹ := hf.1 hfz
    have hgy : g * y * g⁻¹ ∈ K := by rw [← hzy]; exact hz
    exact Subgroup.mem_map_of_mem f ((hg y).mpr hgy)

private lemma ggWAutD_D_zero_one {n : ℕ} (hn : 4 ≤ n) {a0 b0 : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hb0 : (b0 : ℕ) = 1) : CartanMatrix.D n a0 b0 ≠ 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggWAutD_D_zero_other {n : ℕ} (hn : 4 ≤ n) {a0 c : Fin n}
    (ha0 : (a0 : ℕ) = 0) (hc0 : (c : ℕ) ≠ 0) (hc1 : (c : ℕ) ≠ 1) :
    CartanMatrix.D n a0 c = 0 := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggWAutD_wt_ggDSimple {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    ggBCWt (ggDSimple 3 n i) = 2 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [ggWAutD_ggDSimple_eq_coroot i hi, ggWAutD_coroot_chain i hi 1]
    rw [ggQ2x_wt_sub_single i ⟨(i : ℕ) + 1, hi⟩ (by
      intro hh; have := congrArg Fin.val hh; simp at this)]
  · let a : Fin n := ⟨n - 2, by omega⟩
    have hai : a ≠ i := by
      intro h; have := congrArg Fin.val h; simp only [a] at this; omega
    have ha : (a : ℕ) + 2 = n := by simp only [a]; omega
    have hi' : (i : ℕ) + 1 = n := by omega
    rw [ggWAutD_ggDSimple_last a i hai ha hi',
      ggQ2x_wt_single_add_single a i hai 1 1 one_ne_zero one_ne_zero]

private lemma ggWAutD_refl_mul_self {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc * ggBCRefl c hc = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  have hd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := by
    have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
    exact hcast _ hc
  have hdot : c ⬝ᵥ (v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c) =
      2 * (c ⬝ᵥ v) := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, mul_assoc, hd, mul_one]
    ring
  rw [hdot]
  have hsc : ∀ x d : ZMod 3, x * d + (2 * x) * d = 0 := by decide
  rw [add_assoc, ← add_smul,
    show (c ⬝ᵥ v) * (c ⬝ᵥ c) + (2 * (c ⬝ᵥ v)) * (c ⬝ᵥ c) = 0 from
      hsc (c ⬝ᵥ v) (c ⬝ᵥ c)]
  simp

private lemma ggWAutD_negLin_mul_self {n : ℕ} (a : Fin n) :
    ggWAutD_negLin a * ggWAutD_negLin a = 1 := by
  ext v i
  rw [LinearEquiv.mul_apply]
  simp only [ggWAutD_negLin_apply]
  by_cases h : i = a <;> simp [h]

private lemma ggWAutD_negLin_isReflLin {n : ℕ} (a : Fin n) :
    IsReflLin (ggWAutD_negLin a) := by
  refine ⟨(Pi.single a (1 : ZMod 3) : GGBCV n),
    (2 / ((Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ Pi.single a 1)) •
      ggBCDot (Pi.single a (1 : ZMod 3) : GGBCV n), ?_, ?_⟩
  · rw [LinearMap.smul_apply, ggQ2x_ggBCDot_apply, smul_eq_mul]
    field_simp
  · rw [ggWAutD_negLin]
    rfl

private lemma ggWAutD_negLin_wt {n : ℕ} (a : Fin n) (v : GGBCV n) :
    ggBCWt (ggWAutD_negLin a v) = ggBCWt v := by
  unfold ggBCWt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ggWAutD_negLin_apply]
  by_cases h : i = a <;> simp [h]

private lemma ggWAutD_refl_wt_two {n : ℕ} {a c : GGBCV n}
    (haw : ggBCWt a = 2) (hcw : ggBCWt c = 2)
    (ha : a ⬝ᵥ a ≠ 0) (_hc : c ⬝ᵥ c ≠ 0) :
    ggBCWt (ggBCRefl a ha c) = 2 := by
  have hnorm : (ggBCRefl a ha c) ⬝ᵥ (ggBCRefl a ha c) = 2 := by
    rw [ggWAutD_refl_isometry a ha c c, ggQ2x_dot_self_eq_wt, hcw]; decide
  have hbound : ggBCWt (ggBCRefl a ha c) ≤ 4 := by
    rw [ggQ2x_ggBCRefl_apply]
    unfold ggBCWt
    have hsub : (Finset.univ.filter
        (fun i => (c + (a ⬝ᵥ c * (a ⬝ᵥ a)) • a) i ≠ 0))
        ⊆ (Finset.univ.filter (fun i => a i ≠ 0)) ∪
          (Finset.univ.filter (fun i => c i ≠ 0)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hi ⊢
      by_cases ha0 : a i = 0
      · by_cases hc0 : c i = 0
        · exact absurd hi (by simp [ha0, hc0])
        · exact Or.inr hc0
      · exact Or.inl ha0
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le (Finset.univ.filter (fun i => a i ≠ 0))
      (Finset.univ.filter (fun i => c i ≠ 0))).trans ?_
    change ggBCWt a + ggBCWt c ≤ 4
    omega
  have hwmod : (ggBCWt (ggBCRefl a ha c) : ZMod 3) = 2 := by
    rw [← ggQ2x_dot_self_eq_wt]
    exact hnorm
  have hnat : ∀ m : ℕ, m ≤ 4 → (m : ZMod 3) = 2 → m = 2 := by
    intro m h4 h2
    interval_cases m
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · rfl
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
  exact hnat _ hbound hwmod

private lemma ggWAutD_conj_refl {n : ℕ} (g : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (hg : ∀ x y : GGBCV n, (g x) ⬝ᵥ (g y) = x ⬝ᵥ y)
    (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (hgc : (g c) ⬝ᵥ (g c) ≠ 0) :
    g * ggBCRefl c hc * g⁻¹ = ggBCRefl (g c) hgc := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsym : g (g⁻¹ v) = v := LinearEquiv.apply_symm_apply g v
  rw [hsym]
  have hv : (g c) ⬝ᵥ v = c ⬝ᵥ (g⁻¹ v) := by
    have h := hg c (g⁻¹ v)
    rwa [hsym] at h
  rw [hv, hg c c]

private lemma ggWAutD_DReflSet_conj_mem {n : ℕ}
    {s t : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hs : s ∈ ggDReflSet n) (ht : t ∈ ggDReflSet n) :
    s * t * s⁻¹ ∈ ggDReflSet n := by
  obtain ⟨a, haw, ha, rfl⟩ := hs
  obtain ⟨c, hcw, hc, rfl⟩ := ht
  refine ⟨ggBCRefl a ha c, ggWAutD_refl_wt_two haw hcw ha hc, ?_, ?_⟩
  · rw [ggWAutD_refl_isometry a ha c c, ggQ2x_dot_self_eq_wt, hcw]; decide
  · exact ggWAutD_conj_refl (ggBCRefl a ha) (ggWAutD_refl_isometry a ha) c hc _

private lemma ggWAutD_Dgp_conj_Dset {n : ℕ}
    {P : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (hP : P ∈ ggBCReflGp (ggDRoots n))
    {r : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (hr : r ∈ ggDReflSet n) :
    P * r * P⁻¹ ∈ ggDReflSet n := by
  rw [ggBCReflGp] at hP
  refine Subgroup.closure_induction_left (p := fun P _ => P * r * P⁻¹ ∈ ggDReflSet n)
    ?one ?mul ?inv hP
  · simpa using hr
  · intro x hx y hy ihy
    have hx' : x ∈ ggDReflSet n := by
      obtain ⟨c, hc, hcc, rfl⟩ := hx
      exact ⟨c, by simpa [ggDRoots] using hc, hcc, rfl⟩
    rw [show (x * y) * r * (x * y)⁻¹ = x * (y * r * y⁻¹) * x⁻¹ by group]
    exact ggWAutD_DReflSet_conj_mem hx' ihy
  · intro x hx y hy ihy
    obtain ⟨c, hc, hcc, rfl⟩ := hx
    have hxinv : (ggBCRefl c hcc)⁻¹ = ggBCRefl c hcc :=
      inv_eq_of_mul_eq_one_right (ggWAutD_refl_mul_self c hcc)
    rw [show (ggBCRefl c hcc)⁻¹ * y * r * ((ggBCRefl c hcc)⁻¹ * y)⁻¹ =
        (ggBCRefl c hcc)⁻¹ * (y * r * y⁻¹) * ((ggBCRefl c hcc)⁻¹)⁻¹ by group]
    rw [hxinv]
    exact ggWAutD_DReflSet_conj_mem
      ⟨c, by simpa [ggDRoots] using hc, hcc, rfl⟩ ihy

private lemma ggWAutD_negLin_conj_Dgp {n : ℕ} (a : Fin n) {d : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hd : d ∈ ggBCReflGp (ggDRoots n)) :
    ggWAutD_negLin a * d * (ggWAutD_negLin a)⁻¹ ∈ ggBCReflGp (ggDRoots n) := by
  rw [ggBCReflGp] at hd ⊢
  refine Subgroup.closure_induction_left
    (p := fun d _ => ggWAutD_negLin a * d * (ggWAutD_negLin a)⁻¹ ∈
      Subgroup.closure (ggBCReflSet (ggDRoots n))) ?one ?mul ?inv hd
  · simp
  · intro x hx y hy ihy
    obtain ⟨c, hc, hcc, rfl⟩ := hx
    have hwt : ggBCWt (ggWAutD_negLin a c) = 2 := by
      rw [ggWAutD_negLin_wt, hc]
    have hcc' : (ggWAutD_negLin a c) ⬝ᵥ (ggWAutD_negLin a c) ≠ 0 := by
      simpa [ggWAutD_negLin_isometry] using hcc
    have hbase : ggWAutD_negLin a * ggBCRefl c hcc * (ggWAutD_negLin a)⁻¹ ∈
        Subgroup.closure (ggBCReflSet (ggDRoots n)) := by
      rw [ggWAutD_conj_refl (ggWAutD_negLin a) (ggWAutD_negLin_isometry a) c hcc hcc']
      exact Subgroup.subset_closure ⟨ggWAutD_negLin a c, by simpa [ggDRoots] using hwt,
        hcc', rfl⟩
    rw [show ggWAutD_negLin a * (ggBCRefl c hcc * y) * (ggWAutD_negLin a)⁻¹ =
        (ggWAutD_negLin a * ggBCRefl c hcc * (ggWAutD_negLin a)⁻¹) *
          (ggWAutD_negLin a * y * (ggWAutD_negLin a)⁻¹) by group]
    exact Subgroup.mul_mem _ hbase ihy
  · intro x hx y hy ihy
    obtain ⟨c, hc, hcc, rfl⟩ := hx
    rw [show ggWAutD_negLin a * ((ggBCRefl c hcc)⁻¹ * y) *
        (ggWAutD_negLin a)⁻¹ =
        (ggWAutD_negLin a * (ggBCRefl c hcc)⁻¹ * (ggWAutD_negLin a)⁻¹) *
          (ggWAutD_negLin a * y * (ggWAutD_negLin a)⁻¹) by group]
    have hc' : ggBCWt (ggWAutD_negLin a c) = 2 := by rw [ggWAutD_negLin_wt, hc]
    have hcc' : (ggWAutD_negLin a c) ⬝ᵥ (ggWAutD_negLin a c) ≠ 0 := by
      simpa [ggWAutD_negLin_isometry] using hcc
    have hbase : ggWAutD_negLin a * (ggBCRefl c hcc)⁻¹ * (ggWAutD_negLin a)⁻¹ ∈
        Subgroup.closure (ggBCReflSet (ggDRoots n)) := by
      rw [show (ggBCRefl c hcc)⁻¹ = ggBCRefl c hcc from
        inv_eq_of_mul_eq_one_right (ggWAutD_refl_mul_self c hcc)]
      rw [ggWAutD_conj_refl (ggWAutD_negLin a) (ggWAutD_negLin_isometry a) c hcc hcc']
      exact Subgroup.subset_closure ⟨ggWAutD_negLin a c, by simpa [ggDRoots] using hc',
        hcc', rfl⟩
    exact Subgroup.mul_mem _ hbase ihy

private lemma ggWAutD_pair_flip_eq {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ggWAutD_negLin a * ggWAutD_negLin b =
      ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1)
        (by rw [ggQ2_DW_add_norm a b hab]; decide) *
      ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b 1)
        (by rw [ggQ2_DW_sub_norm a b hab]; decide) := by
  ext v i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  have hdadd : ((Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1) = 2 :=
    ggQ2_DW_add_norm a b hab
  have hdsub : ((Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b 1) = 2 :=
    ggQ2_DW_sub_norm a b hab
  have hdotadd : ∀ w : GGBCV n,
      ((Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1) ⬝ᵥ w = w a + w b := by
    intro w
    rw [add_dotProduct, ggWAutD_dot_single, ggWAutD_dot_single]
    ring
  have hdotsub : ∀ w : GGBCV n,
      ((Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b 1) ⬝ᵥ w = w a - w b := by
    intro w
    rw [sub_dotProduct, ggWAutD_dot_single, ggWAutD_dot_single]
    ring
  rw [hdotadd, hdotsub, hdadd, hdsub]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ggWAutD_negLin_apply]
  by_cases hia : i = a
  · have hib : ¬ i = b := fun h => hab (hia.symm.trans h)
    simp [hia, hab, Ne.symm hab]
    ring_nf
    exact (by decide : ∀ x : ZMod 3, -x = x * 5) (v a)
  · by_cases hib : i = b
    · have hia' : ¬ i = a := fun h => hab (h.symm.trans hib)
      simp [hib, hab, Ne.symm hab]
      ring_nf
      exact (by decide : ∀ x : ZMod 3, -x = x * 5) (v b)
    · simp [hia, hib, hab, Ne.symm hab]

private lemma ggWAutD_pair_flip_mem {n : ℕ} (_hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ggWAutD_negLin a * ggWAutD_negLin b ∈ ggBCReflGp (ggDRoots n) := by
  rw [ggWAutD_pair_flip_eq hab]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact Subgroup.subset_closure
      ⟨_, by simpa [ggDRoots] using ggQ2_DW_Wt_add_single a b hab,
        by rw [ggQ2_DW_add_norm a b hab]; decide, rfl⟩
  · exact Subgroup.subset_closure
      ⟨_, by simpa [ggDRoots] using ggQ2_DW_Wt_sub_single a b hab,
        by rw [ggQ2_DW_sub_norm a b hab]; decide, rfl⟩

private lemma ggWAutD_BCW_cases {n : ℕ} (hn : 5 ≤ n) (a0 : Fin n)
    {g : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (hg : g ∈ ggBCW n) :
    g ∈ ggBCReflGp (ggDRoots n) ∨
      ∃ w ∈ ggBCReflGp (ggDRoots n), g = ggWAutD_negLin a0 * w := by
  classical
  rw [ggBCW] at hg
  have hsD : ∀ d ∈ ggBCReflGp (ggDRoots n),
      ggWAutD_negLin a0 * d * (ggWAutD_negLin a0)⁻¹ ∈ ggBCReflGp (ggDRoots n) :=
    fun d hd => ggWAutD_negLin_conj_Dgp a0 hd
  have hs_inv : (ggWAutD_negLin a0)⁻¹ = ggWAutD_negLin a0 :=
    inv_eq_of_mul_eq_one_right (ggWAutD_negLin_mul_self a0)
  have hss : ggWAutD_negLin a0 * ggWAutD_negLin a0 = 1 :=
    ggWAutD_negLin_mul_self a0
  refine Subgroup.closure_induction
    (p := fun g _ => g ∈ ggBCReflGp (ggDRoots n) ∨
      ∃ w ∈ ggBCReflGp (ggDRoots n), g = ggWAutD_negLin a0 * w)
    ?gen ?one ?mul ?inv hg
  · rintro t ⟨c, hcroot, hc, rfl⟩
    rcases hcroot with ⟨h1, h2⟩
    have hw : ggBCWt c = 1 ∨ ggBCWt c = 2 := by omega
    rcases hw with hw | hw
    · obtain ⟨a, l, hl, hcl⟩ := ggWAutD_Wt_eq_one hw
      have hsingle : (Pi.single a (1 : ZMod 3) : GGBCV n) ⬝ᵥ Pi.single a 1 ≠ 0 :=
        ggWAutD_hc_single a
      have hlcdot : (l • (Pi.single a (1 : ZMod 3) : GGBCV n)) ⬝ᵥ (l • Pi.single a 1) ≠ 0 :=
        ggWAutD_smul_hc l hl _ hsingle
      have heq : ggBCRefl c hc = ggWAutD_negLin a :=
        (ggQ2_DW_refl_congr hcl hc hlcdot).trans
          (ggWAutD_refl_smul l hl (Pi.single a 1) hsingle hlcdot)
      rw [heq]
      by_cases ha : a = a0
      · right
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [ha, mul_one]
      · right
        refine ⟨ggWAutD_negLin a0 * ggWAutD_negLin a,
          ggWAutD_pair_flip_mem hn (Ne.symm ha), ?_⟩
        rw [← mul_assoc, ggWAutD_negLin_mul_self, one_mul]
    · exact Or.inl (Subgroup.subset_closure
        ⟨c, by simpa [ggDRoots] using hw, hc, rfl⟩)
  · exact Or.inl (Subgroup.one_mem _)
  · intro x y hx hy ihx ihy
    have hx_eq : ∀ z : GGBCV n ≃ₗ[ZMod 3] GGBCV n,
        z * ggWAutD_negLin a0 =
          ggWAutD_negLin a0 *
            (ggWAutD_negLin a0 * z * ggWAutD_negLin a0) := by
      intro z
      calc z * ggWAutD_negLin a0
          = ((ggWAutD_negLin a0 * ggWAutD_negLin a0) * z) * ggWAutD_negLin a0 := by
            rw [hss, one_mul]
        _ = ggWAutD_negLin a0 *
              (ggWAutD_negLin a0 * z * ggWAutD_negLin a0) := by group
    rcases ihx with hx' | ⟨dx, hdx, rfl⟩
    · rcases ihy with hy' | ⟨dy, hdy, rfl⟩
      · exact Or.inl (Subgroup.mul_mem _ hx' hy')
      · right
        refine ⟨(ggWAutD_negLin a0 * x * ggWAutD_negLin a0) * dy,
          Subgroup.mul_mem _ (hsD x hx') hdy, ?_⟩
        calc x * (ggWAutD_negLin a0 * dy)
            = (x * ggWAutD_negLin a0) * dy := by group
          _ = (ggWAutD_negLin a0 *
                (ggWAutD_negLin a0 * x * ggWAutD_negLin a0)) * dy := by
                rw [hx_eq x]
          _ = ggWAutD_negLin a0 *
                ((ggWAutD_negLin a0 * x * ggWAutD_negLin a0) * dy) := by group
    · rcases ihy with hy' | ⟨dy, hdy, rfl⟩
      · right
        exact ⟨dx * y, Subgroup.mul_mem _ hdx hy', by group⟩
      · left
        have h1 : ggWAutD_negLin a0 * dx * ggWAutD_negLin a0 ∈
            ggBCReflGp (ggDRoots n) := hsD dx hdx
        have hdxs : dx * ggWAutD_negLin a0 =
            ggWAutD_negLin a0 *
              (ggWAutD_negLin a0 * dx * ggWAutD_negLin a0) := hx_eq dx
        have heq : (ggWAutD_negLin a0 * dx) * (ggWAutD_negLin a0 * dy) =
            (ggWAutD_negLin a0 * dx * ggWAutD_negLin a0) * dy := by
          calc (ggWAutD_negLin a0 * dx) * (ggWAutD_negLin a0 * dy)
              = ggWAutD_negLin a0 * (dx * ggWAutD_negLin a0 * dy) := by group
            _ = ggWAutD_negLin a0 *
                  ((ggWAutD_negLin a0 *
                    (ggWAutD_negLin a0 * dx * ggWAutD_negLin a0)) * dy) := by
                  rw [hdxs]
            _ = (ggWAutD_negLin a0 * ggWAutD_negLin a0) *
                  ((ggWAutD_negLin a0 * dx * ggWAutD_negLin a0) * dy) := by group
            _ = (ggWAutD_negLin a0 * dx * ggWAutD_negLin a0) * dy := by
                  rw [hss, one_mul]
        rw [heq]
        exact Subgroup.mul_mem _ h1 hdy
  · intro x hx ihx
    rcases ihx with hx' | ⟨dx, hdx, rfl⟩
    · exact Or.inl (Subgroup.inv_mem _ hx')
    · right
      have hdxs : dx⁻¹ * ggWAutD_negLin a0 =
          ggWAutD_negLin a0 *
            (ggWAutD_negLin a0 * dx⁻¹ * ggWAutD_negLin a0) := by
        calc dx⁻¹ * ggWAutD_negLin a0
            = ((ggWAutD_negLin a0 * ggWAutD_negLin a0) * dx⁻¹) *
                ggWAutD_negLin a0 := by rw [hss, one_mul]
          _ = ggWAutD_negLin a0 *
                (ggWAutD_negLin a0 * dx⁻¹ * ggWAutD_negLin a0) := by group
      refine ⟨ggWAutD_negLin a0 * dx⁻¹ * ggWAutD_negLin a0,
        hsD dx⁻¹ (Subgroup.inv_mem _ hdx), ?_⟩
      calc (ggWAutD_negLin a0 * dx)⁻¹
          = dx⁻¹ * (ggWAutD_negLin a0)⁻¹ := by group
        _ = dx⁻¹ * ggWAutD_negLin a0 := by rw [hs_inv]
        _ = ggWAutD_negLin a0 *
              (ggWAutD_negLin a0 * dx⁻¹ * ggWAutD_negLin a0) := hdxs

private noncomputable def ggWAutD_coordProd {n : ℕ} (v : GGBCV n) : ZMod 3 := ∏ i, v i

private lemma ggWAutD_coordProd_negLin {n : ℕ} (a : Fin n) (v : GGBCV n) :
    ggWAutD_coordProd (ggWAutD_negLin a v) = - ggWAutD_coordProd v := by
  unfold ggWAutD_coordProd
  rw [Finset.prod_eq_mul_prod_diff_singleton a (fun i => ggWAutD_negLin a v i)
    (by intro h; exact absurd (Finset.mem_univ a) h)]
  rw [Finset.prod_eq_mul_prod_diff_singleton a (fun i => v i)
    (by intro h; exact absurd (Finset.mem_univ a) h)]
  have hrest : ∏ x ∈ Finset.univ \ {a}, ggWAutD_negLin a v x =
      ∏ x ∈ Finset.univ \ {a}, v x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxa : x ≠ a := by simpa using hx
    simp [ggWAutD_negLin_apply, hxa]
  rw [hrest]
  simp [ggWAutD_negLin_apply]

private lemma ggWAutD_coordProd_update_neg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {f g : GGBCV n} (hi : f i = - g j) (hj : f j = - g i)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    ggWAutD_coordProd f = ggWAutD_coordProd g := by
  unfold ggWAutD_coordProd
  rw [Finset.prod_eq_mul_prod_diff_singleton i f
    (by intro h; exact absurd (Finset.mem_univ i) h)]
  rw [Finset.prod_eq_mul_prod_diff_singleton i g
    (by intro h; exact absurd (Finset.mem_univ i) h)]
  have hji : j ∈ Finset.univ \ {i} := by simp [hij.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton j f (by intro h; exact absurd hji h)]
  rw [Finset.prod_eq_mul_prod_diff_singleton j g (by intro h; exact absurd hji h)]
  have hrest : ∏ x ∈ (Finset.univ \ {i}) \ {j}, f x =
      ∏ x ∈ (Finset.univ \ {i}) \ {j}, g x := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    obtain ⟨hxmem, hxj⟩ := hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hxmem
    exact hother x (by simpa using hxmem.2) (by simpa using hxj)
  rw [hrest, hi, hj]
  ring

private lemma ggWAutD_coordProd_update_pos {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {f g : GGBCV n} (hi : f i = g j) (hj : f j = g i)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    ggWAutD_coordProd f = ggWAutD_coordProd g := by
  unfold ggWAutD_coordProd
  rw [Finset.prod_eq_mul_prod_diff_singleton i f
    (by intro h; exact absurd (Finset.mem_univ i) h)]
  rw [Finset.prod_eq_mul_prod_diff_singleton i g
    (by intro h; exact absurd (Finset.mem_univ i) h)]
  have hji : j ∈ Finset.univ \ {i} := by simp [hij.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton j f (by intro h; exact absurd hji h)]
  rw [Finset.prod_eq_mul_prod_diff_singleton j g (by intro h; exact absurd hji h)]
  have hrest : ∏ x ∈ (Finset.univ \ {i}) \ {j}, f x =
      ∏ x ∈ (Finset.univ \ {i}) \ {j}, g x := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    obtain ⟨hxmem, hxj⟩ := hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hxmem
    exact hother x (by simpa using hxmem.2) (by simpa using hxj)
  rw [hrest, hi, hj]
  ring

private lemma ggWAutD_coordProd_refl_add {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : GGBCV n) :
    ggWAutD_coordProd
      (ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1)
        (by rw [ggQ2_DW_add_norm i j hij]; decide) v) = ggWAutD_coordProd v := by
  let c : GGBCV n := (Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1
  have hc : c ⬝ᵥ c ≠ 0 := by
    dsimp [c]; rw [ggQ2_DW_add_norm i j hij]; decide
  have hdot : c ⬝ᵥ v = v i + v j := by
    dsimp [c]; rw [add_dotProduct, ggWAutD_dot_single, ggWAutD_dot_single]; ring
  have hci : c i = 1 := by dsimp [c]; simp [hij]
  have hcj : c j = 1 := by dsimp [c]; simp [Ne.symm hij]
  have hck : ∀ k, k ≠ i → k ≠ j → c k = 0 := by
    intro k hki hkj; dsimp [c]; simp [hki, hkj]
  apply ggWAutD_coordProd_update_neg (i := i) (j := j) hij
  · rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_add_norm i j hij]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, mul_one, add_zero]
    exact (by decide : ∀ x y : ZMod 3, x + (x + y) * 2 = -y) (v i) (v j)
  · rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_add_norm i j hij]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hij), mul_one, zero_add]
    exact (by decide : ∀ x y : ZMod 3, y + (x + y) * 2 = -x) (v i) (v j)
  · intro k hki hkj
    rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_add_norm i j hij]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hki,
      Pi.single_eq_of_ne hkj, mul_zero, add_zero]

private lemma ggWAutD_coordProd_refl_sub {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : GGBCV n) :
    ggWAutD_coordProd
      (ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1)
        (by rw [ggQ2_DW_sub_norm i j hij]; decide) v) = ggWAutD_coordProd v := by
  let c : GGBCV n := (Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1
  have hc : c ⬝ᵥ c ≠ 0 := by
    dsimp [c]; rw [ggQ2_DW_sub_norm i j hij]; decide
  have hdot : c ⬝ᵥ v = v i - v j := by
    dsimp [c]; rw [sub_dotProduct, ggWAutD_dot_single, ggWAutD_dot_single]; ring
  have hci : c i = 1 := by dsimp [c]; simp [hij]
  have hcj : c j = -1 := by dsimp [c]; simp [Ne.symm hij]
  have hck : ∀ k, k ≠ i → k ≠ j → c k = 0 := by
    intro k hki hkj; dsimp [c]; simp [hki, hkj]
  apply ggWAutD_coordProd_update_pos (i := i) (j := j) hij
  · rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_sub_norm i j hij]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, mul_one, sub_zero]
    exact (by decide : ∀ x y : ZMod 3, x + (x - y) * 2 = y) (v i) (v j)
  · rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_sub_norm i j hij]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hij)]
    exact (by decide : ∀ x y : ZMod 3, y + (x - y) * 2 * -1 = x) (v i) (v j)
  · intro k hki hkj
    rw [ggQ2x_ggBCRefl_apply, hdot, ggQ2_DW_sub_norm i j hij]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, mul_zero, add_zero,
      sub_zero]

private lemma ggWAutD_coordProd_refl {n : ℕ} {c : GGBCV n}
    (hwt : ggBCWt c = 2) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggWAutD_coordProd (ggBCRefl c hc v) = ggWAutD_coordProd v := by
  obtain ⟨i, j, l, k, hij, hl, hk, hc_eq⟩ := ggQ2_DW_weight_two hwt
  have hcadd : ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1) ≠ 0 := by
    rw [ggQ2_DW_add_norm i j hij]; decide
  have hcsub : ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1) ≠ 0 := by
    rw [ggQ2_DW_sub_norm i j hij]; decide
  rcases ggQ2_DW_eq_one_or_neg_one l hl with rfl | rfl <;>
    rcases ggQ2_DW_eq_one_or_neg_one k hk with rfl | rfl
  · have hc' : c = (Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1 := by
      rw [hc_eq]; ext t; simp [Pi.add_apply, one_smul]
    rw [show ggBCRefl c hc = ggBCRefl ((Pi.single i 1 : GGBCV n) + Pi.single j 1) hcadd
      from ggQ2_DW_refl_congr hc' hc hcadd]
    exact ggWAutD_coordProd_refl_add i j hij v
  · have hc' : c = (Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1 := by
      rw [hc_eq]; ext t
      simp [Pi.add_apply, Pi.sub_apply]
      ring
    rw [show ggBCRefl c hc = ggBCRefl ((Pi.single i 1 : GGBCV n) - Pi.single j 1) hcsub
      from ggQ2_DW_refl_congr hc' hc hcsub]
    exact ggWAutD_coordProd_refl_sub i j hij v
  · have hc' : c = -((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1) := by
      rw [hc_eq]; ext t
      simp [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
    have hneg : (-((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i 1 : GGBCV n) - Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self]; exact hcsub
    rw [show ggBCRefl c hc =
        ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV n) - Pi.single j 1)) hneg
      from ggQ2_DW_refl_congr hc' hc hneg]
    rw [ggQ2_DW_refl_neg]
    exact ggWAutD_coordProd_refl_sub i j hij v
  · have hc' : c = -((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1) := by
      rw [hc_eq]; ext t
      simp [Pi.add_apply, Pi.neg_apply]
      ring
    have hneg : (-((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i 1 : GGBCV n) + Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self]; exact hcadd
    rw [show ggBCRefl c hc =
        ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV n) + Pi.single j 1)) hneg
      from ggQ2_DW_refl_congr hc' hc hneg]
    rw [ggQ2_DW_refl_neg]
    exact ggWAutD_coordProd_refl_add i j hij v

private lemma ggWAutD_coordProd_mem_Dgp {n : ℕ} {g : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hg : g ∈ ggBCReflGp (ggDRoots n)) :
    ∀ v : GGBCV n, ggWAutD_coordProd (g v) = ggWAutD_coordProd v := by
  rw [ggBCReflGp] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ v : GGBCV n, ggWAutD_coordProd (g v) = ggWAutD_coordProd v)
    ?gen ?one ?mul ?inv hg
  · rintro t ⟨c, hcroot, hc, rfl⟩
    intro v
    exact ggWAutD_coordProd_refl (by simpa [ggDRoots] using hcroot) hc v
  · intro v; simp [ggWAutD_coordProd]
  · intro x y hx hy ihx ihy v
    rw [LinearEquiv.mul_apply, ihx (y v), ihy v]
  · intro x hx ih v
    have h1 := ih (x.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm

private lemma ggWAutD_negLin_not_mem_Dgp {n : ℕ} (a : Fin n) :
    ggWAutD_negLin a ∉ ggBCReflGp (ggDRoots n) := by
  intro hmem
  have hv := ggWAutD_coordProd_mem_Dgp hmem (fun _ : Fin n => (1 : ZMod 3))
  have hleft : ggWAutD_coordProd
      (ggWAutD_negLin a (fun _ : Fin n => (1 : ZMod 3))) = -1 := by
    rw [ggWAutD_coordProd_negLin]
    simp [ggWAutD_coordProd]
  have hright : ggWAutD_coordProd (fun _ : Fin n => (1 : ZMod 3)) = 1 := by
    simp [ggWAutD_coordProd]
  rw [hleft, hright] at hv
  exact absurd hv (by decide)

private lemma ggWAutD_linConj_cancel {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V' ≃ₗ[ZMod p] V') :
    ggLinConj τ (ggLinConj τ.symm g) = g := by
  ext v; simp [ggLinConj_apply]

private lemma ggWAutD_mem_W_iff {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    {W : Subgroup (V ≃ₗ[ZMod p] V)} {Dgp : Subgroup (V' ≃ₗ[ZMod p] V')}
    {τ : V ≃ₗ[ZMod p] V'} (hmap : Subgroup.map (ggLinConj τ).toMonoidHom W = Dgp)
    (x : V' ≃ₗ[ZMod p] V') : ggLinConj τ.symm x ∈ W ↔ x ∈ Dgp := by
  rw [← hmap]
  constructor
  · intro hx
    simpa [ggWAutD_linConj_cancel] using
      Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hx
  · intro hx
    exact (Subgroup.mem_map_iff_mem (f := (ggLinConj τ).toMonoidHom)
      (ggLinConj τ).injective).mp (by simpa [ggWAutD_linConj_cancel] using hx)

private lemma ggWAutD_conj_eq_of_pm {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {T w : V ≃ₗ[ZMod p] V}
    (h : (∀ v, T v = w v) ∨ (∀ v, T v = -(w v))) :
    ∀ g : V ≃ₗ[ZMod p] V, T * g * T⁻¹ = w * g * w⁻¹ := by
  intro g
  rcases h with h | h
  · have hT : T = w := LinearEquiv.ext h
    rw [hT]
  · ext v
    have hy : T⁻¹ v = -(w⁻¹ v) := by
      change T.symm v = -(w.symm v)
      have hh := h (T.symm v)
      rw [LinearEquiv.apply_symm_apply] at hh
      have h2 : w (T.symm v) = -v := ((congrArg Neg.neg hh).trans (neg_neg _)).symm
      calc T.symm v = w.symm (w (T.symm v)) :=
            (LinearEquiv.symm_apply_apply w (T.symm v)).symm
        _ = w.symm (-v) := by rw [h2]
        _ = -(w.symm v) := by rw [map_neg]
    simp only [LinearEquiv.mul_apply, hy]
    rw [map_neg, h, map_neg, neg_neg]

private noncomputable def ggWAutD_negOne {n : ℕ} : GGBCV n ≃ₗ[ZMod 3] GGBCV n where
  toFun v := -v
  invFun v := -v
  map_add' x y := by ext i; simp only [Pi.neg_apply]; exact neg_add (x i) (y i)
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf
  left_inv v := by ext i; simp only [Pi.neg_apply]; exact neg_neg (v i)
  right_inv v := by ext i; simp only [Pi.neg_apply]; exact neg_neg (v i)

private lemma ggWAutD_negOne_apply {n : ℕ} (v : GGBCV n) : ggWAutD_negOne v = -v := rfl

private lemma ggWAutD_negOne_comm {n : ℕ} (x : GGBCV n ≃ₗ[ZMod 3] GGBCV n) :
    ggWAutD_negOne * x = x * ggWAutD_negOne := by
  ext v i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggWAutD_negOne_apply,
    ggWAutD_negOne_apply, Pi.neg_apply, map_neg, Pi.neg_apply]

private lemma ggWAutD_negOne_mul_self {n : ℕ} :
    ggWAutD_negOne * ggWAutD_negOne = (1 : GGBCV n ≃ₗ[ZMod 3] GGBCV n) := by
  ext v i
  simp [LinearEquiv.mul_apply, ggWAutD_negOne_apply]

private lemma ggWAutD_negOne_inv {n : ℕ} :
    (ggWAutD_negOne : GGBCV n ≃ₗ[ZMod 3] GGBCV n)⁻¹ = ggWAutD_negOne :=
  inv_eq_of_mul_eq_one_right ggWAutD_negOne_mul_self

private lemma ggWAutD_negOne_conj {n : ℕ} (x : GGBCV n ≃ₗ[ZMod 3] GGBCV n) :
    ggWAutD_negOne * x * ggWAutD_negOne⁻¹ = x := by
  rw [ggWAutD_negOne_inv, ggWAutD_negOne_comm, mul_assoc, ggWAutD_negOne_mul_self, mul_one]

private lemma ggWAutD_negLin_mem_ggBCW {n : ℕ} (a : Fin n) :
    ggWAutD_negLin a ∈ ggBCW n := by
  rw [ggBCW]
  refine Subgroup.subset_closure ⟨Pi.single a (1 : ZMod 3), ?_, ggWAutD_hc_single a, rfl⟩
  rw [ggBCRoots]
  refine ⟨?_, ?_⟩ <;> rw [ggQ2x_wt_single]; omega

private lemma ggWAutD_negOne_mem_ggBCW {n : ℕ} (hn : 3 ≤ n) :
    ggWAutD_negOne ∈ ggBCW n := by
  apply ggQ2_bc_normalizer n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [ggWAutD_negOne_conj]

private noncomputable def ggWAutD_negNegLin {n : ℕ} (a : Fin n) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggWAutD_negOne * ggWAutD_negLin a

private lemma ggWAutD_negNegLin_mem_ggBCW {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    ggWAutD_negNegLin a ∈ ggBCW n :=
  Subgroup.mul_mem _ (ggWAutD_negOne_mem_ggBCW hn) (ggWAutD_negLin_mem_ggBCW a)

private lemma ggWAutD_negLin_inv {n : ℕ} (a : Fin n) :
    (ggWAutD_negLin a)⁻¹ = ggWAutD_negLin a :=
  inv_eq_of_mul_eq_one_right (ggWAutD_negLin_mul_self a)

private lemma ggWAutD_negLin_eq_negOne_mul {n : ℕ} (a : Fin n) :
    ggWAutD_negLin a = ggWAutD_negOne * ggWAutD_negNegLin a := by
  rw [ggWAutD_negNegLin, ← mul_assoc, ggWAutD_negOne_mul_self, one_mul]

private lemma ggWAutD_negOne_not_mem_Dgp {n : ℕ} (hodd : Odd n) :
    ggWAutD_negOne ∉ ggBCReflGp (ggDRoots n) := by
  intro hmem
  have hv := ggWAutD_coordProd_mem_Dgp hmem (fun _ : Fin n => (1 : ZMod 3))
  have hN : ggWAutD_negOne (fun _ : Fin n => (1 : ZMod 3)) = fun _ => -1 := by
    ext i; rw [ggWAutD_negOne_apply]; rfl
  rw [hN] at hv
  have hleft : ggWAutD_coordProd (fun _ : Fin n => (-1 : ZMod 3)) = -1 := by
    simp only [ggWAutD_coordProd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hodd.neg_one_pow
  have hright : ggWAutD_coordProd (fun _ : Fin n => (1 : ZMod 3)) = 1 := by
    simp [ggWAutD_coordProd]
  rw [hleft, hright] at hv
  exact absurd hv (by decide)

private lemma ggWAutD_negNegLin_mem_Dgp {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n) (a0 : Fin n) :
    ggWAutD_negNegLin a0 ∈ ggBCReflGp (ggDRoots n) := by
  have hg0 : ggWAutD_negNegLin a0 ∈ ggBCW n := ggWAutD_negNegLin_mem_ggBCW (by omega) a0
  rcases ggWAutD_BCW_cases (by omega) a0 hg0 with h | ⟨w, hw, hgw⟩
  · exact h
  · exfalso
    have hw1 : w = ggWAutD_negOne := by
      calc w = (ggWAutD_negLin a0)⁻¹ * (ggWAutD_negLin a0 * w) := by
              rw [← mul_assoc, inv_mul_cancel, one_mul]
           _ = (ggWAutD_negLin a0)⁻¹ * ggWAutD_negNegLin a0 := by rw [← hgw]
           _ = ggWAutD_negLin a0 * (ggWAutD_negOne * ggWAutD_negLin a0) := by
                rw [ggWAutD_negLin_inv, ggWAutD_negNegLin]
           _ = ggWAutD_negOne := by
                rw [← mul_assoc, ← ggWAutD_negOne_comm (ggWAutD_negLin a0), mul_assoc,
                  ggWAutD_negLin_mul_self, mul_one]
    exact ggWAutD_negOne_not_mem_Dgp hodd (hw1 ▸ hw)

private lemma ggWAutD_negOne_transport {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (τ : U ≃ₗ[ZMod 3] GGBCV n) (x : U) :
    ggLinConj τ.symm (ggWAutD_negOne : GGBCV n ≃ₗ[ZMod 3] GGBCV n) x = -x := by
  simp [ggLinConj_apply, ggWAutD_negOne_apply]

private lemma ggWAutD_normD_core {n : ℕ} (hn : 5 ≤ n) [Fact (Nat.Prime 3)]
    {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U)
    (hb : LinearIndependent (ZMod 3) h) (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.D n i j : ℤ) : ZMod 3))
    (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U))) :
    ∃ (g : GGBCV n ≃ₗ[ZMod 3] GGBCV n) (τ : U ≃ₗ[ZMod 3] GGBCV n),
      g ∈ ggBCW n ∧
      ((∀ v, T v = ggLinConj τ.symm g v) ∨ (∀ v, T v = -(ggLinConj τ.symm g v))) ∧
      Subgroup.map (ggLinConj τ).toMonoidHom (ggQ2WeylOf h α) = ggBCReflGp (ggDRoots n) ∧
      ∀ i, τ (h i) = ggDSimple 3 n i := by
  classical
  have hm4 : 4 ≤ n := by omega
  have hfr : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  let D' : GGQ2Lin 3 :=
    { ι := Fin n
      coxeter := ggCoxeterMatrixD n
      cartan := CartanMatrix.D n
      V := U
      coroot := h
      root := α
      a := ⟨0, by omega⟩
      b := ⟨1, by omega⟩
      a_ne_b := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      a_leaf := by
        refine ⟨⟨1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
        · intro hh
          have := congrArg Fin.val hh
          simp at this
        · exact ggWAutD_D_zero_one (n := n) (by omega) rfl rfl
        · intro y hy
          obtain ⟨hyne, hyC⟩ := hy
          have hyval : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by
            by_cases h0 : (y : ℕ) = 0
            · exact Or.inl h0
            · by_cases h1 : (y : ℕ) = 1
              · exact Or.inr h1
              · exfalso
                exact hyC (ggWAutD_D_zero_other (n := n) (by omega) rfl h0 h1)
          rcases hyval with h0 | h1
          · exact (hyne (Fin.ext h0)).elim
          · exact Fin.ext h1
      isWeyl := Or.inl ⟨n, Equiv.refl _, by omega,
        Or.inr (Or.inr ⟨by omega, (ggWAutD_reindex_refl (ggCoxeterMatrixD n)).symm⟩)⟩
      isCartan := ggIntCartan_D n
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin n) = Module.finrank (ZMod 3) U
    exact ⟨hb, by simp [hfr]⟩
  have hgen : Set.range D'.simpleRefl =
      {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, fun v => by rw [GGQ2Lin.simpleRefl, Module.reflection_apply]⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      ext v
      rw [hj v, GGQ2Lin.simpleRefl, Module.reflection_apply]
  have hWclos : D'.weyl = Subgroup.closure (Set.range D'.simpleRefl) := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]
  have hweylEq : D'.weyl = ggQ2WeylOf h α := by
    rw [hWclos, hgen]
    rfl
  have hT' : T ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)) := by
    rwa [hweylEq]
  have hB : D'.coxeter = (ggCoxeterMatrixD n).reindex (Equiv.refl (Fin n)) :=
    (ggWAutD_reindex_refl (ggCoxeterMatrixD n)).symm
  obtain ⟨τ, hτ, hroot⟩ :=
    ggQ2_D_coordinates (p := 3) (by decide) D' hbas (by omega) (Equiv.refl (Fin n)) hB
  have hmapWc : (D'.weyl).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc 3 n (by omega) :=
    ggQ2_DW_linWeylMap D' (by omega) (Equiv.refl (Fin n)) τ hτ hroot
  have hDle : ggBCReflGp (ggDRoots n) ≤ (D'.weyl).map (ggLinConj τ).toMonoidHom :=
    ggQ2_DW_Droots_le_map D' hbas (by omega) (Equiv.refl (Fin n)) hB τ hτ hroot
      D'.weyl le_rfl
  have hWc_le_D : ggQ2_DW_Wc 3 n (by omega) ≤ ggBCReflGp (ggDRoots n) := by
    rw [ggQ2_DW_Wc, Subgroup.closure_le]
    rintro t ⟨i, rfl⟩
    rw [ggQ2_DW_r_eq_bc (by omega) i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 n i, by simpa [ggDRoots] using ggWAutD_wt_ggDSimple (by omega) i,
        by rw [ggQ2_DW_simple_norm (by omega) i]; decide, rfl⟩
  have hmapD : (D'.weyl).map (ggLinConj τ).toMonoidHom = ggBCReflGp (ggDRoots n) := by
    apply le_antisymm
    · rw [hmapWc]; exact hWc_le_D
    · exact hDle
  let a : GGBCV n ≃ₗ[ZMod 3] GGBCV n := ggLinConj τ T
  have haN : a ∈ Subgroup.normalizer
      (ggBCReflGp (ggDRoots n) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
    rw [← hmapD]
    exact ggWAutD_map_normalizer (ggLinConj τ).toMonoidHom
      ⟨(ggLinConj τ).injective, (ggLinConj τ).surjective⟩ D'.weyl hT'
  have : Module.Finite (ZMod 3) U := by
    have hfin : Module.Finite (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range h)) :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_range h)
    rw [hspan] at hfin
    exact Module.Finite.equiv (Submodule.topEquiv)
  have : Finite U := Module.finite_of_finite (ZMod 3)
  have hFT : TauCeti.IsFiniteType (CartanMatrix.D n) := by
    rw [← CFSG.LieType.Universal.Spin.cartanD_eq]
    exact CFSG.LieType.Universal.Spin.isFiniteType_cartanD n
  have hsSimple : ∀ i (v : U), D'.simpleRefl i v = v - D'.root i v • D'.coroot i := by
    intro i v
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply]
  have hclosed := ggReflClosed_of_indep (p := 3) (by decide) hFT (ggIntCartan_D n)
    D'.coroot D'.root D'.pairing hbas.1 D'.simpleRefl hsSimple
  have hDset_r : ∀ k : Fin n, ggQ2_DW_r 3 n (by omega) k ∈ ggDReflSet n := by
    intro k
    rw [ggQ2_DW_r_eq_bc (by omega) k]
    exact ⟨ggDSimple 3 n k, ggWAutD_wt_ggDSimple (by omega) k,
      by rw [ggQ2_DW_simple_norm (by omega) k]; decide, rfl⟩
  let π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
    fun t => a * t * a⁻¹
  have hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n := by
    intro t ht
    obtain ⟨ct, hwt, hct, rfl⟩ := ht
    have htD : ggBCRefl ct hct ∈ ggBCReflGp (ggDRoots n) :=
      Subgroup.subset_closure ⟨ct, by simpa [ggDRoots] using hwt, hct, rfl⟩
    have htmap : ggBCRefl ct hct ∈ (D'.weyl).map (ggLinConj τ).toMonoidHom := by
      rw [hmapD]; exact htD
    obtain ⟨u, huW, hueq⟩ := Subgroup.mem_map.mp htmap
    have huRefl : IsReflLin u := by
      apply (ggLinConj_isReflLin τ u).mp
      have hEq : ggLinConj τ u = ggBCRefl ct hct := hueq
      rw [hEq]
      exact ggWAutD_refl_isReflLin ct hct
    have hTuW : T * u * T⁻¹ ∈ D'.weyl := by
      have h := (Subgroup.mem_normalizer_iff.mp hT') u
      exact h.mp huW
    have hTuRefl : IsReflLin (T * u * T⁻¹) := ggQ2_isReflLin_conj T u huRefl
    have hTuSq : (T * u * T⁻¹) ^ 2 = 1 := ggWAutD_isReflLin_sq hTuRefl
    have hTuNe : T * u * T⁻¹ ≠ 1 := ggWAutD_isReflLin_ne_one hTuRefl
    have hTuForm := ggWAutD_isReflLin_form hTuRefl
    obtain ⟨v, hvW, k, hvk⟩ := hclosed (T * u * T⁻¹) (hWclos ▸ hTuW) hTuSq hTuNe hTuForm
    have hata : a * ggBCRefl ct hct * a⁻¹ =
        ggLinConj τ (T * u * T⁻¹) := by
      rw [show ggBCRefl ct hct = ggLinConj τ u from hueq.symm]
      simp only [a, map_mul, map_inv]
    rw [show π (ggBCRefl ct hct) = a * ggBCRefl ct hct * a⁻¹ from rfl, hata, hvk]
    have hvD : ggLinConj τ v ∈ ggBCReflGp (ggDRoots n) := by
      have hmem : ggLinConj τ v ∈ (D'.weyl).map (ggLinConj τ).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (hWclos.symm ▸ hvW)
      rwa [hmapD] at hmem
    have hkD : ggLinConj τ (D'.simpleRefl k) ∈ ggDReflSet n := by
      have h := ggQ2_DW_linConj_simpleRefl D' (by omega) (Equiv.refl (Fin n)) τ hτ hroot k
      have h' : ggLinConj τ (D'.simpleRefl k) = ggQ2_DW_r 3 n (by omega) k := by simpa using h
      rw [h']
      exact hDset_r k
    rw [map_mul, map_mul, map_inv]
    exact ggWAutD_Dgp_conj_Dset hvD hkD
  have hinj : Set.InjOn π (ggDReflSet n) := by
    intro s hs t ht hst
    have h := congrArg (fun x => a⁻¹ * x * a) hst
    simpa [π, mul_assoc] using h
  have hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹ := by
    intro s hs t ht
    simp only [π]
    group
  obtain ⟨g, hgB, hgt⟩ := ggQ2_quandle_aut_D n (by omega) π hπT hinj hπ
  let g' : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm g
  have hsymm_a : ggLinConj τ.symm a = T := by
    dsimp [a]
    ext v
    simp [ggLinConj_apply]
  have hconj : ∀ k : Fin n,
      T * D'.simpleRefl k * T⁻¹ = g' * D'.simpleRefl k * g'⁻¹ := by
    intro k
    have hrel := hgt (ggQ2_DW_r 3 n (by omega) k) (hDset_r k)
    have h := congrArg (ggLinConj τ.symm) hrel
    have hs : ggLinConj τ.symm (ggQ2_DW_r 3 n (by omega) k) = D'.simpleRefl k := by
      rw [← ggQ2_DW_linConj_simpleRefl D' (by omega) (Equiv.refl (Fin n)) τ hτ hroot k]
      ext v
      simp [ggLinConj_apply]
    have hR : ggLinConj τ.symm
        (ggQ2_DW_r 3 n (by omega) k) = D'.simpleRefl k := hs
    have h1 : ggLinConj τ.symm
        (a * ggQ2_DW_r 3 n (by omega) k * a⁻¹) =
        ggLinConj τ.symm a * ggLinConj τ.symm (ggQ2_DW_r 3 n (by omega) k) *
          (ggLinConj τ.symm a)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hsymm_a, hR] at h1
    have h2 : ggLinConj τ.symm
        (g * ggQ2_DW_r 3 n (by omega) k * g⁻¹) =
        ggLinConj τ.symm g * D'.simpleRefl k * (ggLinConj τ.symm g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hR]
    rw [h1, h2] at h
    simpa [g'] using h
  have hpm : (∀ v, T v = g' v) ∨ (∀ v, T v = -(g' v)) :=
    ggQ2_lemmaN (p := 3) rfl D' hbas (by
      have hc : Fintype.card D'.ι = n := by dsimp [D']; simp
      omega) T g' hconj
  exact ⟨g, τ, hgB, hpm, by simpa [← hweylEq] using hmapD, fun i => hτ i⟩

theorem ggQ2WeylNormD_holds {n : ℕ} (hn : 5 ≤ n) :
    ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
      LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
      ∀ (α : Fin n → Module.Dual (ZMod 3) U),
        (∀ i j, α i (h j) = ((CartanMatrix.D n i j : ℤ) : ZMod 3)) →
        ∀ T : U ≃ₗ[ZMod 3] U,
          T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
          (∃ w ∈ ggQ2WeylOf h α, (∀ v, T v = w v) ∨ (∀ v, T v = -(w v))) ∨
            ∃ s : U ≃ₗ[ZMod 3] U, IsReflLin s ∧ s ∉ ggQ2WeylOf h α ∧ ∃ w ∈ ggQ2WeylOf h α,
              (∀ v, T v = s (w v)) ∨ (∀ v, T v = -(s (w v))) := by
  classical
  intro U instACG instMod h hb hspan α hα T hT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, τ, hgB, hpm, hmap, -⟩ := ggWAutD_normD_core hn h hb hspan α hα T hT
  let a0 : Fin n := ⟨n - 1, by omega⟩
  have hmem_iff : ∀ {x : GGBCV n ≃ₗ[ZMod 3] GGBCV n},
      ggLinConj τ.symm x ∈ ggQ2WeylOf h α ↔ x ∈ ggBCReflGp (ggDRoots n) :=
    fun {x} => ggWAutD_mem_W_iff hmap x
  rcases ggWAutD_BCW_cases (by omega) a0 hgB with hgD | ⟨w, hwD, hgw⟩
  · left
    refine ⟨ggLinConj τ.symm g, (hmem_iff).mpr hgD, hpm⟩
  · right
    let s : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm (ggWAutD_negLin a0)
    let w' : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm w
    have hgw' : ggLinConj τ.symm g = s * w' := by
      dsimp [s, w']
      rw [hgw, map_mul]
    have hsRefl : IsReflLin s :=
      (ggLinConj_isReflLin τ.symm (ggWAutD_negLin a0)).mpr (ggWAutD_negLin_isReflLin a0)
    have hsNot : s ∉ ggQ2WeylOf h α := by
      intro hsW
      have hmap' : ggWAutD_negLin a0 ∈ ggBCReflGp (ggDRoots n) := by
        have hmem := Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hsW
        change ggLinConj τ s ∈
          (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom at hmem
        rw [show ggLinConj τ s = ggWAutD_negLin a0 from by
          dsimp [s]; ext v; simp [ggLinConj_apply]] at hmem
        rwa [hmap] at hmem
      exact ggWAutD_negLin_not_mem_Dgp a0 hmap'
    refine ⟨s, hsRefl, hsNot, w', (hmem_iff).mpr hwD, ?_⟩
    rcases hpm with hh | hh
    · left; intro v; rw [hh v, hgw']; rfl
    · right; intro v; rw [hh v, hgw']; rfl

private lemma ggWAutD_negLin_ggDSimple {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ggWAutD_negLin (⟨n - 1, by omega⟩ : Fin n) (ggDSimple 3 n j) =
      ggDSimple 3 n (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j) := by
  funext k
  rw [ggWAutD_negLin_apply]
  have hk := k.isLt
  have hj := j.isLt
  by_cases h2 : (j : ℕ) = n - 2
  · have hjeq : j = ⟨n - 2, by omega⟩ := Fin.ext h2
    rw [hjeq, Equiv.swap_apply_left]
    simp only [ggDSimple, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · by_cases h1 : (j : ℕ) = n - 1
    · have hjeq : j = ⟨n - 1, by omega⟩ := Fin.ext h1
      rw [hjeq, Equiv.swap_apply_right]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne (fun hh => h2 (by simpa using congrArg Fin.val hh))
        (fun hh => h1 (by simpa using congrArg Fin.val hh))]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega

theorem ggQ2WeylNormD_fork {n : ℕ} (hn : 5 ≤ n) {U : Type} [AddCommGroup U]
    [Module (ZMod 3) U] (h : Fin n → U) (hb : LinearIndependent (ZMod 3) h)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) (α : Fin n → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.D n i j : ℤ) : ZMod 3)) (T : U ≃ₗ[ZMod 3] U)
    (hT : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U))) :
    ∃ s : U ≃ₗ[ZMod 3] U, IsReflLin s ∧ s ∉ ggQ2WeylOf h α ∧
      (∀ j, s (h j) = h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j)) ∧
      ((∃ w ∈ ggQ2WeylOf h α, (∀ v, T v = w v) ∨ (∀ v, T v = -(w v))) ∨
        ∃ w ∈ ggQ2WeylOf h α, (∀ v, T v = s (w v)) ∨ (∀ v, T v = -(s (w v)))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, τ, hgB, hpm, hmap, hτh⟩ := ggWAutD_normD_core hn h hb hspan α hα T hT
  let a0 : Fin n := ⟨n - 1, by omega⟩
  have hmem_iff : ∀ {x : GGBCV n ≃ₗ[ZMod 3] GGBCV n},
      ggLinConj τ.symm x ∈ ggQ2WeylOf h α ↔ x ∈ ggBCReflGp (ggDRoots n) :=
    fun {x} => ggWAutD_mem_W_iff hmap x
  let s : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm (ggWAutD_negLin a0)
  have hsRefl : IsReflLin s :=
    (ggLinConj_isReflLin τ.symm (ggWAutD_negLin a0)).mpr (ggWAutD_negLin_isReflLin a0)
  have hsNot : s ∉ ggQ2WeylOf h α := by
    intro hsW
    have hmap' : ggWAutD_negLin a0 ∈ ggBCReflGp (ggDRoots n) := by
      have hmem := Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hsW
      change ggLinConj τ s ∈
        (ggQ2WeylOf h α).map (ggLinConj τ).toMonoidHom at hmem
      rw [show ggLinConj τ s = ggWAutD_negLin a0 from by
        dsimp [s]; ext v; simp [ggLinConj_apply]] at hmem
      rwa [hmap] at hmem
    exact ggWAutD_negLin_not_mem_Dgp a0 hmap'
  have hsfork : ∀ j, s (h j) =
      h (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ j) := by
    intro j
    apply τ.injective
    have h1 : τ (s (h j)) = ggWAutD_negLin a0 (τ (h j)) := by
      simp [s, ggLinConj_apply]
    rw [h1, hτh j, hτh, ggWAutD_negLin_ggDSimple (by omega) j]
  refine ⟨s, hsRefl, hsNot, hsfork, ?_⟩
  rcases ggWAutD_BCW_cases (by omega) a0 hgB with hgD | ⟨w, hwD, hgw⟩
  · left
    exact ⟨ggLinConj τ.symm g, (hmem_iff).mpr hgD, hpm⟩
  · right
    let w' : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm w
    have hgw' : ggLinConj τ.symm g = s * w' := by
      dsimp [s, w']
      rw [hgw, map_mul]
    refine ⟨w', (hmem_iff).mpr hwD, ?_⟩
    rcases hpm with hh | hh
    · left; intro v; rw [hh v, hgw']; rfl
    · right; intro v; rw [hh v, hgw']; rfl

theorem ggQ2WeylInner_D_odd {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n) :
    GGQ2WeylInner n (CartanMatrix.D n) := by
  classical
  intro U instACG instMod h hb hspan α hα T hT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, τ, hgB, hpm, hmap, -⟩ := ggWAutD_normD_core hn h hb hspan α hα T hT
  let a0 : Fin n := ⟨n - 1, by omega⟩
  have hmem_iff : ∀ {x : GGBCV n ≃ₗ[ZMod 3] GGBCV n},
      ggLinConj τ.symm x ∈ ggQ2WeylOf h α ↔ x ∈ ggBCReflGp (ggDRoots n) :=
    fun {x} => ggWAutD_mem_W_iff hmap x
  rcases ggWAutD_BCW_cases (by omega) a0 hgB with hgD | ⟨w, hwD, hgw⟩
  · refine ⟨ggLinConj τ.symm g, (hmem_iff).mpr hgD,
      fun g _ => ggWAutD_conj_eq_of_pm hpm g⟩
  · have hneg : ggWAutD_negNegLin a0 ∈ ggBCReflGp (ggDRoots n) :=
      ggWAutD_negNegLin_mem_Dgp (by omega) hodd a0
    let u : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm (ggWAutD_negNegLin a0)
    let w' : U ≃ₗ[ZMod 3] U := ggLinConj τ.symm w
    have huW : u ∈ ggQ2WeylOf h α := (hmem_iff).mpr hneg
    have hw'W : w' ∈ ggQ2WeylOf h α := (hmem_iff).mpr hwD
    have hhW : u * w' ∈ ggQ2WeylOf h α := (ggQ2WeylOf h α).mul_mem huW hw'W
    have hg_eq : g = ggWAutD_negOne * (ggWAutD_negNegLin a0 * w) := by
      rw [hgw, ggWAutD_negLin_eq_negOne_mul, mul_assoc]
    have h1 : ggLinConj τ.symm g =
        ggLinConj τ.symm ggWAutD_negOne * (u * w') := by
      rw [hg_eq, map_mul, map_mul]
    have hpt : ∀ v, ggLinConj τ.symm g v = -((u * w') v) := by
      intro v
      have hthis := congrArg (fun f : U ≃ₗ[ZMod 3] U => f v) h1
      rw [LinearEquiv.mul_apply, ggWAutD_negOne_transport] at hthis
      exact hthis
    have hpm' : (∀ v, T v = (u * w') v) ∨ (∀ v, T v = -((u * w') v)) := by
      rcases hpm with hh | hh
      · right; intro v; rw [hh v, hpt v]
      · left; intro v; rw [hh v, hpt v, neg_neg]
    exact ⟨u * w', hhW, fun g _ => ggWAutD_conj_eq_of_pm hpm' g⟩

@[expose] def GGQ2WeylNormB (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    ∀ (α : Fin n → Module.Dual (ZMod 3) U), (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
      ∀ T : U ≃ₗ[ZMod 3] U,
        T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) → T ∈ ggQ2WeylOf h α

private theorem ggWAutD_normB_C (n : ℕ) (hn : 3 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : GGIntCartan (CoxeterMatrix.B n) C) : GGQ2WeylNormB n C := by
  classical
  intro U instACG instMod h hb hspan α hα T hT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfr : Module.finrank (ZMod 3) U = n := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  let D' : GGQ2Lin 3 :=
    { ι := Fin n
      coxeter := CoxeterMatrix.B n
      cartan := C
      V := U
      coroot := h
      root := α
      a := ⟨0, by omega⟩
      b := ⟨1, by omega⟩
      a_ne_b := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      a_leaf := by
        refine ⟨⟨1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
        · intro hh
          have := congrArg Fin.val hh
          simp at this
        · have hB3 : (CoxeterMatrix.B n) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 3 :=
            ggWAutD_B_zero_one (n := n) (by omega) rfl rfl
          rcases hC.2 (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (by
              intro hh; have := congrArg Fin.val hh; simp at this) with
            ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
          · rw [hB3] at hm; omega
          · rw [h1]; decide
          · rw [hB3] at hm; omega
          · rw [hB3] at hm; omega
        · intro y hy
          obtain ⟨hyne, hyC⟩ := hy
          have hBne2 : (CoxeterMatrix.B n) (⟨0, by omega⟩ : Fin n) y ≠ 2 := by
            intro hm2
            rcases hC.2 (⟨0, by omega⟩ : Fin n) y hyne.symm with
              ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
            · exact hyC h1
            · rw [hm2] at hm; omega
            · rw [hm2] at hm; omega
            · rw [hm2] at hm; omega
          have hyval : (y : ℕ) = 0 ∨ (y : ℕ) = 1 := by
            by_contra hcon
            push Not at hcon
            exact hBne2 (ggWAutD_B_zero_other (n := n) (by omega) rfl hcon.1 hcon.2)
          apply Fin.ext
          rcases hyval with h0 | h1
          · exact (hyne (Fin.ext h0)).elim
          · exact h1
      isWeyl := Or.inl ⟨n, Equiv.refl _, by omega,
        Or.inr (Or.inl ⟨by omega, (ggWAutD_reindex_refl (CoxeterMatrix.B n)).symm⟩)⟩
      isCartan := hC
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin n) = Module.finrank (ZMod 3) U
    exact ⟨hb, by simp [hfr]⟩
  have hgen : Set.range D'.simpleRefl =
      {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, fun v => by rw [GGQ2Lin.simpleRefl, Module.reflection_apply]⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      ext v
      rw [hj v, GGQ2Lin.simpleRefl, Module.reflection_apply]
  have hWclos : D'.weyl = Subgroup.closure (Set.range D'.simpleRefl) := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]
  have hweylEq : D'.weyl = ggQ2WeylOf h α := by
    rw [hWclos, hgen]
    rfl
  have hT' : T ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)) := by
    rwa [hweylEq]
  have hB : D'.coxeter = (CoxeterMatrix.B n).reindex (Equiv.refl (Fin n)) :=
    (ggWAutD_reindex_refl (CoxeterMatrix.B n)).symm
  obtain ⟨τ, ε, hε, hcor, hroot⟩ :=
    ggQ2_BC_coordinates D' hbas hn (Equiv.refl (Fin n)) hB
  let Tm := ggQ2x_Tm D' τ
  have hmapW : Subgroup.map Tm D'.weyl = ggBCW n := by
    rw [ggQ2x_map_weyl D' (Equiv.refl (Fin n)) τ ε hε hcor hroot,
      ggQ2x_W_eq_simple n (by omega)]
  have haN : Tm T ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
    have hmemN : Tm T ∈ (Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U))).map Tm :=
      Subgroup.mem_map_of_mem Tm hT'
    have h := (Subgroup.le_normalizer_map (f := Tm)) hmemN
    rwa [hmapW] at h
  have ha : Tm T ∈ ggBCW n := ggQ2_bc_normalizer n hn (Tm T) haN
  have hT'' : T ∈ D'.weyl := by
    have hmem : Tm T ∈ Subgroup.map Tm D'.weyl := by rw [hmapW]; exact ha
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
    have : y = T := ggQ2x_Tm_injective D' τ hyeq
    rwa [this] at hy
  exact hweylEq ▸ hT''

theorem ggQ2WeylNormB_holds {n : ℕ} (hn : 3 ≤ n) :
    GGQ2WeylNormB n (CartanMatrix.B n) ∧ GGQ2WeylNormB n (CartanMatrix.C n) :=
  ⟨ggWAutD_normB_C n hn (CartanMatrix.B n) (ggIntCartan_B n),
   ggWAutD_normB_C n hn (CartanMatrix.C n) (ggIntCartan_C n)⟩

theorem ggQ2WeylInner_B {m : ℕ} (hm : 3 ≤ m) : GGQ2WeylInner m (CartanMatrix.B m) := by
  intro U instACG instMod h hb hspan α hα T hT
  have hW : T ∈ ggQ2WeylOf h α :=
    (ggQ2WeylNormB_holds hm).1 h hb hspan α hα T hT
  exact ⟨T, hW, fun g _ => rfl⟩

theorem ggQ2WeylInner_C {m : ℕ} (hm : 3 ≤ m) : GGQ2WeylInner m (CartanMatrix.C m) := by
  intro U instACG instMod h hb hspan α hα T hT
  have hW : T ∈ ggQ2WeylOf h α :=
    (ggQ2WeylNormB_holds hm).2 h hb hspan α hα T hT
  exact ⟨T, hW, fun g _ => rfl⟩

end CFSG.StandardType

end
