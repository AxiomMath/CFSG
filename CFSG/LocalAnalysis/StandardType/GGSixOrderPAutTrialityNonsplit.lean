module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityPlanes
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.StandardType

open Module Multiplicative CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

namespace OrdPTri

variable {K : Type} [Field K] [Finite K] [CharP K 2]

namespace Frame4

variable {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}

omit [Finite K] in
theorem polar_pr (h : Frame4 ι₁) {i : Fin 4} {z : Fin (2 * 4) → K} (hz : z ∈ plane ι₁ i)
    (x : Fin (2 * 4) → K) :
    QuadraticMap.polar (coordinateQuadPlus 4 K) x z =
      QuadraticMap.polar (coordinateQuadPlus 4 K) (pr ι₁ i x) z := by
  conv_lhs => rw [h.eq_sum_pr x]
  have hsum : QuadraticMap.polar (coordinateQuadPlus 4 K) (∑ j, pr ι₁ j x) z =
      ∑ j, QuadraticMap.polar (coordinateQuadPlus 4 K) (pr ι₁ j x) z := by
    have e : QuadraticMap.polarBilin (coordinateQuadPlus 4 K) (∑ j, pr ι₁ j x) z =
        ∑ j, QuadraticMap.polarBilin (coordinateQuadPlus 4 K) (pr ι₁ j x) z := by
      rw [map_sum, LinearMap.sum_apply]
    exact e
  rw [hsum, Finset.sum_eq_single i]
  · intro j _ hji
    exact h.polar_eq_zero hji (h.pr_mem j x) hz
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [Finite K] in
theorem eq_zero_of_polar (h : Frame4 ι₁) {i : Fin 4} {y : Fin (2 * 4) → K}
    (hy : y ∈ plane ι₁ i)
    (horth : ∀ z ∈ plane ι₁ i, QuadraticMap.polar (coordinateQuadPlus 4 K) y z = 0) : y = 0 := by
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  refine hnd.1 y fun z => ?_
  change QuadraticMap.polar (coordinateQuadPlus 4 K) y z = 0
  rw [QuadraticMap.polar_comm, h.polar_pr hy z, QuadraticMap.polar_comm]
  exact horth _ (h.pr_mem i z)

end Frame4

theorem ggD4NonsplitTwoLocalInput_holds : GGD4NonsplitTwoLocalInput := by
  classical
  intro K _ _ _ h3 E hE h81 T hT hET
  obtain ⟨ι₁, -, hrange, hkerle, hdim⟩ := exists_frame_four hE h81
  have hF : Frame4 ι₁ := ⟨hkerle, hdim⟩
  have hEmem : ∀ s, ι₁ (ofAdd s) ∈ E := fun s => hrange ▸ ⟨_, rfl⟩
  set W : Submodule K (Fin (2 * 4) → K) := ⨅ t : T, LinearMap.ker (omRep (t : Om8 K) - 1)
    with hWdef
  have hmemW : ∀ v, v ∈ W ↔ ∀ t ∈ T, omRep t v = v := by
    intro v
    rw [hWdef, Submodule.mem_iInf]
    constructor
    · intro hv t ht
      have h1 := hv ⟨t, ht⟩
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    · intro hv t
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hv t t.2
  have hWE : ∀ s, ∀ v ∈ W, Frame4.fr ι₁ s v ∈ W := by
    intro s v hv
    rw [hmemW] at hv ⊢
    intro t ht
    set e := ι₁ (ofAdd s)
    have he : e⁻¹ * t * e ∈ T := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hET (hEmem s))) t).mp ht
      rwa [inv_inv] at h1
    have h2 : omRep t (omRep e v) = omRep e (omRep (e⁻¹ * t * e) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        show e * (e⁻¹ * t * e) = t * e by group]
    change omRep t (omRep e v) = omRep e v
    rw [h2, hv _ he]
  have hWpr : ∀ i, ∀ v ∈ W, Frame4.pr ι₁ i v ∈ W := fun i v hv => by
    rw [Frame4.pr_apply]
    exact W.add_mem (hWE _ v hv) (hWE _ _ (hWE _ v hv))
  have hdich : ∀ i, Frame4.plane ι₁ i ≤ W ∨ ∀ v ∈ W, Frame4.pr ι₁ i v = 0 := by
    intro i
    by_cases hall : ∀ v ∈ W, Frame4.pr ι₁ i v = 0
    · exact Or.inr hall
    · left
      push Not at hall
      obtain ⟨w, hw, hw0⟩ := hall
      have hpw := hWpr i w hw
      intro z hz
      obtain ⟨α, β, rfl⟩ := hF.exists_eq_smul_add h3 (hF.pr_mem i w) hw0 hz
      exact W.add_mem (W.smul_mem _ hpw) (W.smul_mem _ (hWE _ _ hpw))
  set S : Finset (Fin 4) := Finset.univ.filter (fun i => Frame4.plane ι₁ i ≤ W) with hSdef
  set U : Submodule K (Fin (2 * 4) → K) := ⨅ i ∈ S, LinearMap.ker (Frame4.pr ι₁ i) with hUdef
  have hmemU : ∀ v, v ∈ U ↔ ∀ i ∈ S, Frame4.pr ι₁ i v = 0 := by
    intro v
    simp only [hUdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hmemS : ∀ i, i ∈ S ↔ Frame4.plane ι₁ i ≤ W := by
    intro i
    simp [hSdef]
  have hUW : ∀ v ∈ U, v ∈ W → v = 0 := by
    intro v hvU hvW
    rw [hF.eq_sum_pr v]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · exact (hmemU v).mp hvU i hi
    · exact ((hdich i).resolve_left fun h => hi ((hmemS i).mpr h)) v hvW
  have hTU : ∀ t ∈ T, ∀ u ∈ U, omRep t u ∈ U := by
    intro t ht u hu
    rw [hmemU]
    intro i hi
    have hPW := (hmemS i).mp hi
    refine hF.eq_zero_of_polar (hF.pr_mem i _) fun z hz => ?_
    have hzW : omRep t z = z := (hmemW z).mp (hPW hz) t ht
    rw [← hF.polar_pr hz, ← hzW, Frame4.polar_omRep, hF.polar_pr hz,
      (hmemU u).mp hu i hi, QuadraticMap.polar_zero_left]
  have hUbot : U = ⊥ := by
    by_contra hne
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let ρU : T →* Module.End K U :=
      { toFun := fun t => (omRep (t : Om8 K)).restrict (fun u hu => hTU t t.2 u hu)
        map_one' := by
          refine LinearMap.ext fun u => Subtype.ext ?_
          simp
        map_mul' := by
          intro a b
          refine LinearMap.ext fun u => Subtype.ext ?_
          simp [Module.End.mul_apply] }
    obtain ⟨v, hv0, hvfix⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero ρU 2 ⊤
      (hT.to_subgroup ⊤)
    apply hv0
    refine Subtype.ext (hUW _ v.2 ((hmemW _).mpr fun t ht => ?_))
    have h1 := hvfix ⟨t, ht⟩ (Subgroup.mem_top _)
    exact congrArg Subtype.val h1
  have hS : ∀ i, Frame4.plane ι₁ i ≤ W := by
    intro i
    by_contra hi
    have hle : Frame4.plane ι₁ i ≤ U := by
      intro v hv
      rw [hmemU]
      intro j hj
      have hji : j ≠ i := fun e => hi (e ▸ (hmemS j).mp hj)
      exact hF.pr_eq_zero hji hv
    rw [hUbot] at hle
    have h2 := hF.finrank_plane i
    rw [le_bot_iff.mp hle, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  have hWtop : ∀ v, v ∈ W := by
    intro v
    rw [hF.eq_sum_pr v]
    exact Submodule.sum_mem _ fun i _ => hS i (hF.pr_mem i v)
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have h1 : ∀ v, omRep t v = v := fun v => (hmemW v).mp (hWtop v) t ht
  have hmat : ((t : Om8 K) : GL (Fin (2 * 4)) K).val = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← omRep_apply, h1]
  exact Subtype.ext (Units.ext hmat)

omit [Finite K] [CharP K 2] in
theorem not_two_dvd_card_aut [Finite K] [CharP K 2] (h3 : ¬ 3 ∣ Nat.card K - 1) :
    ¬ 2 ∣ Nat.card (K ≃+* K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hAut := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    hK).1
  change Nat.card (RingAut K) = (n : ℕ) at hAut
  change ¬ 2 ∣ Nat.card (RingAut K)
  rw [hAut]
  rintro ⟨m, hm⟩
  apply h3
  rw [hK, hm, pow_mul]
  have h := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 m
  rwa [one_pow, show 2 ^ 2 - 1 = 3 by norm_num] at h

omit [Finite K] [CharP K 2] in
theorem fieldAutP_eq_one_of_sq (h2 : ¬ 2 ∣ Nat.card (K ≃+* K)) {σ : K ≃+* K}
    (h : AutOm.fieldAutP 4 σ ^ 2 = 1) : AutOm.fieldAutP 4 σ = 1 := by
  have h1 : orderOf (AutOm.fieldAutP 4 σ) ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h2' : orderOf (AutOm.fieldAutP 4 σ) ∣ orderOf σ := orderOf_map_dvd _ σ
  have h3' : orderOf σ ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard σ
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2'.trans h3') h2

theorem fieldAutP_sq_mem_inner {γ : Om8 K} {σ : K ≃+* K} {c : MulAut (Om8 K)}
    (hc : c = AutOm.fieldAutP 4 σ ∨ c = AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ)
    (h : (MulAut.conj γ * c) ^ 2 = 1) : AutOm.fieldAutP 4 σ ^ 2 ∈ Inn (Om8 K) := by
  have hc2 : c ^ 2 = AutOm.fieldAutP 4 σ ^ 2 := by
    rcases hc with rfl | rfl
    · rfl
    · rw [sq, sq, mul_assoc, ← mul_assoc (AutOm.fieldAutP 4 σ),
        ← AutOm.plusRefl_mul_fieldAutP, mul_assoc, ← mul_assoc (AutOm.plusRefl one_le_four),
        AutOm.plusRefl_mul_self, one_mul]
  rw [conj_mul_sq, hc2] at h
  rw [eq_inv_of_mul_eq_one_right h, ← map_inv]
  exact ⟨_, rfl⟩

theorem exists_conj_mul_compl_of_fix_six (α : MulAut (Om8 K)) {b : Om8 K}
    (hb3 : b ^ 3 = 1) (hb6 : omFixDim b = 6) (hfix : α b = b) :
    ∃ γ : Om8 K, ∃ c ∈ AutOm.plusCompl (K := K) one_le_four,
      α = MulAut.conj γ * c := by
  obtain ⟨ι, ⟨γ, rfl⟩, k, c, ⟨σ, hcσ⟩, htd⟩ := exists_inner_mul_theta_pow_mul α
  have hαb := hfix
  rw [htd, MulAut.mul_apply, MulAut.mul_apply] at hαb
  have hd1 : omFixDim ((theta ^ k) (c b)) = 6 := by
    rw [← omFixDim_conj γ, hαb, hb6]
  have hdc : omFixDim (c b) = 6 := by
    rcases hcσ with rfl | rfl
    · rw [omFixDim_fieldAutP, hb6]
    · rw [MulAut.mul_apply, omFixDim_plusRefl, omFixDim_fieldAutP, hb6]
  have hcb3 : c b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hcls := (ggD4TrialityClassInput_holds K (c b) hcb3).1 hdc
  have hk : (theta : MulAut (Om8 K)) ^ k = 1 := by
    rw [pow_eq_pow_mod k theta_cube] at hd1 ⊢
    have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hkm : k % 3
    · rfl
    · rw [pow_one] at hd1
      omega
    · rw [theta_sq] at hd1
      omega
  rw [hk, one_mul] at htd
  exact ⟨γ, c, ⟨σ, hcσ⟩, htd⟩

theorem exists_matrixIsometry_of_fix_six_of_card_two (hK : Nat.card K = 2)
    (α : MulAut (Om8 K)) {b : Om8 K} (hb3 : b ^ 3 = 1) (hb6 : omFixDim b = 6)
    (hfix : α b = b) :
    ∃ g : GL (Fin (2 * 4)) K, g ∈ matrixIsometries (coordinateQuadPlus 4 K) ∧
      ∀ y : Om8 K, ((α y : Om8 K) : GL (Fin (2 * 4)) K) = g * y * g⁻¹ := by
  obtain ⟨γ, c, ⟨σ, hc⟩, hα⟩ := exists_conj_mul_compl_of_fix_six α hb3 hb6 hfix
  obtain ⟨a, -, hau⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have ha1 : a = 1 := (hau 1 one_ne_zero).symm
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro z
    change σ z = z
    by_cases hz : z = 0
    · simp [hz]
    · rw [hau z hz, ha1, map_one]
  have hfield : AutOm.fieldAutP 4 σ = 1 := by rw [hσ, map_one]
  rcases hc with hc | hc
  · rw [hc, hfield, mul_one] at hα
    refine ⟨γ, matrixDerived_le_isometries _ γ.2, ?_⟩
    intro y
    rw [hα, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [hc, hfield, mul_one] at hα
    let r : GL (Fin (2 * 4)) K := reflMat (coordinateQuadPlus 4 K)
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four)
    let g : GL (Fin (2 * 4)) K := (γ : GL (Fin (2 * 4)) K) * r
    refine ⟨g, (matrixIsometries _).mul_mem (matrixDerived_le_isometries _ γ.2)
      (reflMat_mem_isometries _ _), ?_⟩
    intro y
    rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    change (γ : GL (Fin (2 * 4)) K) * (AutOm.plusRefl one_le_four y).val *
      (γ : GL (Fin (2 * 4)) K)⁻¹ = g * y * g⁻¹
    rw [reflAut_apply_val]
    dsimp [g, r]
    rw [mul_inv_rev]
    simp only [mul_assoc]

theorem ggD4NonsplitOuterInvolutionInput_holds : GGD4NonsplitOuterInvolutionInput := by
  classical
  intro K _ _ _ h3 E hE h81 t ht2 htI
  by_contra hfix
  push Not at hfix
  obtain ⟨ι₁, -, hrange, hkerle, hdim⟩ := exists_frame_four hE h81
  have hF : Frame4 ι₁ := ⟨hkerle, hdim⟩
  have hEmem : ∀ s, ι₁ (ofAdd s) ∈ E := fun s => hrange ▸ ⟨_, rfl⟩
  set b := ι₁ (ofAdd (uvec 0)) with hbdef
  have hb6 : omFixDim b = 6 := hF.finrank_ker_b 0
  have hb3 : b ^ 3 = 1 := ofAdd_pow_three ι₁ _
  have htb := hfix b (hEmem _)
  obtain ⟨γ, c, ⟨σ, hcσ⟩, htd⟩ := exists_conj_mul_compl_of_fix_six t hb3 hb6 htb
  have hodd := not_two_dvd_card_aut h3
  have hφ : AutOm.fieldAutP 4 σ = 1 := by
    refine fieldAutP_eq_one_of_sq hodd ?_
    have hmem := fieldAutP_sq_mem_inner hcσ (by rw [← htd]; exact ht2)
    rw [← map_pow] at hmem ⊢
    exact NbrGraphD4.fieldAutP_eq_one_of_mem_inner hmem
  rcases hcσ with rfl | rfl
  · rw [hφ, mul_one] at htd
    exact htI (htd ▸ ⟨γ, rfl⟩)
  rw [hφ, mul_one] at htd
  set g : GL (Fin (2 * 4)) K := (γ : GL (Fin (2 * 4)) K) * reflMat (coordinateQuadPlus 4 K)
    (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
    (AutOm.plusUnitVector_form_ne_zero one_le_four) with hgdef
  have htg : ∀ x : Om8 K, ((t x : Om8 K) : GL (Fin (2 * 4)) K) = g * x * g⁻¹ := by
    intro x
    rw [htd, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    change (γ : GL (Fin (2 * 4)) K) * (AutOm.plusRefl one_le_four x).val *
      (γ : GL (Fin (2 * 4)) K)⁻¹ = g * x * g⁻¹
    rw [reflAut_apply_val, hgdef, mul_inv_rev]
    simp only [mul_assoc]
  have hgE : ∀ s, glin g * Frame4.fr ι₁ s = Frame4.fr ι₁ s * glin g := by
    intro s
    have h1 := congrArg (fun x : Om8 K => (x : GL (Fin (2 * 4)) K))
      (hfix (ι₁ (ofAdd s)) (hEmem s))
    rw [htg] at h1
    have h2 : g * (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K) = (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K) * g := by
      calc g * (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K)
          = (g * (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K) * g⁻¹) * g := by group
        _ = (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K) * g := by rw [h1]
    have hfr : Frame4.fr ι₁ s = glin (ι₁ (ofAdd s) : GL (Fin (2 * 4)) K) :=
      LinearMap.ext fun v => by rw [omRep_apply, glin_apply]
    rw [hfr, ← glin_mul, ← glin_mul, h2]
  have hgq : g ^ (Nat.card K ^ 2) = g := by
    apply glin_injective
    have h1 := hF.pow_card_sq_eq h3 hgE
    rw [← h1]
    clear h1
    induction Nat.card K ^ 2 with
    | zero => rw [pow_zero, pow_zero, glin_one]
    | succ m ih => rw [pow_succ, pow_succ, glin_mul, ih]
  have htm : ∀ m : ℕ, ∀ x : Om8 K, (((t ^ m) x : Om8 K) : GL (Fin (2 * 4)) K) =
      g ^ m * x * (g ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, htg]
      group
  have hfin : Nat.card K ^ 2 ≠ 0 := pow_ne_zero 2 Nat.card_pos.ne'
  obtain ⟨m, hm⟩ : ∃ m, Nat.card K ^ 2 = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hfin).symm⟩
  have hgm : g ^ m = 1 := by
    rw [hm, pow_succ] at hgq
    exact mul_eq_right.mp hgq
  have htm1 : t ^ m = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [htm, hgm, one_mul, inv_one, mul_one, MulAut.one_apply]
  have h2K : 2 ∣ Nat.card K := by
    classical
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.pos.ne'
  have hmodd : Odd m := by
    obtain ⟨a, ha⟩ := h2K
    rw [ha] at hm
    have hm' : m + 1 = 4 * (a * a) := by rw [← hm]; ring
    exact ⟨2 * (a * a) - 1, by omega⟩
  obtain ⟨j, hj⟩ := hmodd
  have ht1 : t = 1 := by
    have e : t = t ^ m * ((t ^ 2) ^ j)⁻¹ := by
      rw [← pow_mul, hj, pow_succ', mul_inv_cancel_right]
    rw [e, htm1, ht2, one_pow, inv_one, one_mul]
  exact htI (ht1 ▸ one_mem _)

end OrdPTri

end CFSG.StandardType
