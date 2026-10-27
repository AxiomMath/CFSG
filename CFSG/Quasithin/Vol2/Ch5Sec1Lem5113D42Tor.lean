module

public import CFSG.Quasithin.H13.NQCatBND4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4LeviZ

public section

namespace CFSG.Quasithin.H13.D42C

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.RankTwoExceptional.D4

section Field

variable {K : Type} [Field K] (σ : K ≃+* K)


theorem cube_apply [Finite K] (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) (c : K) :
    σ (σ (σ c)) = c := by
  have := Fintype.ofFinite K
  have h8 : c ^ 8 = c := by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at this
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
  exact h8

theorem eq_zero_or_one_of_mem (hσ : ∀ c, σ c = c ^ 2) {c : K}
    (hc : c ∈ trialityFixedField K σ.toRingHom) : c = 0 ∨ c = 1 := by
  have h1 : c ^ 2 = c := by
    rw [← hσ]
    exact hc
  have h2 : c * (c - 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem units_fixed_eq_one (hσ : ∀ c, σ c = c ^ 2)
    (β : (trialityFixedField K σ.toRingHom)ˣ) : β = 1 := by
  rcases eq_zero_or_one_of_mem σ hσ (β : trialityFixedField K σ.toRingHom).2 with h | h
  · exact absurd (Subtype.ext h) β.ne_zero
  · exact Units.ext (Subtype.ext h)

theorem norm_eq_one [Finite K] (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) (a : Kˣ) :
    (a : K) * σ a * σ (σ a) = 1 := by
  have := Fintype.ofFinite K
  have h7 : (a : K) ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (a : K) a.ne_zero
    rwa [← Nat.card_eq_fintype_card, hK] at this
  rw [hσ, hσ, ← pow_mul]
  calc (a : K) * (a : K) ^ 2 * (a : K) ^ (2 * 2) = (a : K) ^ 7 := by ring
    _ = 1 := h7

end Field

section SL2

variable {L : Type*} [Field L] [CharP L 2]

theorem uSL_one_sq : uSL (1 : L) * uSL 1 = 1 := by
  have h2 : (1 : L) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem vSL_one_sq : vSL (1 : L) * vSL 1 = 1 := by
  have h2 : (1 : L) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_vSL, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem coe_uSL_mul_vSL :
    ((uSL (1 : L) * vSL 1 : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 1] := by
  have h2 : (1 : L) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem uSL_mul_vSL_pow_three : (uSL (1 : L) * vSL 1) ^ 3 = 1 := by
  have h2 : (1 : L) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_uSL_mul_vSL, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem uSL_mul_vSL_ne_one : uSL (1 : L) * vSL 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simp only [coe_uSL_mul_vSL, Matrix.SpecialLinearGroup.coe_one] at h1
  simp at h1

theorem uSL_conj_uSL_mul_vSL :
    uSL (1 : L) * (uSL 1 * vSL 1) * (uSL 1)⁻¹ = (uSL 1 * vSL 1)⁻¹ := by
  have hu : (uSL (1 : L))⁻¹ = uSL 1 := inv_eq_of_mul_eq_one_right uSL_one_sq
  have hv : (vSL (1 : L))⁻¹ = vSL 1 := inv_eq_of_mul_eq_one_right vSL_one_sq
  rw [mul_inv_rev, hu, hv, ← mul_assoc, uSL_one_sq, one_mul]

theorem WSL_mul_uSL_mul_vSL :
    WSL * (uSL (1 : L) * vSL 1) = (uSL 1 * vSL 1) ^ 2 * WSL := by
  have h2 : (1 : L) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hn : (-1 : L) = 1 := CharTwo.neg_eq 1
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_WSL,
    coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, h2, hn]

theorem WSL_conj_uSL_mul_vSL :
    WSL * (uSL (1 : L) * vSL 1) * WSL⁻¹ = (uSL 1 * vSL 1) ^ 2 := by
  rw [WSL_mul_uSL_mul_vSL, mul_inv_cancel_right]

end SL2

section Conj

variable {G : Type*} [Group G]

theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_eq_of_conj_mem {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : H.map (MulAut.conj g).toMonoidHom = H := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem mem_normalizer_of_conj_mem {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hmap := map_conj_eq_of_conj_mem h
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  exact this ▸ hy

theorem exists_conj_of_card_eq_three [Finite G] {H D D' : Subgroup G} (hD : D ≤ H)
    (hD' : D' ≤ H) (h3 : Nat.card D = 3) (h3' : Nat.card D' = 3) (h9 : ¬ 9 ∣ Nat.card H) :
    ∃ h ∈ H, D.map (MulAut.conj h).toMonoidHom = D' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := D.subgroupOf H
  set Q := D'.subgroupOf H
  have hcP : Nat.card P = 3 := by
    rw [← h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  have hcQ : Nat.card Q = 3 := by
    rw [← h3']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD').toEquiv
  have hidx : ∀ S : Subgroup ↥H, Nat.card S = 3 → ¬ 3 ∣ S.index := by
    intro S hS hd
    apply h9
    have h := S.card_mul_index
    rw [hS] at h
    obtain ⟨m, hm⟩ := hd
    rw [hm] at h
    exact ⟨m, by rw [← h]; ring⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hcP, pow_one])
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hcQ, pow_one])
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (hP3.toSylow (hidx P hcP))
    (hQ3.toSylow (hidx Q hcQ))
  have hPQ : P.map (MulAut.conj h).toMonoidHom = Q := by
    have h1 := congrArg (fun S : Sylow 3 ↥H => (S : Subgroup ↥H)) hh
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨h, h.2, ?_⟩
  have eD : P.map H.subtype = D := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD]
  have eD' : Q.map H.subtype = D' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD']
  rw [← eD, ← eD', ← hPQ, Subgroup.map_map, Subgroup.map_map]
  congr 1

end Conj


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem exists_eq_outerTorus (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {h : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :
    ∃ a : Kˣ, h = trialityOuterTorus K σ a := by
  have hσ3 := cube_apply σ hK hσ
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, hT, hU, rfl⟩ :=
    exists_borel_coords σ hσ3 (graphFixedRootTorus_le_graphFixedRootBorel hh)
  have hβ := units_fixed_eq_one σ hσ β
  subst hβ
  have hu : d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊓
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    refine ⟨?_, hU⟩
    have := mul_mem (inv_mem hT) hh
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  rw [graphFixedRootTorus_inf_graphFixedPosUnipotent, Subgroup.mem_bot] at hu
  refine ⟨a, ?_⟩
  rw [hu, mul_one, trialityMiddleTorus, map_one, torusElt_one, mul_one]

theorem torus_commute_d4x₂ (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {h : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (c : K) : h * d4x₂ K c = d4x₂ K c * h := by
  obtain ⟨a, rfl⟩ := exists_eq_outerTorus σ hK hσ hh
  have h1 := ho_conj_d4x₂ σ a c
  rw [norm_eq_one σ hK hσ a, inv_one, one_mul] at h1
  calc trialityOuterTorus K σ a * d4x₂ K c =
      trialityOuterTorus K σ a * d4x₂ K c * (trialityOuterTorus K σ a)⁻¹ *
        trialityOuterTorus K σ a := by group
    _ = d4x₂ K c * trialityOuterTorus K σ a := by rw [h1]

theorem torus_commute_d4y₂ (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {h : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (c : K) : h * d4y₂ K c = d4y₂ K c * h := by
  obtain ⟨a, rfl⟩ := exists_eq_outerTorus σ hK hσ hh
  have h1 := ho_conj_d4y₂ σ a c
  rw [norm_eq_one σ hK hσ a, inv_one, inv_one, one_mul] at h1
  calc trialityOuterTorus K σ a * d4y₂ K c =
      trialityOuterTorus K σ a * d4y₂ K c * (trialityOuterTorus K σ a)⁻¹ *
        trialityOuterTorus K σ a := by group
    _ = d4y₂ K c * trialityOuterTorus K σ a := by rw [h1]

theorem torus_commute_d4Ma (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {h : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    {m : ModGL TwistTag.D4.tag K} (hm : m ∈ d4Ma K σ) : h * m = m * h := by
  have hC : d4Ma K σ ≤ Subgroup.centralizer {h} := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      dsimp only
      rw [coe_orbitX_one_d4]
      exact (torus_commute_d4x₂ σ hK hσ hh _).symm
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      dsimp only
      rw [coe_orbitY_one_d4]
      exact (torus_commute_d4y₂ σ hK hσ hh _).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hm)).symm


section Ma

@[expose] noncomputable def subgroupThree : Subgroup (ModGL TwistTag.D4.tag K) :=
  (Subgroup.zpowers (uSL (1 : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) *
    vSL 1)).map (orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)

omit
  [Finite K] [CharP K 2] in
theorem subgroupThree_le_d4Ma : subgroupThree σ ≤ d4Ma K σ := by
  rintro _ ⟨g, -, rfl⟩
  change _ ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
  rw [orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ⟨g, rfl⟩

theorem card_subgroupThree (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card (subgroupThree σ) = 3 := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => cube_apply σ hK hσ c
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [subgroupThree, Subgroup.card_map_of_injective (orbitRankOneHom_injective_D4 hσ3 _),
    Nat.card_zpowers]
  exact orderOf_eq_prime uSL_mul_vSL_pow_three uSL_mul_vSL_ne_one

omit
  [Finite K] in
theorem orbitX_conj_of_mem_subgroupThree {f : ModGL TwistTag.D4.tag K}
    (hf : f ∈ subgroupThree σ) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K) * f *
      (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K)⁻¹ = f⁻¹ := by
  obtain ⟨g, ⟨k, rfl⟩, rfl⟩ := hf
  rw [← orbitRankOneHom_uSL, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  change uSL 1 * (uSL 1 * vSL 1) ^ k * (uSL 1)⁻¹ = ((uSL 1 * vSL 1) ^ k)⁻¹
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, uSL_conj_uSL_mul_vSL, inv_zpow]

omit
  [Finite K] in
theorem canonicalRep_conj_mem_subgroupThree {f : ModGL TwistTag.D4.tag K}
    (hf : f ∈ subgroupThree σ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection ⟨1, by decide⟩) * f *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection ⟨1, by decide⟩))⁻¹ ∈ subgroupThree σ := by
  obtain ⟨g, ⟨k, rfl⟩, rfl⟩ := hf
  rw [canonicalRep_orbitReflection_eq_orbitN (σ := σ.toRingHom), ← orbitRankOneHom_WSL,
    ← map_inv, ← map_mul, ← map_mul]
  refine ⟨_, ⟨2 * k, ?_⟩, rfl⟩
  change (uSL 1 * vSL 1) ^ (2 * k) = WSL * (uSL 1 * vSL 1) ^ k * WSL⁻¹
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, WSL_conj_uSL_mul_vSL, ← zpow_natCast,
    ← zpow_mul]
  norm_num

end Ma

theorem not_isSolvable_d4Mr (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) :
    ¬ Group.IsSolvable ↥(d4Mr K σ) := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => cube_apply σ hK hσ c
  set L := orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ with hLdef
  have hL : Nat.card L = 8 := by
    rw [hLdef, orbitField_D4_zero_eq_top σ (cube_apply σ hK hσ), ← hK]
    exact Nat.card_congr Subfield.topEquiv.toEquiv
  have h4 : ∃ s : Finset L, s.card = 4 := by
    have := Fintype.ofFinite L
    have hle : 4 ≤ (Finset.univ : Finset L).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hL]
      norm_num
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  intro hs
  apply CFSG.Quasithin.H13.NQCat.BN.not_isSolvable_sl2 h4
  let e : SL2 L ≃* ↥(d4Mr K σ) :=
    (MonoidHom.ofInjective (orbitRankOneHom_injective_D4 hσ3 ⟨0, by decide⟩)).trans
      (MulEquiv.subgroupCongr (orbitRankOneHom_range (t := TwistTag.D4) (K := K)
        (σ := σ.toRingHom) ⟨0, by decide⟩))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

section Over

omit [Finite K] [CharP K 2]
  in
theorem map_conj_le_of_cell {R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hUR : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ R)
    (hBU : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)))
    (a : Fin TwistTag.D4.foldedTag.rank) {c u : ModGL TwistTag.D4.tag K}
    (hc : c ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hg : c * canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) * u ∈
      R) :
    (orbitRankOneGroup TwistTag.D4 K σ.toRingHom a).map (MulAut.conj c).toMonoidHom ≤ R := by
  rw [orbitRankOneGroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, (⟨d, rfl⟩ | ⟨d, rfl⟩), rfl⟩
  · refine hUR ?_
    change c * (orbitX TwistTag.D4 K σ.toRingHom a d : ModGL TwistTag.D4.tag K) * c⁻¹ ∈ _
    exact (Subgroup.mem_normalizer_iff.mp (hBU hc) _).mp
      (orbitX_mem_graphFixedPosUnipotent _ _ a d)
  · have hx : u⁻¹ * (orbitX TwistTag.D4 K σ.toRingHom a (-d) : ModGL TwistTag.D4.tag K) * u ∈ R :=
      hUR (mul_mem (mul_mem (inv_mem hu) (orbitX_mem_graphFixedPosUnipotent _ _ a (-d))) hu)
    have h1 := mul_mem (mul_mem hg hx) (inv_mem hg)
    change c * (orbitY TwistTag.D4 K σ.toRingHom a d : ModGL TwistTag.D4.tag K) * c⁻¹ ∈ R
    rw [← canonicalRep_orbitReflection_conj_orbitX TwistTag.D4 σ.toRingHom a d]
    convert h1 using 1
    group

omit [Finite K] [CharP K 2] in
theorem borel_le_normalizer :
    graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have h := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  rw [← h]
  exact inf_le_right

omit [Finite K] [CharP K 2] in
theorem inf_normalizer_eq_borel :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K)) =
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  exact (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1

theorem solvable_overgroup (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hUR : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ R)
    (hRC : R ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hR : Group.IsSolvable ↥R) :
    R ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom ∨
      (R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} ∧
        ∃ c ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
          (d4Ma K σ).map (MulAut.conj c).toMonoidHom ≤ R) := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => cube_apply σ hK hσ c
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hres := CFSG.QuasithinUnique.Setup.X6.triality_residualOvergroupsAt σ
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hRne : R.subgroupOf C ≠ ⊤ := by
    intro htop
    have hCR : C ≤ R := fun x hx => by
      have : (⟨x, hx⟩ : ↥C) ∈ R.subgroupOf C := htop ▸ Subgroup.mem_top _
      exact this
    apply not_isSolvable_d4Mr σ hK hσ
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion ((d4Mr_le σ hσ3).trans hCR)) (Subgroup.inclusion_injective _)
  obtain ⟨M', hM', hRM'⟩ := (eq_top_or_exists_le_coatom (R.subgroupOf C)).resolve_left hRne
  have hUR' : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C ≤ R.subgroupOf C :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (hUR (Subgroup.mem_subgroupOf.mp hx))
  have hUM' : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C ≤ M' :=
    hUR'.trans hRM'
  obtain ⟨j, hj⟩ := (hres.2.2.1 M' hUM').mp hM'.covBy_top
  set a := CFSG.QuasithinUnique.Setup.X6.d4Index j with ha
  have hRP : R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
    intro x hx
    have : (⟨x, hRC hx⟩ : ↥C) ∈ M' := hRM' hx
    rw [hj, Subgroup.mem_subgroupOf] at this
    exact this
  by_cases hRB : R ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom
  · exact Or.inl hRB
  obtain ⟨g, hgR, hgB⟩ := Set.not_subset.mp hRB
  rcases (CFSG.Quasithin.F134.LieD4.mem_graphFixedParabolic_singleton_iff σ.surjective).mp
    (hRP hgR) with hg | ⟨c, hc, u, hu, rfl⟩
  · exact absurd hg hgB
  have hcM := map_conj_le_of_cell σ hUR (borel_le_normalizer σ) a hc
    (graphFixedInversionUnipotent_le_graphFixedPosUnipotent _ hu) hgR
  rcases CFSG.QuasithinUnique.Setup.X6.foldedRank_D4_cases a with h0 | h1
  · exfalso
    apply not_isSolvable_d4Mr σ hK hσ
    rw [h0] at hcM
    have e := (d4Mr K σ).equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    have : Group.IsSolvable ↥((d4Mr K σ).map (MulAut.conj c).toMonoidHom) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hcM)
        (Subgroup.inclusion_injective _)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · rw [h1] at hRP hcM
    exact Or.inr ⟨hRP, c, hc, hcM⟩

end Over

section Para

omit [Finite K] [CharP K 2]
  in
theorem orbitRankOneGroup_le_parabolic (a : Fin TwistTag.D4.foldedTag.rank) :
    orbitRankOneGroup TwistTag.D4 K σ.toRingHom a ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
  have hX : ∀ c : orbitField TwistTag.D4 K σ.toRingHom a,
      (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := fun c =>
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
      (graphFixedPosUnipotent_le_graphFixedRootBorel
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _))
  have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, rfl, rfl⟩)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hX c
  · show (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈ _
    rw [← canonicalRep_orbitReflection_conj_orbitX TwistTag.D4 σ.toRingHom a c]
    exact mul_mem (mul_mem hn (hX _)) (inv_mem hn)

omit
  [Finite K] [CharP K 2] in
theorem subgroupThree_le_parabolic :
    subgroupThree σ ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} :=
  (subgroupThree_le_d4Ma σ).trans (orbitRankOneGroup_le_parabolic σ _)

omit [CharP K 2] in
theorem card_parabolic (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩}) =
      3 * Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) := by
  rw [CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton σ.surjective,
    CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ (n := 1) le_rfl
      (by rw [hK]; norm_num) (fun c => by rw [hσ c]; norm_num),
    (CFSG.QuasithinUnique.Setup.X6.card_orbit_D4).2]
  ring

theorem not_nine_dvd_card_parabolic (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2) :
    ¬ 9 ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩}) := by
  rw [card_parabolic σ hK hσ]
  have h3 := CFSG.Quasithin.F134.LieD4.not_three_dvd_card_graphFixedRootBorel (t := TwistTag.D4)
    (σ := σ.toRingHom) σ.surjective (by rw [hK])
  omega

end Para

section Three

theorem orbitX_mem_normalizer_subgroupThree :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K) ∈
      Subgroup.normalizer (subgroupThree σ : Set (ModGL TwistTag.D4.tag K)) := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  refine mem_normalizer_of_conj_mem fun f hf => ?_
  rw [orbitX_conj_of_mem_subgroupThree σ hf]
  exact inv_mem hf

theorem inversionUnipotent_le_normalizer (hσ : ∀ c, σ c = c ^ 2) :
    graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom
        (TwistTag.D4.orbitReflection ⟨1, by decide⟩) ≤
      Subgroup.normalizer (subgroupThree σ : Set (ModGL TwistTag.D4.tag K)) := by
  have hU : graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection ⟨1, by decide⟩) =
        orbitXSubgroup TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ := by
    rw [orbitXSubgroup, closure_range_orbitX, graphFixedInversionUnipotent,
      inversionSet_orbitReflection]
  rw [hU, orbitXSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  have hc : (c : K) = 0 ∨ (c : K) = 1 := by
    have h1 : σ (c : K) = c := (mem_orbitField_D4_one σ).1 c.2
    have h2 : (c : K) * ((c : K) - 1) = 0 := by
      rw [hσ] at h1
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hc with h | h
  · have : c = 0 := Subtype.ext h
    rw [this]
    dsimp only
    rw [orbitX_zero TwistTag.D4 σ.toRingHom, OneMemClass.coe_one]
    exact one_mem _
  · have : c = 1 := Subtype.ext h
    rw [this]
    exact orbitX_mem_normalizer_subgroupThree σ

theorem exists_map_conj_eq (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩}) :
    ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      (subgroupThree σ).map (MulAut.conj g).toMonoidHom =
        (subgroupThree σ).map (MulAut.conj u).toMonoidHom := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hB : ∀ c ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
      ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
        (subgroupThree σ).map (MulAut.conj c).toMonoidHom =
          (subgroupThree σ).map (MulAut.conj u).toMonoidHom := by
    intro c hc
    have hc' : c ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)) := hc
    rw [graphFixedRootBorel_eq_mul σ.surjective] at hc'
    obtain ⟨h, hh, u, hu, rfl⟩ := hc'
    have hhB := graphFixedRootTorus_le_graphFixedRootBorel hh
    refine ⟨h * u * h⁻¹, (Subgroup.mem_normalizer_iff.mp (borel_le_normalizer σ hhB) u).mp hu, ?_⟩
    rw [map_conj_mul, map_conj_mul, map_conj_mul,
      map_conj_eq_of_conj_mem (g := h⁻¹) fun f hf => by
        rw [torus_commute_d4Ma σ hK hσ (inv_mem hh) (subgroupThree_le_d4Ma σ hf),
          mul_inv_cancel_right]
        exact hf]
  rcases (CFSG.Quasithin.F134.LieD4.mem_graphFixedParabolic_singleton_iff σ.surjective).mp hg with
    hg | ⟨c, hc, v, hv, rfl⟩
  · exact hB g hg
  obtain ⟨u, hu, hcu⟩ := hB c hc
  refine ⟨u, hu, ?_⟩
  rw [mul_assoc, map_conj_mul, map_conj_eq_of_conj_mem (H := subgroupThree σ)
    (g := canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection ⟨1, by decide⟩) * v) (fun f hf => ?_), hcu]
  have hvN := inversionUnipotent_le_normalizer σ hσ hv
  have h1 : v * f * v⁻¹ ∈ subgroupThree σ := (Subgroup.mem_normalizer_iff.mp hvN f).mp hf
  have h2 := canonicalRep_conj_mem_subgroupThree σ h1
  have e : canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection ⟨1, by decide⟩) * v * f *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection ⟨1, by decide⟩) * v)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection ⟨1, by decide⟩) * (v * f * v⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection ⟨1, by decide⟩))⁻¹ := by
    group
  rw [e]
  exact h2

theorem exists_inverting (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {F : Subgroup (ModGL TwistTag.D4.tag K)}
    (hFP : F ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩})
    (hF : Nat.card F = 3) :
    ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, ∀ f ∈ F, u * f * u⁻¹ = f⁻¹ := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨g, hgP, hg⟩ := exists_conj_of_card_eq_three (subgroupThree_le_parabolic σ) hFP
    (card_subgroupThree σ hK hσ) hF (not_nine_dvd_card_parabolic σ hK hσ)
  obtain ⟨u, hu, hmap⟩ := exists_map_conj_eq σ hK hσ hgP
  have hx := orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom ⟨1, by decide⟩ 1
  refine ⟨u * orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 * u⁻¹,
    mul_mem (mul_mem hu hx) (inv_mem hu), fun f hf => ?_⟩
  rw [← hg, hmap] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  have h1 := orbitX_conj_of_mem_subgroupThree σ hf'
  change u * (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K) *
      u⁻¹ * (u * f' * u⁻¹) * (u * orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 * u⁻¹)⁻¹ =
    (u * f' * u⁻¹)⁻¹
  calc _ = u * ((orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K) *
        f' * (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K)⁻¹) *
        u⁻¹ := by group
    _ = (u * f' * u⁻¹)⁻¹ := by rw [h1]; group

theorem le_borel_or_relIndex_eq (hK : Nat.card K = 8) (hσ : ∀ c, σ c = c ^ 2)
    {R : Subgroup (ModGL TwistTag.D4.tag K)}
    (hUR : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ R)
    (hRC : R ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hR : Group.IsSolvable ↥R) :
    R ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom ∨
      (R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} ∧
        (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex R = 3) := by
  rcases solvable_overgroup σ hK hσ hUR hRC hR with h | ⟨hRP, -⟩
  · exact Or.inl h
  rcases CFSG.Quasithin.F134.LieD4.le_or_relIndex_eq σ.surjective hUR hRP with h | h
  · exact Or.inl h
  · refine Or.inr ⟨hRP, ?_⟩
    rw [h, CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ (n := 1) le_rfl
      (by rw [hK]; norm_num) (fun c => by rw [hσ c]; norm_num),
      (CFSG.QuasithinUnique.Setup.X6.card_orbit_D4).2]
    norm_num

end Three

section Abstract

theorem solvable_overgroup_3d42 {Y : Type} [Group Y] [Finite Y]
    (hY : ChevalleyExceptionalModel Y .trialityD4 2 1) {U : Subgroup Y}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {R : Subgroup Y} (hUR : U ≤ R)
    (hR : Group.IsSolvable ↥R) :
    R ≤ Subgroup.normalizer (U : Set Y) ∨
      (Nat.card R = 3 * Nat.card ↥(R ⊓ Subgroup.normalizer (U : Set Y)) ∧ ¬ 9 ∣ Nat.card R ∧
        ∀ F : Subgroup Y, F ≤ R → Nat.card F = 3 → ∃ u ∈ U, ∀ f ∈ F, u * f * u⁻¹ = f⁻¹) := by
  obtain ⟨K, _, _, σ, φ, hK, hσ, hφU, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_triality hY hU
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c]; norm_num
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) (by rw [hK8]; norm_num : Nat.card K = 2 ^ 3)
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  let ι : Y →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιC : ∀ y, ι y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun y => (φ y).2
  have hU₀C : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hmemU : ∀ y, y ∈ U ↔ ι y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    intro y
    have h1 : φ y ∈ U.map φ.toMonoidHom ↔ y ∈ U :=
      ⟨fun ⟨y', hy', he⟩ => φ.injective he ▸ hy', fun hy => ⟨y, hy, rfl⟩⟩
    rw [← h1, hφU, Subgroup.mem_subgroupOf]
    rfl
  have hU₀ι : ∀ v ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, ∃ u ∈ U, ι u = v := by
    intro v hv
    have hv' : (⟨v, hU₀C hv⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
        U.map φ.toMonoidHom := by
      rw [hφU, Subgroup.mem_subgroupOf]
      exact hv
    obtain ⟨u, hu, he⟩ := hv'
    exact ⟨u, hu, congrArg Subtype.val he⟩
  have hmemN : ∀ y, y ∈ Subgroup.normalizer (U : Set Y) ↔
      ι y ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    intro y
    constructor
    · intro hy
      rw [← inf_normalizer_eq_borel σ]
      refine ⟨hιC y, mem_normalizer_of_conj_mem fun v hv => ?_⟩
      obtain ⟨u, hu, rfl⟩ := hU₀ι v hv
      rw [← map_inv, ← map_mul, ← map_mul, ← hmemU]
      exact (Subgroup.mem_normalizer_iff.mp hy u).mp hu
    · intro hy
      have hyN := borel_le_normalizer σ hy
      refine mem_normalizer_of_conj_mem fun u hu => ?_
      rw [hmemU, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyN _).mp ((hmemU u).mp hu)
  have hUR₀ : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ R.map ι := fun v hv => by
    obtain ⟨u, hu, rfl⟩ := hU₀ι v hv
    exact ⟨u, hUR hu, rfl⟩
  have hR₀C : R.map ι ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨r, -, rfl⟩
    exact hιC r
  have eR := R.equivMapOfInjective ι hι
  have hR₀s : Group.IsSolvable ↥(R.map ι) :=
    Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom) eR.symm.injective
  have hcard : Nat.card (R.map ι) = Nat.card R := Subgroup.card_map_of_injective hι
  rcases le_borel_or_relIndex_eq σ hK8 hσ2 hUR₀ hR₀C hR₀s with hB | ⟨hRP, h3⟩
  · left
    intro r hr
    exact (hmemN r).mpr (hB ⟨r, hr, rfl⟩)
  right
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
      (R.map ι)
    have h2 : (R ⊓ Subgroup.normalizer (U : Set Y)).map ι =
        graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⊓ R.map ι := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyR, hyN⟩, rfl⟩
        exact ⟨(hmemN y).mp hyN, y, hyR, rfl⟩
      · rintro ⟨hzB, y, hyR, rfl⟩
        exact ⟨y, ⟨hyR, (hmemN y).mpr hzB⟩, rfl⟩
    rw [← hcard, ← h1, h3, ← h2, Subgroup.card_map_of_injective hι]
  · rw [← hcard]
    intro h9
    exact not_nine_dvd_card_parabolic σ hK8 hσ2 (h9.trans (Subgroup.card_dvd_of_le hRP))
  · intro F hFR hF
    have hF₀ : Nat.card (F.map ι) = 3 := by rw [Subgroup.card_map_of_injective hι, hF]
    obtain ⟨v, hv, hinv⟩ := exists_inverting σ hK8 hσ2
      ((Subgroup.map_mono hFR).trans hRP) hF₀
    obtain ⟨u, hu, rfl⟩ := hU₀ι v hv
    refine ⟨u, hu, fun f hf => hι ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinv _ ⟨f, hf, rfl⟩

end Abstract

end CFSG.Quasithin.H13.D42C
