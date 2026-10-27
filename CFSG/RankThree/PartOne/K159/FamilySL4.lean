module

public import CFSG.RankThree.PartOne.K159.FamilyConj
public import CFSG.RankThree.PartOne.K159.BorelSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
import CFSG.LieType.BorelTits.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

section Transport

variable {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}

theorem map_mem_maximalParabolics_equiv [Fact p.Prime] (e : G ≃* G') {M : Subgroup G}
    (h : M ∈ maximalParabolics G p) : M.map e.toMonoidHom ∈ maximalParabolics G' p := by
  obtain ⟨hM, B₀, ⟨T, rfl⟩, hle⟩ := h
  refine ⟨(OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) M).mpr hM, _,
    ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T, rfl⟩, ?_⟩
  rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hle

theorem map_mem_maximalParabolics_equiv_iff [Fact p.Prime] (e : G ≃* G') (M : Subgroup G) :
    M.map e.toMonoidHom ∈ maximalParabolics G' p ↔ M ∈ maximalParabolics G p := by
  refine ⟨fun h => ?_, map_mem_maximalParabolics_equiv e⟩
  have : Finite G' := Finite.of_equiv G e.toEquiv
  have := map_mem_maximalParabolics_equiv e.symm h
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rwa [Subgroup.map_map, hid, Subgroup.map_id] at this

end Transport

section Bridge

variable {K : Type} [Field K] [CharP K 2]

theorem scalars_four_eq_bot : scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have hc1 : (c : K) = 1 := by
    have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have h5 : ((c : K) - 1) ^ (2 ^ 2) = 0 := by
      rw [sub_pow_char_pow]
      simp [h4]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h5)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hA, hc1]
  simp

@[expose] noncomputable def slEquivProj : SpecialLinearGroup (Fin 4) K ≃* projectiveSL 4 K :=
  MulEquiv.ofBijective (proj 4 K)
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, scalars_four_eq_bot]), proj_surjective 4 K⟩

theorem map_slEquivProj_stabilizer (W : Submodule K (Fin 4 → K)) :
    (stabilizer W).map slEquivProj.toMonoidHom = projStabilizer W := rfl

end Bridge

theorem index_map_toMonoidHom {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) :
    (H.map e.toMonoidHom).index = H.index :=
  Subgroup.index_map_of_bijective e.bijective H

section Planes

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def planeIndex (q : ℕ) : ℕ := (q ^ 2 + 1) * (q ^ 2 + q + 1)

@[expose] def planeStabilizers (K : Type*) [Field K] :
    Set (Subgroup (SpecialLinearGroup (Fin 4) K)) :=
  {M | ∃ W : Submodule K (Fin 4 → K), finrank K W = 2 ∧ M = stabilizer W}

theorem gaussianCoeff_four_two {q : ℕ} (hq : 2 ≤ q) :
    gaussianCoeff 4 2 q = (planeIndex q : ℚ) := by
  have h1 : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have h2 : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    nlinarith
  simp only [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_zero, planeIndex]
  push_cast
  field_simp
  ring

omit [CharP K 2] in
theorem two_le_card : 2 ≤ Nat.card K := Finite.one_lt_card

omit [Finite K] [CharP K 2] in
theorem finrank_pos_lt_of_two {W : Submodule K (Fin 4 → K)} (hW : finrank K W = 2) :
    ⊥ < W ∧ W < ⊤ := by
  refine ⟨bot_lt_iff_ne_bot.2 fun h => ?_, lt_top_iff_ne_top.2 fun h => ?_⟩
  · rw [h] at hW
    simp at hW
  · rw [h] at hW
    simp at hW

theorem index_stabilizer_plane {W : Submodule K (Fin 4 → K)} (hW : finrank K W = 2) :
    (stabilizer W).index = planeIndex (Nat.card K) := by
  have h1 := (subspace_index (K := K) (n := 4) (k := 2) (by norm_num)).2 W hW
  rw [gaussianCoeff_four_two two_le_card] at h1
  have h2 : (stabilizer W).index = (projStabilizer W).index := by
    rw [← map_slEquivProj_stabilizer, index_map_toMonoidHom]
  rw [h2]
  exact_mod_cast h1

theorem mem_planeStabilizers_iff {M : Subgroup (SpecialLinearGroup (Fin 4) K)} :
    M ∈ planeStabilizers K ↔ M ∈ maximalParabolics (SpecialLinearGroup (Fin 4) K) 2 ∧
      M.index = planeIndex (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := maximal_parabolics (K := K) (n := 4) 2 (by norm_num)
  constructor
  · rintro ⟨W, hW, rfl⟩
    refine ⟨(map_mem_maximalParabolics_equiv_iff slEquivProj _).1 ?_, index_stabilizer_plane hW⟩
    rw [map_slEquivProj_stabilizer, hmax.1]
    exact ⟨W, finrank_pos_lt_of_two hW, rfl⟩
  · rintro ⟨hM, hidx⟩
    have hM' := (map_mem_maximalParabolics_equiv_iff slEquivProj M).2 hM
    rw [hmax.1] at hM'
    obtain ⟨W, ⟨h0, htop⟩, hWM⟩ := hM'
    obtain ⟨hk1, hk4⟩ := one_le_finrank_and_lt h0 htop
    have hidxW : ((projStabilizer W).index : ℚ) = gaussianCoeff 4 (finrank K W) (Nat.card K) :=
      (subspace_index (K := K) (n := 4) (k := finrank K W) hk4.le).2 W rfl
    have hpidx : (projStabilizer W).index = M.index := by
      rw [hWM, index_map_toMonoidHom]
    have hq2 := two_le_card (K := K)
    have hk : finrank K W = 2 := by
      by_contra hne
      have hg : gaussianCoeff 4 (finrank K W) (Nat.card K) = gaussianCoeff 4 2 (Nat.card K) := by
        rw [← hidxW, hpidx, hidx, gaussianCoeff_four_two hq2]
      have hmin := gaussian_minimum hq2 (n := 4) (by norm_num) hk1 hk4
      have hmin2 := gaussian_minimum hq2 (n := 4) (by norm_num) (k := 2) (by norm_num) (by norm_num)
      have h1 : gaussianCoeff 4 (finrank K W) (Nat.card K) = gaussianCoeff 4 1 (Nat.card K) :=
        hmin.2.2.mpr (by omega)
      have h2 : gaussianCoeff 4 2 (Nat.card K) = gaussianCoeff 4 1 (Nat.card K) := hg ▸ h1
      have := hmin2.2.2.mp h2
      omega
    refine ⟨W, hk, ?_⟩
    apply Subgroup.map_injective slEquivProj.injective
    exact hWM.symm

theorem map_mem_planeStabilizers (α : MulAut (SpecialLinearGroup (Fin 4) K))
    {M : Subgroup (SpecialLinearGroup (Fin 4) K)} (hM : M ∈ planeStabilizers K) :
    M.map α.toMonoidHom ∈ planeStabilizers K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := mem_planeStabilizers_iff.1 hM
  refine mem_planeStabilizers_iff.2 ⟨map_mem_maximalParabolics α h1, ?_⟩
  rw [index_map_toMonoidHom]
  exact h2

theorem card_planeStabilizers :
    Nat.card ↥(planeStabilizers K) = planeIndex (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := maximal_parabolics (K := K) (n := 4) 2 (by norm_num)
  have hinj : Set.InjOn (fun W : Submodule K (Fin 4 → K) => stabilizer W)
      {W | finrank K W = 2} := by
    intro W hW W' hW' h
    have h1 : projStabilizer W = projStabilizer W' := by
      rw [← map_slEquivProj_stabilizer, ← map_slEquivProj_stabilizer]
      exact congrArg (fun N => N.map slEquivProj.toMonoidHom) h
    exact hmax.2.1 (finrank_pos_lt_of_two hW) (finrank_pos_lt_of_two hW') h1
  have himg : planeStabilizers K = (fun W : Submodule K (Fin 4 → K) => stabilizer W) ''
      {W | finrank K W = 2} := by
    ext M
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact ⟨W, hW, rfl⟩
    · rintro ⟨W, hW, rfl⟩
      exact ⟨W, hW, rfl⟩
  rw [himg, Nat.card_image_of_injOn hinj]
  have h1 := card_finrank_eq (K := K) (n := 4) (k := 2) (by norm_num)
  rw [gaussianCoeff_four_two two_le_card] at h1
  have h2 : Nat.card ↥{W : Submodule K (Fin 4 → K) | finrank K W = 2} =
      Nat.card {W : Submodule K (Fin 4 → K) // finrank K W = 2} := rfl
  rw [h2]
  exact_mod_cast h1

end Planes

section Arith

theorem not_dvd_planeIndex {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) :
    ¬ p ∣ planeIndex q := by
  intro h
  have h1 : ((q : ℕ) : ZMod p) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 := (ZMod.natCast_eq_zero_iff _ p).2 h
  unfold planeIndex at h2
  push_cast at h2
  rw [h1] at h2
  norm_num at h2
  have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
  have h4 := (ZMod.natCast_eq_zero_iff 2 p).1 h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)

variable {K : Type} [Field K] [Finite K]

theorem dvd_card_specialLinear_four {p : ℕ} (hpq : p ∣ Nat.card K + 1) :
    p ∣ Nat.card (SpecialLinearGroup (Fin 4) K) := by
  rw [card_SL_eq (by norm_num : 1 ≤ 4)]
  refine Dvd.dvd.mul_left ?_ _
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _
    (Finset.mem_Icc.2 ⟨le_rfl, by norm_num⟩ : (2 : ℕ) ∈ Finset.Icc 2 4))
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h1 : Nat.card K + 1 ∣ Nat.card K ^ 2 - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [ha]
    simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  exact hpq.trans h1

end Arith

section Radical

variable {K : Type} [Field K] {n : ℕ}

theorem mulVec_inv_mulVec_sl (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec_sl (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def radical (W : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W) ∧
    ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w}
  one_mem' := by
    refine ⟨fun v => ?_, fun w _ => ?_⟩
    · simp
    · simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h1 := hg1 ((h : Matrix (Fin n) (Fin n) K) *ᵥ v)
      have h2 := hh1 v
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have := W.add_mem h1 h2
      simpa using this
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh2 w hw, hg2 w hw]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h1 := hg1 (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      rw [mulVec_inv_mulVec_sl] at h1
      have := W.neg_mem h1
      simpa using this
    · have h1 := hg2 w hw
      calc ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w =
          ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) := by rw [h1]
        _ = w := inv_mulVec_mulVec_sl g w

theorem radical_le_stabilizer (W : Submodule K (Fin n → K)) : radical W ≤ stabilizer W := by
  intro g hg
  rw [mem_stabilizer]
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, hg.2 w hw]
    exact hw
  · intro hx
    exact ⟨x, hx, by rw [mulVecLin_apply, hg.2 x hx]⟩

omit [Field K] in
theorem vec_add_self_eq_zero {K : Type} [Field K] [CharP K 2] (y : Fin n → K) : y + y = 0 := by
  rw [← two_smul K y, CharTwo.two_eq_zero, zero_smul]

theorem radical_mul_self [CharP K 2] {W : Submodule K (Fin n → K)}
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ radical W) : g * g = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have h1 := hg.1 v
  have h2 := hg.2 _ h1
  rw [Matrix.mulVec_sub] at h2
  have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v + (g : Matrix (Fin n) (Fin n) K) *ᵥ v) - v := by
    rw [sub_eq_iff_eq_add.1 h2]
    abel
  rw [h3, vec_add_self_eq_zero, zero_sub]
  exact neg_eq_of_add_eq_zero_right (vec_add_self_eq_zero v)

theorem isPGroup_radical [CharP K 2] (W : Submodule K (Fin n → K)) : IsPGroup 2 ↥(radical W) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, pow_two]
  exact radical_mul_self g.2

theorem radical_conj_mem {W : Submodule K (Fin n → K)} {y : SpecialLinearGroup (Fin n) K}
    (hy : y ∈ stabilizer W) {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ radical W) :
    y * u * y⁻¹ ∈ radical W := by
  have hyW : ∀ w ∈ W, (y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro w hw
    have : (y : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W.map (mulVecLin (y : Matrix (Fin n) (Fin n) K)) :=
      ⟨w, hw, rfl⟩
    rwa [mem_stabilizer.1 hy] at this
  have hy' : y⁻¹ ∈ stabilizer W := inv_mem hy
  have hyW' : ∀ w ∈ W, ((y⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro w hw
    have : ((y⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
        W.map (mulVecLin ((y⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      ⟨w, hw, rfl⟩
    rwa [mem_stabilizer.1 hy'] at this
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    set z : Fin n → K := ((y⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
      with hz
    have hyz : (y : Matrix (Fin n) (Fin n) K) *ᵥ z = v := mulVec_inv_mulVec_sl y v
    have h1 := hyW _ (hu.1 z)
    rw [Matrix.mulVec_sub, hyz] at h1
    exact h1
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hu.2 _ (hyW' w hw)]
    exact mulVec_inv_mulVec_sl y w

theorem radical_le_pCoreOf [CharP K 2] (W : Submodule K (Fin n → K)) :
    radical W ≤ pCoreOf 2 (stabilizer W) := by
  refine le_pCoreOf_of_le_normalizer 2 (radical_le_stabilizer W) (fun y hy => ?_)
    (isPGroup_radical W)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => radical_conj_mem hy hh, fun hh => ?_⟩
  have := radical_conj_mem (inv_mem hy) hh
  simpa [mul_assoc] using this

theorem transvSL_mem_radical_flag {i j : Fin 4} (hi : (i : ℕ) < 2) (hj : 2 ≤ (j : ℕ)) (hij : i < j)
    (c : K) : transvSL hij c ∈ radical (flagSpace 4 K 2) := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [transvSL_coe, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      add_sub_cancel_left, Matrix.single_mulVec_eq, mem_flagSpace]
    intro k hk
    have hki : k ≠ i := fun h => by
      subst h
      omega
    simp [hki]
  · rw [transvSL_coe, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq]
    have h0 : w j = 0 := mem_flagSpace.1 hw j hj
    simp [h0]

end Radical

section Centralizer

variable {K : Type} [Field K]

@[expose] def mkSL {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.det = 1) :
    SpecialLinearGroup (Fin n) K := ⟨M, h⟩

theorem mkSL_coe {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.det = 1) :
    ((mkSL M h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := rfl

theorem eq_smul_unitriangular_of_commute_radical (x : SpecialLinearGroup (Fin 4) K)
    (hcomm : ∀ t ∈ radical (flagSpace 4 K 2), x * t = t * x) :
    ∃ (lam : K) (u : SpecialLinearGroup (Fin 4) K), u ∈ unitriangular 4 K ∧
      (x : Matrix (Fin 4) (Fin 4) K) = lam • (u : Matrix (Fin 4) (Fin 4) K) := by
  classical
  set X : Matrix (Fin 4) (Fin 4) K := (x : Matrix (Fin 4) (Fin 4) K) with hXdef
  have hE : ∀ i j : Fin 4, (i : ℕ) < 2 → 2 ≤ (j : ℕ) →
      X * Matrix.single i j (1 : K) = Matrix.single i j (1 : K) * X := by
    intro i j hi hj
    have hij : i < j := by
      rw [Fin.lt_def]
      omega
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
      (hcomm _ (transvSL_mem_radical_flag hi hj hij 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul, transvSL_coe] at h1
    simp only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul] at h1
    exact add_left_cancel h1
  have hcol : ∀ i j : Fin 4, (i : ℕ) < 2 → 2 ≤ (j : ℕ) → ∀ k, k ≠ i → X k i = 0 := by
    intro i j hi hj k hki
    have h := congrFun (congrFun (hE i j hi hj) k) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hki] at h
    simpa using h
  have hrow : ∀ i j : Fin 4, (i : ℕ) < 2 → 2 ≤ (j : ℕ) → ∀ l, l ≠ j → X j l = 0 := by
    intro i j hi hj l hlj
    have h := congrFun (congrFun (hE i j hi hj) i) l
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hlj, Matrix.single_mul_apply_same] at h
    simpa using h.symm
  have hdiag : ∀ i j : Fin 4, (i : ℕ) < 2 → 2 ≤ (j : ℕ) → X i i = X j j := by
    intro i j hi hj
    have h := congrFun (congrFun (hE i j hi hj) i) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at h
    simpa using h
  have hshape : ∀ k l : Fin 4, k ≠ l → ¬ ((k : ℕ) < 2 ∧ 2 ≤ (l : ℕ)) → X k l = 0 := by
    intro k l hkl hno
    by_cases hl : (l : ℕ) < 2
    · exact hcol l 2 hl (by decide) k hkl
    · have hk2 : 2 ≤ (k : ℕ) := by
        by_contra hk
        exact hno ⟨by omega, by omega⟩
      exact hrow 0 k (by decide) hk2 l (fun h => hkl h.symm)
  have hlam : ∀ i : Fin 4, X i i = X 0 0 := by
    intro i
    fin_cases i
    · rfl
    · exact (hdiag 1 2 (by decide) (by decide)).trans (hdiag 0 2 (by decide) (by decide)).symm
    · exact (hdiag 0 2 (by decide) (by decide)).symm
    · exact (hdiag 0 3 (by decide) (by decide)).symm
  set lam : K := X 0 0 with hlamdef
  have hup : X.IsUpperTriangular := fun i j (hji : j < i) => by
    refine hshape i j hji.ne' ?_
    rintro ⟨h1, h2⟩
    have := Fin.lt_def.1 hji
    omega
  have hdet : lam ^ 4 = 1 := by
    have h1 : X.det = 1 := x.2
    rw [Matrix.det_of_isUpperTriangular hup] at h1
    simpa [hlam, Finset.prod_const, Finset.card_univ] using h1
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hdetu : (lam⁻¹ • X).det = 1 := by
    rw [Matrix.det_smul, x.2, Fintype.card_fin, mul_one, inv_pow, hdet, inv_one]
  refine ⟨lam, mkSL (lam⁻¹ • X) hdetu, ?_, ?_⟩
  · rw [mem_unitriangular]
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [mkSL_coe, Matrix.smul_apply, smul_eq_mul, hshape a b hab.ne' (fun h => by
        have := Fin.lt_def.1 hab
        omega), mul_zero]
    · rw [mkSL_coe, Matrix.smul_apply, smul_eq_mul, hlam a, inv_mul_cancel₀ hlam0]
  · rw [mkSL_coe, smul_smul, mul_inv_cancel₀ hlam0, one_smul]

theorem eq_one_of_eq_smul_unitriangular {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hmp : Nat.gcd m p = 1) (hT2 : IsPGroup 2 ↥(unitriangular m K))
    (x : SpecialLinearGroup (Fin m) K) (hxp : x ^ p = 1) (lam : K)
    (u : SpecialLinearGroup (Fin m) K) (huT : u ∈ unitriangular m K)
    (hXu : (x : Matrix (Fin m) (Fin m) K) = lam • (u : Matrix (Fin m) (Fin m) K)) : x = 1 := by
  classical
  set X : Matrix (Fin m) (Fin m) K := (x : Matrix (Fin m) (Fin m) K) with hXdef
  let first : Fin m := ⟨0, hm⟩
  have hXp : X ^ p = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hxp
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  rw [hXu, smul_pow] at hXp
  have hUp : ((u ^ p : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (u : Matrix (Fin m) (Fin m) K) ^ p := Matrix.SpecialLinearGroup.coe_pow u p
  have hdiag1 : ((u ^ p : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) first first =
      1 := (mem_unitriangular.1 (pow_mem huT p)).2 first
  have hlamp : lam ^ p = 1 := by
    have := congrFun (congrFun hXp first) first
    rw [Matrix.smul_apply, ← hUp, hdiag1, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this
  have hUp1 : u ^ p = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hUp]
    rw [hlamp, one_smul] at hXp
    rw [hXp, Matrix.SpecialLinearGroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨u, huT⟩
  have hord : orderOf (⟨u, huT⟩ : ↥(unitriangular m K)) ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext hUp1)
  rw [hk] at hord
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ p := (dvd_pow_self 2 hk0).trans hord
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hu1 : u = 1 := by
    have h1 : orderOf (⟨u, huT⟩ : ↥(unitriangular m K)) = 1 := by rw [hk, hk0, pow_zero]
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  have hX1 : X = lam • (1 : Matrix (Fin m) (Fin m) K) := by
    rw [hXu, hu1, Matrix.SpecialLinearGroup.coe_one]
  have hlam1 : lam = 1 := by
    have hdet : lam ^ m = 1 := by
      have h1 : X.det = 1 := x.2
      rw [hX1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have h1 : lam ^ Nat.gcd m p = 1 := pow_gcd_eq_one.2 ⟨hdet, hlamp⟩
    rwa [hmp, pow_one] at h1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  show X i j = (1 : Matrix (Fin m) (Fin m) K) i j
  rw [hX1, hlam1, one_smul]

variable [Finite K] [CharP K 2]

theorem exists_noncomm_radical_flag {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : SpecialLinearGroup (Fin 4) K) (hx : orderOf x = p) :
    ∃ t ∈ radical (flagSpace 4 K 2), x * t ≠ t * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT⟩ := exists_sylow_unitriangular (K := K) 2 (by norm_num : 1 ≤ 4)
  have hT2 : IsPGroup 2 ↥(unitriangular 4 K) := by
    rw [← hT]
    exact T.isPGroup'
  obtain ⟨lam, u, huT, hXu⟩ := eq_smul_unitriangular_of_commute_radical x hcon
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hgcd : Nat.gcd 4 p = 1 := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
    have h4 : p ∣ 2 ^ 2 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hx1 := eq_one_of_eq_smul_unitriangular hp hp2 (by norm_num) hgcd hT2 x hxp lam u huT hXu
  rw [hx1, orderOf_one] at hx
  exact hp.ne_one hx.symm

theorem exists_noncomm_pCoreOf_stabilizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {W : Submodule K (Fin 4 → K)} (hW : finrank K W = 2) (x : SpecialLinearGroup (Fin 4) K)
    (hxW : x ∈ stabilizer W) (hx : orderOf x = p) :
    ∃ t ∈ pCoreOf 2 (stabilizer W), x * t ≠ t * x := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  rw [hW] at hg
  have hconj := stabilizer_map_conj g (flagSpace 4 K 2)
  rw [hg] at hconj
  rw [← hconj] at hxW
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxW
  have hyo : orderOf y = p := by
    rw [← hx, ← hyx]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).symm
  obtain ⟨t₀, ht₀, hne⟩ := exists_noncomm_radical_flag hp hp2 y hyo
  have ht₀' : t₀ ∈ pCoreOf 2 (stabilizer (flagSpace 4 K 2)) := radical_le_pCoreOf _ ht₀
  have hcore : pCoreOf 2 (stabilizer W) =
      Subgroup.map (MulAut.conj g).toMonoidHom (pCoreOf 2 (stabilizer (flagSpace 4 K 2))) := by
    rw [← hconj]
    exact pCoreOf_map_mulEquiv 2 (MulAut.conj g) (stabilizer (flagSpace 4 K 2))
  have hyx' : (MulAut.conj g) y = x := hyx
  refine ⟨MulAut.conj g t₀, ?_, fun hc => hne ?_⟩
  · rw [hcore]
    exact Subgroup.mem_map_of_mem _ ht₀'
  · apply (MulAut.conj g).injective
    rw [map_mul, map_mul, hyx']
    exact hc

end Centralizer

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem familyFactsGrp_specialLinear_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : FamilyFactsGrp p (SpecialLinearGroup (Fin 4) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨planeStabilizers K, ?_, fun α M hM => map_mem_planeStabilizers α hM, ?_⟩
  · rw [card_planeStabilizers]
    exact not_dvd_planeIndex hp hp2 hpq
  · rintro M ⟨W, hW, rfl⟩
    refine ⟨?_, pCoreOf 2 (stabilizer W), pCoreOf_le 2 _, pCoreOf_isPGroup 2 _, ?_, ?_⟩
    · have h1 := Subgroup.card_mul_index (stabilizer W)
      rw [index_stabilizer_plane hW] at h1
      have hpS := dvd_card_specialLinear_four hpq
      rw [← h1] at hpS
      exact (hp.dvd_mul.1 hpS).resolve_right (not_dvd_planeIndex hp hp2 hpq)
    · intro α hα
      have := pCoreOf_map_mulEquiv 2 α (stabilizer W)
      rw [hα] at this
      exact this.symm
    · intro x hx hxo
      exact exists_noncomm_pCoreOf_stabilizer hp hp2 hW x hx hxo

end Main

end CFSG.RankThree.PartOne.K159
