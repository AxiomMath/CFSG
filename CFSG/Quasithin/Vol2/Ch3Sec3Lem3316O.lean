module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316N

public section

namespace CFSG.Quasithin.H13.L3316.Sp4Aut

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {F : Type} [Field F]

@[expose] def torVec (j : Fin 2) : Fˣ →* (Fin 2 → Fˣ) where
  toFun l i := if j = 0 ∧ i = 1 then 1 else l
  map_one' := by
    funext i
    simp
  map_mul' a b := by
    funext i
    simp only [Pi.mul_apply]
    split_ifs <;> simp

@[expose] noncomputable def torSp (j : Fin 2) : Fˣ →* StatedSp 2 F :=
  SymplecticTorusWeyl.torusHom.comp (torVec j)

theorem spMat_torSp (j : Fin 2) (l : Fˣ) :
    spMat (torSp j l) = diagonal (Sum.elim (fun i => ((torVec j l i : Fˣ) : F))
      fun i => (((torVec j l i)⁻¹ : Fˣ) : F)) :=
  SymplecticTorusWeyl.coe_torusHom _

theorem torSp_mem_borel (j : Fin 2) (l : Fˣ) : torSp j l ∈ borelSubgroup 2 F :=
  torus_le_borelSubgroup ⟨_, rfl⟩

theorem torSp_mem_normalizer (j : Fin 2) (l : Fˣ) :
    torSp j l ∈ Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
  rw [normalizer_unipotent]
  exact torSp_mem_borel j l

theorem torSp_mem_Q2 (j : Fin 2) (l : Fˣ) : torSp j l ∈ Q2 F j :=
  borelSubgroup_le_Q2 j (torSp_mem_borel j l)

theorem unipotent_le_Q2 (j : Fin 2) : unipotent 2 F ≤ Q2 F j := by
  intro u hu
  refine borelSubgroup_le_Q2 j ?_
  rw [← normalizer_unipotent]
  exact Subgroup.le_normalizer hu

theorem blkQ_torSp (j : Fin 2) (l : Fˣ) :
    ∃ s : F, blkQ j ⟨torSp j l, torSp_mem_Q2 j l⟩ = scalar (Fin 2) s := by
  rw [blkQ_apply, spMat_torSp]
  rcases fin_two_cases j with rfl | rfl
  · refine ⟨1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [blkIdx, sigma2_zero, torVec, diagonal]
  · refine ⟨l, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [blkIdx, sigma2_one, torVec, diagonal]

theorem blkQ_commutator {j : Fin 2} {a b : ↥(Q2 F j)}
    (h : (∃ s : F, blkQ j a = scalar (Fin 2) s) ∨ ∃ s : F, blkQ j b = scalar (Fin 2) s) :
    blkQ j (a * b * a⁻¹ * b⁻¹) = 1 := by
  have hi : ∀ c : ↥(Q2 F j), blkQ j c * blkQ j c⁻¹ = 1 := fun c => by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, map_mul]
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hc : blkQ j a * blkQ j b = blkQ j b * blkQ j a := by
      rw [hs]
      exact (scalar_commute s (fun r => Commute.all s r) (blkQ j b)).eq
    rw [hc, Matrix.mul_assoc (blkQ j b), hi, Matrix.mul_one, hi]
  · have hc : blkQ j b * blkQ j a⁻¹ = blkQ j a⁻¹ * blkQ j b := by
      rw [hs]
      exact (scalar_commute s (fun r => Commute.all s r) (blkQ j a⁻¹)).eq
    rw [Matrix.mul_assoc (blkQ j a) (blkQ j b), hc, ← Matrix.mul_assoc, hi, Matrix.one_mul, hi]

variable (F) in
@[expose] noncomputable def radSp (j : Fin 2) : Subgroup (StatedSp 2 F) :=
  unipotent 2 F ⊓ ((blkQ (K := F) j).toHomUnits.ker.map (Q2 F j).subtype)

theorem mem_radSp {j : Fin 2} {g : StatedSp 2 F} :
    g ∈ radSp F j ↔ g ∈ unipotent 2 F ∧ ∃ h : g ∈ Q2 F j, blkQ j ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨hU, ⟨q, hq, rfl⟩⟩
    exact ⟨hU, q.2, congrArg Units.val hq⟩
  · rintro ⟨hU, h, h1⟩
    exact ⟨hU, ⟨⟨g, h⟩, Units.ext h1, rfl⟩⟩

theorem radSp_le (j : Fin 2) : radSp F j ≤ unipotent 2 F := inf_le_left

theorem commutator_mem_radSp {j : Fin 2} {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (l : Fˣ) :
    u * torSp j l * u⁻¹ * (torSp j l)⁻¹ ∈ radSp F j := by
  have hN := torSp_mem_normalizer (F := F) j l
  have hU : u * torSp j l * u⁻¹ * (torSp j l)⁻¹ ∈ unipotent 2 F := by
    have h1 : torSp j l * u⁻¹ * (torSp j l)⁻¹ ∈ unipotent 2 F :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu)
    have h2 := mul_mem hu h1
    simpa only [mul_assoc] using h2
  refine mem_radSp.mpr ⟨hU, unipotent_le_Q2 j hU, ?_⟩
  have h := blkQ_commutator (j := j) (a := ⟨u, unipotent_le_Q2 j hu⟩)
    (b := ⟨torSp j l, torSp_mem_Q2 j l⟩) (Or.inr (blkQ_torSp j l))
  exact h

theorem card_unipotent_four [Finite F] (hF : Nat.card F = 4) :
    Nat.card ↥(unipotent 2 F) = 2 ^ 8 := by
  rw [card_unipotent, hF]
  norm_num

theorem exists_mem_unipotent_not_mem_radSp [Finite F] (j : Fin 2) :
    ∃ u ∈ unipotent 2 F, u ∉ radSp F j := by
  classical
  rcases fin_two_cases j with rfl | rfl
  ·
    have hC : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 0; 0, 1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    refine ⟨upperUnipotentSp 2 F hC, ⟨1, _, isUnitriangular_one, hC, ?_⟩, fun hR => ?_⟩
    · rw [coe_upperUnipotentSp]
      simp [blockMat]
    · obtain ⟨-, h, h1⟩ := mem_radSp.mp hR
      have := congrFun₂ h1 0 1
      rw [blkQ_apply, sigma2_zero] at this
      simp [blkIdx, coe_upperUnipotentSp] at this
  ·
    let A : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    refine ⟨spLevi 1 A, ⟨!![1, 1; 0, 1], 0, ⟨?_, ?_⟩, by simp, ?_⟩, fun hR => ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro a
      fin_cases a <;> rfl
    · change spMat (spLevi 1 A) = _
      rw [spMat_leviSp_one, blockMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def]
      simp [A, Matrix.det_fin_two]
    · obtain ⟨-, h, h1⟩ := mem_radSp.mp hR
      have := congrFun₂ h1 0 1
      rw [blkQ_apply, sigma2_one, spMat_leviSp_one] at this
      simp [blkIdx, A] at this

theorem card_radSp_le [Finite F] (hF : Nat.card F = 4) (j : Fin 2) :
    Nat.card ↥(radSp F j) ≤ 2 ^ 7 := by
  have hdvd : Nat.card ↥(radSp F j) ∣ 2 ^ 8 := by
    rw [← card_unipotent_four hF]
    exact Subgroup.card_dvd_of_le (radSp_le j)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hne : Nat.card ↥(radSp F j) ≠ 2 ^ 8 := by
    intro heq
    obtain ⟨u, hu, hu'⟩ := exists_mem_unipotent_not_mem_radSp (F := F) j
    have : radSp F j = unipotent 2 F :=
      Subgroup.eq_of_le_of_card_ge (radSp_le j) (by rw [heq, card_unipotent_four hF])
    exact hu' (this ▸ hu)
  rw [hk'] at hne ⊢
  have hk8 : k ≠ 8 := fun h => hne (by rw [h])
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Field F] in
theorem sq_ne_one_of_ne_one {F : Type} [Field F] [CharP F 2] {l : F} (hl : l ≠ 1) :
    l ^ 2 ≠ 1 := by
  intro h
  apply hl
  have h1 : (l + 1) ^ 2 = 0 := by
    linear_combination h + (l + 1) * (two_eq_zero' : (2 : F) = 0)
  have h2 : l + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  linear_combination h2 - (two_eq_zero' : (2 : F) = 0)

theorem spMat_upperUnipotentSp {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    spMat (upperUnipotentSp 2 F hC) = fromBlocks 1 C 0 1 :=
  coe_upperUnipotentSp hC

theorem torSp_eq (j : Fin 2) (l : Fˣ) :
    torSp j l = SymplecticTorusWeyl.leviSp (TauCeti.diagGL (torVec j l)) := rfl

theorem spLevi_one_eq (A : SpecialLinearGroup (Fin 2) F) :
    spLevi 1 A = SymplecticTorusWeyl.leviSp (Matrix.SpecialLinearGroup.toGL A) := by
  simp [spLevi]

theorem spMat_torSp_one (l : Fˣ) :
    spMat (torSp 1 l) = fromBlocks !![(l : F), 0; 0, (l : F)] 0 0
      !![((l⁻¹ : Fˣ) : F), 0; 0, ((l⁻¹ : Fˣ) : F)] := by
  rw [spMat_torSp, ← fromBlocks_diagonal, diagonal_fin_two, diagonal_fin_two]
  simp [torVec]

theorem exists_noncomm [CharP F 2] (j : Fin 2) {l : Fˣ} (hl : l ≠ 1) :
    ∃ u ∈ unipotent 2 F, ∃ B : SpecialLinearGroup (Fin 2) F,
      spLevi j B * (u * torSp j l * u⁻¹ * (torSp j l)⁻¹) ≠
        u * torSp j l * u⁻¹ * (torSp j l)⁻¹ * spLevi j B := by
  classical
  have hl' : (l : F) ≠ 1 := fun h => hl (Units.ext h)
  have hli : (l : F) * ((l⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ∀ u W y x : StatedSp 2 F, W * x * u = u * x → y * W ≠ W * y →
      y * (u * x * u⁻¹ * x⁻¹) ≠ u * x * u⁻¹ * x⁻¹ * y := by
    intro u W y x hW hy
    have : u * x * u⁻¹ * x⁻¹ = W := by
      rw [← hW]
      group
    rw [this]
    exact hy
  rcases fin_two_cases j with rfl | rfl
  ·
    let A : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let Aν : SpecialLinearGroup (Fin 2) F :=
      ⟨!![1, 1 - (l : F); 0, 1], by simp [Matrix.det_fin_two]⟩
    let B : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
    refine ⟨spLevi 1 A, ⟨!![1, 1; 0, 1], 0, ⟨?_, ?_⟩, by simp, ?_⟩, B,
      key _ (spLevi 1 Aν) _ _ ?_ ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro a
      fin_cases a <;> rfl
    · change spMat (spLevi 1 A) = _
      rw [spMat_leviSp_one, blockMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def]
      simp [A, Matrix.det_fin_two]
    · rw [spLevi_one_eq, spLevi_one_eq, torSp_eq, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, TauCeti.diagGL_coe, diagonal_fin_two]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Aν, A, torVec, Matrix.mul_apply, Fin.sum_univ_two]
    · intro h
      have := congrFun₂ (congrArg spMat h) (Sum.inl 0) (Sum.inl 1)
      rw [spMat_mul, spMat_mul, spMat_lam, spMat_leviSp_one] at this
      simp [Aν, B, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        SymplecticTorusWeyl.pairMat] at this
      exact hl' (by linear_combination -this)
  ·
    have hC : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![1, 0; 0, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hC' : (!![1 - (l : F) ^ 2, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ =
        !![1 - (l : F) ^ 2, 0; 0, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    let B : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    refine ⟨upperUnipotentSp 2 F hC, ⟨1, _, isUnitriangular_one, hC, ?_⟩, B,
      key _ (upperUnipotentSp 2 F hC') _ _ ?_ ?_⟩
    · rw [coe_upperUnipotentSp]
      simp [blockMat]
    · apply SymplecticTorusWeyl.statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      change spMat (upperUnipotentSp 2 F hC') * spMat (torSp 1 l) *
        spMat (upperUnipotentSp 2 F hC) = spMat (upperUnipotentSp 2 F hC) * spMat (torSp 1 l)
      rw [spMat_upperUnipotentSp, spMat_upperUnipotentSp, spMat_torSp_one, fromBlocks_multiply,
        fromBlocks_multiply, fromBlocks_multiply]
      simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
        zero_add]
      refine fromBlocks_inj.mpr ⟨rfl, ?_, rfl, rfl⟩
      ext a b
      have hli' : (l : F) * (l : F)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero l)
      fin_cases a <;> fin_cases b
      · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
        linear_combination (-(l : F)) * hli'
      all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    · intro h
      have := congrFun₂ (congrArg spMat h) (Sum.inl 0) (Sum.inr 1)
      rw [spMat_mul, spMat_mul, spMat_leviSp_one, spMat_upperUnipotentSp,
        Matrix.SpecialLinearGroup.coe_inv, fromBlocks_multiply, fromBlocks_multiply] at this
      simp [B, Matrix.adjugate_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this
      exact sq_ne_one_of_ne_one hl' (by linear_combination -this)

end CFSG.Quasithin.H13.L3316.Sp4Aut
