module

public import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
public import CFSG.Quasithin.Vol2.KGNatSL3Line

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin Ch11.SecA KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] def LineTorusFacts {W : Type*} [Group W] (H S : Subgroup (MulAut W)) (Z U₂ : Subgroup W)
    (q : ℕ) : Prop :=
  (∀ w : W, (∀ s ∈ S, s w * w⁻¹ ∈ Z) → w ∈ U₂) ∧
  (∀ X : Subgroup W, Z ≤ X → X ≤ U₂ → (∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ x ∈ X, s x ∈ X) →
    X = Z ∨ X = U₂) ∧
  ∃ t ∈ H ⊓ stabW U₂, t ^ (q - 1) = 1 ∧
    (∀ s ∈ perfectCore (H ⊓ stabW U₂),
      t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ stabW U₂))) ∧
    ∃ u ∈ U₂, t u ≠ u

section Matrices

variable {K : Type} [Field K]

theorem eq_uSL_of_lev2 {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabRow2 K)
    (hl : lev2 (B : Matrix (Fin 3) (Fin 3) K) = 1) :
    B = uSL 0 ((B : Matrix (Fin 3) (Fin 3) K) 0 2) ((B : Matrix (Fin 3) (Fin 3) K) 1 2) := by
  obtain ⟨h20, h21, h22⟩ := mem_stabRow2.mp hB
  have h00 := congrFun (congrFun hl 0) 0
  have h01 := congrFun (congrFun hl 0) 1
  have h10 := congrFun (congrFun hl 1) 0
  have h11 := congrFun (congrFun hl 1) 1
  simp only [lev2_apply, Fin.castSucc_zero, Fin.castSucc_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat, h00, h01, h10, h11, h20, h21, h22]

theorem isPGroup_ker_leviHom2 [CharP K 2] : IsPGroup 2 (leviHom2 K).ker := by
  intro B
  refine ⟨1, ?_⟩
  have hl : lev2 (((B : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← leviHom2_coe, MonoidHom.mem_ker.mp B.2, Matrix.SpecialLinearGroup.coe_one]
  have hB := eq_uSL_of_lev2 (B : ↥(stabRow2 K)).2 hl
  apply Subtype.ext
  apply Subtype.ext
  rw [pow_one, sq]
  show ((B : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K) *
    ((B : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K) = 1
  rw [hB, uSL_mul]
  simp only [zero_mul, CharTwo.add_self_eq_zero, uSL_zero]

theorem uSL_mem_stabRow2 (b c : K) : uSL 0 b c ∈ stabRow2 K :=
  mem_stabRow2.mpr ⟨by simp [coe_uSL, uMat], by simp [coe_uSL, uMat], by simp [coe_uSL, uMat]⟩

theorem lev2_uSL (b c : K) : lev2 ((uSL 0 b c : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lev2, coe_uSL, uMat]

@[expose] noncomputable def dLine (c : Kˣ) : SpecialLinearGroup (Fin 3) K := tSL (c, c)

theorem dLine_inv (c : Kˣ) : (dLine c)⁻¹ = dLine (K := K) c⁻¹ := by
  rw [dLine, dLine, ← map_inv, Prod.inv_mk]

theorem dLine_conj_apply (c : Kˣ) (B : SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    ((dLine c * B * (dLine c)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      ![(c : K), (c : K), (((c * c)⁻¹ : Kˣ) : K)] i * (B : Matrix (Fin 3) (Fin 3) K) i j *
        ![((c⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K), (((c⁻¹ * c⁻¹)⁻¹ : Kˣ) : K)] j := by
  have e : ((dLine c * B * (dLine c)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![(c : K), (c : K), (((c * c)⁻¹ : Kˣ) : K)] *
        (B : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![((c⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K), (((c⁻¹ * c⁻¹)⁻¹ : Kˣ) : K)] := by
    rw [dLine_inv]
    rfl
  rw [e, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dLine_conj_mem (c : Kˣ) {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabRow2 K) :
    dLine c * B * (dLine c)⁻¹ ∈ stabRow2 K := by
  obtain ⟨h20, h21, h22⟩ := mem_stabRow2.mp hB
  refine mem_stabRow2.mpr ⟨?_, ?_, ?_⟩ <;> rw [dLine_conj_apply]
  · simp [h20]
  · simp [h21]
  · have e : ((c * c)⁻¹ * (c⁻¹ * c⁻¹)⁻¹ : Kˣ) = 1 := by group
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, h22, mul_one]
    rw [← Units.val_mul, e, Units.val_one]

theorem lev2_dLine_conj (c : Kˣ) (B : SpecialLinearGroup (Fin 3) K) :
    lev2 ((dLine c * B * (dLine c)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = lev2 (B : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : ∀ i : Fin 2,
      (![(c : K), (c : K), (((c * c)⁻¹ : Kˣ) : K)] : Fin 3 → K) i.castSucc = c := by
    intro i
    fin_cases i <;> rfl
  have h2 : ∀ i : Fin 2, (![((c⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K),
      (((c⁻¹ * c⁻¹)⁻¹ : Kˣ) : K)] : Fin 3 → K) i.castSucc = ((c⁻¹ : Kˣ) : K) := by
    intro i
    fin_cases i <;> rfl
  have hc : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  rw [lev2_apply, lev2_apply, dLine_conj_apply, h1, h2, mul_comm _ ((c⁻¹ : Kˣ) : K), ← mul_assoc,
    mul_comm _ (c : K), hc, one_mul]

theorem dLine_pow_card_sub_one [Finite K] (c : Kˣ) :
    dLine (K := K) c ^ (Nat.card K - 1) = 1 := by
  classical
  have := Fintype.ofFinite K
  have hc : c ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
    exact pow_card_eq_one
  rw [dLine, ← map_pow, Prod.pow_mk, hc, Prod.mk_one_one, map_one]

end Matrices

section Coord

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem exists_equiv_stabRow2 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (Assembly.LowTwoRank.StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) :
    ∃ e : ↥(stabRow2 K) ≃* ↥(perfectCore (H ⊓ stabW
        (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))),
      ∀ B : ↥(stabRow2 K), ((e B : MulAut W)) =
        ((rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) : ↥H) : MulAut W) := by
  set L := perfectCore (H ⊓ stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)) with hL
  let φ : ↥(stabRow2 K) →* ↥L := MonoidHom.codRestrict
    (H.subtype.comp ((rho3 π).comp ((MulAut.conj g).toMonoidHom.comp (stabRow2 K).subtype))) L
    (fun B => (mem_perfectCore_HU2_iff hSL hf g _).mpr
      ⟨(B : SpecialLinearGroup (Fin 3) K), B.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro B B' h
    have h1 : rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) =
        rho3 π (g * (B' : SpecialLinearGroup (Fin 3) K) * g⁻¹) :=
      Subtype.ext (congrArg (fun z : ↥L => (z : MulAut W)) h)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel ((rho3_bijective hf).1 h1)))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU2_iff hSL hf g y).mp hy
    exact ⟨⟨B, hB⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun B => rfl⟩

theorem mem_pCoreOf_of_lev2 [CharP K 2] (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (Assembly.LowTwoRank.StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K)
    {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabRow2 K)
    (hl : lev2 (B : Matrix (Fin 3) (Fin 3) K) = 1) :
    ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) ∈
      pCoreOf 2 (perfectCore (H ⊓ stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))) := by
  obtain ⟨e, he⟩ := exists_equiv_stabRow2 hSL hf g
  have hN : ((leviHom2 K).ker.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hle : (leviHom2 K).ker.map e.toMonoidHom ≤ CFSG.Open.pCore 2 ↥(perfectCore (H ⊓
      stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))) :=
    le_sSup ⟨hN, isPGroup_ker_leviHom2.map _⟩
  have hker : (⟨B, hB⟩ : ↥(stabRow2 K)) ∈ (leviHom2 K).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [leviHom2_coe, Matrix.SpecialLinearGroup.coe_one]
    exact hl
  exact ⟨e ⟨B, hB⟩, hle ⟨_, hker, rfl⟩, he _⟩

theorem eq_or_eq_of_stable_line (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (Assembly.LowTwoRank.StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K)
    {X : Subgroup W} (hZX : Z ≤ X) (hXU : X ≤ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)
    (hX : ∀ s ∈ perfectCore (H ⊓ stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)),
      ∀ x ∈ X, s x ∈ X) :
    X = Z ∨ X = hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
  by_cases h : X ≤ Z
  · exact Or.inl (le_antisymm h hZX)
  right
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp h
  refine le_antisymm hXU fun u hu => ?_
  have hfz : ∀ w : W, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w
      = 0 → w ∈ Z := fun w hw => by
    rw [← hf.ker, ← g_ginv_mulVec g (f w), hw, Matrix.mulVec_zero]
  have hy2 := (mem_pre_plane_iff hf g x).mp (hXU hxX)
  have hv2 := (mem_pre_plane_iff hf g u).mp hu
  obtain ⟨y, hy⟩ : ∃ y, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f x = y := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f u = v := ⟨_, rfl⟩
  rw [hy] at hy2
  rw [hv] at hv2
  by_cases hv0 : (![v 0, v 1] : Fin 2 → K) = 0
  · refine hZX (hfz u (hv.trans (vec3_eq ?_ ?_ ?_)))
    · simpa using congrFun hv0 0
    · simpa using congrFun hv0 1
    · simpa using hv2
  have hy0 : (![y 0, y 1] : Fin 2 → K) ≠ 0 := by
    intro h0
    refine hxZ (hfz x (hy.trans (vec3_eq ?_ ?_ ?_)))
    · simpa using congrFun h0 0
    · simpa using congrFun h0 1
    · simpa using hy2
  obtain ⟨A, hA⟩ := GroupTheory.SteinbergBK.exists_sl2_mulVec_eq _ _ hy0 hv0
  have hA0 := congrFun hA 0
  have hA1 := congrFun hA 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hA0 hA1
  set s := ((rho3 π (g * blockSL A * g⁻¹) : ↥H) : MulAut W) with hs
  have hsS : s ∈ perfectCore (H ⊓ stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)) :=
    (mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨blockSL A, blockSL_mem A, rfl⟩
  have hfe : f (s x) = f u := by
    rw [hs, hf.act3, gconj_mulVec, hy, blockSL_mulVec, ← g_ginv_mulVec g (f u), hv]
    congr 1
    refine vec3_eq ?_ ?_ ?_
    · simpa using hA0
    · simpa using hA1
    · simpa using hy2.trans hv2.symm
  have hz : u * (s x)⁻¹ ∈ Z := (hf.eq_iff _ _).mp hfe.symm
  have := X.mul_mem (hZX hz) (hX s hsS x hxX)
  rwa [inv_mul_cancel_right] at this

omit [Finite K] in
theorem dLine_mem_stabW (hf : IsCoord (linModelNat (Assembly.LowTwoRank.StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) (c : Kˣ) :
    ((rho3 π (g * dLine c * g⁻¹) : ↥H) : MulAut W) ∈
      stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) := by
  rw [hf.rho3_mem_stabW_iff (hf.le_pre _), hf.img_pre]
  intro y
  change y ∈ gmap g _ ↔ _ ∈ gmap g _
  rw [mem_gmap, mem_gmap, conj_mulVec, ← stdPlane_eq_flagSpace, mem_stdPlane, mem_stdPlane,
    dLine, tSL_mulVec]
  simp

end Coord

theorem lineTorusFacts_SL3 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)).RealizesVia H ⊤ Z π)
    {S : Subgroup (MulAut W)}
    (hS : QuasithinUnique.IsSylowTwoOf S H) {U₂ : Subgroup W}
    (hU₂ : IsFlagW H S Z (2 ^ n) 2 U₂) : LineTorusFacts H S Z U₂ (2 ^ n) := by
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hR
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hS
  rw [← hK] at hU₂
  have hUeq := eq_U2_of_isFlagW hW2 hf hg hU₂
  subst hUeq
  refine ⟨fun w hw => ?_, fun X hZX hXU hX => eq_or_eq_of_stable_line hSL hf g hZX hXU hX, ?_⟩
  · have h1 := (fixedW_iff hf hg w).mp hw
    rw [mem_gmap, mem_stdLine] at h1
    exact (mem_pre_plane_iff hf g w).mpr h1.2
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (by have := four_le_card hn hK; omega)
  set d : Kˣ := Units.mk0 c hc0 with hd
  set t := ((rho3 π (g * dLine d * g⁻¹) : ↥H) : MulAut W) with ht
  refine ⟨t, ⟨(rho3 π _).2, dLine_mem_stabW hf g d⟩, ?_, fun s hs => ?_, ?_⟩
  · rw [ht, ← Subgroup.coe_pow, ← map_pow, conj_pow, ← hK, dLine_pow_card_sub_one,
      mul_one, mul_inv_cancel, map_one, Subgroup.coe_one]
  · obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU2_iff hSL hf g s).mp hs
    have hB' : (B⁻¹ : SpecialLinearGroup (Fin 3) K) ∈ stabRow2 K := (stabRow2 K).inv_mem hB
    have hC : dLine d * B * (dLine d)⁻¹ * B⁻¹ ∈ stabRow2 K :=
      (stabRow2 K).mul_mem (dLine_conj_mem d hB) hB'
    have hl : lev2 ((dLine d * B * (dLine d)⁻¹ * B⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      have e1 : leviHom2 K ⟨dLine d * B * (dLine d)⁻¹, dLine_conj_mem d hB⟩ =
          leviHom2 K ⟨B, hB⟩ :=
        Subtype.ext (by rw [leviHom2_coe, leviHom2_coe]; exact lev2_dLine_conj d B)
      have e2 : leviHom2 K ⟨dLine d * B * (dLine d)⁻¹ * B⁻¹, hC⟩ =
          leviHom2 K ⟨dLine d * B * (dLine d)⁻¹, dLine_conj_mem d hB⟩ *
            (leviHom2 K ⟨B, hB⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e1, mul_inv_cancel] at e2
      show lev2 (((⟨_, hC⟩ : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1
      rw [← leviHom2_coe, e2, Matrix.SpecialLinearGroup.coe_one]
    have hmem := mem_pCoreOf_of_lev2 hSL hf g hC hl
    have e : g * (dLine d * B * (dLine d)⁻¹ * B⁻¹) * g⁻¹ =
        (g * dLine d * g⁻¹) * (g * B * g⁻¹) * (g * dLine d * g⁻¹)⁻¹ * (g * B * g⁻¹)⁻¹ := by
      group
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
    simpa [ht] using hmem
  · obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    refine ⟨u, (mem_pre_plane_iff hf g u).mpr (by rw [hu, ginv_g_mulVec]; rfl), fun h => ?_⟩
    have h1 := congrArg f h
    rw [ht, hf.act3, gconj_mulVec, hu, ginv_g_mulVec, dLine, tSL_mulVec] at h1
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [ginv_g_mulVec] at h2
    have h3 := congrFun h2 0
    simp [hd] at h3
    exact hc1 h3


end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
