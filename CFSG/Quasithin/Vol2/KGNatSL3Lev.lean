module

public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped MatrixGroups

theorem eq_bot_of_normal_isPGroup_SL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {N : Subgroup SL(2, F)} [hNn : N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : N ≤ CFSG.CGT.Timmesfeld75.utri F :=
    hN.le_sylow_of_normal (CFSG.CGT.Timmesfeld75.utriSylow F)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp (hle hx)
  have hw := hle (hNn.conj_mem _ hx CFSG.CGT.Timmesfeld75.wElt)
  have h10 : (CFSG.CGT.Timmesfeld75.wElt * CFSG.CGT.Timmesfeld75.utriElt s *
      CFSG.CGT.Timmesfeld75.wElt⁻¹ : SL(2, F)) 1 0 = 0 := hw.1
  rw [CFSG.CGT.Timmesfeld75.conj_utriElt_apply_10, CFSG.CGT.Timmesfeld75.wElt_apply_10] at h10
  have hs : s = 0 := by linear_combination -h10
  rw [Subgroup.mem_bot, hs, CFSG.CGT.Timmesfeld75.utriElt_zero]

section Levi

variable {K : Type} [Field K]

variable (K) in
@[expose] def stabE0 : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {B | (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0]}
  mul_mem' := fun {a b} ha hb => by
    change ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [show (b : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] from hb]
    exact ha
  one_mem' := by
    change ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    conv_lhs => rw [← show (a : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] from ha]
    rw [ginv_g_mulVec]

theorem mem_stabE0 {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ stabE0 K ↔ (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := Iff.rfl

theorem stabE0_entries {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabE0 K) :
    (B : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧ (B : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have h := mem_stabE0.mp hB
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 2

@[expose] def lev (B : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => B i.succ j.succ

omit [Field K] in
theorem lev_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 2) : lev B i j = B i.succ j.succ :=
  rfl

theorem lev_mul {A B : Matrix (Fin 3) (Fin 3) K} (a10 : A 1 0 = 0) (a20 : A 2 0 = 0) :
    lev (A * B) = lev A * lev B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lev, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, a10, a20]

theorem det_lev {B : Matrix (Fin 3) (Fin 3) K} (h00 : B 0 0 = 1) (h10 : B 1 0 = 0)
    (h20 : B 2 0 = 0) : (lev B).det = B.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three, h00, h10, h20]
  simp [lev]

variable (K) in
@[expose] noncomputable def leviHom : ↥(stabE0 K) →* SL(2, K) where
  toFun B := ⟨lev ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
    obtain ⟨h00, h10, h20⟩ := stabE0_entries B.2
    rw [det_lev h00 h10 h20]
    exact (B : SpecialLinearGroup (Fin 3) K).2⟩
  map_one' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lev])
  map_mul' A B := by
    obtain ⟨-, a10, a20⟩ := stabE0_entries A.2
    refine Subtype.ext ?_
    change lev ((((A * B : ↥(stabE0 K)) : SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) = lev ((A : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * lev ((B : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, lev_mul a10 a20]

theorem leviHom_coe (B : ↥(stabE0 K)) :
    ((leviHom K B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      lev ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem leviHom_surjective : Function.Surjective (leviHom K) := by
  intro A
  have hA := A.2
  rw [Matrix.det_fin_two] at hA
  refine ⟨⟨⟨!![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1], ?_⟩, ?_⟩, ?_⟩
  · rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hA
  · refine mem_stabE0.mpr ?_
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · refine Subtype.ext ?_
    rw [leviHom_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem mulVec_of_leviHom_eq_one {B : ↥(stabE0 K)} (hB : leviHom K B = 1) (v : Fin 3 → K) :
    (((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 ∧
      (((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2 := by
  obtain ⟨-, h10, h20⟩ := stabE0_entries B.2
  have hl : lev ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← leviHom_coe, hB, Matrix.SpecialLinearGroup.coe_one]
  have h11 := congrFun (congrFun hl 0) 0
  have h12 := congrFun (congrFun hl 0) 1
  have h21 := congrFun (congrFun hl 1) 0
  have h22 := congrFun (congrFun hl 1) 1
  simp only [lev_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h11 h12 h21 h22
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h11, h12, h21, h22]
  simp

end Levi

section HU1

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem levi_of_mem_pCoreOf_HU1 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {x : MulAut W}
    (hx : x ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)))) :
    ∃ B : SpecialLinearGroup (Fin 3) K, (∀ v : Fin 3 → K,
      ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 ∧
        ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2) ∧
      x = ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) := by
  set L := perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))
    with hL
  let φ : ↥(stabE0 K) →* ↥L := MonoidHom.codRestrict
    (H.subtype.comp ((rho3 π).comp ((MulAut.conj g).toMonoidHom.comp (stabE0 K).subtype))) L
    (fun B => (mem_perfectCore_HU1_iff hSL hf g _).mpr
      ⟨(B : SpecialLinearGroup (Fin 3) K), B.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro B B' h
    have h1 : rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) =
        rho3 π (g * (B' : SpecialLinearGroup (Fin 3) K) * g⁻¹) :=
      Subtype.ext (congrArg (fun z : ↥L => (z : MulAut W)) h)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel ((rho3_bijective hf).1 h1)))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU1_iff hSL hf g y).mp hy
    exact ⟨⟨B, hB⟩, rfl⟩
  set e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with he
  set Λ : ↥L →* SL(2, K) := (leviHom K).comp e.symm.toMonoidHom with hΛ
  have hΛsurj : Function.Surjective Λ := leviHom_surjective.comp e.symm.surjective
  have hcore : CFSG.Open.pCore 2 ↥L ≤ Λ.ker := by
    rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_
    rw [← Subgroup.map_eq_bot_iff]
    have : (N.map Λ).Normal := hN.map Λ hΛsurj
    exact eq_bot_of_normal_isPGroup_SL2 (hp.map Λ)
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨e.symm y, fun v => mulVec_of_leviHom_eq_one (MonoidHom.mem_ker.mp (hcore hy)) v, ?_⟩
  have h1 : φ (e.symm y) = y := e.apply_symm_apply y
  exact (congrArg L.subtype h1).symm

end HU1

end CFSG.Quasithin.Vol2.KGNat
