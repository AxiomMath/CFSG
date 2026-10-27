module

public import CFSG.Quasithin.Background.SmithB45J2SylCheck

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

section Drop

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem card_inf_ker_mul_le [Finite M] (W : Submodule K M) (φ : M →ₗ[K] N) {x : M} (hx : x ∈ W)
    (hφ : φ x ≠ 0) : Nat.card ↥(W ⊓ LinearMap.ker φ) * Nat.card K ≤ Nat.card ↥W := by
  let f : K × ↥(W ⊓ LinearMap.ker φ) → ↥W := fun p =>
    ⟨p.1 • x + p.2, W.add_mem (W.smul_mem _ hx) (Submodule.mem_inf.mp p.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨c, k⟩ ⟨c', k'⟩ h
    have h1 : c • x + (k : M) = c' • x + k' := congrArg Subtype.val h
    have hk : φ k = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp k.2).2
    have hk' : φ k' = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp k'.2).2
    have h2 : φ (c • x + k) = φ (c' • x + k') := by rw [h1]
    rw [map_add, map_add, map_smul, map_smul, hk, hk', add_zero, add_zero] at h2
    have hc : c = c' := by
      by_contra hne
      apply hφ
      have h3 : (c - c') • φ x = 0 := by rw [sub_smul, h2, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)
    subst hc
    exact Prod.ext rfl (Subtype.ext (add_left_cancel h1))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, mul_comm] at this

@[expose] def ChainOK (W : Submodule K M) : List ((M →ₗ[K] K) × M) → Prop
  | [] => True
  | p :: c => p.2 ∈ W ∧ p.1 p.2 ≠ 0 ∧ ChainOK (W ⊓ LinearMap.ker p.1) c

@[expose] def chainSub (W : Submodule K M) : List ((M →ₗ[K] K) × M) → Submodule K M
  | [] => W
  | p :: c => chainSub (W ⊓ LinearMap.ker p.1) c

theorem card_chainSub [Finite M] (W : Submodule K M) (c : List ((M →ₗ[K] K) × M))
    (h : ChainOK W c) : Nat.card ↥(chainSub W c) * Nat.card K ^ c.length ≤ Nat.card ↥W := by
  induction c generalizing W with
  | nil => simp [chainSub]
  | cons p c ih =>
    obtain ⟨hx, hℓ, hc⟩ := h
    have h1 := ih _ hc
    have h2 := card_inf_ker_mul_le W p.1 hx hℓ
    calc Nat.card ↥(chainSub W (p :: c)) * Nat.card K ^ (p :: c).length
        = Nat.card ↥(chainSub (W ⊓ LinearMap.ker p.1) c) * Nat.card K ^ c.length *
          Nat.card K := by simp [chainSub, pow_succ, mul_assoc]
      _ ≤ Nat.card ↥(W ⊓ LinearMap.ker p.1) * Nat.card K := Nat.mul_le_mul_right _ h1
      _ ≤ Nat.card ↥W := h2

theorem le_chainSub {U W : Submodule K M} (hU : U ≤ W) (c : List ((M →ₗ[K] K) × M))
    (hker : ∀ p ∈ c, U ≤ LinearMap.ker p.1) : U ≤ chainSub W c := by
  induction c generalizing W with
  | nil => exact hU
  | cons p c ih =>
    exact ih (le_inf hU (hker p List.mem_cons_self)) fun q hq => hker q (List.mem_cons_of_mem _ hq)

end Drop

abbrev V6 := Fin 6 → FieldFour

abbrev M6 := Matrix (Fin 6) (Fin 6) FieldFour

abbrev GL6 := Matrix.GeneralLinearGroup (Fin 6) FieldFour

@[expose] noncomputable def fixM (M : M6) : Submodule FieldFour V6 :=
  LinearMap.ker (Matrix.mulVecLin (M - 1))

theorem mem_fixM {M : M6} {v : V6} : v ∈ fixM M ↔ M *ᵥ v = v := by
  rw [fixM, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]

@[expose] noncomputable def ell (M : M6) (q : Fin 6) : V6 →ₗ[FieldFour] FieldFour :=
  (LinearMap.proj q).comp (Matrix.mulVecLin (M - 1))

theorem ell_apply (M : M6) (q : Fin 6) (v : V6) : ell M q v = ((M - 1) *ᵥ v) q := rfl

theorem fixM_le_ker_ell (M : M6) (q : Fin 6) : fixM M ≤ LinearMap.ker (ell M q) := by
  intro v hv
  rw [LinearMap.mem_ker, ell_apply]
  rw [fixM, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  rw [hv]
  rfl

theorem card_V6 : Nat.card V6 = 4096 := by
  rw [Nat.card_fun, FieldFour.natCard_eq, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem card_top : Nat.card ↥(⊤ : Submodule FieldFour V6) = 4096 := by
  rw [Nat.card_congr (Submodule.topEquiv (R := FieldFour) (M := V6)).toEquiv, card_V6]

theorem toVec_disp (m : BM) (x : BV) : (disp m x).toVec = (m.toMat - 1) *ᵥ x.toVec := by
  rw [disp, BV.toVec_add, BM.toVec_mv, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  rw [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg, CharTwo.neg_eq]

@[expose] noncomputable def prevSub (M : M6) (prev : List (Fin 6)) : Submodule FieldFour V6 :=
  prev.foldr (fun q W => LinearMap.ker (ell M q) ⊓ W) ⊤

theorem mem_prevSub {M : M6} {prev : List (Fin 6)} {v : V6} :
    v ∈ prevSub M prev ↔ ∀ q ∈ prev, ell M q v = 0 := by
  induction prev with
  | nil => simp [prevSub]
  | cons q prev ih =>
    simp only [prevSub, List.foldr_cons, Submodule.mem_inf, LinearMap.mem_ker, List.mem_cons,
      forall_eq_or_imp] at ih ⊢
    rw [ih]

theorem ell_eq_get (m : BM) (q : Fin 6) (x : BV) : ell m.toMat q x.toVec = (disp m x).get q := by
  rw [ell_apply, ← toVec_disp]
  rfl

@[expose] noncomputable def chainInterp (m : BM) (c : List (Fin 6 × BV)) :
    List ((V6 →ₗ[FieldFour] FieldFour) × V6) :=
  c.map fun p => (ell m.toMat p.1, p.2.toVec)

theorem chainOK_sound (m : BM) (c : List (Fin 6 × BV)) (prev : List (Fin 6))
    (h : chainOK m c prev = true) : ChainOK (prevSub m.toMat prev) (chainInterp m c) := by
  induction c generalizing prev with
  | nil => trivial
  | cons p c ih =>
    obtain ⟨q, x⟩ := p
    simp only [chainOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hnz, hprev⟩, hc⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_prevSub]
      intro q' hq'
      rw [ell_eq_get]
      have h1 := hprev q' hq'
      by_contra hne
      have := (BV.nz_iff _ _).mpr hne
      rw [this] at h1
      exact absurd h1 (by decide)
    · show ell m.toMat q x.toVec ≠ 0
      rw [ell_eq_get]
      exact (BV.nz_iff _ _).mp hnz
    · have := ih (q :: prev) hc
      show ChainOK (prevSub m.toMat prev ⊓ LinearMap.ker (ell m.toMat q)) (chainInterp m c)
      rw [inf_comm]
      exact this

theorem card_fixM_of_chainOK (m : BM) (c : List (Fin 6 × BV)) (h : chainOK m c [] = true) :
    Nat.card ↥(fixM m.toMat) * 4 ^ c.length ≤ 4096 := by
  have hc := chainOK_sound m c [] h
  have h1 := card_chainSub _ _ hc
  have hle : fixM m.toMat ≤ chainSub (prevSub m.toMat []) (chainInterp m c) := by
    refine le_chainSub le_top _ fun p hp => ?_
    obtain ⟨⟨q, x⟩, -, rfl⟩ := List.mem_map.mp hp
    exact fixM_le_ker_ell _ q
  have h2 := Nat.card_le_card_of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)
  rw [FieldFour.natCard_eq, chainInterp, List.length_map] at h1
  have h3 : prevSub m.toMat [] = ⊤ := rfl
  rw [h3, card_top] at h1
  calc Nat.card ↥(fixM m.toMat) * 4 ^ c.length ≤
      Nat.card ↥(chainSub ⊤ (chainInterp m c)) * 4 ^ c.length := Nat.mul_le_mul_right _ h2
    _ ≤ 4096 := by rw [← h3]; exact h1

theorem toMat_eq_of_eqv {m n : BM} (h : m.eqv n = true) : m.toMat = n.toMat :=
  (BM.eqv_iff m n).mp h

@[expose] noncomputable def gA : GL6 :=
  ⟨a6.toMat, a6i.toMat, by rw [← BM.toMat_mul, toMat_eq_of_eqv gen_check.1, BM.toMat_one],
    by rw [← BM.toMat_mul, toMat_eq_of_eqv gen_check.2.1, BM.toMat_one]⟩

@[expose] noncomputable def gB : GL6 :=
  ⟨b6.toMat, b6i.toMat, by rw [← BM.toMat_mul, toMat_eq_of_eqv gen_check.2.2.1, BM.toMat_one],
    by rw [← BM.toMat_mul, toMat_eq_of_eqv gen_check.2.2.2, BM.toMat_one]⟩

@[expose] noncomputable def Γ₆ : Subgroup GL6 := Subgroup.closure {gA, gB}

@[expose] noncomputable def gen4GL : Fin 4 → GL6 := ![gA, gA⁻¹, gB, gB⁻¹]

@[expose] noncomputable def wordGL : List (Fin 4) → GL6
  | [] => 1
  | g :: l => gen4GL g * wordGL l

theorem coe_gen4GL (g : Fin 4) : (gen4GL g : M6) = (gen4 g).toMat := by
  fin_cases g <;> rfl

theorem coe_wordGL (l : List (Fin 4)) : (wordGL l : M6) = (evalW l).toMat := by
  induction l with
  | nil => rw [wordGL, evalW, BM.toMat_one]; rfl
  | cons g l ih => rw [wordGL, evalW, Units.val_mul, ih, coe_gen4GL, BM.toMat_mul]

theorem gen4GL_mem (g : Fin 4) : gen4GL g ∈ Γ₆ := by
  have hA : gA ∈ Γ₆ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : gB ∈ Γ₆ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases g
  · exact hA
  · exact Γ₆.inv_mem hA
  · exact hB
  · exact Γ₆.inv_mem hB

theorem wordGL_mem (l : List (Fin 4)) : wordGL l ∈ Γ₆ := by
  induction l with
  | nil => exact Γ₆.one_mem
  | cons g l ih => exact Γ₆.mul_mem (gen4GL_mem g) ih

@[expose] noncomputable def sGenGL (k : Fin 4) : GL6 := wordGL (sWord k)

theorem coe_sGenGL (k : Fin 4) : (sGenGL k : M6) = (sGen k).toMat := by
  rw [sGenGL, coe_wordGL]
  have h := sGen_check
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  exact toMat_eq_of_eqv (h k)

theorem sGenGL_mul_self (k : Fin 4) : sGenGL k * sGenGL k = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_sGenGL, ← BM.toMat_mul, Units.val_one]
  have h := sGen_sq_check
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  rw [toMat_eq_of_eqv (h k), BM.toMat_one]

@[expose] noncomputable def S₂ : Subgroup GL6 := Subgroup.closure (Set.range sGenGL)

theorem S₂_le : S₂ ≤ Γ₆ := by
  rw [S₂, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact wordGL_mem _

theorem sMul_spec (i : Fin 128) (g : Fin 4) :
    (sGen g).toMat * (sEl i).toMat = (sEl sMulV[i][g]).toMat := by
  have h := sMul_check
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  rw [← BM.toMat_mul]
  exact toMat_eq_of_eqv (h i g)

theorem exists_sEl_of_mem {x : GL6} (hx : x ∈ S₂) : ∃ i : Fin 128, (x : M6) = (sEl i).toMat := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by rw [Units.val_one, toMat_eq_of_eqv sEl_zero, BM.toMat_one]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨i, hi⟩ := ih
    exact ⟨sMulV[i][k], by rw [Units.val_mul, hi, coe_sGenGL, sMul_spec]⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨i, hi⟩ := ih
    have hinv : (sGenGL k)⁻¹ = sGenGL k := inv_eq_of_mul_eq_one_right (sGenGL_mul_self k)
    exact ⟨sMulV[i][k], by rw [hinv, Units.val_mul, hi, coe_sGenGL, sMul_spec]⟩

theorem exists_mem_of_sEl (i : Fin 128) : ∃ x ∈ S₂, (x : M6) = (sEl i).toMat := by
  suffices key : ∀ n, ∀ i : Fin 128, i.val = n → ∃ x ∈ S₂, (x : M6) = (sEl i).toMat from
    key _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro i hin
    have ih : ∀ j : Fin 128, j < i → ∃ x ∈ S₂, (x : M6) = (sEl j).toMat := fun j hj =>
      ihn j.val (hin ▸ hj) j rfl
    have h := sPar_check
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h i with h0 | ⟨hlt, hmul⟩
    · subst h0
      exact ⟨1, S₂.one_mem, by rw [Units.val_one, toMat_eq_of_eqv sEl_zero, BM.toMat_one]⟩
    · obtain ⟨y, hy, hyi⟩ := ih _ hlt
      refine ⟨sGenGL sParV[i].2 * y, S₂.mul_mem (Subgroup.subset_closure ⟨_, rfl⟩) hy, ?_⟩
      rw [Units.val_mul, hyi, coe_sGenGL, sMul_spec, hmul]

theorem key_eq_of_toMat_eq {m n : BM} (h : m.toMat = n.toMat) : m.key = n.key := by
  have h' := (BM.eqv_iff m n).mpr h
  simp only [BM.eqv, BV.eqv, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨e1, e2⟩, e3, e4⟩, e5, e6⟩, e7, e8⟩, e9, e10⟩, e11, e12⟩ := h'
  unfold BM.key
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

theorem sEl_injective {i j : Fin 128} (h : (sEl i).toMat = (sEl j).toMat) : i = j := by
  have hk := sKey_check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hk
  rcases hk i j with h1 | h1
  · exact h1
  · exact absurd (key_eq_of_toMat_eq h) h1

theorem card_S₂ : Nat.card S₂ = 128 := by
  classical
  choose f hf using fun x : ↥S₂ => exists_sEl_of_mem x.2
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    rw [hf x, hf y, hxy]
  have hsurj : Function.Surjective f := by
    intro i
    obtain ⟨x, hx, hxi⟩ := exists_mem_of_sEl i
    exact ⟨⟨x, hx⟩, sEl_injective (by rw [← hf ⟨x, hx⟩, ← hxi])⟩
  rw [Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_invD {x : GL6} (hx : x ∈ S₂) (h2 : x * x = 1) (h1 : x ≠ 1) :
    ∃ d ∈ inv2A ++ inv2B, (x : M6) = (sEl d.idx).toMat := by
  obtain ⟨i, hi⟩ := exists_sEl_of_mem hx
  have h := sInv_check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, List.any_eq_true] at h
  rcases h i with ((h3 | h3) | ⟨d, hd, hdi⟩) | ⟨d, hd, hdi⟩
  · exfalso
    have h4 : ((sEl i).mul (sEl i)).eqv BM.one = true := by
      rw [BM.eqv_iff, BM.toMat_mul, ← hi, BM.toMat_one, ← Units.val_mul, h2, Units.val_one]
    rw [h4] at h3
    exact absurd h3 (by decide)
  · subst h3
    exact absurd (Units.ext (by rw [hi, toMat_eq_of_eqv sEl_zero, BM.toMat_one]; rfl)) h1
  · exact ⟨d, List.mem_append_left _ hd, by rw [hi, hdi]⟩
  · exact ⟨d, List.mem_append_right _ hd, by rw [hi, hdi]⟩

theorem invOK_spec {n : ℕ} {d : InvD} (h : invOK n d = true) :
    (∀ x ∈ d.beta, x.toVec ∈ fixM (sEl d.idx).toMat) ∧
      Nat.card ↥(fixM (sEl d.idx).toMat) * 4 ^ (6 - n) ≤ 4096 := by
  simp only [invOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨-, hb⟩, hl⟩, hc⟩ := h
  refine ⟨fun x hx => mem_fixM.mpr ?_, ?_⟩
  · rw [← BM.toVec_mv]
    exact (BV.eqv_iff _ _).mp (hb x hx)
  · rw [← hl]
    exact card_fixM_of_chainOK _ _ hc

theorem invOK_of_mem {d : InvD} (hd : d ∈ inv2A ++ inv2B) :
    invOK 4 d = true ∨ invOK 3 d = true := by
  rcases List.mem_append.mp hd with hd | hd
  · have h := inv2A_check
    rw [List.all_eq_true] at h
    exact Or.inl (h d hd)
  · have h := inv2B_check
    simp only [List.all_eq_true, Bool.and_eq_true] at h
    exact Or.inr (h d hd).1

theorem beta_mem {d : InvD} (hd : d ∈ inv2A ++ inv2B) {x : BV} (hx : x ∈ d.beta) :
    x.toVec ∈ fixM (sEl d.idx).toMat := by
  rcases invOK_of_mem hd with h | h
  · exact (invOK_spec h).1 x hx
  · exact (invOK_spec h).1 x hx

theorem card_fixM_2A {d : InvD} (hd : d ∈ inv2A) : Nat.card ↥(fixM (sEl d.idx).toMat) ≤ 256 := by
  have h := inv2A_check
  rw [List.all_eq_true] at h
  have := (invOK_spec (h d hd)).2
  norm_num at this
  omega

theorem card_fixM_2B {d : InvD} (hd : d ∈ inv2B) : Nat.card ↥(fixM (sEl d.idx).toMat) ≤ 64 := by
  have h := inv2B_check
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  have := (invOK_spec (h d hd).1).2
  norm_num at this
  omega

theorem card_fixM_le {d : InvD} (hd : d ∈ inv2A ++ inv2B) :
    Nat.card ↥(fixM (sEl d.idx).toMat) ≤ 256 := by
  rcases List.mem_append.mp hd with hd | hd
  · exact card_fixM_2A hd
  · exact (card_fixM_2B hd).trans (by norm_num)

theorem moves_spec {m : BM} {beta : List BV} (h : moves m beta = true) :
    ∃ x ∈ beta, m.toMat *ᵥ x.toVec ≠ x.toVec := by
  simp only [moves, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨x, hx, hne⟩ := h
  refine ⟨x, hx, fun he => ?_⟩
  rw [← BM.toVec_mv, ← BV.eqv_iff] at he
  rw [he] at hne
  exact absurd hne (by decide)

theorem card_fixM_inf_le {a y : M6} {x : V6} (hx : x ∈ fixM a) (hy : y *ᵥ x ≠ x) :
    Nat.card ↥(fixM a ⊓ fixM y) * 4 ≤ Nat.card ↥(fixM a) := by
  have h := card_inf_ker_mul_le (fixM a) (Matrix.mulVecLin (y - 1)) hx (by
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_ne_zero]
    exact hy)
  rwa [FieldFour.natCard_eq] at h

@[expose] def mFix (B : Subgroup GL6) : Submodule FieldFour V6 where
  carrier := {v | ∀ b ∈ B, (b : M6) *ᵥ v = v}
  add_mem' := fun {v w} hv hw b hb => by rw [Matrix.mulVec_add, hv b hb, hw b hb]
  zero_mem' := fun b _ => Matrix.mulVec_zero _
  smul_mem' := fun c {v} hv b hb => by rw [Matrix.mulVec_smul, hv b hb]

theorem mem_mFix {B : Subgroup GL6} {v : V6} : v ∈ mFix B ↔ ∀ b ∈ B, (b : M6) *ᵥ v = v :=
  Iff.rfl

theorem mFix_le_fixM {B : Subgroup GL6} {b : GL6} (hb : b ∈ B) : mFix B ≤ fixM b :=
  fun _ hv => mem_fixM.mpr (hv b hb)

theorem card_mono {U W : Submodule FieldFour V6} (h : U ≤ W) : Nat.card ↥U ≤ Nat.card ↥W :=
  Nat.card_le_card_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem exists_mem_notMem {B : Subgroup GL6} (s : Finset GL6) (h : s.card < Nat.card B) :
    ∃ c ∈ B, c ∉ s := by
  by_contra hc
  push Not at hc
  have h1 : Nat.card ↥(B : Set GL6) ≤ Nat.card ↥(s : Set GL6) :=
    Nat.card_mono s.finite_toSet fun x hx => hc x hx
  rw [Nat.card_coe_set_eq (s : Set GL6), Set.ncard_coe_finset] at h1
  exact absurd h1 (not_le.mpr h)

theorem card_range_mul_card_fixM (a : M6) :
    Nat.card ↥(LinearMap.range (Matrix.mulVecLin (a - 1))) * Nat.card ↥(fixM a) = 4096 := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Matrix.mulVecLin (a - 1)))
  have h2 := Nat.card_congr (LinearMap.quotKerEquivRange (Matrix.mulVecLin (a - 1))).toEquiv
  rw [card_V6] at h1
  rw [fixM, ← h2, mul_comm, ← h1]

theorem units_eq_of_toMat {x y : GL6} {m : BM} (hx : (x : M6) = m.toMat) (hy : (y : M6) = m.toMat) :
    x = y :=
  Units.ext (hx.trans hy.symm)

theorem idx_ne {x y : GL6} {d e : InvD} (hx : (x : M6) = (sEl d.idx).toMat)
    (hy : (y : M6) = (sEl e.idx).toMat) (hne : x ≠ y) : d.idx ≠ e.idx := by
  intro h
  apply hne
  apply Units.ext
  rw [hx, hy, h]

theorem one_lt_card_fixM_one : 256 < Nat.card ↥(fixM (1 : M6)) := by
  have h : fixM (1 : M6) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_fixM, Matrix.one_mulVec]
  rw [h, card_top]
  norm_num

theorem ne_one_of_mem_inv2B {x : GL6} {d : InvD} (hd : d ∈ inv2B)
    (hx : (x : M6) = (sEl d.idx).toMat) : x ≠ 1 := by
  rintro rfl
  have h1 := card_fixM_2B hd
  rw [← hx, Units.val_one] at h1
  have := one_lt_card_fixM_one
  omega

theorem fixOK_spec {d : InvD} (h : fixOK d = true) :
    ∃ f₁ f₂ : Fin 128, (sEl d.idx).toMat * (sEl f₁).toMat = (sEl f₂).toMat ∧
      ∀ e ∈ inv2A ++ inv2B, e.idx = d.idx ∨ e.idx = f₁ ∨ e.idx = f₂ ∨
        moves (sEl e.idx) d.beta = true := by
  unfold fixOK at h
  split at h
  · rename_i f₁ f₂ _
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨f₁, f₂, by rw [← BM.toMat_mul]; exact toMat_eq_of_eqv h1, fun e he => ?_⟩
    rcases h2 e he with ((h3 | h3) | h3) | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))
  · exact absurd h (by decide)

theorem mem_comm2A {d e : InvD} (hd : d ∈ inv2A) (he : e ∈ inv2A) (hne : e.idx ≠ d.idx)
    (hc : (sEl d.idx).toMat * (sEl e.idx).toMat = (sEl e.idx).toMat * (sEl d.idx).toMat) :
    (d.idx, e.idx) ∈ comm2A := by
  have h := comm2A_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h d hd e he with (h1 | h1) | h1
  · exact absurd h1 hne
  · exact List.elem_iff.mp h1
  · rw [← BM.toMat_mul, ← BM.toMat_mul, ← BM.eqv_iff] at hc
    rw [hc] at h1
    exact absurd h1 (by decide)

section Bounds

variable {B : Subgroup GL6}

theorem exists_ne_one (h : 2 ≤ Nat.card B) : ∃ a ∈ B, a ≠ 1 := by
  obtain ⟨a, ha, ha1⟩ := exists_mem_notMem {1} (B := B) (by simp; omega)
  exact ⟨a, ha, by simpa using ha1⟩

theorem card_mFix_of_two (hB : B ≤ S₂) (hsq : ∀ x ∈ B, x * x = 1) (h2 : 2 ≤ Nat.card B) :
    Nat.card ↥(mFix B) ≤ 256 := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one h2
  obtain ⟨d, hd, hda⟩ := exists_invD (hB ha) (hsq a ha) ha1
  calc Nat.card ↥(mFix B) ≤ Nat.card ↥(fixM (a : M6)) := card_mono (mFix_le_fixM ha)
    _ = Nat.card ↥(fixM (sEl d.idx).toMat) := by rw [hda]
    _ ≤ 256 := card_fixM_le hd

theorem card_mFix_of_three (hB : B ≤ S₂) (hsq : ∀ x ∈ B, x * x = 1) (h3 : 3 ≤ Nat.card B) :
    Nat.card ↥(mFix B) ≤ 64 := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one (B := B) (by omega)
  obtain ⟨b, hb, hb1⟩ := exists_mem_notMem {1, a} (B := B)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb1
  obtain ⟨d, hd, hda⟩ := exists_invD (hB ha) (hsq a ha) ha1
  obtain ⟨e, he, heb⟩ := exists_invD (hB hb) (hsq b hb) hb1.1
  by_cases hd2 : d ∈ inv2B
  · calc Nat.card ↥(mFix B) ≤ Nat.card ↥(fixM (a : M6)) := card_mono (mFix_le_fixM ha)
      _ = Nat.card ↥(fixM (sEl d.idx).toMat) := by rw [hda]
      _ ≤ 64 := card_fixM_2B hd2
  by_cases he2 : e ∈ inv2B
  · calc Nat.card ↥(mFix B) ≤ Nat.card ↥(fixM (b : M6)) := card_mono (mFix_le_fixM hb)
      _ = Nat.card ↥(fixM (sEl e.idx).toMat) := by rw [heb]
      _ ≤ 64 := card_fixM_2B he2
  have hdA : d ∈ inv2A := (List.mem_append.mp hd).resolve_right hd2
  have heA : e ∈ inv2A := (List.mem_append.mp he).resolve_right he2
  have hne : e.idx ≠ d.idx := idx_ne heb hda hb1.2
  have hp := pair2A_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp d hdA e heA with h | h
  · exact absurd h hne
  obtain ⟨x, hx, hxm⟩ := moves_spec h
  have hdrop := card_fixM_inf_le (beta_mem hd hx) hxm
  have h256 := card_fixM_2A hdA
  rw [← hda, ← heb] at hdrop
  rw [← hda] at h256
  have hab : mFix B ≤ fixM (a : M6) ⊓ fixM (b : M6) := le_inf (mFix_le_fixM ha) (mFix_le_fixM hb)
  have := card_mono hab
  omega

theorem exists_mem_inv2B (hB : B ≤ S₂) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h5 : 5 ≤ Nat.card B) :
    ∃ a ∈ B, ∃ d ∈ inv2B, (a : M6) = (sEl d.idx).toMat := by
  by_contra hno
  push Not at hno
  have h2A : ∀ x ∈ B, x ≠ 1 → ∃ d ∈ inv2A, (x : M6) = (sEl d.idx).toMat := by
    intro x hx hx1
    obtain ⟨d, hd, hdx⟩ := exists_invD (hB hx) (hsq x hx) hx1
    rcases List.mem_append.mp hd with hd | hd
    · exact ⟨d, hd, hdx⟩
    · exact absurd hdx (hno x hx d hd)
  obtain ⟨a, ha, ha1⟩ := exists_ne_one (B := B) (by omega)
  obtain ⟨b, hb, hb1⟩ := exists_mem_notMem {1, a} (B := B)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨c, hc, hc1⟩ := exists_mem_notMem {1, a, b, a * b} (B := B)
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb1 hc1
  obtain ⟨d, hd, hda⟩ := h2A a ha ha1
  obtain ⟨e, he, heb⟩ := h2A b hb hb1.1
  obtain ⟨f, hf, hfc⟩ := h2A c hc hc1.1
  have hcm : ∀ {x y : GL6} {d e : InvD}, x ∈ B → y ∈ B → (x : M6) = (sEl d.idx).toMat →
      (y : M6) = (sEl e.idx).toMat →
        (sEl d.idx).toMat * (sEl e.idx).toMat = (sEl e.idx).toMat * (sEl d.idx).toMat := by
    intro x y d e hx hy hxd hye
    rw [← hxd, ← hye, ← Units.val_mul, ← Units.val_mul, hcomm x hx y hy]
  have hab := mem_comm2A hd he (idx_ne heb hda hb1.2) (hcm ha hb hda heb)
  have hac := mem_comm2A hd hf (idx_ne hfc hda hc1.2.1) (hcm ha hc hda hfc)
  have hbc := mem_comm2A he hf (idx_ne hfc heb hc1.2.2.1) (hcm hb hc heb hfc)
  have h5' := d5_check
  simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h5'
  rcases h5' _ hab _ hac with ((h1 | h1) | h1) | h1
  · exact h1 rfl
  · exact absurd h1.symm (idx_ne hfc heb hc1.2.2.1)
  · have h2 : comm2A.contains (e.idx, f.idx) = true := List.elem_eq_true_of_mem hbc
    simp only at h1
    rw [h2] at h1
    exact absurd h1 (by decide)
  · apply hc1.2.2.2
    apply Units.ext
    rw [hfc, toMat_eq_of_eqv h1, BM.toMat_mul, Units.val_mul, hda, heb]

theorem card_mFix_of_five (hB : B ≤ S₂) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h5 : 5 ≤ Nat.card B) :
    Nat.card ↥(mFix B) ≤ 16 ∧ ∃ x ∈ B, ∃ y ∈ B, ((y : M6) - 1) * ((x : M6) - 1) ≠ 0 := by
  obtain ⟨a, ha, d, hd, hda⟩ := exists_mem_inv2B hB hcomm hsq h5
  have ha1 := ne_one_of_mem_inv2B hd hda
  have h64 := card_fixM_2B hd
  rw [← hda] at h64
  have hdd : d ∈ inv2A ++ inv2B := List.mem_append_right _ hd
  have hfix := inv2B_check
  simp only [List.all_eq_true, Bool.and_eq_true] at hfix
  obtain ⟨f₁, f₂, hf12, hfe⟩ := fixOK_spec (hfix d hd).2
  obtain ⟨b, hb, hb1⟩ := exists_mem_notMem {1, a} (B := B)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨c, hc, hc1⟩ := exists_mem_notMem {1, a, b, a * b} (B := B)
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb1 hc1
  obtain ⟨e, he, heb⟩ := exists_invD (hB hb) (hsq b hb) hb1.1
  obtain ⟨f, hf, hfc⟩ := exists_invD (hB hc) (hsq c hc) hc1.1
  have hmove : ∃ y ∈ B, ∃ x ∈ d.beta, (y : M6) *ᵥ x.toVec ≠ x.toVec := by
    rcases hfe e he with h | h | h | h
    · exact absurd h (idx_ne heb hda hb1.2)
    · rcases hfe f hf with h' | h' | h' | h'
      · exact absurd h' (idx_ne hfc hda hc1.2.1)
      · exact absurd (h.trans h'.symm) (idx_ne heb hfc (Ne.symm hc1.2.2.1))
      · exfalso
        apply hc1.2.2.2
        apply Units.ext
        rw [hfc, h', ← hf12, ← h, Units.val_mul, hda, heb]
      · obtain ⟨x, hx, hxm⟩ := moves_spec h'
        exact ⟨c, hc, x, hx, by rw [hfc]; exact hxm⟩
    · rcases hfe f hf with h' | h' | h' | h'
      · exact absurd h' (idx_ne hfc hda hc1.2.1)
      · exfalso
        apply hc1.2.2.2
        have hsa : a * a = 1 := hsq a ha
        have hb' : b = a * c := by
          apply Units.ext
          rw [heb, h, ← hf12, ← h', Units.val_mul, hda, hfc]
        rw [hb', ← mul_assoc, hsa, one_mul]
      · exact absurd (h.trans h'.symm) (idx_ne heb hfc (Ne.symm hc1.2.2.1))
      · obtain ⟨x, hx, hxm⟩ := moves_spec h'
        exact ⟨c, hc, x, hx, by rw [hfc]; exact hxm⟩
    · obtain ⟨x, hx, hxm⟩ := moves_spec h
      exact ⟨b, hb, x, hx, by rw [heb]; exact hxm⟩
  obtain ⟨y, hy, x, hx, hxm⟩ := hmove
  have hxa : x.toVec ∈ fixM (a : M6) := by rw [hda]; exact beta_mem hdd hx
  have hdrop := card_fixM_inf_le hxa hxm
  have hay : mFix B ≤ fixM (a : M6) ⊓ fixM (y : M6) := le_inf (mFix_le_fixM ha) (mFix_le_fixM hy)
  have hcard := card_mono hay
  have h16 : Nat.card ↥(mFix B) ≤ 16 := by omega
  refine ⟨h16, ?_⟩
  by_contra hq
  push Not at hq
  have hrange : LinearMap.range (Matrix.mulVecLin ((a : M6) - 1)) ≤ mFix B := by
    rintro _ ⟨v, rfl⟩ z hz
    have h0 := congrArg (fun M => M *ᵥ v) (hq a ha z hz)
    simp only [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h0
    rw [Matrix.mulVecLin_apply]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have h4 := Nat.mul_le_mul ((card_mono hrange).trans h16) h64
  rw [card_range_mul_card_fixM] at h4
  norm_num at h4

end Bounds

end CFSG.Quasithin.J2Row
