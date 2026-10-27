module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U6
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.LineU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

private theorem p9u7a_permMatrix_apply (π : Equiv.Perm (Fin m)) (a b : Fin m) :
    π.permMatrix F a b = if π a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private lemma p9u7a_exists_diag_rootT (h : UnitaryFieldData 2 1 F) {ω : F}
    (hω : IsPrimitiveRoot ω 3) {a b : Fin m} (hab : a ≠ b) :
    ∃ D : ↥(unitarySU 2 1 F m),
      ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (TypeA.rootT ω a b) := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  refine exists_diagSU (n := 1) (d := m) h (fun i => ?_) (TypeA.prod_rootT hω0 hab)
  rw [show 2 ^ 1 + 1 = 3 by norm_num]
  exact TypeA.rootT_pow (p := 3) hω3 a b i

private lemma p9u7a_comm_of_involution (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    (N : GL (Fin m) F)
    (hN : ∀ s ∈ unitarySU 2 1 F m, ∃ c : F,
      ((N * s * N⁻¹ * s⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun _ => c))
    {s : ↥(unitarySU 2 1 F m)} (hs : s ^ 2 = 1) :
    N * (s : GL (Fin m) F) * N⁻¹ = (s : GL (Fin m) F) := by
  haveI : CharP F 2 := h.charP
  obtain ⟨c, hc⟩ := hN (s : GL (Fin m) F) s.2
  set S : Matrix (Fin m) (Fin m) F := ((s : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hS
  set V : GL (Fin m) F := N * (s : GL (Fin m) F) * N⁻¹ with hV
  have hsgl : (s : GL (Fin m) F) * (s : GL (Fin m) F) = 1 := by
    rw [← pow_two, ← Subgroup.coe_pow, hs, Subgroup.coe_one]
  have hsS : S * S = 1 := by
    rw [hS, ← Units.val_mul, hsgl, Units.val_one]
  have hVmat : (V : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c) * S := by
    have hVe : V = (V * (s : GL (Fin m) F)⁻¹) * (s : GL (Fin m) F) := by group
    rw [hVe, Units.val_mul, hc, hS]
  have hVV : V * V = 1 := by
    rw [hV]
    rw [show N * (s : GL (Fin m) F) * N⁻¹ * (N * (s : GL (Fin m) F) * N⁻¹)
        = N * ((s : GL (Fin m) F) * (s : GL (Fin m) F)) * N⁻¹ from by group, hsgl,
      mul_one, mul_inv_cancel]
  have hVVsq : (V : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F) =
      diagonal (fun _ => c ^ 2) := by
    rw [hVmat]
    have hcommD : S * diagonal (fun _ => c) = diagonal (fun _ => c) * S := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
    calc (diagonal (fun _ => c) * S) * (diagonal (fun _ => c) * S)
        = diagonal (fun _ => c) * (S * diagonal (fun _ => c)) * S := by noncomm_ring
      _ = diagonal (fun _ => c) * (diagonal (fun _ => c) * S) * S := by rw [hcommD]
      _ = (diagonal (fun _ => c) * diagonal (fun _ => c)) * (S * S) := by noncomm_ring
      _ = diagonal (fun _ => c ^ 2) := by
          rw [hsS, mul_one, Matrix.diagonal_mul_diagonal, pow_two]
  have hdiag : diagonal (fun _ => c ^ 2) = (1 : Matrix (Fin m) (Fin m) F) := by
    rw [← hVVsq, ← Units.val_mul, hVV, Units.val_one]
  have hc2 : c ^ 2 = 1 := by
    have h := congrFun (congrFun hdiag ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h
  have hc1 : c = 1 := by
    refine CharTwo.sq_inj.mp ?_
    rw [hc2, one_pow]
  have hVmat1 : (V : Matrix (Fin m) (Fin m) F) = S := by
    rw [hVmat, hc1]
    simp
  exact Units.ext (hVmat1.trans hS)

private lemma p9u7a_diag_mul_perm {ω : F} (hω : IsPrimitiveRoot ω 3)
    {a b k : Fin m} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    diagonal (TypeA.rootT ω a k) * (Equiv.swap a b).permMatrix F *
        diagonal (fun i => (TypeA.rootT ω a k i)⁻¹) *
        (Equiv.swap a b).permMatrix F = diagonal (TypeA.rootT ω a b) := by
  classical
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  set t : Fin m → F := TypeA.rootT ω a k with ht
  have hσP : (Equiv.swap a b).permMatrix F = (Equiv.swap a b)⁻¹.permMatrix F := by
    rw [Equiv.swap_inv]
  have hstep : (Equiv.swap a b).permMatrix F * diagonal (fun i => (t i)⁻¹) *
      (Equiv.swap a b).permMatrix F =
        diagonal ((fun i => (t i)⁻¹) ∘ (Equiv.swap a b)) := by
    nth_rewrite 2 [hσP]
    exact CFSG.StandardType.TypeANbrDvd.permMatrix_mul_diagonal_mul_inv (Equiv.swap a b)
      (fun i => (t i)⁻¹)
  have hfun : (fun i => t i * (t (Equiv.swap a b i))⁻¹) = TypeA.rootT ω a b := by
    funext i
    by_cases hia : i = a
    · rw [hia, Equiv.swap_apply_left, ht, TypeA.rootT_left,
        TypeA.rootT_other ω (Ne.symm hab) (Ne.symm hkb), TypeA.rootT_left]
      simp
    · by_cases hib : i = b
      · rw [hib, Equiv.swap_apply_right, ht,
          TypeA.rootT_other ω (Ne.symm hab) (Ne.symm hkb), TypeA.rootT_left,
          TypeA.rootT_right ω hab]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib, ht, TypeA.rootT_other ω hia hib]
        have hne : TypeA.rootT ω a k i ≠ 0 := by
          intro h0
          have h3 := TypeA.rootT_pow (p := 3) hω3 a k i
          rw [h0, zero_pow (by norm_num)] at h3
          exact zero_ne_one h3
        rw [mul_inv_cancel₀ hne]
  calc diagonal t * (Equiv.swap a b).permMatrix F * diagonal (fun i => (t i)⁻¹) *
        (Equiv.swap a b).permMatrix F
      = diagonal t * ((Equiv.swap a b).permMatrix F * diagonal (fun i => (t i)⁻¹) *
          (Equiv.swap a b).permMatrix F) := by noncomm_ring
    _ = diagonal t * diagonal ((fun i => (t i)⁻¹) ∘ (Equiv.swap a b)) := by rw [hstep]
    _ = diagonal (fun i => t i * (((fun i => (t i)⁻¹) ∘ (Equiv.swap a b)) i)) := by
          rw [Matrix.diagonal_mul_diagonal]
    _ = diagonal (TypeA.rootT ω a b) := by
          simpa only [Function.comp_apply] using congrArg diagonal hfun

private lemma p9u7a_perm_conj_diag (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {ω : F} (hω : IsPrimitiveRoot ω 3) {a b : Fin m} (hab : a ≠ b) :
    ∃ (P X Y : ↥(unitarySU 2 1 F m)),
      P ^ 2 = 1 ∧ (X * P * X⁻¹) ^ 2 = 1 ∧
      ((X * P * X⁻¹ * P : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) = (Y : GL (Fin m) F) ∧
      ((Y : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (TypeA.rootT ω a b) := by
  obtain ⟨k, hka, hkb⟩ := exists_not_mem_two hm a b
  obtain ⟨X, hX⟩ := p9u7a_exists_diag_rootT h hω (Ne.symm hka)
  set P : ↥(unitarySU 2 1 F m) := permSU h (Equiv.swap a b) with hP
  have hP2 : P ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two, hP, coe_permSU, ← map_mul,
      Equiv.swap_mul_self, map_one]
  have hPmat : ((P : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (Equiv.swap a b).permMatrix F := by
    rw [hP, coe_permSU, coe_permGL_matrix, Equiv.swap_inv]
  let Q : ↥(unitarySU 2 1 F m) := X * P * X⁻¹
  have hQ2 : Q ^ 2 = 1 := by
    dsimp only [Q]
    rw [pow_two]
    calc (X * P * X⁻¹) * (X * P * X⁻¹) = X * (P * P) * X⁻¹ := by group
      _ = X * 1 * X⁻¹ := by rw [← pow_two, hP2]
      _ = 1 := by group
  obtain ⟨Y, hY⟩ := p9u7a_exists_diag_rootT h hω hab
  have hQPmat : ((Q * P : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) = (Y : GL (Fin m) F) := by
    apply Units.ext
    rw [hY, Subgroup.coe_mul, Units.val_mul]
    have hQmat : ((Q : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (TypeA.rootT ω a k) * (Equiv.swap a b).permMatrix F *
          diagonal (fun i => (TypeA.rootT ω a k i)⁻¹) := by
      dsimp only [Q]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hX, hPmat,
        coe_inv_diag hX]
    rw [hQmat, hPmat, p9u7a_diag_mul_perm hω hab hka hkb]
  exact ⟨P, X, Y, hP2, hQ2, hQPmat, hY⟩

private lemma p9u7a_comm_diag_rootT (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    (N : GL (Fin m) F)
    (hN : ∀ s ∈ unitarySU 2 1 F m, ∃ c : F,
      ((N * s * N⁻¹ * s⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun _ => c))
    {ω : F} (hω : IsPrimitiveRoot ω 3) {a b : Fin m} (hab : a ≠ b) :
    (N : Matrix (Fin m) (Fin m) F) * diagonal (TypeA.rootT ω a b) =
      diagonal (TypeA.rootT ω a b) * (N : Matrix (Fin m) (Fin m) F) := by
  obtain ⟨P, X, Y, hP2, hQ2, hQPY, hY⟩ := p9u7a_perm_conj_diag h hm hω hab
  let Q : ↥(unitarySU 2 1 F m) := X * P * X⁻¹
  have hPcomm := p9u7a_comm_of_involution h hm N hN hP2
  have hQcomm := p9u7a_comm_of_involution h hm N hN hQ2
  have hQPcomm : N * ((X * P * X⁻¹ * P : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) * N⁻¹ =
      ((X * P * X⁻¹ * P : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) := by
    have hQPeq : ((X * P * X⁻¹ * P : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
        (Q : GL (Fin m) F) * (P : GL (Fin m) F) := by
      rw [show X * P * X⁻¹ * P = Q * P from rfl, Subgroup.coe_mul]
    rw [hQPeq]
    calc N * ((Q : GL (Fin m) F) * (P : GL (Fin m) F)) * N⁻¹
        = (N * (Q : GL (Fin m) F) * N⁻¹) * (N * (P : GL (Fin m) F) * N⁻¹) := by group
      _ = (Q : GL (Fin m) F) * (P : GL (Fin m) F) := by rw [hQcomm, hPcomm]
  rw [hQPY] at hQPcomm
  have hNY : N * (Y : GL (Fin m) F) = (Y : GL (Fin m) F) * N := by
    calc N * (Y : GL (Fin m) F) = (N * (Y : GL (Fin m) F) * N⁻¹) * N := by group
      _ = (Y : GL (Fin m) F) * N := by rw [hQPcomm]
  have hmat := congrArg (fun u : GL (Fin m) F => (u : Matrix (Fin m) (Fin m) F)) hNY
  simpa only [Units.val_mul, hY] using hmat

private lemma p9u7a_offdiag_zero {N : GL (Fin m) F} {ω : F} (hωne : ω ≠ ω⁻¹)
    (hroot : ∀ a b : Fin m, a ≠ b →
      (N : Matrix (Fin m) (Fin m) F) * diagonal (TypeA.rootT ω a b) =
        diagonal (TypeA.rootT ω a b) * (N : Matrix (Fin m) (Fin m) F))
    {i j : Fin m} (hij : i ≠ j) : (N : Matrix (Fin m) (Fin m) F) i j = 0 := by
  have h := congrFun (congrFun (hroot i j hij) i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, TypeA.rootT_left,
    TypeA.rootT_right ω hij] at h
  have hfactor : (N : Matrix (Fin m) (Fin m) F) i j * (ω⁻¹ - ω) = 0 := by
    rw [mul_sub, h, mul_comm ω ((N : Matrix (Fin m) (Fin m) F) i j), sub_self]
  exact (mul_eq_zero.mp hfactor).resolve_right (sub_ne_zero.mpr (Ne.symm hωne))

private lemma p9u7a_diag_eq_of_swap (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    (N : GL (Fin m) F)
    (hN : ∀ s ∈ unitarySU 2 1 F m, ∃ c : F,
      ((N * s * N⁻¹ * s⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun _ => c))
    (hNdiag : (N : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (N : Matrix (Fin m) (Fin m) F) i i))
    {a b : Fin m} (hab : a ≠ b) :
    (N : Matrix (Fin m) (Fin m) F) a a = (N : Matrix (Fin m) (Fin m) F) b b := by
  haveI : CharP F 2 := h.charP
  set P : ↥(unitarySU 2 1 F m) := permSU h (Equiv.swap a b) with hP
  have hP2 : P ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two, hP, coe_permSU, ← map_mul,
      Equiv.swap_mul_self, map_one]
  have hPc := p9u7a_comm_of_involution h hm N hN hP2
  have hNP : N * (P : GL (Fin m) F) = (P : GL (Fin m) F) * N := by
    calc N * (P : GL (Fin m) F) = (N * (P : GL (Fin m) F) * N⁻¹) * N := by group
      _ = (P : GL (Fin m) F) * N := by rw [hPc]
  have hmat := congrArg (fun u : GL (Fin m) F => (u : Matrix (Fin m) (Fin m) F)) hNP
  simp only [Units.val_mul] at hmat
  have hPmat : ((P : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (Equiv.swap a b).permMatrix F := by
    rw [hP, coe_permSU, coe_permGL_matrix, Equiv.swap_inv]
  have h := congrFun (congrFun hmat a) b
  rw [hNdiag, Matrix.diagonal_mul, Matrix.mul_diagonal, hPmat, p9u7a_permMatrix_apply,
    Equiv.swap_apply_left, if_pos rfl] at h
  simpa using h

private lemma p9u7a_mono_hyp (h : UnitaryFieldData 2 1 F) (g : GL (Fin m) F)
    (hg : ∀ t ∈ UTorus.detOne F m,
      ((g : Matrix (Fin m) (Fin m) F) * diagonal (fun i => (t i : F)) *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).IsDiag)
    {ω : F} (hω : IsPrimitiveRoot ω 3) {i j : Fin m} (hij : i ≠ j) :
    ∃ D : Fin m → F,
      (g : Matrix (Fin m) (Fin m) F) * diagonal (TypeA.rootT ω i j) =
        diagonal D * (g : Matrix (Fin m) (Fin m) F) := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  let u : Fˣ := Units.mk0 ω hω0
  have hu : (u : F) = ω := Units.val_mk0 hω0
  let t : Fin m → Fˣ := fun k => if k = i then u else if k = j then u⁻¹ else 1
  have htfun : (fun k => (t k : F)) = TypeA.rootT ω i j := by
    funext k
    simp only [t, TypeA.rootT]
    split_ifs <;> simp [hu]
  have htprod : ∏ k, t k = 1 := by
    apply Units.ext
    rw [Units.coe_prod]
    rw [Finset.prod_congr rfl (fun k _ => congrFun htfun k)]
    exact TypeA.prod_rootT hω0 hij
  have ht : t ∈ UTorus.detOne F m := by
    rw [UTorus.mem_detOne]
    exact htprod
  set M : Matrix (Fin m) (Fin m) F :=
    (g : Matrix (Fin m) (Fin m) F) * diagonal (fun i => (t i : F)) *
      ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hM
  have hMdiag : M = diagonal (fun k => M k k) := by
    have h := (Matrix.isDiag_iff_diagonal_diag M).mp (hg t ht)
    exact h.symm
  have hgprod : ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      (g : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨fun k => M k k, ?_⟩
  calc (g : Matrix (Fin m) (Fin m) F) * diagonal (TypeA.rootT ω i j)
      = (g : Matrix (Fin m) (Fin m) F) * diagonal (fun k => (t k : F)) := by rw [htfun]
    _ = M * (g : Matrix (Fin m) (Fin m) F) := by
          rw [hM, Matrix.mul_assoc, hgprod, Matrix.mul_one]
    _ = diagonal (fun k => M k k) * (g : Matrix (Fin m) (Fin m) F) := by
          conv_lhs => rw [hMdiag]

theorem P9_U7a_eq_scalar_of_comm (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) (N : GL (Fin m) F)
    (hN : ∀ s ∈ unitarySU 2 1 F m, ∃ c : F,
      ((N * s * N⁻¹ * s⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) :
    ∃ c : F, (N : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c) := by
  haveI : CharP F 2 := h.charP
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot (ℓ := 2) (f := 1)
    (p := 3) (K := F) h (by norm_num) (by norm_num)
  have hωne : ω ≠ ω⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hω (by norm_num) (by norm_num)
  have hroot : ∀ a b : Fin m, a ≠ b →
      (N : Matrix (Fin m) (Fin m) F) * diagonal (TypeA.rootT ω a b) =
        diagonal (TypeA.rootT ω a b) * (N : Matrix (Fin m) (Fin m) F) :=
    fun a b hab => p9u7a_comm_diag_rootT h hm N hN hω hab
  have hNdiag : (N : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (N : Matrix (Fin m) (Fin m) F) i i) := by
    ext i j
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact p9u7a_offdiag_zero hωne hroot hij
  let i₀ : Fin m := ⟨0, by omega⟩
  refine ⟨(N : Matrix (Fin m) (Fin m) F) i₀ i₀, ?_⟩
  calc (N : Matrix (Fin m) (Fin m) F) =
        diagonal (fun i => (N : Matrix (Fin m) (Fin m) F) i i) := hNdiag
    _ = diagonal (fun _ => (N : Matrix (Fin m) (Fin m) F) i₀ i₀) := by
        have hd : (fun i => (N : Matrix (Fin m) (Fin m) F) i i) =
            (fun _ => (N : Matrix (Fin m) (Fin m) F) i₀ i₀) := by
          funext i
          by_cases hi : i = i₀
          · rw [hi]
          · exact p9u7a_diag_eq_of_swap h hm N hN hNdiag hi
        rw [hd]

theorem P9_U7a_exists_perm_of_conj_diag (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    (g : GL (Fin m) F)
    (hg : ∀ t ∈ UTorus.detOne F m, ((g : Matrix (Fin m) (Fin m) F) *
      diagonal (fun i => (t i : F)) * ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).IsDiag) :
    ∃ σ : Equiv.Perm (Fin m), ∀ u : Fin m → F,
      (g : Matrix (Fin m) (Fin m) F) * diagonal u *
          ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun i => u (σ.symm i)) := by
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot (ℓ := 2) (f := 1)
    (p := 3) (K := F) h (by norm_num) (by norm_num)
  have hωne : ω ≠ ω⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hω (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := TypeA.exists_perm_mul_diagonal (d := m) (K := F) hωne g
    (fun i j hij => p9u7a_mono_hyp h g hg hω hij)
  refine ⟨π.symm, fun u => ?_⟩
  have hgprod : (g : Matrix (Fin m) (Fin m) F) *
      ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (g : Matrix (Fin m) (Fin m) F) * diagonal u *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
      = (diagonal (u ∘ π) * (g : Matrix (Fin m) (Fin m) F)) *
          ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by rw [hπ u]
    _ = diagonal (u ∘ π) := by rw [Matrix.mul_assoc, hgprod, Matrix.mul_one]
    _ = diagonal (fun i => u ((π.symm).symm i)) := by simp

end CFSG.StandardType.FrameRoute

end
