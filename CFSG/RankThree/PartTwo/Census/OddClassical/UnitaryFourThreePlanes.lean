module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionPaired
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.RankThree.PartTwo.Census.UnitaryFourThree

open Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

local notation "M⟦" x "⟧" => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

theorem det_eq_pow_mul_pow_of_isCompl {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {W₁ W₂ : Submodule F V}
    (hc : IsCompl W₁ W₂) {f : Module.End F V} {a b : F} (h₁ : ∀ v ∈ W₁, f v = a • v)
    (h₂ : ∀ v ∈ W₂, f v = b • v) :
    LinearMap.det f = a ^ finrank F W₁ * b ^ finrank F W₂ := by
  set e := Submodule.prodEquivOfIsCompl W₁ W₂ hc
  set P : Module.End F (W₁ × W₂) := LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id)
  have key : f ∘ₗ (e : W₁ × W₂ →ₗ[F] V) = (e : W₁ × W₂ →ₗ[F] V) ∘ₗ P := by
    apply LinearMap.prod_ext <;> apply LinearMap.ext <;> intro x
    · simp [e, P, h₁ _ x.2]
    · simp [e, P, h₂ _ x.2]
  have hf : f = (e : W₁ × W₂ →ₗ[F] V) ∘ₗ P ∘ₗ (e.symm : V →ₗ[F] W₁ × W₂) := by
    rw [← LinearMap.comp_assoc, ← key, LinearMap.comp_assoc]
    refine LinearMap.ext fun v => ?_
    simp
  rw [hf, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

theorem exists_eq_smul_one_of_commute {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hV : finrank F V = 2)
    [CharP F 3] {u x : Module.End F V} (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    (hxu : x * u = u * x) {n : ℕ} (hxn : x ^ (2 ^ n) = 1) : ∃ a : F, x = a • 1 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h3E : (3 : Module.End F V) = 0 := by
    rw [← map_ofNat (algebraMap F (Module.End F V)) 3, h3, map_zero]
  set N := u - 1 with hN
  have hN0 : N ≠ 0 := sub_ne_zero.mpr hu1
  have hN3 : N ^ 3 = 0 := by
    have : N ^ 3 = u ^ 3 - 1 - 3 * (u ^ 2 - u) := by rw [hN]; noncomm_ring
    rw [this, hu3, h3E, zero_mul, sub_zero, sub_self]
  have hNNN : ∀ z, N (N (N z)) = 0 := fun z => by
    have := congrArg (fun T : Module.End F V => T z) hN3
    simpa [pow_succ, Module.End.mul_apply] using this
  have hN2 : ∀ y, N (N y) = 0 := by
    intro y
    by_contra hy
    have hli : LinearIndependent F ![y, N y, N (N y)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
      have e2 := congrArg (fun z => N (N z)) hg
      simp only [map_add, map_smul, hNNN, smul_zero, add_zero, map_zero] at e2
      have g0 : g 0 = 0 := (smul_eq_zero.mp e2).resolve_right hy
      rw [g0, zero_smul, zero_add] at hg
      have e1 := congrArg N hg
      simp only [map_add, map_smul, hNNN, smul_zero, add_zero, map_zero] at e1
      have g1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hy
      rw [g1, zero_smul, zero_add] at hg
      have g2 : g 2 = 0 := (smul_eq_zero.mp hg).resolve_right hy
      intro i
      fin_cases i
      · exact g0
      · exact g1
      · exact g2
    have := hli.fintype_card_le_finrank
    simp [hV] at this
  obtain ⟨y, hy⟩ : ∃ y, N y ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (LinearMap.ext h)
  set l := N y with hl
  have hNl : N l = 0 := hN2 y
  have hli : LinearIndependent F ![l, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg N hst
    simp only [map_add, map_smul, hNl, smul_zero, zero_add, map_zero] at e1
    have ht : t = 0 := (smul_eq_zero.mp e1).resolve_right hy
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hy, ht⟩
  let bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hbs0 : bs 0 = l := by simp [bs]
  have hbs1 : bs 1 = y := by simp [bs]
  have hxN : x * N = N * x := by rw [hN, mul_sub, sub_mul, hxu, mul_one, one_mul]
  set α := bs.repr (x y) 0
  set β := bs.repr (x y) 1
  have hxy : x y = α • l + β • y := by
    have := bs.sum_repr (x y)
    rw [Fin.sum_univ_two, hbs0, hbs1] at this
    exact this.symm
  have hxl : x l = β • l := by
    calc x l = (x * N) y := rfl
      _ = N (x y) := by rw [hxN, Module.End.mul_apply]
      _ = β • l := by rw [hxy, map_add, map_smul, map_smul, hNl, smul_zero, zero_add]
  set M := x - β • (1 : Module.End F V) with hMdef
  have hM : M * M = 0 := by
    apply bs.ext
    intro i
    fin_cases i
    · simp [hbs0, hMdef, hxl]
    · simp [hbs1, hMdef, hxy, hxl]
  have hx3 : x ^ 3 = β ^ 3 • (1 : Module.End F V) := by
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
    have : CharP (Module.End F V) 3 :=
      charP_of_injective_algebraMap (algebraMap F (Module.End F V)).injective 3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hx : x = M + algebraMap F (Module.End F V) β := by
      rw [hMdef, Algebra.algebraMap_eq_smul_one, sub_add_cancel]
    rw [hx, add_pow_char_of_commute 3 (Algebra.commute_algebraMap_right β M)]
    have hM3 : M ^ 3 = 0 := by rw [pow_succ, pow_two, hM, zero_mul]
    rw [hM3, zero_add, ← map_pow, Algebra.algebraMap_eq_smul_one]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 3)
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxn)
      (Nat.Coprime.pow_right n (by norm_num)))
  refine ⟨(β ^ 3) ^ m, ?_⟩
  rw [← hm, hx3, smul_pow, one_pow]

theorem exists_planes (h : UnitaryFieldData 3 1 F) {A : Matrix (Fin 4) (Fin 4) F}
    (hdet : A.det = 1)
    (hiso : ∀ v w, stdHermForm h 4 (A *ᵥ v) (A *ᵥ w) = stdHermForm h 4 v w)
    {c : F} (hc : A * A = c • 1) (hns : ∀ d : F, A ≠ d • 1) :
    ∃ Vp Vm : Submodule F (Fin 4 → F), IsCompl Vp Vm ∧ finrank F Vp = 2 ∧ finrank F Vm = 2 ∧
      (∀ v ∈ Vp, ∀ w ∈ Vm, stdHermForm h 4 v w = 0) ∧
      (∀ X : Matrix (Fin 4) (Fin 4) F, X * A = A * X →
        (∀ v ∈ Vp, X *ᵥ v ∈ Vp) ∧ (∀ v ∈ Vm, X *ᵥ v ∈ Vm)) ∧
      (∀ X : Matrix (Fin 4) (Fin 4) F, X * A = -(A * X) →
        (∀ v ∈ Vp, X *ᵥ v ∈ Vm) ∧ (∀ v ∈ Vm, X *ᵥ v ∈ Vp)) := by
  have := h.finite
  have : CharP F 3 := h.charP
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h (by norm_num)
  set B := stdHermForm h 4
  have hc4 : c ^ 4 = 1 := by
    have := congrArg Matrix.det hc
    rw [Matrix.det_mul, hdet, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at this
    linear_combination -this
  have hN : h.norm c = 1 := by
    rw [UnitaryFieldData.norm, h.bar_apply, pow_one, ← pow_succ', hc4]
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h (by norm_num) hN
  set L : Module.End F (Fin 4 → F) := Matrix.toLin' A with hL
  set Vp : Submodule F (Fin 4 → F) := LinearMap.ker (L - l • 1)
  set Vm : Submodule F (Fin 4 → F) := LinearMap.ker (L + l • 1)
  have memp : ∀ v, v ∈ Vp ↔ A *ᵥ v = l • v := fun v => by
    simp [Vp, hL, sub_eq_zero]
  have memm : ∀ v, v ∈ Vm ↔ A *ᵥ v = -(l • v) := fun v => by
    simp [Vm, hL, add_eq_zero_iff_eq_neg]
  have hAA : ∀ v, A *ᵥ (A *ᵥ v) = (l ^ 2) • v := fun v => by
    rw [Matrix.mulVec_mulVec, hc, hlc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcompl : IsCompl Vp Vm := by
    refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_,
      Submodule.codisjoint_iff_exists_add_eq.mpr fun v => ?_⟩
    · rw [memp] at hv
      rw [memm, hv] at hv'
      have h3 : (2 * l) • v = 0 := by
        calc (2 * l) • v = l • v + l • v := by rw [mul_smul, two_smul]
          _ = l • v + -(l • v) := congrArg (l • v + ·) hv'
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hl0)
    · refine ⟨(2 * l)⁻¹ • (l • v + A *ᵥ v), (2 * l)⁻¹ • (l • v - A *ᵥ v), ?_, ?_, ?_⟩
      · rw [memp, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hAA, smul_comm l]
        congr 1
        rw [smul_add, smul_smul, ← pow_two, add_comm]
      · rw [memm, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hAA, smul_comm l]
        rw [← smul_neg]
        congr 1
        rw [smul_sub, smul_smul, ← pow_two, neg_sub]
      · rw [← smul_add, add_add_sub_cancel, ← two_smul F (l • v), smul_smul, smul_smul,
          mul_assoc, inv_mul_cancel₀ (mul_ne_zero h2 hl0), one_smul]
  have hBp : ∀ v ∈ Vp, ∀ w ∈ Vp, (h.norm l - 1) * B v w = 0 := fun v hv w hw => by
    have := hiso v w
    rw [(memp v).mp hv, (memp w).mp hw, sesq_smul_smul] at this
    linear_combination this
  have hBm : ∀ v ∈ Vm, ∀ w ∈ Vm, (h.norm l - 1) * B v w = 0 := fun v hv w hw => by
    have := hiso v w
    rw [(memm v).mp hv, (memm w).mp hw] at this
    simp only [map_neg, LinearMap.neg_apply, neg_neg] at this
    rw [sesq_smul_smul] at this
    linear_combination this
  have hBpm : ∀ v ∈ Vp, ∀ w ∈ Vm, (h.norm l + 1) * B v w = 0 := fun v hv w hw => by
    have := hiso v w
    rw [(memp v).mp hv, (memm w).mp hw, map_neg, sesq_smul_smul] at this
    linear_combination -this
  have hNl : h.norm l = c ^ 2 := by
    rw [UnitaryFieldData.norm, h.bar_apply, pow_one, ← pow_succ', ← hlc, ← pow_mul]
  have hc2 : c ^ 2 = 1 ∨ c ^ 2 = -1 := by
    have : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul, hc4]
    exact mul_self_eq_one_iff.mp (by rw [← pow_two]; exact this)
  have hVm : Vm ≠ ⊥ := by
    intro h0
    have htop : Vp = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [h0, sup_bot_eq] at this
    apply hns l
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_smul, Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply]
    exact (memp v).mp (htop ▸ Submodule.mem_top)
  have hVp : Vp ≠ ⊥ := by
    intro h0
    have htop : Vm = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [h0, bot_sup_eq] at this
    apply hns (-l)
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_smul, Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply,
      neg_smul]
    exact (memm v).mp (htop ▸ Submodule.mem_top)
  have hsum : finrank F Vp + finrank F Vm = 4 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  have hp1 : 1 ≤ finrank F Vp :=
    Nat.one_le_iff_ne_zero.mpr fun h0 => hVp (Submodule.finrank_eq_zero.mp h0)
  have hm1 : 1 ≤ finrank F Vm :=
    Nat.one_le_iff_ne_zero.mpr fun h0 => hVm (Submodule.finrank_eq_zero.mp h0)
  have hdetL : l ^ finrank F Vp * (-l) ^ finrank F Vm = 1 := by
    rw [← det_eq_pow_mul_pow_of_isCompl hcompl (f := L) (fun v hv => by
        rw [hL, Matrix.toLin'_apply]; exact (memp v).mp hv) (fun v hv => by
        rw [hL, Matrix.toLin'_apply, neg_smul]; exact (memm v).mp hv), hL,
      LinearMap.det_toLin', hdet]
  have hdecomp : ∀ x : Fin 4 → F, ∃ y ∈ Vp, ∃ z ∈ Vm, y + z = x := fun x => by
    obtain ⟨y, z, hy, hz, hyz⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint x
    exact ⟨y, hy, z, hz, hyz⟩
  rcases hc2 with hc2 | hc2
  ·
    have hN1 : h.norm l = 1 := by rw [hNl, hc2]
    have hdm : finrank F Vm = 2 := by
      have hpow : (-1 : F) ^ finrank F Vm = 1 := by
        have h4 : l ^ (finrank F Vp + finrank F Vm) = 1 := by
          rw [hsum, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hlc, hc2]
        calc (-1 : F) ^ finrank F Vm =
              (-1) ^ finrank F Vm * l ^ (finrank F Vp + finrank F Vm) := by rw [h4, mul_one]
          _ = l ^ finrank F Vp * (-l) ^ finrank F Vm := by rw [neg_pow l, pow_add]; ring
          _ = 1 := hdetL
      have hm3 : finrank F Vm ≤ 3 := by omega
      interval_cases hm : finrank F Vm
      · exfalso
        rw [pow_one] at hpow
        exact h2 (by linear_combination -hpow)
      · rfl
      · exfalso
        rw [show (-1 : F) ^ 3 = -1 by ring] at hpow
        exact h2 (by linear_combination -hpow)
    refine ⟨Vp, Vm, hcompl, by omega, hdm, fun v hv w hw => ?_, ?_, ?_⟩
    · have := hBpm v hv w hw
      rw [hN1, one_add_one_eq_two] at this
      exact (mul_eq_zero.mp this).resolve_left h2
    · intro X hX
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [memp] at hv ⊢
        rw [Matrix.mulVec_mulVec, ← hX, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
      · rw [memm] at hv ⊢
        rw [Matrix.mulVec_mulVec, ← hX, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_neg,
          Matrix.mulVec_smul]
    · intro X hX
      have hX' : A * X = -(X * A) := by rw [hX, neg_neg]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [memp] at hv
        rw [memm, Matrix.mulVec_mulVec, hX', Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hv,
          Matrix.mulVec_smul]
      · rw [memm] at hv
        rw [memp, Matrix.mulVec_mulVec, hX', Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hv,
          Matrix.mulVec_neg, Matrix.mulVec_smul, neg_neg]
  ·
    exfalso
    have hNm : h.norm l = -1 := by rw [hNl, hc2]
    have h2' : (-1 - 1 : F) ≠ 0 := by
      rw [show (-1 - 1 : F) = -2 by ring]
      exact neg_ne_zero.mpr h2
    have hisoP : ∀ v ∈ Vp, ∀ w ∈ Vp, B v w = 0 := fun v hv w hw => by
      have := hBp v hv w hw
      rw [hNm] at this
      exact (mul_eq_zero.mp this).resolve_left h2'
    have hisoM : ∀ v ∈ Vm, ∀ w ∈ Vm, B v w = 0 := fun v hv w hw => by
      have := hBm v hv w hw
      rw [hNm] at this
      exact (mul_eq_zero.mp this).resolve_left h2'
    have hle1 : finrank F Vm ≤ finrank F Vp := by
      refine finrank_le_of_pairing (h := h) (B := B) fun w hw hwv => ?_
      refine stdHermForm_separatingLeft h 4 w fun x => ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := hdecomp x
      rw [map_add, hwv y hy, hisoM w hw z hz, add_zero]
    have hle2 : finrank F Vp ≤ finrank F Vm := by
      refine finrank_le_of_pairing (h := h) (B := B) fun w hw hwv => ?_
      refine stdHermForm_separatingLeft h 4 w fun x => ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := hdecomp x
      rw [map_add, hisoP w hw y hy, hwv z hz, zero_add]
    have hp2 : finrank F Vp = 2 := by omega
    have hm2 : finrank F Vm = 2 := by omega
    rw [hp2, hm2, neg_sq, ← pow_add, show (2 + 2 : ℕ) = 2 * 2 from rfl, pow_mul, hlc,
      hc2] at hdetL
    exact h2 (by linear_combination -hdetL)

theorem mem_S43 (h : UnitaryFieldData 3 1 F) {g : GL (Fin 4) F} :
    g ∈ StatedSU 4 3 F ↔ (g : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      ∀ v w, stdHermForm h 4 ((g : Matrix _ _ F) *ᵥ v) ((g : Matrix _ _ F) *ᵥ w) =
        stdHermForm h 4 v w :=
  mem_unitarySU_iff_isometry h

theorem sq_eq_one_of_mul_eq_smul {X Y : Matrix (Fin 4) (Fin 4) F} {c d : F} (hY : Y * Y = c • 1)
    (hc0 : c ≠ 0) (hX0 : X ≠ 0) (hXY : X * Y = d • (Y * X)) : d ^ 2 = 1 := by
  have h1 : X * (Y * Y) = d ^ 2 • (Y * Y * X) := by
    calc X * (Y * Y) = X * Y * Y := (Matrix.mul_assoc _ _ _).symm
      _ = d • (Y * X * Y) := by rw [hXY, Matrix.smul_mul]
      _ = d • (Y * (X * Y)) := by rw [Matrix.mul_assoc]
      _ = d • (Y * (d • (Y * X))) := by rw [hXY]
      _ = d ^ 2 • (Y * Y * X) := by rw [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, sq]
  rw [hY, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h1
  have h2 : ((d ^ 2 - 1) * c) • X = 0 := by rw [sub_mul, sub_smul, ← h1, one_mul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have := (mul_eq_zero.mp h3).resolve_right hc0
    linear_combination this
  · exact absurd h3 hX0

theorem pow_mul_eq_smul {X Y : Matrix (Fin 4) (Fin 4) F} {d : F} (hXY : X * Y = d • (Y * X))
    (j : ℕ) : X ^ j * Y = d ^ j • (Y * X ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc X ^ (j + 1) * Y = X ^ j * (X * Y) := by rw [pow_succ, Matrix.mul_assoc]
      _ = d • (X ^ j * Y * X) := by rw [hXY, Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = d ^ (j + 1) • (Y * X ^ (j + 1)) := by
        rw [ih, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, ← pow_succ, pow_succ' d]

theorem mul_pow_eq_smul {X Y : Matrix (Fin 4) (Fin 4) F} {d : F} (hXY : X * Y = d • (Y * X))
    (j : ℕ) : X * Y ^ j = d ^ j • (Y ^ j * X) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc X * Y ^ (j + 1) = X * Y ^ j * Y := by rw [pow_succ, Matrix.mul_assoc]
      _ = d ^ j • (Y ^ j * (X * Y)) := by rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
      _ = d ^ (j + 1) • (Y ^ (j + 1) * X) := by
        rw [hXY, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, ← pow_succ Y j, ← pow_succ d j]

theorem commute_of_pow_three_eq_one {X Y : Matrix (Fin 4) (Fin 4) F} {d : F} (hd4 : d ^ 4 = 1)
    (hY3 : Y ^ 3 = 1) (hX0 : X ≠ 0) (hXY : X * Y = d • (Y * X)) : X * Y = Y * X := by
  have h3 := mul_pow_eq_smul hXY 3
  rw [hY3, Matrix.mul_one, Matrix.one_mul] at h3
  have hd3 : d ^ 3 = 1 := by
    have h2 : (d ^ 3 - 1) • X = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hX0)
  have hd1 : d = 1 := by
    have : d ^ 4 = d ^ 3 * d := pow_succ d 3
    rw [hd4, hd3, one_mul] at this
    exact this.symm
  rw [hXY, hd1, one_smul]

@[expose] noncomputable def restrictHom (C : Subgroup (GL (Fin 4) F)) (W : Submodule F (Fin 4 → F))
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) :
    C →* LinearMap.GeneralLinearGroup F W where
  toFun g := glRestrict W (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) F))
    (fun v hv => by
      rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
      exact hW g g.2 v hv)
    (fun v hv => by
      rw [← map_inv, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
      exact hW _ (inv_mem g.2) v hv)
  map_one' := Units.ext (LinearMap.ext fun v => Subtype.ext (by
    simp [coe_glRestrict_apply]))
  map_mul' g g' := Units.ext (LinearMap.ext fun v => Subtype.ext (by
    simp [coe_glRestrict_apply, Matrix.mulVec_mulVec]))

theorem restrictHom_apply (C : Subgroup (GL (Fin 4) F)) (W : Submodule F (Fin 4 → F))
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) (g : C) (v : W) :
    (((restrictHom C W hW g : LinearMap.GeneralLinearGroup F W) : Module.End F W) v :
      Fin 4 → F) = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (v : Fin 4 → F) := by
  simp [restrictHom, coe_glRestrict_apply]

theorem restrictHom_mem (h : UnitaryFieldData 3 1 F) (C : Subgroup (GL (Fin 4) F))
    (hCS : C ≤ StatedSU 4 3 F) (W : Submodule F (Fin 4 → F))
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) (g : C) :
    restrictHom C W hW g ∈ sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ W W) :=
  fun x y => by
    simp only [LinearMap.domRestrict₁₂_apply]
    have hx := restrictHom_apply C W hW g x
    have hy := restrictHom_apply C W hW g y
    rw [hx, hy]
    exact ((mem_unitarySU_iff_isometry h).mp (hCS g.2)).2 x y

@[expose] noncomputable def unitaryRestrict (h : UnitaryFieldData 3 1 F)
    (C : Subgroup (GL (Fin 4) F))
    (hCS : C ≤ StatedSU 4 3 F) (W : Submodule F (Fin 4 → F))
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) :
    C →* sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ W W) :=
  (restrictHom C W hW).codRestrict _ (restrictHom_mem h C hCS W hW)

theorem unitaryRestrict_apply (h : UnitaryFieldData 3 1 F) (C : Subgroup (GL (Fin 4) F))
    (hCS : C ≤ StatedSU 4 3 F) (W : Submodule F (Fin 4 → F))
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) (g : C) (v : W) :
    ((((unitaryRestrict h C hCS W hW g : sesqUnitaryGroup _) :
      LinearMap.GeneralLinearGroup F W) : Module.End F W) v : Fin 4 → F) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (v : Fin 4 → F) :=
  restrictHom_apply C W hW g v

theorem card_unitary_plane (h : UnitaryFieldData 3 1 F) {W : Submodule F (Fin 4 → F)}
    (hW : finrank F W = 2) (hsep : ((stdHermForm h 4).domRestrict₁₂ W W).SeparatingLeft) :
    Nat.card (sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ W W)) = 96 := by
  have := h.finite
  have hB : ((stdHermForm h 4).domRestrict₁₂ W W).IsSymm :=
    ⟨fun x y => (stdHermForm_isSymm h 4).eq x y⟩
  have h1 := (unitary_full_group_order h hB hsep hW (by norm_num)).1
  have h96 : ((3 ^ 1 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 2, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide
  exact_mod_cast h1.trans h96

theorem eq_of_mulVec_eq {Vp Vm : Submodule F (Fin 4 → F)} (hc : IsCompl Vp Vm)
    {X Y : Matrix (Fin 4) (Fin 4) F} (hp : ∀ v ∈ Vp, X *ᵥ v = Y *ᵥ v)
    (hm : ∀ v ∈ Vm, X *ᵥ v = Y *ᵥ v) : X = Y := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  obtain ⟨y, z, hy, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_add, hp y hy,
    hm z hz]

theorem card_dvd_of_planes (h : UnitaryFieldData 3 1 F) (C : Subgroup (GL (Fin 4) F))
    (hCS : C ≤ StatedSU 4 3 F) {Vp Vm : Submodule F (Fin 4 → F)} (hc : IsCompl Vp Vm)
    (hp2 : finrank F Vp = 2) (hm2 : finrank F Vm = 2)
    (horth : ∀ v ∈ Vp, ∀ w ∈ Vm, stdHermForm h 4 v w = 0)
    (hWp : ∀ g ∈ C, ∀ v ∈ Vp, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ Vp)
    (hWm : ∀ g ∈ C, ∀ v ∈ Vm, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ Vm) :
    Nat.card C ∣ 96 * 96 := by
  have hsp := separatingLeft_domRestrict_of_orth (stdHermForm_separatingLeft h 4) hc horth
  have hsm := separatingLeft_domRestrict_of_orth (stdHermForm_separatingLeft h 4) hc.symm
    (fun v hv w hw => by
      rw [← (stdHermForm_isSymm h 4).eq, horth w hw v hv, map_zero])
  set f := (unitaryRestrict h C hCS Vp hWp).prod (unitaryRestrict h C hCS Vm hWm)
  have hf : Function.Injective f := by
    intro g g' hgg
    have h1 := congrArg Prod.fst hgg
    have h2 := congrArg Prod.snd hgg
    simp only [f, MonoidHom.prod_apply] at h1 h2
    refine Subtype.ext (Units.ext (eq_of_mulVec_eq hc (fun v hv => ?_) (fun v hv => ?_)))
    · have := congrArg (fun u : sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ Vp Vp) =>
        ((((u : LinearMap.GeneralLinearGroup F Vp) : Module.End F Vp) ⟨v, hv⟩ : Vp) :
          Fin 4 → F)) h1
      simpa only [unitaryRestrict_apply] using this
    · have := congrArg (fun u : sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ Vm Vm) =>
        ((((u : LinearMap.GeneralLinearGroup F Vm) : Module.End F Vm) ⟨v, hv⟩ : Vm) :
          Fin 4 → F)) h2
      simpa only [unitaryRestrict_apply] using this
  have hcard : Nat.card C = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [hcard, show (96 * 96 : ℕ) = Nat.card
      (sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ Vp Vp) ×
        sesqUnitaryGroup ((stdHermForm h 4).domRestrict₁₂ Vm Vm)) by
      rw [Nat.card_prod, card_unitary_plane h hp2 hsp, card_unitary_plane h hm2 hsm]]
  exact Subgroup.card_subgroup_dvd_card f.range

theorem exists_smul_of_commute {C : Subgroup (GL (Fin 4) F)} [CharP F 3]
    {W : Submodule F (Fin 4 → F)} (hW2 : finrank F W = 2)
    (hW : ∀ g ∈ C, ∀ v ∈ W, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W) {x u : GL (Fin 4) F}
    (hx : x ∈ C) (hu : u ∈ C) (hu3 : u ^ 3 = 1)
    (hu1 : ∃ v ∈ W, (u : Matrix (Fin 4) (Fin 4) F) *ᵥ v ≠ v) (hxu : x * u = u * x) {n : ℕ}
    (hxn : x ^ (2 ^ n) = 1) :
    ∃ a : F, ∀ v ∈ W, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v = a • v := by
  set r := restrictHom C W hW
  set X' : Module.End F W := (↑(r ⟨x, hx⟩) : Module.End F W)
  set U' : Module.End F W := (↑(r ⟨u, hu⟩) : Module.End F W)
  have happ : ∀ (g : C) (v : W), (((r g : LinearMap.GeneralLinearGroup F W) :
      Module.End F W) v : Fin 4 → F) = ((g : GL (Fin 4) F) : Matrix _ _ F) *ᵥ (v : Fin 4 → F) :=
    restrictHom_apply C W hW
  have hU1 : U' ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hne⟩ := hu1
    apply hne
    have := happ ⟨u, hu⟩ ⟨v, hv⟩
    rw [show ((r ⟨u, hu⟩ : LinearMap.GeneralLinearGroup F W) : Module.End F W) = U' from rfl,
      h1] at this
    exact this.symm
  have hU3 : U' ^ 3 = 1 := by
    have : (⟨u, hu⟩ : C) ^ 3 = 1 := Subtype.ext hu3
    rw [show U' ^ 3 = ((r (⟨u, hu⟩ ^ 3) : LinearMap.GeneralLinearGroup F W) : Module.End F W) by
      rw [map_pow, Units.val_pow_eq_pow_val], this, map_one, Units.val_one]
  have hXU : X' * U' = U' * X' := by
    have : (⟨x, hx⟩ : C) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨x, hx⟩ := Subtype.ext hxu
    have h2 := congrArg (fun g => ((r g : LinearMap.GeneralLinearGroup F W) : Module.End F W)) this
    simpa only [map_mul, Units.val_mul] using h2
  have hXn : X' ^ (2 ^ n) = 1 := by
    have : (⟨x, hx⟩ : C) ^ (2 ^ n) = 1 := Subtype.ext hxn
    rw [show X' ^ (2 ^ n) = ((r (⟨x, hx⟩ ^ (2 ^ n)) : LinearMap.GeneralLinearGroup F W) :
      Module.End F W) by rw [map_pow, Units.val_pow_eq_pow_val], this, map_one, Units.val_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_one_of_commute hW2 hU1 hU3 hXU hXn
  refine ⟨a, fun v hv => ?_⟩
  have := happ ⟨x, hx⟩ ⟨v, hv⟩
  rw [show ((r ⟨x, hx⟩ : LinearMap.GeneralLinearGroup F W) : Module.End F W) = X' from rfl,
    ha] at this
  simpa using this.symm

theorem pow_four_eq_one_of_smul (h : UnitaryFieldData 3 1 F) {x : StatedSU 4 3 F}
    {W : Submodule F (Fin 4 → F)} (hW2 : finrank F W = 2)
    (hsep : ((stdHermForm h 4).domRestrict₁₂ W W).SeparatingLeft) {a : F}
    (ha : ∀ v ∈ W, M⟦x⟧ *ᵥ v = a • v) : a ^ 4 = 1 := by
  have hWne : W ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hW2; exact absurd hW2 (by norm_num)
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨w, hw⟩ : ∃ w : W, (stdHermForm h 4) v w ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hv0 (congrArg Subtype.val (hsep ⟨v, hvW⟩ fun y => hno y))
  have h1 := ((mem_S43 h).mp x.2).2 v w
  rw [ha v hvW, ha w w.2, sesq_smul_smul] at h1
  have h2 : h.norm a = 1 := by
    have h3 : (h.norm a - 1) * (stdHermForm h 4) v w = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hw)
  rw [UnitaryFieldData.norm, h.bar_apply, pow_one, ← pow_succ'] at h2
  exact h2

theorem exists_trivial_on (h : UnitaryFieldData 3 1 F) {H' : Subgroup (GL (Fin 4) F)}
    (hH'S : H' ≤ StatedSU 4 3 F) (hH' : Nat.card H' = 9) {W₁ W₂ : Submodule F (Fin 4 → F)}
    (hc : IsCompl W₁ W₂) (h₂ : finrank F W₂ = 2)
    (hsep₂ : ((stdHermForm h 4).domRestrict₁₂ W₂ W₂).SeparatingLeft)
    (hW₂ : ∀ g ∈ H', ∀ v ∈ W₂, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W₂) :
    ∃ g ∈ H', g ^ 3 = 1 ∧ (∀ v ∈ W₂, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v = v) ∧
      ∃ v ∈ W₁, (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ≠ v := by
  have := h.finite
  set r := unitaryRestrict h H' hH'S W₂ hW₂
  have hprod : Nat.card r.ker * Nat.card r.range = 9 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hH']
  have hb96 : Nat.card r.range ∣ 96 := by
    rw [← card_unitary_plane h h₂ hsep₂]
    exact Subgroup.card_subgroup_dvd_card _
  have hb9 : Nat.card r.range ∣ 3 ^ 2 := Dvd.intro_left _ hprod
  have h3 : 3 ∣ Nat.card r.ker := by
    obtain ⟨i, hi, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hb9
    interval_cases i
    · rw [hb, pow_zero, mul_one] at hprod
      rw [hprod]; norm_num
    · rw [hb, pow_one] at hprod
      exact ⟨1, by omega⟩
    · rw [hb] at hb96; norm_num at hb96
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨((y : H') : GL (Fin 4) F), (y : H').2, ?_, fun v hv => ?_, ?_⟩
  · have hy3 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have : (y : H') ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  · have hry : r (y : H') = 1 := y.2
    have := unitaryRestrict_apply h H' hH'S W₂ hW₂ (y : H') ⟨v, hv⟩
    rw [hry] at this
    exact this.symm
  · by_contra hno
    push Not at hno
    have hry : r (y : H') = 1 := y.2
    have h1 : ((y : H') : GL (Fin 4) F) = 1 := by
      refine Units.ext (eq_of_mulVec_eq hc (fun v hv => ?_) (fun v hv => ?_))
      · rw [hno v hv, Units.val_one, Matrix.one_mulVec]
      · have := unitaryRestrict_apply h H' hH'S W₂ hW₂ (y : H') ⟨v, hv⟩
        rw [hry] at this
        rw [Units.val_one, Matrix.one_mulVec]
        exact this.symm
    have h2 : y = 1 := Subtype.ext (Subtype.ext h1)
    rw [h2, orderOf_one] at hy
    exact absurd hy (by norm_num)

end CFSG.RankThree.PartTwo.Census.UnitaryFourThree
