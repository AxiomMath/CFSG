module

public import CFSG.Quasithin.Vol2.Ch9H11Count
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11P

open CFSG.Quasithin (fixV mem_fixV rk rkIdx)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open scoped Matrix

variable {K : Type} [Field K]

abbrev NLm (K : Type) [Field K] : Subgroup (MulAut (VM K)) :=
  Subgroup.normalizer ((Lm K : Subgroup (MulAut (VM K))) : Set (MulAut (VM K)))

theorem isSemi_of_form {x : MulAut (VM K)} {c : K} {P Q : SL₂ K} {σ : K ≃+* K}
    (h : (∀ X, addMap x X = c • ((P : Mat K) * σ.mapMatrix X * (Q : Mat K)ᵀ)) ∨
      (∀ X, addMap x X = c • ((P : Mat K) * σ.mapMatrix Xᵀ * (Q : Mat K)ᵀ))) : IsSemi x σ := by
  intro l X
  rcases h with h | h
  · rw [h, h, mapMatrix_smul, Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  · rw [h, h, Matrix.transpose_smul, mapMatrix_smul, Matrix.mul_smul, Matrix.smul_mul, smul_comm]

theorem mapMatrix_one_apply (M : Mat K) : (1 : K ≃+* K).mapMatrix M = M := by
  ext a b
  rfl

variable [CharP K 2] [Finite K]

theorem isSemi_of_normal (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)} (hx : x ∈ NLm K) :
    ∃ σ, IsSemi x σ := by
  obtain ⟨c, -, P, Q, σ, h⟩ := normal_form h4 hx
  exact ⟨σ, isSemi_of_form h⟩

theorem mem_Lm_or_swap (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)} (hx : x ∈ NLm K)
    (hK : x ∈ kLin K) (hxx : x * x = 1) :
    x ∈ Lm K ∨ ∃ (c : K) (_ : c ≠ 0) (P Q : SL₂ K),
      ∀ X, addMap x X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ) := by
  obtain ⟨c, hc0, P, Q, σ, h⟩ := normal_form h4 hx
  have hσ : σ = 1 := (isSemi_of_form h).unique hK
  subst hσ
  rcases h with h | h
  · left
    have h1 : ∀ X, addMap x X = c • ((P : Mat K) * X * (Q : Mat K)ᵀ) := fun X => by
      rw [h, mapMatrix_one_apply]
    have hxx' : addMap x (addMap x 1) = 1 := by rw [← addMap_mul, hxx, addMap_one]
    rw [h1, h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul] at hxx'
    have hdet := congrArg Matrix.det hxx'
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, P.2, Q.2, Matrix.det_one, Fintype.card_fin] at hdet
    have hc2 : (c * c) ^ 2 = 1 := by simpa using hdet
    have hc1 : c * c = 1 := eq_one_of_sq_eq_one hc2
    have hc : c = 1 := eq_one_of_sq_eq_one (by rw [sq]; exact hc1)
    refine ⟨(P, Q), eq_of_addMap fun X => ?_⟩
    rw [addMap_rho, h1, hc, one_smul]
  · right
    exact ⟨c, hc0, P, Q, fun X => by rw [h, mapMatrix_one_apply]⟩

omit [CharP K 2] in
theorem ringAut_invol_unique {n : ℕ} (hK : Nat.card K = 2 ^ n) {σ τ : K ≃+* K} (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1) : σ = τ := by
  classical
  have hcyc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    hK).2
  have : Finite (RingAut K) := Finite.of_injective (fun ρ : RingAut K => (ρ : K → K))
    fun a b h => RingEquiv.ext (congrFun h)
  have : Fintype (RingAut K) := Fintype.ofFinite _
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
  have hsub : ({1, σ, τ} : Finset (RingAut K)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact hσ2
    · rw [sq]
      exact hτ2
  have h1 : (1 : RingAut K) ∉ ({σ, τ} : Finset (RingAut K)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ, Ne.symm hτ⟩
  have hcard : ({1, σ, τ} : Finset (RingAut K)).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair hne]
  have := Finset.card_le_card hsub
  omega

omit [CharP K 2] [Finite K] in
theorem uu_add (s t : K) : uu (s + t) = uu s * uu t := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_uu, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

omit [CharP K 2] [Finite K] in
theorem uu_zero : uu (0 : K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_uu]

omit [CharP K 2] [Finite K] in
theorem uu_neg (s : K) : uu (-s) = (uu s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← uu_add, neg_add_cancel, uu_zero]

omit [CharP K 2] [Finite K] in
theorem uu_injective : Function.Injective (uu (K := K)) := fun s t h => by
  have := congrArg (fun g : SL₂ K => (g : Mat K) 0 1) h
  simpa [coe_uu] using this

@[expose] def Uu (K : Type) [Field K] : Subgroup (SL₂ K) where
  carrier := Set.range uu
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, uu_add s t⟩
  one_mem' := ⟨0, uu_zero⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, uu_neg s⟩

omit [CharP K 2] [Finite K] in
theorem mem_Uu {g : SL₂ K} : g ∈ Uu K ↔ ∃ s, uu s = g := Iff.rfl

omit [CharP K 2] [Finite K] in
theorem card_Uu : Nat.card (Uu K) = Nat.card K :=
  (Nat.card_congr (Equiv.ofInjective uu uu_injective)).symm

omit [CharP K 2] in
theorem card_SL2 : Nat.card (SL₂ K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card (α := K)]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have hpos : 0 < Fintype.card K - 1 := by have := Fintype.one_lt_card (α := K); omega
  have h1 : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (Fintype.card K ^ 2 - 1) * (Fintype.card K * (Fintype.card K - 1)) =
    Fintype.card K * (Fintype.card K ^ 2 - 1) * (Fintype.card K - 1) by ring,
    Nat.mul_div_cancel _ hpos]

omit [CharP K 2] in
theorem exists_conj_le_Uu {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {H : Subgroup (SL₂ K)}
    (hH : IsPGroup 2 H) : ∃ g : SL₂ K, H.map (MulAut.conj g).toMonoidHom ≤ Uu K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (Uu K) := IsPGroup.of_card (by rw [card_Uu, hK])
  have hidx : ¬ 2 ∣ (Uu K).index := by
    intro h2
    have hc := (Uu K).card_mul_index
    rw [card_Uu, card_SL2] at hc
    have hq0 : 0 < Nat.card K := Nat.card_pos
    have hidx' : (Uu K).index = Nat.card K ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left hq0 hc
    have hq2 : 2 ∣ Nat.card K ^ 2 := by
      rw [hK, ← pow_mul]
      exact dvd_pow_self 2 (by omega)
    have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq0
    rw [hidx'] at h2
    omega
  let SU : Sylow 2 (SL₂ K) := hU2.toSylow hidx
  obtain ⟨S, hHS⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL₂ K) S SU
  refine ⟨g, ?_⟩
  have hS : ((g • S : Sylow 2 (SL₂ K)) : Subgroup (SL₂ K)) = Uu K := by rw [hg]; rfl
  rw [Sylow.coe_subgroup_smul] at hS
  rw [← hS]
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ (hHS hy)

abbrev UU (K : Type) [Field K] : Subgroup (MulAut (VM K)) := ((Uu K).prod (Uu K)).map rho

omit [CharP K 2] [Finite K] in
theorem fix_uu_eqs {s t : K} {X : Mat K} (h : addMap (rho (uu s, uu t)) X = X) :
    s * X 1 1 = 0 ∧ t * X 1 1 = 0 ∧ s * X 1 0 + t * X 0 1 + s * t * X 1 1 = 0 := by
  rw [addMap_rho] at h
  simp only [coe_uu] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e01
  · linear_combination e10
  · linear_combination e00

omit [CharP K 2] [Finite K] in
theorem fix_uu_of_eqs {s t : K} {X : Mat K} (h1 : s * X 1 1 = 0) (h2 : t * X 1 1 = 0)
    (h3 : s * X 1 0 + t * X 0 1 + s * t * X 1 1 = 0) : addMap (rho (uu s, uu t)) X = X := by
  rw [addMap_rho]
  simp only [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · linear_combination h3
  · linear_combination h1
  · linear_combination h2
  · ring

omit [CharP K 2] [Finite K] in
theorem mat_ext {X Y : Mat K} (h00 : X 0 0 = Y 0 0) (h01 : X 0 1 = Y 0 1) (h10 : X 1 0 = Y 1 0)
    (h11 : X 1 1 = Y 1 1) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

abbrev Wset (B : Subgroup (MulAut (VM K))) : Set (K × K) := {p | rho (uu p.1, uu p.2) ∈ B}

omit [Finite K] in
theorem rho_uu_injective : Function.Injective (fun p : K × K => rho (uu p.1, uu p.2)) := by
  intro p p' h
  have h1 := rho_injective h
  exact Prod.ext (uu_injective (congrArg Prod.fst h1)) (uu_injective (congrArg Prod.snd h1))

omit [Finite K] in
theorem card_eq_card_Wset {B : Subgroup (MulAut (VM K))} (hB : B ≤ UU K) :
    Nat.card B = Nat.card (Wset B) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun p => ⟨rho (uu p.1.1, uu p.1.2), p.2⟩) ⟨?_, ?_⟩
  · intro p p' h
    exact Subtype.ext (rho_uu_injective (congrArg Subtype.val h))
  · rintro ⟨b, hb⟩
    obtain ⟨⟨g, h⟩, ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, rfl⟩ := hB hb
    exact ⟨⟨(s, t), hb⟩, rfl⟩

omit [CharP K 2] in
theorem card_le_of_entries {Y : Subgroup (VM K)} (h : ∀ X, MemM Y X → X 1 1 = 0 ∧ X 1 0 = 0 ∧
    X 0 1 = 0) : Nat.card Y ≤ Nat.card K := by
  rw [card_eq_card_memM]
  refine Nat.card_le_card_of_injective (fun X => (X : Mat K) 0 0) fun X Y hXY => ?_
  obtain ⟨hX1, hX2, hX3⟩ := h X X.2
  obtain ⟨hY1, hY2, hY3⟩ := h Y Y.2
  exact Subtype.ext (mat_ext hXY (by rw [hX3, hY3]) (by rw [hX2, hY2]) (by rw [hX1, hY1]))

omit [CharP K 2] in
theorem card_le_of_line {Y : Subgroup (VM K)} {a b : K} (hab : (a, b) ≠ 0)
    (h : ∀ X, MemM Y X → X 1 1 = 0 ∧ a * X 1 0 + b * X 0 1 = 0) :
    Nat.card Y ≤ Nat.card K ^ 2 := by
  rw [card_eq_card_memM, sq, ← Nat.card_prod]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := fun hb => hab (by rw [ha, hb]; rfl)
    refine Nat.card_le_card_of_injective (fun X => ((X : Mat K) 0 0, (X : Mat K) 1 0))
      fun X Y hXY => ?_
    obtain ⟨hX1, hX2⟩ := h X X.2
    obtain ⟨hY1, hY2⟩ := h Y Y.2
    rw [ha, zero_mul, zero_add] at hX2 hY2
    have hX3 := (mul_eq_zero.mp hX2).resolve_left hb
    have hY3 := (mul_eq_zero.mp hY2).resolve_left hb
    exact Subtype.ext (mat_ext (congrArg Prod.fst hXY) (by rw [hX3, hY3])
      (congrArg Prod.snd hXY) (by rw [hX1, hY1]))
  · refine Nat.card_le_card_of_injective (fun X => ((X : Mat K) 0 0, (X : Mat K) 0 1))
      fun X Y hXY => ?_
    obtain ⟨hX1, hX2⟩ := h X X.2
    obtain ⟨hY1, hY2⟩ := h Y Y.2
    have h01 : (X : Mat K) 0 1 = (Y : Mat K) 0 1 := congrArg Prod.snd hXY
    have h10 : (X : Mat K) 1 0 = (Y : Mat K) 1 0 := by
      have e : a * ((X : Mat K) 1 0 - (Y : Mat K) 1 0) = 0 := by
        linear_combination hX2 - hY2 - b * h01
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha)
    exact Subtype.ext (mat_ext (congrArg Prod.fst hXY) h01 h10 (by rw [hX1, hY1]))

theorem card_fix_le_of_uu {B : Subgroup (MulAut (VM K))} (hB : B ≤ UU K) (hB1 : B ≠ ⊥) :
    Nat.card B * Nat.card (fixV B) * Nat.card K ≤ Nat.card K ^ 4 ∧
      Nat.card B ≤ Nat.card K ^ 2 := by
  have hBW := card_eq_card_Wset hB
  have hW2 : Nat.card (Wset B) ≤ Nat.card K ^ 2 := by
    rw [sq, ← Nat.card_prod]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hfixeq : ∀ X, MemM (fixV B) X → ∀ p ∈ Wset B, p.1 * X 1 1 = 0 ∧ p.2 * X 1 1 = 0 ∧
      p.1 * X 1 0 + p.2 * X 0 1 + p.1 * p.2 * X 1 1 = 0 := fun X hX p hp =>
    fix_uu_eqs ((memM_fixV.mp hX) _ hp)
  have hX11 : ∀ X, MemM (fixV B) X → ∀ p ∈ Wset B, p ≠ 0 → X 1 1 = 0 := by
    intro X hX p hp hp0
    obtain ⟨h1, h2, -⟩ := hfixeq X hX p hp
    by_contra hx
    apply hp0
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_right hx) ((mul_eq_zero.mp h2).resolve_right hx)
  obtain ⟨p₀, hp₀, hp₀0⟩ : ∃ p ∈ Wset B, p ≠ 0 := by
    by_contra hne
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨⟨g, h⟩, ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, rfl⟩ := hB hb
    have hst : (s, t) = 0 := by
      by_contra h0
      exact hne ⟨(s, t), hb, h0⟩
    have hs : s = 0 := congrArg Prod.fst hst
    have ht : t = 0 := congrArg Prod.snd hst
    rw [Subgroup.mem_bot, hs, ht, uu_zero]
    exact map_one rho
  by_cases hind : ∃ p ∈ Wset B, ∃ p' ∈ Wset B, p.1 * p'.2 ≠ p'.1 * p.2
  ·
    obtain ⟨p, hp, p', hp', hpp'⟩ := hind
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hpp' (by simp)
    have hC : Nat.card (fixV B) ≤ Nat.card K := by
      apply card_le_of_entries
      intro X hX
      have h11 := hX11 X hX p hp hp0
      obtain ⟨-, -, e1⟩ := hfixeq X hX p hp
      obtain ⟨-, -, e2⟩ := hfixeq X hX p' hp'
      rw [h11, mul_zero, add_zero] at e1 e2
      have hne : p.1 * p'.2 - p'.1 * p.2 ≠ 0 := sub_ne_zero.mpr hpp'
      refine ⟨h11, ?_, ?_⟩
      · have e : (p.1 * p'.2 - p'.1 * p.2) * X 1 0 = 0 := by
          linear_combination p'.2 * e1 - p.2 * e2
        exact (mul_eq_zero.mp e).resolve_left hne
      · have e : (p.1 * p'.2 - p'.1 * p.2) * X 0 1 = 0 := by
          linear_combination p.1 * e2 - p'.1 * e1
        exact (mul_eq_zero.mp e).resolve_left hne
    refine ⟨?_, hBW ▸ hW2⟩
    calc Nat.card B * Nat.card (fixV B) * Nat.card K
        ≤ Nat.card K ^ 2 * Nat.card K * Nat.card K := by
          gcongr
          exact hBW ▸ hW2
      _ = Nat.card K ^ 4 := by ring
  ·
    push Not at hind
    have hWq : Nat.card (Wset B) ≤ Nat.card K := by
      by_cases ha : p₀.1 = 0
      · have hb : p₀.2 ≠ 0 := fun hb => hp₀0 (Prod.ext ha hb)
        refine Nat.card_le_card_of_injective (fun p : Wset B => (p : K × K).2) fun p p' h => ?_
        have h1 : (p : K × K).1 = 0 := by
          have := hind p p.2 p₀ hp₀
          rw [ha, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_right hb
        have h2 : (p' : K × K).1 = 0 := by
          have := hind p' p'.2 p₀ hp₀
          rw [ha, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_right hb
        exact Subtype.ext (Prod.ext (by rw [h1, h2]) h)
      · refine Nat.card_le_card_of_injective (fun p : Wset B => (p : K × K).1) fun p p' h => ?_
        have h1 := hind p p.2 p₀ hp₀
        have h2 := hind p' p'.2 p₀ hp₀
        have h' : (p : K × K).1 = (p' : K × K).1 := h
        rw [h'] at h1
        have e : p₀.1 * ((p : K × K).2 - (p' : K × K).2) = 0 := by linear_combination h2 - h1
        exact Subtype.ext (Prod.ext h' (sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha)))
    have hC : Nat.card (fixV B) ≤ Nat.card K ^ 2 := by
      apply card_le_of_line (a := p₀.1) (b := p₀.2) (by simpa using hp₀0)
      intro X hX
      have h11 := hX11 X hX p₀ hp₀ hp₀0
      obtain ⟨-, -, e⟩ := hfixeq X hX p₀ hp₀
      rw [h11, mul_zero, add_zero] at e
      exact ⟨h11, e⟩
    refine ⟨?_, hBW ▸ hWq.trans (Nat.le_self_pow (by norm_num) _)⟩
    calc Nat.card B * Nat.card (fixV B) * Nat.card K
        ≤ Nat.card K * Nat.card K ^ 2 * Nat.card K := by
          gcongr
          exact hBW ▸ hWq
      _ = Nat.card K ^ 4 := by ring

omit [CharP K 2] [Finite K] in
theorem memM_fixV_zpowers {a : MulAut (VM K)} {X : Mat K} :
    MemM (fixV (Subgroup.zpowers a)) X ↔ addMap a X = X := by
  rw [memM_fixV]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h g hg
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut (VM K))
        (Multiplicative.ofAdd X) := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact congrArg Multiplicative.ofAdd h
    have := hle hg
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    exact congrArg Multiplicative.toAdd this

omit [CharP K 2] [Finite K] in
theorem mul_uu_eqs {P : Mat K} {s t : K}
    (h : P * ((uu t : SL₂ K) : Mat K) = ((uu s : SL₂ K) : Mat K) * P) :
    s * P 1 0 = 0 ∧ P 0 0 * t = s * P 1 1 ∧ P 1 0 * t = 0 := by
  simp only [coe_uu] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -e00
  · linear_combination e01
  · linear_combination e11

theorem card_fix_swap {B : Subgroup (MulAut (VM K))} (hB : B ≤ UU K) (hB1 : B ≠ ⊥)
    {a : MulAut (VM K)} {c : K} (hc : c ≠ 0) {P Q : SL₂ K}
    (ha : ∀ X, addMap a X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ)) (haa : a * a = 1)
    (ha1 : a ≠ 1) (hcomm : ∀ b ∈ B, a * b = b * a)
    (hfix : ∀ X, MemM (fixV B) X → addMap a X = X) :
    Nat.card (fixV (Subgroup.zpowers a)) * Nat.card K = Nat.card K ^ 4 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hPQ : ∀ p ∈ Wset B, (P : Mat K) * ((uu p.2 : SL₂ K) : Mat K) =
      ((uu p.1 : SL₂ K) : Mat K) * P ∧ (Q : Mat K) * ((uu p.1 : SL₂ K) : Mat K) =
      ((uu p.2 : SL₂ K) : Mat K) * Q := by
    intro p hp
    have hc' := hcomm _ hp
    have key : ∀ Z : Mat K, addMap (rho (P * uu p.2, Q * uu p.1)) Z =
        addMap (rho (uu p.1 * P, uu p.2 * Q)) Z := by
      intro Z
      have e := congrArg (fun φ : MulAut (VM K) => addMap φ Zᵀ) hc'
      simp only [addMap_mul, addMap_rho, ha] at e
      rw [Matrix.mul_smul, Matrix.smul_mul] at e
      have e2 := smul_right_injective (Mat K) hc e
      simp only [addMap_rho, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose] at e2 ⊢
      simpa only [Matrix.mul_assoc] using e2
    have hrho := rho_injective (eq_of_addMap key)
    have h1 := congrArg (fun g : SL₂ K × SL₂ K => (g.1 : Mat K)) hrho
    have h2' := congrArg (fun g : SL₂ K × SL₂ K => (g.2 : Mat K)) hrho
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1 h2'
    exact ⟨h1, h2'⟩
  obtain ⟨p₀, hp₀, hp₀0⟩ : ∃ p ∈ Wset B, p ≠ 0 := by
    by_contra hne
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨⟨g, h⟩, ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, rfl⟩ := hB hb
    have hst : (s, t) = 0 := by
      by_contra h0
      exact hne ⟨(s, t), hb, h0⟩
    rw [Subgroup.mem_bot, show s = 0 from congrArg Prod.fst hst,
      show t = 0 from congrArg Prod.snd hst, uu_zero]
    exact map_one rho
  obtain ⟨hP0, hQ0⟩ := hPQ p₀ hp₀
  obtain ⟨eP1, eP2, eP3⟩ := mul_uu_eqs hP0
  obtain ⟨eQ1, eQ2, eQ3⟩ := mul_uu_eqs hQ0
  have hP10 : (P : Mat K) 1 0 = 0 := by
    by_contra h
    apply hp₀0
    exact Prod.ext ((mul_eq_zero.mp eP1).resolve_right h) ((mul_eq_zero.mp eP3).resolve_left h)
  have hQ10 : (Q : Mat K) 1 0 = 0 := by
    by_contra h
    apply hp₀0
    exact Prod.ext ((mul_eq_zero.mp eQ3).resolve_left h) ((mul_eq_zero.mp eQ1).resolve_right h)
  have hdetP : (P : Mat K) 0 0 * (P : Mat K) 1 1 = 1 := by
    have := P.2
    rw [Matrix.det_fin_two, hP10, mul_zero, sub_zero] at this
    exact this
  have hdetQ : (Q : Mat K) 0 0 * (Q : Mat K) 1 1 = 1 := by
    have := Q.2
    rw [Matrix.det_fin_two, hQ10, mul_zero, sub_zero] at this
    exact this
  set α := (P : Mat K) 0 0 with hα
  have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hdetP
  have ht0 : p₀.2 ≠ 0 := by
    intro h
    apply hp₀0
    refine Prod.ext ?_ h
    rw [h, mul_zero] at eP2
    exact (mul_eq_zero.mp eP2.symm).resolve_right (right_ne_zero_of_mul_eq_one hdetP)
  have hs : ∀ p ∈ Wset B, p.1 = α ^ 2 * p.2 := by
    intro p hp
    obtain ⟨-, e, -⟩ := mul_uu_eqs (hPQ p hp).1
    linear_combination -α * e - p.1 * hdetP
  have hαQ : α * (Q : Mat K) 0 0 = 1 := by
    have e1 := hs p₀ hp₀
    have e2 : (Q : Mat K) 0 0 ^ 2 * p₀.1 = p₀.2 := by
      linear_combination (Q : Mat K) 0 0 * eQ2 + p₀.2 * hdetQ
    have e3 : ((α * (Q : Mat K) 0 0) ^ 2 - 1) * p₀.2 = 0 := by
      linear_combination -(Q : Mat K) 0 0 ^ 2 * e1 + e2
    have e4 := (mul_eq_zero.mp e3).resolve_right ht0
    exact eq_one_of_sq_eq_one (sub_eq_zero.mp e4)
  have hP11 : (P : Mat K) 1 1 = (Q : Mat K) 0 0 := by
    linear_combination (Q : Mat K) 0 0 * hdetP - (P : Mat K) 1 1 * hαQ
  have hQ11 : (Q : Mat K) 1 1 = α := by
    linear_combination α * hdetQ - (Q : Mat K) 1 1 * hαQ
  have hc1 : c = 1 := by
    have hE : (P : Mat K) * (E11 K)ᵀ * (Q : Mat K)ᵀ = E11 K := by
      rw [E11_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hP10, hQ10, ← hα, hαQ]
    have h1 : addMap a (E11 K) = c • E11 K := by rw [ha, hE]
    have h2' : addMap a (addMap a (E11 K)) = E11 K := by
      rw [← addMap_mul, haa, addMap_one]
    rw [h1, ha, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hE, smul_smul] at h2'
    have h3 := congrFun (congrFun h2' 0) 0
    simp only [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one] at h3
    exact eq_one_of_sq_eq_one (by rw [sq]; exact h3)
  subst hc1
  have hY0 : MemM (fixV B) !![0, α ^ 2; 1, 0] := by
    rw [memM_fixV]
    intro b hb
    obtain ⟨⟨g, h⟩, ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, rfl⟩ := hB hb
    have hst := hs (s, t) hb
    simp only at hst
    apply fix_uu_of_eqs
    · simp
    · simp
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination hst + α ^ 2 * t * h2
  have hβ : (Q : Mat K) 0 1 = (P : Mat K) 0 1 := by
    have e := congrFun (congrFun (hfix _ hY0) 0) 0
    rw [ha, one_smul] at e
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e
    rw [← hα] at e
    have e2 : α * ((Q : Mat K) 0 1 - (P : Mat K) 0 1) = 0 := by
      linear_combination e - (P : Mat K) 0 1 * α * hαQ - α * (P : Mat K) 0 1 * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left hα0)
  have hQP : (Q : Mat K) * (P : Mat K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hP10, hQ10, hβ, hP11, hQ11, ← hα]
    · linear_combination hαQ
    · linear_combination (Q : Mat K) 0 0 * (P : Mat K) 0 1 * h2
    · linear_combination hαQ
  have hPQ1 : (P : Mat K) * (Q : Mat K) = 1 := mul_eq_one_comm.mp hQP
  have hsym : ∀ x y z : K, MemM (fixV (Subgroup.zpowers a)) (!![x, y; y, z] * (Q : Mat K)ᵀ) := by
    intro x y z
    rw [memM_fixV_zpowers, ha, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc, hPQ1, Matrix.one_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hlow : Nat.card K ^ 3 ≤ Nat.card (fixV (Subgroup.zpowers a)) := by
    rw [card_eq_card_memM, show Nat.card K ^ 3 = Nat.card (K × K × K) by
      rw [Nat.card_prod, Nat.card_prod]; ring]
    refine Nat.card_le_card_of_injective (fun v => ⟨!![v.1, v.2.1; v.2.1, v.2.2] *
      (Q : Mat K)ᵀ, hsym _ _ _⟩) fun v w hvw => ?_
    have e := congrArg (fun X : {X : Mat K // MemM (fixV (Subgroup.zpowers a)) X} =>
      (X : Mat K) * (P : Mat K)ᵀ) hvw
    simp only [Matrix.mul_assoc, ← Matrix.transpose_mul, hPQ1, Matrix.transpose_one,
      Matrix.mul_one] at e
    have e00 := congrFun (congrFun e 0) 0
    have e01 := congrFun (congrFun e 0) 1
    have e11 := congrFun (congrFun e 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11
    exact Prod.ext e00 (Prod.ext e01 e11)
  have haK : a ∈ kLin K := isSemi_of_form (σ := 1) (Or.inr fun X => by
    rw [ha, mapMatrix_one_apply])
  have hzK : Subgroup.zpowers a ≤ kLin K := Subgroup.zpowers_le.mpr haK
  have hlt : fixV (Subgroup.zpowers a) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ha1 (eq_of_addMap fun X => ?_)
    have : MemM (fixV (Subgroup.zpowers a)) X := by rw [htop]; exact Subgroup.mem_top _
    rw [memM_fixV_zpowers] at this
    rw [this, addMap_one]
  have hup := card_mul_le_of_lt (kClosed_fixV hzK) (fun _ _ _ => Subgroup.mem_top _) hlt
  rw [Subgroup.card_top, card_VM] at hup
  have hq : 0 < Nat.card K := Nat.card_pos
  apply le_antisymm
  · rw [mul_comm]
    exact hup
  · calc Nat.card K ^ 4 = Nat.card K ^ 3 * Nat.card K := by ring
      _ ≤ Nat.card (fixV (Subgroup.zpowers a)) * Nat.card K := Nat.mul_le_mul_right _ hlow

end CFSG.Quasithin.H13.H11P

end
