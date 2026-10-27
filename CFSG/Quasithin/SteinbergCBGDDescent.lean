module

public import CFSG.Quasithin.SteinbergCBGDCocycle
public import CFSG.Quasithin.SteinbergCBGDTrace
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem zpow_mem_fixF {f : ℕ} (j : ℤ) {x : K} (hx : x ∈ fixF σ f) : (σ ^ j) x ∈ fixF σ f := by
  rw [mem_fixF] at hx ⊢
  have hc : σ ^ f * σ ^ j = σ ^ j * σ ^ f := (((Commute.refl σ).pow_left f).zpow_right j).eq
  rw [← RingAut.mul_apply, hc, RingAut.mul_apply, hx]

theorem pow_mem_fixF {f : ℕ} (n : ℕ) {x : K} (hx : x ∈ fixF σ f) : (σ ^ n) x ∈ fixF σ f := by
  have := zpow_mem_fixF (n : ℤ) hx
  rwa [zpow_natCast] at this

@[expose] noncomputable def restrictAut (σ : K ≃+* K) (e f : ℕ) : fixF σ f ≃+* fixF σ f where
  toFun x := ⟨(σ ^ e) x, pow_mem_fixF e x.2⟩
  invFun x := ⟨(σ ^ e).symm x, by
    have h := zpow_mem_fixF (σ := σ) (-(e : ℤ)) x.2
    rwa [_root_.zpow_neg, zpow_natCast, RingAut.inv_apply] at h⟩
  left_inv x := Subtype.ext ((σ ^ e).symm_apply_apply (x : K))
  right_inv x := Subtype.ext ((σ ^ e).apply_symm_apply (x : K))
  map_mul' x y := Subtype.ext (map_mul (σ ^ e) (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add (σ ^ e) (x : K) (y : K))

theorem restrictAut_val (e f : ℕ) (x : fixF σ f) :
    ((restrictAut σ e f x : fixF σ f) : K) = (σ ^ e) x := rfl

theorem restrictAut_pow_val (e f n : ℕ) (x : fixF σ f) :
    (((restrictAut σ e f ^ n) x : fixF σ f) : K) = (σ ^ (e * n)) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, restrictAut_val, ih, mul_add, mul_one, pow_add,
      RingAut.mul_apply]
    have hc : σ ^ e * σ ^ (e * n) = σ ^ (e * n) * σ ^ e := ((Commute.refl σ).pow_pow e (e * n)).eq
    rw [← RingAut.mul_apply, hc, RingAut.mul_apply]

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem orderOf_restrictAut [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) {e r : ℕ} (he : 1 ≤ e)
    (hr : 1 ≤ r) : orderOf (restrictAut σ e (e * r)) = r := by
  rw [orderOf_eq_iff (by omega)]
  refine ⟨?_, fun m hm hm0 h => ?_⟩
  · ext x
    rw [restrictAut_pow_val, RingAut.one_apply]
    exact mem_fixF.1 x.2
  · have hle : fixF σ (e * r) ≤ fixF σ (e * m) := by
      intro x hx
      rw [mem_fixF]
      have := restrictAut_pow_val (σ := σ) e (e * r) m ⟨x, hx⟩
      rw [h, RingAut.one_apply] at this
      exact this.symm
    have h1 := finite_fixF hσ (show 1 ≤ e * m by nlinarith)
    have hc := Nat.card_mono (Set.toFinite ((fixF σ (e * m) : Subfield K) : Set K)) hle
    change Nat.card (fixF σ (e * r)) ≤ Nat.card (fixF σ (e * m)) at hc
    rw [card_fixF hσ (by nlinarith), card_fixF hσ (by nlinarith)] at hc
    have hlt : e * m < e * r := Nat.mul_lt_mul_of_pos_left hm (by omega)
    exact absurd (Nat.pow_lt_pow_right hp.out.one_lt hlt) (not_lt.2 hc)

variable {X : Type*} [Group X] [Fintype X] {d : ℕ}

omit [Fintype X] in
theorem trace_mem_traceField (ρ : X →* GL (Fin d) K) (g : X) :
    Matrix.trace (ρ g : Matrix (Fin d) (Fin d) K) ∈ traceField ρ :=
  Subfield.subset_closure ⟨g, rfl⟩

omit [CharP K p] in
theorem exists_intertw_fixF [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) (hd : 1 ≤ d)
    {ρ : X →* GL (Fin d) K} (hρ : IsIrredRep ρ) {e f : ℕ} (hf : 1 ≤ f)
    (htr : traceField ρ ≤ fixF σ e)
    (hent : ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) K) i j ∈ fixF σ f) :
    ∃ A : Matrix (Fin d) (Fin d) K, IsUnit A ∧ (∀ i j, A i j ∈ fixF σ f) ∧
      ∀ g, A * (ρ g : Matrix (Fin d) (Fin d) K) =
        (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) * A := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have htr' : ∀ g, Matrix.trace (ρ g : Matrix (Fin d) (Fin d) K) =
      Matrix.trace (twistRep (σ ^ e) ρ g : Matrix (Fin d) (Fin d) K) := by
    intro g
    rw [trace_twistRep]
    exact (mem_fixF.1 (htr (trace_mem_traceField ρ g))).symm
  obtain ⟨P, hP⟩ := repIso_of_trace_eq hd hρ (hρ.twist (σ ^ e)) htr'
  set A0 : Matrix (Fin d) (Fin d) K := (P : Matrix (Fin d) (Fin d) K) with hA0def
  have hA0u : IsUnit A0 := P.isUnit
  have hA0det := (Matrix.isUnit_iff_isUnit_det A0).1 hA0u
  have hA0 : ∀ g, A0 * (ρ g : Matrix (Fin d) (Fin d) K) =
      (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) * A0 := by
    intro g
    have h := congrArg Units.val (hP g)
    rw [twistRep_val, Units.val_mul, Units.val_mul] at h
    rw [h, mul_assoc (A0 * _), Units.inv_mul, mul_one]
  have hfixρ : ∀ g, (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ f) = ρ g := fun g => by
    ext i j
    exact mem_fixF.1 (hent g i j)
  have hfixρτ : ∀ g, ((ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e)).map ⇑(σ ^ f) =
      (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) := fun g => by
    ext i j
    exact mem_fixF.1 (pow_mem_fixF e (hent g i j))
  have hB : ∀ g, A0.map ⇑(σ ^ f) * (ρ g : Matrix (Fin d) (Fin d) K) =
      (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) * A0.map ⇑(σ ^ f) := by
    intro g
    have h := congrArg (fun M => M.map ⇑(σ ^ f)) (hA0 g)
    simp only [Matrix.map_mul] at h
    rwa [hfixρ, hfixρτ] at h
  have hinv : ∀ g, A0⁻¹ * (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) =
      (ρ g : Matrix (Fin d) (Fin d) K) * A0⁻¹ := by
    intro g
    calc A0⁻¹ * (ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) =
          A0⁻¹ * ((ρ g : Matrix (Fin d) (Fin d) K).map ⇑(σ ^ e) * A0) * A0⁻¹ := by
          rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hA0det, mul_one]
      _ = A0⁻¹ * (A0 * (ρ g : Matrix (Fin d) (Fin d) K)) * A0⁻¹ := by rw [hA0 g]
      _ = (ρ g : Matrix (Fin d) (Fin d) K) * A0⁻¹ := by
          rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA0det]
  have hC : ∀ g, (A0⁻¹ * A0.map ⇑(σ ^ f)) * (ρ g : Matrix (Fin d) (Fin d) K) =
      (ρ g : Matrix (Fin d) (Fin d) K) * (A0⁻¹ * A0.map ⇑(σ ^ f)) := by
    intro g
    rw [mul_assoc, hB g, ← mul_assoc, hinv g, mul_assoc]
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_comm hd hρ hC
  have hBA : A0.map ⇑(σ ^ f) = μ • A0 := by
    calc A0.map ⇑(σ ^ f) = A0 * (A0⁻¹ * A0.map ⇑(σ ^ f)) := by
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA0det]
      _ = μ • A0 := by rw [hμ, mul_smul_comm, mul_one]
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hBA
    have hA00 : A0 = 0 := by
      ext i j
      have h := congrFun (congrFun hBA i) j
      rw [Matrix.map_apply, Matrix.zero_apply, RingEquiv.map_eq_zero_iff] at h
      exact h
    rw [hA00] at hA0u
    exact not_isUnit_zero hA0u
  have hpf : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.out.one_lt
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq μ⁻¹ (n := p ^ f - 1) (by omega)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hlam
    exact inv_ne_zero hμ0 hlam.symm
  have hτlam : (σ ^ f) lam = lam * μ⁻¹ := by
    rw [pow_apply_eq hσ, show p ^ f = (p ^ f - 1) + 1 by omega, pow_succ', hlam]
  refine ⟨lam • A0, ?_, fun i j => ?_, fun g => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact ((Ne.isUnit hlam0).pow _).mul hA0det
  · rw [mem_fixF, Matrix.smul_apply, smul_eq_mul, map_mul, hτlam]
    have h := congrFun (congrFun hBA i) j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h, mul_assoc, ← mul_assoc μ⁻¹, inv_mul_cancel₀ hμ0, one_mul]
  · rw [smul_mul_assoc, hA0 g, mul_smul_comm]

@[expose] def geomS (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + q * geomS q n

theorem geomS_succ' (q n : ℕ) : geomS q (n + 1) = geomS q n + q ^ n := by
  induction n with
  | zero => simp [geomS]
  | succ n ih =>
    change 1 + q * geomS q (n + 1) = 1 + q * geomS q n + q ^ (n + 1)
    rw [ih, mul_add, pow_succ']
    ring

theorem geomS_pos (q : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ geomS q n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm]
  change 1 ≤ 1 + q * geomS q m
  omega

theorem normIter_eq_pow {k : Type*} [Field k] {s : k ≃+* k} {q : ℕ} (hs : ∀ x, s x = x ^ q)
    (u : k) (n : ℕ) : normIter s u n = u ^ geomS q n := by
  induction n with
  | zero => rw [normIter_zero, show geomS q 0 = 0 from rfl, pow_zero]
  | succ n ih =>
    rw [normIter_succ, ih, hs, ← pow_mul]
    change u * u ^ (geomS q n * q) = u ^ (1 + q * geomS q n)
    rw [pow_add, pow_one, mul_comm (geomS q n)]

theorem realizable_of_traceField_le [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) (hd : 1 ≤ d)
    {ρ : X →* GL (Fin d) K} (hρ : IsIrredRep ρ) {e r : ℕ} (he : 1 ≤ e) (hr : 1 ≤ r)
    (htr : traceField ρ ≤ fixF σ e)
    (hent : ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) K) i j ∈ fixF σ (e * r)) :
    Realizable ρ (fixF σ e) := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hf : 1 ≤ e * r := by nlinarith
  obtain ⟨A, hAu, hAent, hAρ⟩ := exists_intertw_fixF hσ hd hρ hf htr hent
  set L := fixF σ (e * r) with hL
  have : Finite L := finite_fixF hσ hf
  set s := restrictAut σ e (e * r) with hs_def
  have hs : orderOf s = r := orderOf_restrictAut hσ he hr
  have hsr : s ^ r = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs] at h
  set toK : Matrix (Fin d) (Fin d) L → Matrix (Fin d) (Fin d) K := fun M => M.map Subtype.val
    with htoK
  have htoK_inj : Function.Injective toK := Matrix.map_injective Subtype.val_injective
  have htoK_mul : ∀ M N, toK (M * N) = toK M * toK N := fun M N =>
    Matrix.map_mul (f := L.subtype)
  have htoK_map : ∀ M, toK (M.map s) = (toK M).map ⇑(σ ^ e) := fun M => by
    ext i j
    rfl
  have htoK_smul : ∀ (c : L) M, toK (c • M) = (c : K) • toK M := fun c M => by
    ext i j
    rfl
  have htoK_one : toK 1 = 1 := by
    ext i j
    simp only [htoK, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> rfl
  set Rk : X → Matrix (Fin d) (Fin d) L := fun g => Matrix.of fun i j => ⟨_, hent g i j⟩ with hRk
  set Ak : Matrix (Fin d) (Fin d) L := Matrix.of fun i j => ⟨_, hAent i j⟩ with hAk
  have hRkK : ∀ g, toK (Rk g) = ρ g := fun g => by
    ext i j
    rfl
  have hAkK : toK Ak = A := by
    ext i j
    rfl
  have hAkR : ∀ g, Ak * Rk g = (Rk g).map s * Ak := fun g => by
    apply htoK_inj
    rw [htoK_mul, htoK_mul, htoK_map, hRkK, hAkK, hAρ]
  have hdetAk : IsUnit Ak.det := by
    have h1 := RingHom.map_det L.subtype Ak
    rw [RingHom.mapMatrix_apply] at h1
    have h2 : Ak.map L.subtype = A := hAkK
    rw [h2] at h1
    have h3 : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hAu).ne_zero
    rw [← h1] at h3
    exact Ne.isUnit fun h0 => h3 (by rw [h0, map_zero])
  set Bk := Ak⁻¹ with hBk
  have hBku : IsUnit Bk :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdetAk)
  have hBR : ∀ g, Bk * (Rk g).map s = Rk g * Bk := by
    intro g
    calc Bk * (Rk g).map s = Bk * ((Rk g).map s * Ak) * Bk := by
          rw [mul_assoc, mul_assoc, hBk, Matrix.mul_nonsing_inv _ hdetAk, mul_one]
      _ = Bk * (Ak * Rk g) * Bk := by rw [hAkR g]
      _ = Rk g * Bk := by rw [hBk, Matrix.nonsing_inv_mul_cancel_left _ _ hdetAk]
  have hCcomm : ∀ g, iterMat s Bk r * Rk g = Rk g * iterMat s Bk r := by
    intro g
    have := iterMat_comm s (hBR g) r
    rwa [hsr, map_one_aut] at this
  have hCK : ∀ g, toK (iterMat s Bk r) * (ρ g : Matrix (Fin d) (Fin d) K) =
      (ρ g : Matrix (Fin d) (Fin d) K) * toK (iterMat s Bk r) := by
    intro g
    rw [← hRkK, ← htoK_mul, ← htoK_mul, hCcomm]
  obtain ⟨c, hc⟩ := exists_smul_one_of_comm hd hρ hCK
  set e0 : Fin d := ⟨0, by omega⟩
  set c' : L := iterMat s Bk r e0 e0 with hc'
  have hc'K : (c' : K) = c := by
    have := congrFun (congrFun hc e0) e0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this
  have hCr : iterMat s Bk r = c' • 1 := by
    apply htoK_inj
    rw [htoK_smul, htoK_one, hc'K, hc]
  have hBk0 : Bk ≠ 0 := by
    intro h0
    rw [h0] at hBku
    exact not_isUnit_zero hBku
  have hsc : s c' = c' := fixed_of_iterMat_eq s hBk0 hsr hCr
  have hc'0 : c' ≠ 0 := by
    intro h0
    have hu := isUnit_iterMat s hBku r
    rw [hCr, h0, zero_smul] at hu
    exact not_isUnit_zero hu
  set q := p ^ e with hq
  have hsq : ∀ x : L, s x = x ^ q := fun x => by
    apply Subtype.ext
    rw [restrictAut_val, pow_apply_eq hσ, SubmonoidClass.coe_pow]
  have hc'q : (c' : K) ^ q = c' := by
    have := congrArg Subtype.val hsc
    rw [hsq, SubmonoidClass.coe_pow] at this
    exact this
  have hS := geomS_pos q hr
  obtain ⟨u0, hu0⟩ := IsAlgClosed.exists_pow_nat_eq ((c' : K)⁻¹) (n := geomS q r) (by omega)
  have hc'0K : (c' : K) ≠ 0 := fun h => hc'0 (Subtype.ext h)
  have hu0L : u0 ∈ L := by
    rw [hL, mem_fixF_iff hσ, pow_mul]
    change u0 ^ q ^ r = u0
    have hid : geomS q r + q ^ r = q * geomS q r + 1 := by
      rw [← geomS_succ']
      change 1 + q * geomS q r = q * geomS q r + 1
      omega
    have h1 : u0 ^ (q * geomS q r) = u0 ^ geomS q r := by
      rw [mul_comm, pow_mul, hu0, inv_pow, hc'q]
    have h2 : u0 ^ geomS q r * u0 ^ q ^ r = u0 ^ geomS q r * u0 := by
      rw [← pow_add, hid, pow_add, h1, pow_one]
    have h3 : u0 ^ geomS q r ≠ 0 := by
      rw [hu0]
      exact inv_ne_zero hc'0K
    exact mul_left_cancel₀ h3 h2
  set u : L := ⟨u0, hu0L⟩ with hu
  have hNu : normIter s u r = c'⁻¹ := by
    rw [normIter_eq_pow hsq]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subfield.coe_inv]
    exact hu0
  have hu0' : u ≠ 0 := by
    intro h0
    have := hNu
    rw [h0, normIter_eq_pow hsq, zero_pow (by omega)] at this
    exact inv_ne_zero hc'0 this.symm
  set B' := u • Bk with hB'
  have hB'u : IsUnit B' := by
    rw [hB', Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact ((Ne.isUnit hu0').pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hBku)
  have hB'R : ∀ g, B' * (Rk g).map s = Rk g * B' := by
    intro g
    rw [hB', smul_mul_assoc, hBR g, mul_smul_comm]
  have hB'C : iterMat s B' r = 1 := by
    rw [hB', iterMat_smul, hNu, hCr, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
  obtain ⟨P, hPu, hPfix⟩ := exists_fixed_conj s hs (by omega) Rk hB'u hB'R hB'C
  have hPdet := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPK : IsUnit (toK P) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h1 := RingHom.map_det L.subtype P
    rw [RingHom.mapMatrix_apply] at h1
    change IsUnit (P.map L.subtype).det
    rw [← h1]
    exact hPdet.map _
  set U : GL (Fin d) K := hPK.unit with hU
  refine ⟨U⁻¹, fun g i j => ?_⟩
  set Q := P⁻¹ * Rk g * P with hQ
  have hPQ : P * Q = Rk g * P := by
    rw [hQ, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hPdet, one_mul]
  have hPQK : toK P * toK Q = (ρ g : Matrix (Fin d) (Fin d) K) * toK P := by
    rw [← htoK_mul, hPQ, htoK_mul, hRkK]
  have hUval : ((U : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = toK P := IsUnit.unit_spec hPK
  have hval : ((U⁻¹ * ρ g * U⁻¹⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = toK Q := by
    rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hUval, ← hPQK, ← hUval,
      Units.inv_mul_cancel_left]
  rw [hval]
  rw [mem_fixF]
  have hfixQ := congrFun (congrFun (hPfix g) i) j
  rw [Matrix.map_apply] at hfixQ
  have := congrArg Subtype.val hfixQ
  rw [restrictAut_val] at this
  exact this

end CFSG.Quasithin.SteinbergCB.GDescent
