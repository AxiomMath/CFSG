module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoordRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open
open CFSG.StandardType.RCKK1IIISU CFSG.StandardType.LieKnownR2.Short
  CFSG.StandardType.GGOppRadSpU CFSG.QuasithinUnique.B113Lie.Sp

variable {k : ℕ}

theorem rckSU_survivor_mem_suZ0 (hk : 4 ≤ k) {z : SUG k} (hz : z ∈ suZ0 hk) :
    ∃ v : Fin 4 → ZMod 2, suZ hk v = z := by
  rw [suZ0, MonoidHom.mem_range] at hz
  obtain ⟨v, hv⟩ := hz
  exact ⟨v.toAdd, hv⟩

theorem rckSU_suZ0_le_centralizer (hk : 4 ≤ k) :
    suZ0 hk ≤ Subgroup.centralizer ({suR hk} : Set (SUG k)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨v, rfl⟩ := rckSU_survivor_mem_suZ0 hk hz
  have hR : suR hk = suZ hk s5R := rfl
  rw [hR, suZ_add, suZ_add, add_comm]

theorem rckSU_survivor_mul_N_of_commute (hk : 4 ≤ k) (B : GL (Fin k) SUF)
    (hGL : B * (suR hk : GL (Fin k) SUF) = (suR hk : GL (Fin k) SUF) * B) :
    (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk =
      rckSUc_N hk * (B : Matrix (Fin k) (Fin k) SUF) := by
  have h := congrArg (fun g : GL (Fin k) SUF => (g : Matrix (Fin k) (Fin k) SUF)) hGL
  simp only [Units.val_mul] at h
  rw [rckSUc_suR_eq, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h
  exact add_left_cancel h

theorem rckSU_suZ0_conj_mem (hk : 4 ≤ k) {x : SUG k}
    (hx : x ∈ Subgroup.centralizer ({suR hk} : Set (SUG k))) {z : SUG k} (hz : z ∈ suZ0 hk) :
    x * z * x⁻¹ ∈ suZ0 hk := by
  obtain ⟨v, rfl⟩ := rckSU_survivor_mem_suZ0 hk hz
  have hcomm : x * suR hk = suR hk * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hGL : (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) =
      (suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF) :=
    congrArg (fun g : SUG k => (g : GL (Fin k) SUF)) hcomm
  have hGLconj : (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) *
      (x : GL (Fin k) SUF)⁻¹ = (suR hk : GL (Fin k) SUF) := by
    calc (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF)⁻¹
        = ((x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF)) *
            (x : GL (Fin k) SUF)⁻¹ := rfl
      _ = ((suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF)) *
            (x : GL (Fin k) SUF)⁻¹ := by rw [hGL]
      _ = (suR hk : GL (Fin k) SUF) := by group
  have hB : conjTr SUσ ((x : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) * antidiag k *
      ((x : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) = antidiag k := (mem_SU.mp x.2).2
  have hr : ((x : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
      (((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map (RingEquiv.refl SUF)) *
        ((((x : GL (Fin k) SUF))⁻¹ : GL (Fin k) SUF) :
          Matrix (Fin k) (Fin k) SUF) =
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
    have hmap : (((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map
        (RingEquiv.refl SUF)) =
        ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
      change ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map id = _
      rw [Matrix.map_id]
    rw [hmap]
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using
      congrArg (fun g : GL (Fin k) SUF => (g : Matrix (Fin k) (Fin k) SUF)) hGLconj
  obtain ⟨ψ, -, -, -, hconj⟩ :=
    rckSU_act hk (RingEquiv.refl SUF) (x : GL (Fin k) SUF) hB hr
  have hxconj : x * suZ hk v * x⁻¹ =
      suZ hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      suZ_val]
    exact hconj v
  rw [hxconj]
  exact ⟨_, rfl⟩

theorem rckSU_suZ0_normal_centralizer (hk : 4 ≤ k) :
    ((suZ0 hk).subgroupOf
      (Subgroup.centralizer ({suR hk} : Set (SUG k)))).Normal := by
  refine ⟨fun z hz x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using rckSU_suZ0_conj_mem hk x.2 hz

theorem rckSU_isPGroup_suZ0 (hk : 4 ≤ k) : IsPGroup 2 (suZ0 hk) :=
  IsPGroup.of_card (p := 2) (n := 4) (by rw [card_suZ0]; norm_num)

theorem rckSU_suZ0_le_pCoreOf (hk : 4 ≤ k) :
    suZ0 hk ≤ pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) :=
  le_pCoreOf (r := 2) (rckSU_suZ0_le_centralizer hk) (rckSU_suZ0_normal_centralizer hk)
    (rckSU_isPGroup_suZ0 hk)

theorem rckSU_two_by_two_involution_eq_one {K : Type*} [Field K] [CharP K 2]
    (σ : K ≃+* K) (g : Matrix (Fin 2) (Fin 2) K) (hg : g * g = 1)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) K, conjTr σ A = A →
      (g * A * conjTr σ g + A) 0 0 = 0 ∧ (g * A * conjTr σ g + A) 1 1 = 0) :
    g = 1 := by
  have hE11 : conjTr σ !![(1 : K), 0; 0, 0] = !![(1 : K), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr_apply]
  have hE22 : conjTr σ !![(0 : K), 0; 0, 1] = !![(0 : K), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr_apply]
  have hpp : g 0 0 * σ (g 0 0) + 1 = 0 := by
    have h := (hdiag !![(1 : K), 0; 0, 0] hE11).1
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, conjTr_apply] using h
  have hrr : g 1 0 * σ (g 1 0) = 0 := by
    have h := (hdiag !![(1 : K), 0; 0, 0] hE11).2
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, conjTr_apply] using h
  have hqq : g 0 1 * σ (g 0 1) = 0 := by
    have h := (hdiag !![(0 : K), 0; 0, 1] hE22).1
    simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, conjTr_apply] using h
  have hr0 : g 1 0 = 0 := by
    rcases mul_eq_zero.mp hrr with h | h
    · exact h
    · exact σ.injective (by rw [h, map_zero])
  have hq0 : g 0 1 = 0 := by
    rcases mul_eq_zero.mp hqq with h | h
    · exact h
    · exact σ.injective (by rw [h, map_zero])
  have h00 : g 0 0 * g 0 0 + g 0 1 * g 1 0 = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : g 1 0 * g 0 1 + g 1 1 * g 1 1 = 1 := by
    have := congrFun (congrFun hg 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hp : g 0 0 = 1 := by
    rw [hq0, hr0, mul_zero, add_zero] at h00
    exact CharTwo.sq_inj.mp (by simpa [pow_two] using h00)
  have hs : g 1 1 = 1 := by
    rw [hq0, hr0, mul_zero, zero_add] at h11
    exact CharTwo.sq_inj.mp (by simpa [pow_two] using h11)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hp, hq0, hr0, hs, Matrix.one_apply]


theorem rckSU_suR_sq (hk : 4 ≤ k) : suR hk ^ 2 = 1 := by
  rw [suR, sq, suZ_add]
  change suZ hk (s5R + s5R) = 1
  have hv : s5R + s5R = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (s5R i)
  rw [hv, suZ_zero]

theorem rckSU_suZ_inv (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) : (suZ hk v)⁻¹ = suZ hk v := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [suZ_add]
  have hv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [hv, suZ_zero]

theorem rckSU_A_s5R_diag : (rckSUc_A s5R) 0 0 = 0 ∧ (rckSUc_A s5R) 1 1 = 0 := by
  constructor <;> simp [rckSUc_A, rckSUc_beta, rckSUc_alpha, s5R, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]

theorem rckSU_corner_eq_one_of_coreComm (hk : 4 ≤ k) (V : Subgroup (SUG k))
    (hN : ∀ v ∈ V, ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))),
      v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers (suR hk))
    {s : SUG k} (hsV : s ∈ V)
    (hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k))) (hs2 : s ^ 2 = 1) :
    rckSUc_g hk (((s : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) = 1 := by
  set B : GL (Fin k) SUF := (s : GL (Fin k) SUF) with hBdef
  have hcomm : s * suR hk = suR hk * s := Subgroup.mem_centralizer_singleton_iff.mp hsC
  have hGL : B * (suR hk : GL (Fin k) SUF) = (suR hk : GL (Fin k) SUF) * B :=
    congrArg (fun g : SUG k => (g : GL (Fin k) SUF)) hcomm
  have hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * antidiag k *
      (B : Matrix (Fin k) (Fin k) SUF) = antidiag k := (mem_SU.mp s.2).2
  have hBN := rckSU_survivor_mul_N_of_commute hk B hGL
  set ψ : GL (Fin 4) (ZMod 2) := rckSUc_psi hk B (RingEquiv.refl SUF) hB hBN with hψdef
  have hmapid : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) SUF),
      M.map (RingEquiv.refl SUF) = M := by
    intro n M
    change M.map id = M
    rw [Matrix.map_id]
  have hψZ : ∀ v : Fin 4 → ZMod 2,
      s * suZ hk v * s⁻¹ = suZ hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
    intro v
    have h := rckSUc_conj_corner_Binv hk B (RingEquiv.refl SUF) hB hBN v
    have h' : B * suCorner hk v * B⁻¹ =
        suCorner hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
      simpa only [hmapid k (suCorner hk v)] using h
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      suZ_val] using h'
  have hmemZ : ∀ v : Fin 4 → ZMod 2, suZ hk v ∈
      pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) :=
    fun v => rckSU_suZ0_le_pCoreOf hk ⟨v, rfl⟩
  have hsuRsq : suR hk ^ 2 = 1 := rckSU_suR_sq hk
  have hsuRord : orderOf (suR hk) = 2 :=
    orderOf_eq_prime hsuRsq (suR_ne_one hk)
  have hRes : ∀ v : Fin 4 → ZMod 2,
      (ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v + v = 0 ∨
      (ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v + v = s5R := by
    intro v
    have h := hN s hsV (suZ hk v) (hmemZ v)
    rw [hψZ v, rckSU_suZ_inv hk v, suZ_add] at h
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsuRord).mp h with h1 | h1
    · left
      apply suZ_injective hk
      rw [h1, suZ_zero]
    · right
      apply suZ_injective hk
      rw [h1]
      rfl
  have hAadd : ∀ x y : Fin 4 → ZMod 2, rckSUc_A (x + y) = rckSUc_A x + rckSUc_A y := by
    intro x y
    exact congrArg Subtype.val (rckSUc_Ato.map_add x y)
  have hAdiag : ∀ v : Fin 4 → ZMod 2,
      (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) *
          (rckSUc_A v * rckSUc_gstar hk (B : Matrix (Fin k) (Fin k) SUF)) +
        rckSUc_A v) 0 0 = 0 ∧
      (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) *
          (rckSUc_A v * rckSUc_gstar hk (B : Matrix (Fin k) (Fin k) SUF)) +
        rckSUc_A v) 1 1 = 0 := by
    intro v
    have hApsi := rckSUc_A_psi hk B (RingEquiv.refl SUF) hB hBN v
    rw [hmapid 2 (rckSUc_A v)] at hApsi
    have hEq : rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) *
          (rckSUc_A v * rckSUc_gstar hk (B : Matrix (Fin k) (Fin k) SUF)) +
        rckSUc_A v =
        rckSUc_A ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v + v) := by
      rw [hAadd, hApsi]
    rcases hRes v with h0 | hR
    · rw [hEq, h0]
      have hzero : rckSUc_A (0 : Fin 4 → ZMod 2) = 0 := by
        have := rckSUc_Ato.map_zero
        exact congrArg Subtype.val this
      rw [hzero]
      exact ⟨rfl, rfl⟩
    · rw [hEq, hR]
      exact rckSU_A_s5R_diag
  have hB2 : B * B = 1 := by
    have h := congrArg (fun g : SUG k => (g : GL (Fin k) SUF)) hs2
    simpa [B, sq] using h
  have hB2m : (B : Matrix (Fin k) (Fin k) SUF) * (B : Matrix (Fin k) (Fin k) SUF) = 1 := by
    rw [← Units.val_mul, hB2, Units.val_one]
  have hgg : rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) *
      rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) = 1 := by
    ext i j
    have hentry := congrFun (congrFun hB2m (rckSUc_e hk i)) (rckSUc_e hk j)
    rw [Matrix.mul_apply] at hentry
    have hsum : ∑ p : Fin k, (B : Matrix (Fin k) (Fin k) SUF) (rckSUc_e hk i) p *
          (B : Matrix (Fin k) (Fin k) SUF) p (rckSUc_e hk j) =
        ∑ a : Fin 2, (B : Matrix (Fin k) (Fin k) SUF) (rckSUc_e hk i) (rckSUc_e hk a) *
          (B : Matrix (Fin k) (Fin k) SUF) (rckSUc_e hk a) (rckSUc_e hk j) := by
      have hzero : ∀ x ∈ (Finset.univ : Finset (Fin k)),
          x ∉ ({rckSUc_e hk 0, rckSUc_e hk 1} : Finset (Fin k)) →
          (B : Matrix (Fin k) (Fin k) SUF) (rckSUc_e hk i) x *
            (B : Matrix (Fin k) (Fin k) SUF) x (rckSUc_e hk j) = 0 := by
        intro p _ hp
        rw [Finset.mem_insert, Finset.mem_singleton] at hp
        push Not at hp
        have h0 := rckSUc_B_col_of_ne hk (B : Matrix (Fin k) (Fin k) SUF) hBN p hp.1 hp.2
        fin_cases j
        · simp [h0.1]
        · simp [h0.2]
      rw [← Finset.sum_subset (s₁ := ({rckSUc_e hk 0, rckSUc_e hk 1} : Finset (Fin k)))
        (Finset.subset_univ _) hzero, Finset.sum_pair (rckSUc_e_zero_ne_one hk),
        Fin.sum_univ_two]
    rw [hsum] at hentry
    have h1 : (1 : Matrix (Fin k) (Fin k) SUF) (rckSUc_e hk i) (rckSUc_e hk j) =
        (1 : Matrix (Fin 2) (Fin 2) SUF) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : rckSUc_e hk i ≠ rckSUc_e hk j := fun h => hij (rckSUc_e_injective hk h)
        simp [hij, hne]
    rw [h1] at hentry
    rw [Matrix.mul_apply]
    simpa only [rckSUc_g, Matrix.submatrix_apply] using hentry
  have hgdiag : ∀ A : Matrix (Fin 2) (Fin 2) SUF, conjTr SUσ A = A →
      (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) * A *
          conjTr SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)) + A) 0 0 = 0 ∧
      (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) * A *
          conjTr SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)) + A) 1 1 = 0 := by
    intro A hA
    obtain ⟨v, hv⟩ := rckSUc_Ato_surjective (⟨A, rckSUc_mem_herm.mpr hA⟩ : rckSUc_herm)
    have hAv : rckSUc_A v = A := congrArg Subtype.val hv
    simpa only [hAv, rckSUc_gstar, mul_assoc] using hAdiag v
  exact rckSU_two_by_two_involution_eq_one SUσ
    (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)) hgg hgdiag


theorem rckSU_core_le_centralizer_of_le_suZ0 (hk : 4 ≤ k) {V : Subgroup (SUG k)}
    (hV : V ≤ suZ0 hk) :
    pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) ≤
      Subgroup.centralizer (V : Set (SUG k)) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hqZ := rckSU_core hk hq
  rw [Subgroup.mem_centralizer_iff] at hqZ
  exact hqZ v (hV hv)

theorem rckSU_suF_card : Nat.card SUF = (2 ^ 1) ^ 2 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

@[expose] noncomputable def rckSU_std (i : Fin k) : Fin k → SUF := Pi.single i 1

theorem rckSU_suH_std (a b : Fin k) :
    (suH rckSU_suF_card k).β (rckSU_std (k := k) a) (rckSU_std (k := k) b) =
      if Fin.rev a = b then 1 else 0 := by
  change (suForm SUσ (unitaryInvolution_involutive rckSU_suF_card) k).β
    (Pi.single a 1) (Pi.single b 1) = _
  rw [suForm_single]
  simp only [Pi.single_apply, eq_comm]

@[expose] noncomputable def rckSU_U (hk : 4 ≤ k) : Submodule SUF (Fin k → SUF) :=
  Submodule.span SUF {rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)}

theorem rckSU_U_isTotallyIsotropic (hk : 4 ≤ k) :
    (suH rckSU_suF_card k).IsTotallyIsotropic (rckSU_U hk) := by
  have hβ : ∀ (a b : SUF) (z : Fin k → SUF),
      (suH rckSU_suF_card k).β (a • rckSU_std (k := k) (sI0 hk) +
        b • rckSU_std (k := k) (sI1 hk)) z =
      SUσ a * (suH rckSU_suF_card k).β (rckSU_std (sI0 hk)) z +
        SUσ b * (suH rckSU_suF_card k).β (rckSU_std (sI1 hk)) z := by
    intro a b z
    rw [ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left]
    simp only [suH, suForm_σ]
  have h00 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk))
      (rckSU_std (k := k) (sI0 hk)) = 0 := by
    rw [rckSU_suH_std, if_neg (fun h => rckSUc_e_ne_e' hk 0 0 h.symm)]
  have h01 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk))
      (rckSU_std (k := k) (sI1 hk)) = 0 := by
    rw [rckSU_suH_std, if_neg (fun h => rckSUc_e_ne_e' hk 1 0 h.symm)]
  have h10 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk))
      (rckSU_std (k := k) (sI0 hk)) = 0 := by
    rw [rckSU_suH_std, if_neg (fun h => rckSUc_e_ne_e' hk 0 1 h.symm)]
  have h11 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk))
      (rckSU_std (k := k) (sI1 hk)) = 0 := by
    rw [rckSU_suH_std, if_neg (fun h => rckSUc_e_ne_e' hk 1 1 h.symm)]
  rw [ReflForm.IsTotallyIsotropic, rckSU_U, Submodule.span_le]
  rintro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change ∀ w ∈ rckSU_U hk, (suH rckSU_suF_card k).β w x = 0
  rcases hx with rfl | rfl
  · intro y hy
    rw [rckSU_U] at hy
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    rw [hβ, h00, h10]
    simp
  · intro y hy
    rw [rckSU_U] at hy
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    rw [hβ, h01, h11]
    simp


theorem rckSU_suH_std_left (a : Fin k) (y : Fin k → SUF) :
    (suH rckSU_suF_card k).β (rckSU_std (k := k) a) y = y (Fin.rev a) := by
  change (suForm SUσ (unitaryInvolution_involutive rckSU_suF_card) k).β
    (Pi.single a 1) y = _
  rw [suForm_single]

theorem rckSU_suH_std_right (a : Fin k) (x : Fin k → SUF) :
    (suH rckSU_suF_card k).β x (rckSU_std (k := k) a) = SUσ (x (Fin.rev a)) := by
  change (suForm SUσ (unitaryInvolution_involutive rckSU_suF_card) k).β x (Pi.single a 1) = _
  rw [suForm_β, Finset.sum_eq_single (Fin.rev a)]
  · simp
  · intro b _ hb
    have hne : Fin.rev b ≠ a := by
      intro h
      exact hb (by rw [← h, Fin.rev_rev])
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] noncomputable def rckSU_Nlin (hk : 4 ≤ k) : Module.End SUF (Fin k → SUF) :=
  Matrix.toLin' (rckSUc_N hk)

theorem rckSUc_N_mulVec (hk : 4 ≤ k) (x : Fin k → SUF) :
    rckSUc_N hk *ᵥ x =
      x (rckSUc_e' hk 1) • Pi.single (rckSUc_e hk 0) (1 : SUF) +
        x (rckSUc_e' hk 0) • Pi.single (rckSUc_e hk 1) (1 : SUF) := by
  have h1 : (1 : SUF) * x (rckSUc_e' hk 1) = x (rckSUc_e' hk 1) := one_mul _
  have h2 : (1 : SUF) * x (rckSUc_e' hk 0) = x (rckSUc_e' hk 0) := one_mul _
  rw [rckSUc_N, Matrix.add_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, h1, h2]

theorem rckSU_Nlin_apply (hk : 4 ≤ k) (x : Fin k → SUF) :
    rckSU_Nlin hk x =
      x (rckSUc_e' hk 1) • Pi.single (rckSUc_e hk 0) (1 : SUF) +
        x (rckSUc_e' hk 0) • Pi.single (rckSUc_e hk 1) (1 : SUF) := by
  rw [rckSU_Nlin, Matrix.toLin'_apply, rckSUc_N_mulVec]

@[expose] noncomputable def rckSU_A (hk : 4 ≤ k) : Submodule SUF (Fin k → SUF) :=
  LinearMap.range (rckSU_Nlin hk)

theorem rckSU_N_sq (hk : 4 ≤ k) : rckSU_Nlin hk * rckSU_Nlin hk = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, rckSU_Nlin_apply hk x]
  rw [map_add, map_smul, map_smul]
  have h0 : rckSU_Nlin hk (Pi.single (rckSUc_e hk 0) (1 : SUF)) = 0 := by
    rw [rckSU_Nlin_apply]
    simp [Pi.single_apply, rckSUc_e_ne_e' hk 0 1, rckSUc_e_ne_e' hk 0 0, eq_comm]
  have h1 : rckSU_Nlin hk (Pi.single (rckSUc_e hk 1) (1 : SUF)) = 0 := by
    rw [rckSU_Nlin_apply]
    simp [Pi.single_apply, rckSUc_e_ne_e' hk 1 1, rckSUc_e_ne_e' hk 1 0, eq_comm]
  rw [h0, h1, smul_zero, smul_zero, add_zero]
  simp

theorem rckSU_N_selfAdjoint (hk : 4 ≤ k) (x y : Fin k → SUF) :
    (suH rckSU_suF_card k).β (rckSU_Nlin hk x) y =
      (suH rckSU_suF_card k).β x (rckSU_Nlin hk y) := by
  rw [rckSU_Nlin_apply, rckSU_Nlin_apply]
  rw [ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
    ReflForm.add_right, ReflForm.smul_right, ReflForm.smul_right]
  have hL0 : (suH rckSU_suF_card k).β (Pi.single (rckSUc_e hk 0) (1 : SUF)) y =
      y (rckSUc_e' hk 0) := rckSU_suH_std_left (rckSUc_e hk 0) y
  have hL1 : (suH rckSU_suF_card k).β (Pi.single (rckSUc_e hk 1) (1 : SUF)) y =
      y (rckSUc_e' hk 1) := rckSU_suH_std_left (rckSUc_e hk 1) y
  have hR0 : (suH rckSU_suF_card k).β x (Pi.single (rckSUc_e hk 0) (1 : SUF)) =
      SUσ (x (rckSUc_e' hk 0)) := rckSU_suH_std_right (rckSUc_e hk 0) x
  have hR1 : (suH rckSU_suF_card k).β x (Pi.single (rckSUc_e hk 1) (1 : SUF)) =
      SUσ (x (rckSUc_e' hk 1)) := rckSU_suH_std_right (rckSUc_e hk 1) x
  rw [hL0, hL1, hR0, hR1]
  simp only [suH, suForm_σ]
  ring

theorem rckSU_A_isTotallyIsotropic (hk : 4 ≤ k) :
    (suH rckSU_suF_card k).IsTotallyIsotropic (rckSU_A hk) := by
  rw [ReflForm.IsTotallyIsotropic]
  intro u hu
  rw [ReflForm.mem_perp]
  intro v hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  rw [rckSU_N_selfAdjoint,
    show rckSU_Nlin hk (rckSU_Nlin hk a) = 0 from by
      have h := congrArg (fun f : Module.End SUF (Fin k → SUF) => f a) (rckSU_N_sq hk)
      simpa using h,
    ReflForm.β_zero_right]

noncomputable abbrev rckSU_Q (hk : 4 ≤ k) : Subgroup (SUG k) :=
  suStabRad (F := SUF) (f := 1) rckSU_suF_card k (rckSU_A hk)
    (rckSU_A_isTotallyIsotropic hk)

theorem rckSU_Q_le_centralizer (hk : 4 ≤ k) :
    rckSU_Q hk ≤ Subgroup.centralizer ({suR hk} : Set (SUG k)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hfixA : ∀ a ∈ rckSU_A hk, natRep (SU SUσ k) g a = a := (mem_rad.mp hg).1
  have hfixAinv : ∀ a ∈ rckSU_A hk, natRep (SU SUσ k) g⁻¹ a = a :=
    (mem_rad.mp (Subgroup.inv_mem _ hg)).1
  have hNmem : ∀ x, rckSU_Nlin hk x ∈ rckSU_A hk := fun x => ⟨x, rfl⟩
  have hρ : ∀ (h : SUG k) (x y : Fin k → SUF),
      (suH rckSU_suF_card k).β (natRep (SU SUσ k) h x) (natRep (SU SUσ k) h y) =
        (suH rckSU_suF_card k).β x y :=
    isIsometric_natRep_SU SUσ (unitaryInvolution_involutive rckSU_suF_card) k
  have hNg : ∀ x, rckSU_Nlin hk (natRep (SU SUσ k) g x) = rckSU_Nlin hk x := by
    intro x
    have hzero : rckSU_Nlin hk (natRep (SU SUσ k) g x) - rckSU_Nlin hk x = 0 := by
      apply (suH rckSU_suF_card k).nondeg
      intro y
      rw [ReflForm.β_sub_left, rckSU_N_selfAdjoint]
      have hiso := hρ g⁻¹ (natRep (SU SUσ k) g x) (rckSU_Nlin hk y)
      rw [show natRep (SU SUσ k) g⁻¹ (natRep (SU SUσ k) g x) = x from by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply],
        hfixAinv _ (hNmem y)] at hiso
      rw [← hiso, rckSU_N_selfAdjoint, sub_self]
    exact sub_eq_zero.mp hzero
  have hleft : natRep (SU SUσ k) g * rckSU_Nlin hk = rckSU_Nlin hk := by
    refine LinearMap.ext fun x => ?_
    show natRep (SU SUσ k) g (rckSU_Nlin hk x) = rckSU_Nlin hk x
    exact hfixA _ (hNmem x)
  have hright : rckSU_Nlin hk * natRep (SU SUσ k) g = rckSU_Nlin hk := by
    refine LinearMap.ext fun x => ?_
    show rckSU_Nlin hk (natRep (SU SUσ k) g x) = rckSU_Nlin hk x
    exact hNg x
  have hsuReq : natRep (SU SUσ k) (suR hk) = 1 + rckSU_Nlin hk := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, Module.End.one_apply, natRep_apply, rckSUc_suR_eq,
      Matrix.add_mulVec, Matrix.one_mulVec, rckSUc_N_mulVec, rckSU_Nlin_apply]
  have hcomm : natRep (SU SUσ k) g * natRep (SU SUσ k) (suR hk) =
      natRep (SU SUσ k) (suR hk) * natRep (SU SUσ k) g := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hsuReq]
    simp only [LinearMap.add_apply, Module.End.one_apply]
    rw [map_add, hfixA _ (hNmem v), hNg v]
  refine natRep_injective (SU SUσ k) ?_
  rw [map_mul, map_mul]
  exact hcomm


theorem rckSU_centralizer_preserves_A (hk : 4 ≤ k) {c : SUG k}
    (hc : c ∈ Subgroup.centralizer ({suR hk} : Set (SUG k))) :
    (∀ w ∈ rckSU_A hk, natRep (SU SUσ k) c w ∈ rckSU_A hk) ∧
      (∀ w ∈ rckSU_A hk, natRep (SU SUσ k) c⁻¹ w ∈ rckSU_A hk) := by
  have hsuReq : natRep (SU SUσ k) (suR hk) = 1 + rckSU_Nlin hk := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, Module.End.one_apply, natRep_apply, rckSUc_suR_eq,
      Matrix.add_mulVec, Matrix.one_mulVec, rckSUc_N_mulVec, rckSU_Nlin_apply]
  have hcommN : ∀ (d : SUG k), d ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)) →
      natRep (SU SUσ k) d * rckSU_Nlin hk = rckSU_Nlin hk * natRep (SU SUσ k) d := by
    intro d hd
    refine LinearMap.ext fun v => ?_
    have hdr : d * suR hk = suR hk * d := Subgroup.mem_centralizer_singleton_iff.mp hd
    have h : natRep (SU SUσ k) d * natRep (SU SUσ k) (suR hk) =
        natRep (SU SUσ k) (suR hk) * natRep (SU SUσ k) d := by
      rw [← map_mul, ← map_mul, hdr]
    have hv := congrArg (fun f : Module.End SUF (Fin k → SUF) => f v) h
    rw [hsuReq] at hv
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.map_add] at hv
    exact add_left_cancel hv
  constructor
  · intro w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨natRep (SU SUσ k) c v,
      (congrArg (fun f : Module.End SUF (Fin k → SUF) => f v) (hcommN c hc)).symm⟩
  · intro w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨natRep (SU SUσ k) c⁻¹ v,
      (congrArg (fun f : Module.End SUF (Fin k → SUF) => f v)
        (hcommN c⁻¹ (Subgroup.inv_mem _ hc))).symm⟩

theorem rckSU_centralizer_conj_mem_Q (hk : 4 ≤ k) {c : SUG k}
    (hc : c ∈ Subgroup.centralizer ({suR hk} : Set (SUG k))) {q : SUG k}
    (hq : q ∈ rckSU_Q hk) : c * q * c⁻¹ ∈ rckSU_Q hk := by
  obtain ⟨hpre, hpre'⟩ := rckSU_centralizer_preserves_A hk hc
  exact rad_conj_mem (F := suH rckSU_suF_card k) (ρ := natRep (SU SUσ k))
    (isIsometric_natRep_SU SUσ (unitaryInvolution_involutive rckSU_suF_card) k)
    (W := rckSU_A hk) (hW := rckSU_A_isTotallyIsotropic hk) hpre hpre' hq

theorem rckSU_centralizer_le_normalizer_Q (hk : 4 ≤ k) :
    Subgroup.centralizer ({suR hk} : Set (SUG k)) ≤
      Subgroup.normalizer (rckSU_Q hk : Set (SUG k)) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact rckSU_centralizer_conj_mem_Q hk hc hx
  · intro hx
    have h := rckSU_centralizer_conj_mem_Q hk (Subgroup.inv_mem _ hc) hx
    rw [inv_inv] at h
    rwa [show c⁻¹ * (c * x * c⁻¹) * c = x from by group] at h

theorem rckSU_Q_le_pCoreOf (hk : 4 ≤ k) :
    rckSU_Q hk ≤ pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer (r := 2) (rckSU_Q_le_centralizer hk)
    (rckSU_centralizer_le_normalizer_Q hk) ?_
  exact rad_isPGroup (F := suH rckSU_suF_card k) (ρ := natRep (SU SUσ k))
    (isIsometric_natRep_SU SUσ (unitaryInvolution_involutive rckSU_suF_card) k)
    (natRep_injective _) 2 (rckSU_A_isTotallyIsotropic hk)


theorem rckSU_U_eq_range (hk : 4 ≤ k) :
    rckSU_U hk = rckSU_A hk := by
  rw [rckSU_A]
  have h01 : sI0 hk ≠ sI1 hk := fun h => rckSUc_e_zero_ne_one hk (by simpa [rckSUc_e] using h)
  refine le_antisymm ?_ ?_
  · rw [rckSU_U, Submodule.span_le]
    rintro x (rfl | rfl)
    · refine ⟨Pi.single (rckSUc_e' hk 1) (1 : SUF), ?_⟩
      rw [rckSU_Nlin_apply]
      simp [rckSU_std, rckSUc_e, rckSUc_e', Pi.single_apply, eq_comm, Matrix.cons_val_zero,
        Matrix.cons_val_one, rckSUc_e'_one_ne_zero hk, h01]
    · refine ⟨Pi.single (rckSUc_e' hk 0) (1 : SUF), ?_⟩
      rw [rckSU_Nlin_apply]
      simp [rckSU_std, rckSUc_e, rckSUc_e', Pi.single_apply, eq_comm, Matrix.cons_val_zero,
        Matrix.cons_val_one, rckSUc_e'_zero_ne_one hk, h01]
  · rintro _ ⟨x, rfl⟩
    rw [rckSU_Nlin_apply, rckSU_U]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · simp [rckSU_std, rckSUc_e, Matrix.cons_val_zero]
    · simp [rckSU_std, rckSUc_e, Matrix.cons_val_one]


theorem rckSU_eichler_mem_Q (hk : 4 ≤ k) {e a : Fin k → SUF}
    (he : e ∈ rckSU_U hk) (ha : a ∈ (suH rckSU_suF_card k).perp (rckSU_U hk)) :
    ∃ (c : SUF) (q : SUG k), q ∈ rckSU_Q hk ∧
      ((suH rckSU_suF_card k).β a a = 0 → c = 0) ∧
      ∀ v, natRep (SU SUσ k) q v =
        v + (suH rckSU_suF_card k).β e v • (a + c • e) +
          (suH rckSU_suF_card k).β a v • e := by
  have hee : (suH rckSU_suF_card k).β e e = 0 :=
    ((suH rckSU_suF_card k).mem_perp.mp (rckSU_U_isTotallyIsotropic hk he)) e he
  have hea : (suH rckSU_suF_card k).β e a = 0 :=
    ((suH rckSU_suF_card k).mem_perp.mp ha) e he
  obtain ⟨c, q, hc0, hq⟩ :=
    exists_SU_eichler' (F := SUF) (f := 1) rckSU_suF_card hee hea
  have hc0' : (suH rckSU_suF_card k).β a a = 0 → c = 0 := fun h => hc0 h
  have hq' : ∀ v, natRep (SU SUσ k) q v =
      v + (suH rckSU_suF_card k).β e v • (a + c • e) +
        (suH rckSU_suF_card k).β a v • e := fun v => hq v
  refine ⟨c, q, ?_, hc0', hq'⟩
  change q ∈ rad (suH rckSU_suF_card k) (natRep (SU SUσ k))
    (rckSU_A hk) (rckSU_A_isTotallyIsotropic hk)
  refine mem_rad.mpr ⟨?_, ?_⟩
  · intro w hw
    rw [← rckSU_U_eq_range hk] at hw
    have hew : (suH rckSU_suF_card k).β e w = 0 :=
      ((suH rckSU_suF_card k).mem_perp.mp (rckSU_U_isTotallyIsotropic hk hw)) e he
    have haw : (suH rckSU_suF_card k).β a w = 0 :=
      ReflForm.refl (suH rckSU_suF_card k) w a
        (((suH rckSU_suF_card k).mem_perp.mp ha) w hw)
    rw [hq' w, hew, haw, zero_smul, zero_smul, add_zero, add_zero]
  · intro z hz
    rw [← rckSU_U_eq_range hk] at hz
    have hez : (suH rckSU_suF_card k).β e z = 0 :=
      ((suH rckSU_suF_card k).mem_perp.mp hz) e he
    have hsub : natRep (SU SUσ k) q z - z = (suH rckSU_suF_card k).β a z • e := by
      rw [hq' z, hez, zero_smul, add_zero]
      abel
    rw [hsub]
    rw [← rckSU_U_eq_range hk]
    exact Submodule.smul_mem _ _ he


theorem rckSU_std_ne_zero (hk : 4 ≤ k) (i : Fin k) : rckSU_std (k := k) i ≠ 0 := by
  intro h
  have h1 := congrFun h i
  simp [rckSU_std, Pi.single_eq_same] at h1

theorem rckSU_fixes_std_of_corner (hk : 4 ≤ k) {s : SUG k}
    (hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)))
    (hg1 : rckSUc_g hk (((s : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) = 1) :
    natRep (SU SUσ k) s (rckSU_std (k := k) (sI0 hk)) = rckSU_std (sI0 hk) := by
  set B : Matrix (Fin k) (Fin k) SUF := ((s : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)
  have hGL : (s : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) =
      (suR hk : GL (Fin k) SUF) * (s : GL (Fin k) SUF) :=
    congrArg (fun g : SUG k => (g : GL (Fin k) SUF))
      (Subgroup.mem_centralizer_singleton_iff.mp hsC)
  have hBN := rckSU_survivor_mul_N_of_commute hk (s : GL (Fin k) SUF) hGL
  rw [natRep_apply]
  change B *ᵥ rckSU_std (k := k) (sI0 hk) = rckSU_std (k := k) (sI0 hk)
  rw [show rckSU_std (k := k) (sI0 hk) = Pi.single (rckSUc_e hk 0) (1 : SUF) from rfl,
    Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply]
  by_cases hi0 : i = rckSUc_e hk 0
  · subst hi0
    have h00 : B (rckSUc_e hk 0) (rckSUc_e hk 0) = 1 := by
      have := congrFun (congrFun hg1 0) 0
      simpa [B, rckSUc_g, Matrix.submatrix_apply] using this
    rw [h00]
    simp [Pi.single_eq_same]
  · by_cases hi1 : i = rckSUc_e hk 1
    · subst hi1
      have h10 : B (rckSUc_e hk 1) (rckSUc_e hk 0) = 0 := by
        have := congrFun (congrFun hg1 1) 0
        simpa [B, rckSUc_g, Matrix.submatrix_apply] using this
      rw [h10]
      simp [Pi.single_apply, hi0]
    · rw [(rckSUc_B_col_of_ne hk B hBN i hi0 hi1).1]
      simp [Pi.single_apply, hi0]

theorem rckSU_fixes_std1_of_corner (hk : 4 ≤ k) {s : SUG k}
    (hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)))
    (hg1 : rckSUc_g hk (((s : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) = 1) :
    natRep (SU SUσ k) s (rckSU_std (k := k) (sI1 hk)) = rckSU_std (sI1 hk) := by
  set B : Matrix (Fin k) (Fin k) SUF := ((s : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)
  have hGL : (s : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) =
      (suR hk : GL (Fin k) SUF) * (s : GL (Fin k) SUF) :=
    congrArg (fun g : SUG k => (g : GL (Fin k) SUF))
      (Subgroup.mem_centralizer_singleton_iff.mp hsC)
  have hBN := rckSU_survivor_mul_N_of_commute hk (s : GL (Fin k) SUF) hGL
  rw [natRep_apply]
  change B *ᵥ rckSU_std (k := k) (sI1 hk) = rckSU_std (k := k) (sI1 hk)
  rw [show rckSU_std (k := k) (sI1 hk) = Pi.single (rckSUc_e hk 1) (1 : SUF) from rfl,
    Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply]
  by_cases hi1 : i = rckSUc_e hk 1
  · subst hi1
    have h11 : B (rckSUc_e hk 1) (rckSUc_e hk 1) = 1 := by
      have := congrFun (congrFun hg1 1) 1
      simpa [B, rckSUc_g, Matrix.submatrix_apply] using this
    rw [h11]
    simp [Pi.single_eq_same]
  · by_cases hi0 : i = rckSUc_e hk 0
    · subst hi0
      have h01 : B (rckSUc_e hk 0) (rckSUc_e hk 1) = 0 := by
        have := congrFun (congrFun hg1 0) 1
        simpa [B, rckSUc_g, Matrix.submatrix_apply] using this
      rw [h01]
      simp [Pi.single_apply, hi1]
    · rw [(rckSUc_B_col_of_ne hk B hBN i hi0 hi1).2]
      simp [Pi.single_apply, hi1]

theorem rckSU_fixes_U_of_corner (hk : 4 ≤ k) {s : SUG k}
    (hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)))
    (hg1 : rckSUc_g hk (((s : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) = 1) :
    ∀ u ∈ rckSU_U hk, natRep (SU SUσ k) s u = u := by
  have h0 := rckSU_fixes_std_of_corner hk hsC hg1
  have h1 := rckSU_fixes_std1_of_corner hk hsC hg1
  intro u hu
  change u ∈ Submodule.span SUF {rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)} at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, ih]
  | zero => rw [map_zero]

theorem rckSU_maps_perp (hk : 4 ≤ k) {s : SUG k}
    (hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k))) {z : Fin k → SUF}
    (hz : z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk)) :
    natRep (SU SUσ k) s z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk) := by
  obtain ⟨-, hpres⟩ := rckSU_centralizer_preserves_A hk hsC
  rw [ReflForm.mem_perp]
  intro w hw
  have hw' : natRep (SU SUσ k) s⁻¹ w ∈ rckSU_U hk := by
    rw [rckSU_U_eq_range] at hw ⊢
    exact hpres w hw
  have hiso := isIsometric_natRep_SU SUσ (unitaryInvolution_involutive rckSU_suF_card) k
  have h1 : (suH rckSU_suF_card k).β w (natRep (SU SUσ k) s z) =
      (suH rckSU_suF_card k).β (natRep (SU SUσ k) s⁻¹ w) z := by
    have h2 : (suForm SUσ (unitaryInvolution_involutive rckSU_suF_card) k).β
          (natRep (SU SUσ k) s⁻¹ w) z =
        (suForm SUσ (unitaryInvolution_involutive rckSU_suF_card) k).β w
          (natRep (SU SUσ k) s z) := by
      have hs : natRep (SU SUσ k) s⁻¹ (natRep (SU SUσ k) s z) = z := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have h3 := hiso s⁻¹ w (natRep (SU SUσ k) s z)
      rw [hs] at h3
      exact h3
    exact h2.symm
  rw [h1]
  exact (suH rckSU_suF_card k).mem_perp.mp hz _ hw'

theorem rckSU_suR_fixes_perp (hk : 4 ≤ k) {z : Fin k → SUF}
    (hz : z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk)) :
    natRep (SU SUσ k) (suR hk) z = z := by
  have hz0 : z (rckSUc_e' hk 0) = 0 := by
    have h := (suH rckSU_suF_card k).mem_perp.mp hz (rckSU_std (k := k) (sI0 hk))
      (Submodule.subset_span (by simp))
    rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) z =
        z (Fin.rev (sI0 hk)) from rckSU_suH_std_left (sI0 hk) z] at h
    simpa [rckSUc_e, rckSUc_e'] using h
  have hz1 : z (rckSUc_e' hk 1) = 0 := by
    have h := (suH rckSU_suF_card k).mem_perp.mp hz (rckSU_std (k := k) (sI1 hk))
      (Submodule.subset_span (by simp))
    rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk)) z =
        z (Fin.rev (sI1 hk)) from rckSU_suH_std_left (sI1 hk) z] at h
    simpa [rckSUc_e, rckSUc_e'] using h
  rw [natRep_apply, rckSUc_suR_eq, Matrix.add_mulVec, Matrix.one_mulVec]
  have hNz : rckSUc_N hk *ᵥ z = 0 := by
    rw [rckSUc_N_mulVec, hz1, hz0, zero_smul, zero_smul, add_zero]
  rw [hNz, add_zero]


theorem rckSU_mem_Q_of_coreComm (hk : 4 ≤ k) (V : Subgroup (SUG k))
    (hrV : suR hk ∈ V) (hVab : IsElemAbelian 2 V)
    (hN : ∀ v ∈ V, ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))),
      v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers (suR hk))
    {s : SUG k} (hsV : s ∈ V) :
    s ∈ rckSU_Q hk := by
  classical
  by_cases hs1 : s = 1
  · subst hs1
    exact Subgroup.one_mem _
  have hsC : s ∈ Subgroup.centralizer ({suR hk} : Set (SUG k)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp (hVab.1.is_comm.comm ⟨s, hsV⟩ ⟨suR hk, hrV⟩)
  have hs2 : s ^ 2 = 1 := hVab.2 s hsV
  have hg1 := rckSU_corner_eq_one_of_coreComm hk V hN hsV hsC hs2
  have hfixU := rckSU_fixes_U_of_corner hk hsC hg1
  have hsymm : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2)
  have hsuRord : orderOf (suR hk) = 2 := orderOf_eq_prime (rckSU_suR_sq hk) (suR_ne_one hk)
  have he0 : rckSU_std (k := k) (sI0 hk) ∈ rckSU_U hk :=
    Submodule.subset_span (by simp)
  have hperp : ∀ z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk),
      natRep (SU SUσ k) s z - z ∈ rckSU_U hk := by
    intro z hz
    have hzperp : natRep (SU SUσ k) s z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk) :=
      rckSU_maps_perp hk hsC hz
    have hcoef : ∀ a ∈ (suH rckSU_suF_card k).perp (rckSU_U hk),
        (suH rckSU_suF_card k).β a (natRep (SU SUσ k) s z) =
          (suH rckSU_suF_card k).β a z := by
      intro a ha
      obtain ⟨c, q, hqQ, hc0, hq⟩ := rckSU_eichler_mem_Q hk he0 ha
      have hqO2 : q ∈ pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) :=
        rckSU_Q_le_pCoreOf hk hqQ
      have hmem := hN s hsV q hqO2
      have hqz : natRep (SU SUσ k) q z = z + (suH rckSU_suF_card k).β a z •
          rckSU_std (k := k) (sI0 hk) := by
        have hez : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) z = 0 :=
          (suH rckSU_suF_card k).mem_perp.mp hz _ he0
        rw [hq z, hez, zero_smul, add_zero]
      have hsq : s * q * s⁻¹ = q ∨ s * q * s⁻¹ = suR hk * q := by
        rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsuRord).mp hmem with h1 | hr
        · left
          exact mul_inv_eq_one.mp h1
        · right
          calc s * q * s⁻¹ = (s * q * s⁻¹ * q⁻¹) * q := by group
            _ = suR hk * q := by rw [hr]
      have hL : natRep (SU SUσ k) (s * q * s⁻¹) z =
          z + (suH rckSU_suF_card k).β a (natRep (SU SUσ k) s z) •
            rckSU_std (k := k) (sI0 hk) := by
        rw [map_mul, map_mul]
        simp only [Module.End.mul_apply]
        rw [hsymm]
        rw [hq (natRep (SU SUσ k) s z)]
        have hβe : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk))
            (natRep (SU SUσ k) s z) = 0 := by
          have hiso := isIsometric_natRep_SU SUσ (unitaryInvolution_involutive rckSU_suF_card) k
          have h := hiso s (rckSU_std (k := k) (sI0 hk)) z
          rw [hfixU _ he0] at h
          have h2 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk))
              (natRep (SU SUσ k) s z) =
              (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) z := h
          rw [h2]
          exact (suH rckSU_suF_card k).mem_perp.mp hz _ he0
        rw [hβe, zero_smul, add_zero]
        rw [map_add, map_smul]
        have hss : natRep (SU SUσ k) s (natRep (SU SUσ k) s z) = z := by
          have h2 : s * s = 1 := by simpa [pow_two] using hs2
          rw [← Module.End.mul_apply, ← map_mul, h2, map_one, Module.End.one_apply]
        rw [hss, hfixU _ he0]
      have hqzperp : natRep (SU SUσ k) q z ∈ (suH rckSU_suF_card k).perp (rckSU_U hk) := by
        rw [hqz]
        exact Submodule.add_mem _ hz
          (Submodule.smul_mem _ _ (rckSU_U_isTotallyIsotropic hk he0))
      have hR : natRep (SU SUσ k) (s * q * s⁻¹) z =
          z + (suH rckSU_suF_card k).β a z • rckSU_std (k := k) (sI0 hk) := by
        rcases hsq with h1 | hr
        · rw [h1]; exact hqz
        · rw [hr, map_mul]
          simp only [Module.End.mul_apply]
          rw [rckSU_suR_fixes_perp hk hqzperp, hqz]
      have heq : z + (suH rckSU_suF_card k).β a (natRep (SU SUσ k) s z) •
            rckSU_std (k := k) (sI0 hk) =
          z + (suH rckSU_suF_card k).β a z • rckSU_std (k := k) (sI0 hk) := by
        rw [← hL, hR]
      have hcancel : (suH rckSU_suF_card k).β a (natRep (SU SUσ k) s z) •
            rckSU_std (k := k) (sI0 hk) =
          (suH rckSU_suF_card k).β a z • rckSU_std (k := k) (sI0 hk) :=
        add_left_cancel heq
      have hsub : ((suH rckSU_suF_card k).β a (natRep (SU SUσ k) s z) -
            (suH rckSU_suF_card k).β a z) • rckSU_std (k := k) (sI0 hk) = 0 := by
        rw [sub_smul, hcancel, sub_self]
      rcases smul_eq_zero.mp hsub with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 (rckSU_std_ne_zero hk (sI0 hk))
    have hmem : natRep (SU SUσ k) s z - z ∈
        (suH rckSU_suF_card k).perp ((suH rckSU_suF_card k).perp (rckSU_U hk)) := by
      rw [ReflForm.mem_perp]
      intro a ha
      rw [ReflForm.β_sub_right, hcoef a ha, sub_self]
    rw [ReflForm.perp_perp] at hmem
    exact hmem
  change s ∈ rad (suH rckSU_suF_card k) (natRep (SU SUσ k))
    (rckSU_A hk) (rckSU_A_isTotallyIsotropic hk)
  refine mem_rad.mpr ⟨?_, ?_⟩
  · intro w hw
    rw [← rckSU_U_eq_range] at hw
    exact hfixU w hw
  · intro z hz
    rw [← rckSU_U_eq_range] at hz ⊢
    exact hperp z hz

theorem rckSU_mem_perp_U_iff (hk : 4 ≤ k) (x : Fin k → SUF) :
    x ∈ (suH rckSU_suF_card k).perp (rckSU_U hk) ↔
      x (rckSUc_e' hk 0) = 0 ∧ x (rckSUc_e' hk 1) = 0 := by
  constructor
  · intro hx
    constructor
    · have h0 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) x = 0 :=
        (suH rckSU_suF_card k).mem_perp.mp hx (rckSU_std (k := k) (sI0 hk)) (Submodule.subset_span (by simp))
      rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) x =
          x (Fin.rev (sI0 hk)) from rckSU_suH_std_left (sI0 hk) x] at h0
      simpa [rckSUc_e, rckSUc_e'] using h0
    · have h1 : (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk)) x = 0 :=
        (suH rckSU_suF_card k).mem_perp.mp hx (rckSU_std (k := k) (sI1 hk)) (Submodule.subset_span (by simp))
      rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk)) x =
          x (Fin.rev (sI1 hk)) from rckSU_suH_std_left (sI1 hk) x] at h1
      simpa [rckSUc_e, rckSUc_e'] using h1
  · rintro ⟨h0, h1⟩
    rw [ReflForm.mem_perp]
    intro w hw
    change w ∈ Submodule.span SUF {rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)} at hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI0 hk)) x =
            x (Fin.rev (sI0 hk)) from rckSU_suH_std_left (sI0 hk) x]
        simpa [rckSUc_e, rckSUc_e'] using h0
      · rw [show (suH rckSU_suF_card k).β (rckSU_std (k := k) (sI1 hk)) x =
            x (Fin.rev (sI1 hk)) from rckSU_suH_std_left (sI1 hk) x]
        simpa [rckSUc_e, rckSUc_e'] using h1
    | add a b ha hb iha ihb => rw [ReflForm.add_left, iha, ihb, add_zero]
    | smul c a ha iha => rw [ReflForm.smul_left, iha, mul_zero]
    | zero => rw [ReflForm.β_zero_left]

end CFSG.StandardType.RCKC1
