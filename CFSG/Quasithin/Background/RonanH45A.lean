module

public import CFSG.Quasithin.Background.HFL3Hyp
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH45

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem mem_flag_of_rho_eq (hK : Nat.card K = (2 ^ n) ^ 2)
    {g f : SpecialLinearGroup (Fin 3) K} (hf : f ∈ stabZ K ⊓ stabW K)
    (h : rho hK g = rho hK f) : g ∈ stabZ K ⊓ stabW K := by
  have h1 : rho hK (g * f⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.1
    (mem_scalars_of_rho_eq_one hK h1)
  have hent : ∀ i j, (g : Matrix (Fin 3) (Fin 3) K) i j =
      (c : K) * (f : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    have e : (g : Matrix (Fin 3) (Fin 3) K) =
        ((g * f⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (f : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, hc, Matrix.scalar_apply, Matrix.diagonal_mul]
  obtain ⟨⟨hf10, hf20⟩, ⟨-, hf21⟩⟩ := Subgroup.mem_inf.1 hf
  have h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by rw [hent, hf10, mul_zero]
  have h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by rw [hent, hf20, mul_zero]
  have h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by rw [hent, hf21, mul_zero]
  exact Subgroup.mem_inf.2 ⟨⟨h10, h20⟩, ⟨h20, h21⟩⟩

private theorem flag_le_upperTriangular :
    stabZ K ⊓ stabW K ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 K := by
  intro g hg
  obtain ⟨⟨h10, h20⟩, ⟨-, h21⟩⟩ := Subgroup.mem_inf.1 hg
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_upperTriangular]
  intro i j hji
  fin_cases i <;> fin_cases j <;>
    first | exact h10 | exact h20 | exact h21 | exact absurd hji (by decide)

private theorem coe_pow_apply_self {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 K) (m : ℕ)
    (i : Fin 3) :
    ((g ^ m : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      (g : Matrix (Fin 3) (Fin 3) K) i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Matrix.SpecialLinearGroup.coe_mul,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mul_apply_self_of_isUpperTriangular
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_upperTriangular_iff_isUpperTriangular.1
          ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 K).pow_mem hg m))
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_upperTriangular_iff_isUpperTriangular.1
          hg) i, ih]

private theorem le_unitriangular_of_isPGroup {P : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hP2 : IsPGroup 2 P) (hPflag : ∀ g ∈ P, g ∈ stabZ K ⊓ stabW K) :
    P ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 K := by
  intro g hg
  have hut := flag_le_upperTriangular (hPflag g hg)
  obtain ⟨k, hk⟩ := hP2 ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.2
    ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_upperTriangular.1 hut, fun i => ?_⟩
  apply CFSG.Quasithin.H.L3Nine.eq_one_of_pow_two_pow (k := k)
  rw [← coe_pow_apply_self hut (2 ^ k) i, hk', Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq]

theorem le_img_of_mem_aSet (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK)
    (hC : ∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i)
    {T : Subgroup (MulAut (HMod n K))} (hTM : T ≤ M)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ∈ E3.aSet (2 * n + 1) T) : A ≤ img hK := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  intro a ha
  by_contra haL
  have hAT : A ≤ T := hA.1
  have hAe : IsElemAbelian2 A := hA.2.2.1
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hAe
  have hAN : A ≤ norm hK := (hAT.trans hTM).trans hMN
  have haM : a ∈ M := hTM (hAT ha)
  have ha1 : a ≠ 1 := fun h => haL (by rw [h]; exact Subgroup.one_mem _)
  have hord : orderOf a = 2 := orderOf_eq_prime (hAe.2 a ha) ha1
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 ha
  have hzE : IsElemAbelian2 (Subgroup.zpowers a) :=
    ⟨fun x hx y hy => hAe.1 x (hzA hx) y (hzA hy), fun x hx => hAe.2 x (hzA hx)⟩
  have hzP : IsPGroup 2 (Subgroup.zpowers a) := E3.isPGroup_of_isElemAbelian2 hzE
  have haL' : a ∉ linImg hK := fun h => haL (mem_img_of_isPGroup_zpowers hK h hzP)
  have hcardA : Nat.card A ≤ 2 * Nat.card K :=
    card_le_of_not_le_linImg hn hK hAN hAe ha haL'
  have hsz0 : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    have h := E3.card_eq_two_pow_mul hA2 (bot_le : (⊥ : Subgroup (MulAut (HMod n K))) ≤ A)
    rwa [Subgroup.card_bot, mul_one] at h
  have hsz1 : Nat.card A = 2 ^ E3.mQuot A (Subgroup.zpowers a) * 2 := by
    have h := E3.card_eq_two_pow_mul hA2 hzA
    rwa [Nat.card_zpowers, hord] at h
  have hm0 : 2 * n + 1 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hK2 : 2 * Nat.card K = 2 ^ (2 * n + 1) := by rw [hK]; ring
  have hm1 : E3.mQuot A (Subgroup.zpowers a) < 2 * n + 1 := by
    have h1 : 2 ^ (E3.mQuot A (Subgroup.zpowers a) + 1) ≤ 2 ^ (2 * n + 1) := by
      calc 2 ^ (E3.mQuot A (Subgroup.zpowers a) + 1)
          = 2 ^ E3.mQuot A (Subgroup.zpowers a) * 2 := pow_succ _ _
        _ = Nat.card A := hsz1.symm
        _ ≤ 2 * Nat.card K := hcardA
        _ = 2 ^ (2 * n + 1) := hK2
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega
  have hfix : fixV (Subgroup.zpowers a) = fixV A := hA.2.2.2 _ hzA hm1
  have hAC : A ≤ M ⊓ centSub (fixV (Subgroup.zpowers a)) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hTM (hAT hx), mem_centSub.2 fun u hu => ?_⟩
    rw [hfix] at hu
    exact mem_fixV.1 hu x hx
  rw [hC a haM haL hord] at hAC
  have hle : Nat.card A ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hAC
  rw [Nat.card_zpowers, hord] at hle
  have h8 : 8 ≤ Nat.card A := by
    rw [hsz0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem le_rhoQ2_of_mem_aSet (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {T : Subgroup (MulAut (HMod n K))}
    (hTL : T ⊓ img hK ≤ (stabZ K ⊓ stabW K).map (rho hK))
    {A : Subgroup (MulAut (HMod n K))} (hA : A ∈ E3.aSet (2 * n + 1) T) (hAL : A ≤ img hK) :
    A ≤ (Q2 K).map (rho hK) := by
  haveI : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hAT : A ≤ T := hA.1
  have hAe : IsElemAbelian2 A := hA.2.2.1
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hAe
  obtain ⟨P, hP2, hPmap, hinj⟩ :=
    CFSG.Quasithin.H.L3Nine.exists_lift hK (hAL.trans (img_le_linImg hK)) hA2
  have hPflag : ∀ g ∈ P, g ∈ stabZ K ⊓ stabW K := by
    intro g hg
    have hgA : rho hK g ∈ A := by rw [← hPmap]; exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨f, hf, hfg⟩ := Subgroup.mem_map.1 (hTL (Subgroup.mem_inf.2 ⟨hAT hgA, hAL hgA⟩))
    exact mem_flag_of_rho_eq hK hf hfg.symm
  have hPU : P ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 K :=
    le_unitriangular_of_isPGroup hP2 hPflag
  let f : ↥P →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd
        (((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1)
      map_one' := by
        show Multiplicative.ofAdd _ = 1
        simp
      map_mul' := fun x y => by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
        rw [Subgroup.coe_mul, CFSG.Quasithin.H.L3Nine.uni3_mul_01 (hPU x.2) (hPU y.2),
          ofAdd_add, mul_comm] }
  haveI : Finite (Multiplicative K) := inferInstance
  have hQ : Nat.card (Multiplicative K) ≤ 2 ^ (2 * n) := by
    show Nat.card K ≤ 2 ^ (2 * n)
    rw [hK, ← pow_mul, mul_comm]
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup (SpecialLinearGroup (Fin 3) K),
      B = f.ker.map P.subtype := ⟨_, rfl⟩
  have hBP : B ≤ P := by rw [hBdef]; exact Subgroup.map_subtype_le _
  have hidx : B.relIndex P ≤ 2 ^ (2 * n) := by
    rw [hBdef]; exact CFSG.Quasithin.H.L3Nine.relIndex_ker_le f hQ
  have hBA : B.map (rho hK) ≤ A := by
    rw [← hPmap]; exact Subgroup.map_mono (f := rho hK) hBP
  have hBQ2 : B ≤ Q2 K := by
    rw [hBdef]
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : Multiplicative.ofAdd
        (((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) = 1 :=
      MonoidHom.mem_ker.1 hx
    exact CFSG.Quasithin.H.L3Nine.mem_Q2.2 ⟨hPU x.2, ofAdd_eq_one.1 hx1⟩
  have hmQ : E3.mQuot A (B.map (rho hK)) ≤ 2 * n := by
    have h := CFSG.Quasithin.H.L3Nine.mQuot_map_rho_le hK hBP hinj hidx
    rwa [hPmap] at h
  have hfix : fixV (B.map (rho hK)) = fixV A := hA.2.2.2 _ hBA (by omega)
  have hblk : CFSG.Quasithin.H.L3Nine.blkW n K ≤ fixV A := by
    rw [← CFSG.Quasithin.H.L3Nine.fixV_rhoQ2 hn hK, ← hfix]
    intro v hv
    rw [mem_fixV] at hv ⊢
    exact fun x hx => hv x (Subgroup.map_mono (f := rho hK) hBQ2 hx)
  have hPQ2 : P ≤ Q2 K := by
    intro g hg
    refine CFSG.Quasithin.H.L3Nine.mem_Q2.2 ⟨hPU hg, ?_⟩
    have hgA : rho hK g ∈ A := by rw [← hPmap]; exact Subgroup.mem_map_of_mem _ hg
    have hpt : CFSG.Quasithin.H.L3Nine.pt hK ![0, 1, 0] ∈ fixV A :=
      hblk (CFSG.Quasithin.H.L3Nine.pt_mem_blkW hK (by simp))
    have hfixg : rho hK g (CFSG.Quasithin.H.L3Nine.pt hK ![0, 1, 0]) =
        CFSG.Quasithin.H.L3Nine.pt hK ![0, 1, 0] := mem_fixV.1 hpt _ hgA
    have key : rho hK g (CFSG.Quasithin.H.L3Nine.pt hK ![0, 1, 0]) =
        CFSG.Quasithin.H.L3Nine.pt hK ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) :=
      CFSG.Quasithin.H.L3Nine.rhoT_pt hK (SpecialLinearGroup.toGL g) _
    have h2 := key.symm.trans hfixg
    have h3 := congrArg (fun X : HMod n K => CFSG.Quasithin.H.L3Nine.mat X 0 1) h2
    have hg11 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.1 (hPU hg)).2 1
    simp [CFSG.Quasithin.H.L3Nine.mat_pt, CFSG.Quasithin.H.L3Nine.rk1_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, hg11] at h3
    exact h3
  calc A = P.map (rho hK) := hPmap.symm
    _ ≤ (Q2 K).map (rho hK) := Subgroup.map_mono (f := rho hK) hPQ2

theorem part1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK)
    (hC : ∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i)
    {T : Subgroup (MulAut (HMod n K))} (hTM : T ≤ M)
    (hTL : T ⊓ img hK ≤ (stabZ K ⊓ stabW K).map (rho hK)) :
    ∀ A ∈ E3.aSet (2 * n + 1) T, A ≤ (Q2 K).map (rho hK) := fun A hA =>
  le_rhoQ2_of_mem_aSet hn hK hTL hA (le_img_of_mem_aSet hn hK hMN hC hTM hA)

end CFSG.Quasithin.RonanH45
