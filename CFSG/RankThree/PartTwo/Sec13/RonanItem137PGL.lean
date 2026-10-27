module

public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanItem137PGL

open CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

abbrev PGL3 (K : Type) [Field K] := ProjGenLinGroup (Fin 3) K

@[expose] noncomputable def dBar {τ : K} (hτ : τ ^ 3 = 1) : PGL3 K :=
  ProjGenLinGroup.mk (Sec4.diagTau hτ)

@[expose] noncomputable def yBar : PGL3 K := ProjGenLinGroup.mk (Sec4.cycThree : GL (Fin 3) K)

@[expose] noncomputable def uBar {τ : K} (hτ0 : τ ≠ 0) : PGL3 K :=
  ProjGenLinGroup.mk (Sec4.diagE (Units.mk0 τ hτ0))

@[expose] noncomputable def sBar : PGL3 K :=
  ProjGenLinGroup.mk (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K)

@[expose] noncomputable def hessian {τ : K} (hτ : τ ^ 3 = 1) : Subgroup (PGL3 K) :=
  Subgroup.zpowers (dBar hτ) ⊔ Subgroup.zpowers (yBar : PGL3 K)

@[expose] noncomputable def sylow0 {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) : Subgroup (PGL3 K) :=
  hessian hτ ⊔ Subgroup.zpowers (uBar hτ0)

private theorem coe_permSwap :
    ((Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  rw [Sec4.Res417Frame.permGL_apply]
  fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]

private theorem coe_inv_cycThree :
    ((Sec4.cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl

private theorem coe_inv_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((((Sec4.diagTau hτ)⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] := rfl

section Relations

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0)

theorem uBar_mul_dBar : uBar hτ0 * dBar hτ = dBar hτ * uBar hτ0 := by
  have hGL : (Sec4.diagE (Units.mk0 τ hτ0) : GL (Fin 3) K) * Sec4.diagTau hτ =
      Sec4.diagTau hτ * Sec4.diagE (Units.mk0 τ hτ0) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Sec4.coe_diagE, Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  unfold uBar dBar
  rw [← map_mul, ← map_mul, hGL]

theorem uBar_conj_yBar : uBar hτ0 * yBar * (uBar hτ0)⁻¹ = dBar hτ * yBar := by
  have h5 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have hGL : (Sec4.diagE (Units.mk0 τ hτ0) : GL (Fin 3) K) * Sec4.cycThree =
      Sec4.diagTau hτ * Sec4.cycThree * Sec4.diagE (Units.mk0 τ hτ0) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Sec4.coe_diagE, Sec4.coe_cycThree,
      Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h5]
  have hPGL : uBar hτ0 * yBar = dBar hτ * yBar * uBar hτ0 := by
    unfold uBar dBar yBar
    rw [← map_mul, ← map_mul, ← map_mul, hGL]
  exact mul_inv_eq_iff_eq_mul.2 hPGL

theorem yBar_mul_dBar : yBar * dBar hτ = dBar hτ * yBar := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    calc τ ^ 2 * τ ^ 2 = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  have h5 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have hGL : Sec4.cycThree * Sec4.diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) *
        (Sec4.diagTau hτ * Sec4.cycThree) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Sec4.coe_scalar_eq_smul, Sec4.coe_cycThree,
      Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h4, h5]
  unfold yBar dBar
  rw [← map_mul, ← map_mul, hGL, map_mul ProjGenLinGroup.mk (GeneralLinearGroup.scalar _ _),
    CFSG.RankThree.PartTwo.Sec13.mk_scalar, one_mul]

theorem sBar_conj_dBar : sBar * dBar hτ * sBar⁻¹ = (dBar hτ)⁻¹ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    calc τ ^ 2 * τ ^ 2 = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  have h5 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have hGL : (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) *
      Sec4.diagTau hτ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) *
        ((Sec4.diagTau hτ)⁻¹ * (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) :
          GL (Fin 3) K)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Sec4.coe_scalar_eq_smul,
      coe_inv_diagTau hτ, coe_permSwap, Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h4, h5]
  have hPGL : sBar * dBar hτ = (dBar hτ)⁻¹ * sBar := by
    unfold sBar dBar
    rw [← map_mul, ← map_inv, ← map_mul, hGL,
      map_mul ProjGenLinGroup.mk (GeneralLinearGroup.scalar _ _),
      CFSG.RankThree.PartTwo.Sec13.mk_scalar, one_mul]
  exact mul_inv_eq_iff_eq_mul.2 hPGL

theorem sBar_conj_yBar : sBar * yBar * sBar⁻¹ = (yBar : PGL3 K)⁻¹ := by
  have hGL : (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) *
      Sec4.cycThree = (Sec4.cycThree⁻¹ : GL (Fin 3) K) *
        (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_permSwap, Sec4.coe_cycThree, coe_inv_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hPGL : (sBar : PGL3 K) * (yBar : PGL3 K) = (yBar : PGL3 K)⁻¹ * (sBar : PGL3 K) := by
    unfold sBar yBar
    rw [← map_inv, ← map_mul, ← map_mul, hGL]
  exact mul_inv_eq_iff_eq_mul.2 hPGL

theorem sBar_conj_uBar : sBar * uBar hτ0 * sBar⁻¹ = uBar hτ0 := by
  have hGL : (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) *
      Sec4.diagE (Units.mk0 τ hτ0) = Sec4.diagE (Units.mk0 τ hτ0) *
        (Sec4.Res417Frame.permGL (Equiv.swap (1 : Fin 3) 2) : GL (Fin 3) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_permSwap, Sec4.coe_diagE]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hPGL : sBar * uBar hτ0 = uBar hτ0 * sBar := by
    unfold sBar uBar
    rw [← map_mul, ← map_mul, hGL]
  exact mul_inv_eq_iff_eq_mul.2 hPGL

end Relations

section Helpers

private theorem diagTau_cube {σ : K} (h : σ ^ 3 = 1) : Sec4.diagTau h ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Sec4.coe_diagTau_eq_diagonal h, diagonal_pow, Units.val_one,
    ← diagonal_one]
  congr 1
  funext i
  have h6 : (σ ^ 2) ^ 3 = 1 := by rw [← pow_mul, pow_mul', h, one_pow]
  fin_cases i <;> simp [h, h6]

private theorem cycThree_cube : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem uBar_cube_of_cube_one {σ : K} (h : σ ^ 3 = 1) (h0 : σ ≠ 0) :
    uBar h0 ^ 3 = 1 := by
  have h3 : Sec4.diagE (Units.mk0 σ h0) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Sec4.coe_diagE, diagonal_pow, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [h]
  rw [uBar, ← map_pow, h3, map_one]

end Helpers

section Orders

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0)

theorem dBar_pow_three : dBar hτ ^ 3 = 1 := by
  rw [dBar, ← map_pow, diagTau_cube hτ, map_one]

theorem yBar_pow_three : (yBar : PGL3 K) ^ 3 = 1 := by
  rw [yBar, ← map_pow, cycThree_cube, map_one]

include hτ in
theorem uBar_pow_three : uBar hτ0 ^ 3 = 1 := uBar_cube_of_cube_one hτ hτ0

theorem dBar_ne_one (hτ1 : τ ≠ 1) : dBar hτ ≠ 1 := by
  intro h1
  have h2 : ProjGenLinGroup.mk (Sec4.diagTau hτ) = 1 := h1
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨t, ht⟩ := h2
  have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [Sec4.coe_scalar_eq_smul, Sec4.coe_diagTau] at e0 e2
  simp at e0 e2
  rw [e2] at e0
  simp at e0
  exact hτ1 e0.symm

private theorem false_of_commute_uBar_yBar {σ : K} (h3 : σ ^ 3 = 1) (h0 : σ ≠ 0) (h1 : σ ≠ 1)
    (hc : Commute (uBar h0) (yBar : PGL3 K)) : False := by
  have h2 : dBar h3 * yBar = 1 * yBar := by
    rw [one_mul, ← uBar_conj_yBar h3 h0, hc.eq, mul_inv_cancel_right]
  exact dBar_ne_one h3 h1 (mul_right_cancel h2)

theorem yBar_not_mem_zpowers_dBar (hτ1 : τ ≠ 1) :
    (yBar : PGL3 K) ∉ Subgroup.zpowers (dBar hτ) := by
  have h0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  intro hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc : Commute (uBar h0) (dBar hτ) := uBar_mul_dBar hτ h0
  have hcz : Commute (uBar h0) (yBar : PGL3 K) := by
    rw [← hi]
    exact hc.zpow_right i
  exact false_of_commute_uBar_yBar hτ h0 hτ1 hcz

theorem uBar_not_mem_hessian (hτ1 : τ ≠ 1) : uBar hτ0 ∉ hessian hτ := by
  intro hmem
  have hle : hessian hτ ≤ Subgroup.centralizer {(yBar : PGL3 K)} := by
    unfold hessian
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact yBar_mul_dBar hτ
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
  have hc := Subgroup.mem_centralizer_iff.mp (hle hmem) yBar (Set.mem_singleton _)
  exact false_of_commute_uBar_yBar hτ hτ0 hτ1 hc.symm

end Orders

section Membership

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
  (hτ0 : τ ≠ 0)

include hK hq in
theorem dBar_mem_slPi : dBar hτ ∈ projImage (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  exact Subgroup.mem_map_of_mem (ProjGenLinGroup.mk : GL (Fin 3) K →* _)
    (Sec4.diagTau_mem_slPi hπ hq' hτ)

include hK in
theorem yBar_mem_slPi : (yBar : PGL3 K) ∈ projImage (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  exact Subgroup.mem_map_of_mem (ProjGenLinGroup.mk : GL (Fin 3) K →* _)
    (Sec4.cycThree_mem_slPi hπ)

include hK in
theorem sBar_mem_slPi : (sBar : PGL3 K) ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨s, hs, hmk⟩ := Sec4.Res424Six.exists_slPi_mk_permGL hK
    (one_mem (glPi π 3 (p ^ f) K)) (Equiv.swap (1 : Fin 3) 2)
  exact Subgroup.mem_map.mpr ⟨s, hs, hmk.trans (by simp [sBar])⟩

include hK hq hτ in
theorem uBar_mem_glPi : uBar hτ0 ∈ projImage (glPi π 3 (p ^ f) K) := by
  have hu : Units.mk0 τ hτ0 ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one]
  have h1 : (1 : Kˣ) ∈ rootsOfUnity (Sec4.qSubPi π (p ^ f)) K := one_mem _
  exact Subgroup.mem_map_of_mem (ProjGenLinGroup.mk : GL (Fin 3) K →* _)
    (Sec4.diagUnits_mem_glPi hK (Sec4.cube_root_mem_qSubPi hq hu) h1 h1)

end Membership

private instance instFinitePGL3 [Finite K] : Finite (PGL3 K) :=
  Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)

section Generic

variable {G : Type*} [Group G]

private theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
  rwa [← mul_left_cancel (mul_right_cancel hyx')]

private theorem mul_comm_of_mem_zpowers {x a z : G} (h : x * a = a * x)
    (hz : z ∈ Subgroup.zpowers a) : x * z = z * x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ((show Commute x a from h).zpow_right i).eq

private theorem exists_conj_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P A B : Subgroup G}
    (hA : IsSylowOf p A P) (hB : IsSylowOf p B P) :
    ∃ g ∈ P, ∀ x, x ∈ A ↔ g⁻¹ * x * g ∈ B := by
  obtain ⟨QA, hQA⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨QB, hQB⟩ := hB.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) QB QA
  refine ⟨g, g.2, fun x => ?_⟩
  have key : ∀ y : ↥P, y ∈ (QA : Subgroup ↥P) ↔ g⁻¹ * y * g ∈ (QB : Subgroup ↥P) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have hxP : x ∈ P := hA.le hx
    have h1 : (⟨x, hxP⟩ : ↥P) ∈ (QA : Subgroup ↥P) := by rw [hQA]; exact hx
    have h2 := (key ⟨x, hxP⟩).mp h1
    rw [hQB] at h2
    exact h2
  · intro hx
    have hxP : x ∈ P := by
      have := P.mul_mem (P.mul_mem g.2 (hB.le hx)) (P.inv_mem g.2)
      simpa [mul_assoc] using this
    have h2 : g⁻¹ * (⟨x, hxP⟩ : ↥P) * g ∈ (QB : Subgroup ↥P) := by rw [hQB]; exact hx
    have h1 := (key ⟨x, hxP⟩).mpr h2
    rw [hQA] at h1
    exact h1

private theorem commutator_le_of_card [Finite G] {S Z : Subgroup G} (hZS : Z ≤ S)
    (hc : ∀ x ∈ S, ∀ z ∈ Z, x * z = z * x) (hZ : Nat.card Z = 3) (hS : Nat.card S = 27) :
    ⁅S, S⁆ ≤ Z := by
  have hSN : S ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hc x hx z hz).symm)
  haveI : (Z.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZS).mpr hSN
  have hZ' : Nat.card (Z.subgroupOf S) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv).trans hZ
  have hQ : Nat.card (↥S ⧸ Z.subgroupOf S) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf S)
    rw [hS, hZ'] at h
    omega
  haveI : IsMulCommutative (↥S ⧸ Z.subgroupOf S) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  have hle : _root_.commutator ↥S ≤ Z.subgroupOf S :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp this
  have htop : (⊤ : Subgroup ↥S).map S.subtype = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (_root_.commutator ↥S).map S.subtype = ⁅S, S⁆ := by
    rw [commutator_def, Subgroup.map_commutator, htop]
  rw [← h1]
  calc (_root_.commutator ↥S).map S.subtype ≤ (Z.subgroupOf S).map S.subtype :=
        Subgroup.map_mono hle
    _ = Z ⊓ S := Subgroup.subgroupOf_map_subtype _ _
    _ ≤ Z := inf_le_left

end Generic

section Group

variable [Finite K] {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) (hτ1 : τ ≠ 1)

private theorem dBar_mem_sylow0 : dBar hτ ∈ sylow0 hτ hτ0 :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

private theorem yBar_mem_sylow0 : (yBar : PGL3 K) ∈ sylow0 hτ hτ0 :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private theorem uBar_mem_sylow0 : uBar hτ0 ∈ sylow0 hτ hτ0 :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

include hτ1 in
theorem card_hessian : Nat.card (hessian hτ) = 9 :=
  Sec4.card_zpowers_sup_zpowers yBar_pow_three
    (orderOf_eq_prime (dBar_pow_three hτ) (dBar_ne_one hτ hτ1))
    (yBar_not_mem_zpowers_dBar hτ hτ1) (yBar_mul_dBar hτ)

theorem uBar_mem_normalizer_hessian :
    uBar hτ0 ∈ Subgroup.normalizer ((hessian hτ : Subgroup (PGL3 K)) : Set (PGL3 K)) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : hessian hτ ≤ (hessian hτ).comap (MulAut.conj (uBar hτ0)).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · show uBar hτ0 * dBar hτ * (uBar hτ0)⁻¹ ∈ hessian hτ
      rw [uBar_mul_dBar hτ hτ0, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · show uBar hτ0 * yBar * (uBar hτ0)⁻¹ ∈ hessian hτ
      rw [uBar_conj_yBar hτ hτ0]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  exact hle hx

include hτ1 in
theorem card_sylow0 : Nat.card (sylow0 hτ hτ0) = 27 := by
  have hu1 : uBar hτ0 ≠ 1 := fun h => uBar_not_mem_hessian hτ hτ0 hτ1 (h ▸ one_mem _)
  have hord : orderOf (uBar hτ0) = 3 := orderOf_eq_prime (uBar_pow_three hτ hτ0) hu1
  have hnorm : Subgroup.zpowers (uBar hτ0) ≤
      Subgroup.normalizer ((hessian hτ : Subgroup (PGL3 K)) : Set (PGL3 K)) :=
    Subgroup.zpowers_le.mpr (uBar_mem_normalizer_hessian hτ hτ0)
  have h := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf hnorm
  have hinf : hessian hτ ⊓ Subgroup.zpowers (uBar hτ0) = ⊥ := by
    have hcard : Nat.card (hessian hτ ⊓ Subgroup.zpowers (uBar hτ0) : Subgroup (PGL3 K)) ∣ 3 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : hessian hτ ⊓ Subgroup.zpowers (uBar hτ0) ≤ Subgroup.zpowers (uBar hτ0))
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : hessian hτ ⊓ Subgroup.zpowers (uBar hτ0) = Subgroup.zpowers (uBar hτ0) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (le_of_eq (by rw [h3, Nat.card_zpowers, hord]))
      have hmem : uBar hτ0 ∈ hessian hτ ⊓ Subgroup.zpowers (uBar hτ0) := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact uBar_not_mem_hessian hτ hτ0 hτ1 hmem.1
  rw [hinf, Subgroup.card_bot, mul_one, card_hessian hτ hτ1, Nat.card_zpowers, hord] at h
  exact h

theorem commute_dBar_of_mem_sylow0 {x : PGL3 K} (hx : x ∈ sylow0 hτ hτ0) :
    x * dBar hτ = dBar hτ * x := by
  have hle : sylow0 hτ hτ0 ≤ Subgroup.centralizer {dBar hτ} := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
      (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (yBar_mul_dBar hτ)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (uBar_mul_dBar hτ hτ0)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

include hτ1 in
theorem commutator_sylow0_le : ⁅sylow0 hτ hτ0, sylow0 hτ hτ0⁆ ≤ Subgroup.zpowers (dBar hτ) :=
  commutator_le_of_card (Subgroup.zpowers_le.mpr (dBar_mem_sylow0 hτ hτ0))
    (fun _ hx _ hz => mul_comm_of_mem_zpowers (commute_dBar_of_mem_sylow0 hτ hτ0 hx) hz)
    (by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (dBar_pow_three hτ) (dBar_ne_one hτ hτ1))
    (card_sylow0 hτ hτ0 hτ1)

theorem sBar_mem_normalizer_sylow0 :
    (sBar : PGL3 K) ∈ Subgroup.normalizer ((sylow0 hτ hτ0 : Subgroup (PGL3 K)) : Set (PGL3 K)) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : sylow0 hτ hτ0 ≤ (sylow0 hτ hτ0).comap (MulAut.conj (sBar : PGL3 K)).toMonoidHom := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
      (Subgroup.zpowers_le.mpr ?_)
    · show (sBar : PGL3 K) * dBar hτ * (sBar : PGL3 K)⁻¹ ∈ sylow0 hτ hτ0
      rw [sBar_conj_dBar hτ]
      exact inv_mem (dBar_mem_sylow0 hτ hτ0)
    · show (sBar : PGL3 K) * yBar * (sBar : PGL3 K)⁻¹ ∈ sylow0 hτ hτ0
      rw [sBar_conj_yBar]
      exact inv_mem (yBar_mem_sylow0 hτ hτ0)
    · show (sBar : PGL3 K) * uBar hτ0 * (sBar : PGL3 K)⁻¹ ∈ sylow0 hτ hτ0
      rw [sBar_conj_uBar hτ0]
      exact uBar_mem_sylow0 hτ hτ0
  exact hle hx

include hτ1 in
theorem sBar_conj_inv_of_mem_commutator {z : PGL3 K} (hz : z ∈ ⁅sylow0 hτ hτ0, sylow0 hτ hτ0⁆) :
    (sBar : PGL3 K) * z * sBar⁻¹ = z⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (commutator_sylow0_le hτ hτ0 hτ1 hz)
  rw [← conj_zpow, sBar_conj_dBar hτ, _root_.inv_zpow]

include hτ1 in
theorem commute_of_mem_commutator_sylow0 {z x : PGL3 K}
    (hz : z ∈ ⁅sylow0 hτ hτ0, sylow0 hτ hτ0⁆) (hx : x ∈ sylow0 hτ hτ0) : x * z = z * x :=
  mul_comm_of_mem_zpowers (commute_dBar_of_mem_sylow0 hτ hτ0 hx)
    (commutator_sylow0_le hτ hτ0 hτ1 hz)

end Group

section Transport

theorem exists_inverting_of_card_twentySeven (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hY : (Nat.card (projImage (glPi π 3 (p ^ f) K))).factorization 3 = 3)
    {S : Subgroup (PGL3 K)} (hSY : S ≤ projImage (glPi π 3 (p ^ f) K)) (hS : Nat.card S = 27) :
    ∃ σ ∈ projImage (slPi π 3 (p ^ f) K), σ ∈ Subgroup.normalizer (S : Set (PGL3 K)) ∧
      (∀ z ∈ ⁅S, S⁆, σ * z * σ⁻¹ = z⁻¹) ∧ (∀ z ∈ ⁅S, S⁆, ∀ x ∈ S, x * z = z * x) := by
  have hπ : π = false → LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  haveI : Finite K := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set P := projImage (glPi π 3 (p ^ f) K)
  have hSL : projImage (slPi π 3 (p ^ f) K) ≤ P := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hS0P : sylow0 hτ hτ0 ≤ P := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
      (Subgroup.zpowers_le.mpr ?_)
    · exact hSL (dBar_mem_slPi hK hq hτ)
    · exact hSL (yBar_mem_slPi hK)
    · exact uBar_mem_glPi hK hq hτ hτ0
  have hSyl : IsSylowOf 3 S P := isSylowOf_of_card hSY (by rw [hS, hY]; norm_num)
  have hSyl0 : IsSylowOf 3 (sylow0 hτ hτ0) P :=
    isSylowOf_of_card hS0P (by rw [card_sylow0 hτ hτ0 hτ1, hY]; norm_num)
  obtain ⟨g, hgP, hgS⟩ := exists_conj_of_isSylowOf hSyl hSyl0
  have hσ : g * sBar * g⁻¹ ∈ projImage (slPi π 3 (p ^ f) K) := by
    obtain ⟨g', hg', rfl⟩ := hgP
    obtain ⟨s', hs', hs'e⟩ := sBar_mem_slPi hK
    have hg'' : g' ∈ glPi π 3 (p ^ f) K := hg'
    obtain ⟨hs'gl, hs'det⟩ := (Sec4.mem_slPi_iff hπ).mp (show s' ∈ slPi π 3 (p ^ f) K from hs')
    refine ⟨g' * s' * g'⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hs'e]⟩
    show g' * s' * g'⁻¹ ∈ slPi π 3 (p ^ f) K
    refine (Sec4.mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hg'' hs'gl) (inv_mem hg''), ?_⟩
    have h1 : GeneralLinearGroup.det (g' * s' * g'⁻¹) = GeneralLinearGroup.det s' := by
      rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det g'), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [← GeneralLinearGroup.val_det_apply, h1, GeneralLinearGroup.val_det_apply]
    exact hs'det
  have hcomm : ∀ z ∈ ⁅S, S⁆, g⁻¹ * z * g ∈ ⁅sylow0 hτ hτ0, sylow0 hτ hτ0⁆ := by
    intro z hz
    have hle : ⁅S, S⁆ ≤ (⁅sylow0 hτ hτ0, sylow0 hτ hτ0⁆).comap (MulAut.conj g⁻¹).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have ha' : (MulAut.conj g⁻¹).toMonoidHom a ∈ sylow0 hτ hτ0 := by
        simpa [MulAut.conj_apply] using (hgS a).mp ha
      have hb' : (MulAut.conj g⁻¹).toMonoidHom b ∈ sylow0 hτ hτ0 := by
        simpa [MulAut.conj_apply] using (hgS b).mp hb
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ha' hb'
    simpa [MulAut.conj_apply] using hle hz
  refine ⟨g * sBar * g⁻¹, hσ, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hn := Subgroup.mem_normalizer_iff.mp (sBar_mem_normalizer_sylow0 hτ hτ0) (g⁻¹ * x * g)
    rw [hgS x, hgS (g * sBar * g⁻¹ * x * (g * sBar * g⁻¹)⁻¹)]
    have e : g⁻¹ * (g * sBar * g⁻¹ * x * (g * sBar * g⁻¹)⁻¹) * g = sBar * (g⁻¹ * x * g) * sBar⁻¹ :=
      by group
    rw [e]
    exact hn
  · intro z hz
    have h7 := sBar_conj_inv_of_mem_commutator hτ hτ0 hτ1 (hcomm z hz)
    calc g * sBar * g⁻¹ * z * (g * sBar * g⁻¹)⁻¹
        = g * (sBar * (g⁻¹ * z * g) * sBar⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g)⁻¹ * g⁻¹ := by rw [h7]
      _ = z⁻¹ := by group
  · intro z hz x hx
    have h8 := commute_of_mem_commutator_sylow0 hτ hτ0 hτ1 (hcomm z hz) ((hgS x).mp hx)
    calc x * z = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h8]
      _ = z * x := by group

end Transport

end CFSG.RankThree.PartTwo.Sec13.RonanItem137PGL
