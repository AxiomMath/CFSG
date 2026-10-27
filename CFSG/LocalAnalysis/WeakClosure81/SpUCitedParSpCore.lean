module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpStd
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParMulEquiv
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRootEq
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped Pointwise

private theorem spUCited_rank_sub_one_conj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {H : Subgroup (GL ι F)} (g h : ↥H) :
    Matrix.rank (((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) - 1) =
      Matrix.rank (((g : GL ι F) : Matrix ι ι F) - 1) := by
  set A : Matrix ι ι F := ((h : GL ι F) : Matrix ι ι F) with hA
  set B : Matrix ι ι F := ((g : GL ι F) : Matrix ι ι F) with hB
  have hcoe : ((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) = A * B * A⁻¹ := by
    rw [hA, hB, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hAC : A * A⁻¹ = 1 := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hdetA : IsUnit A.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det (h : GL ι F)).isUnit
  have hdetC : IsUnit A⁻¹.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det ((h⁻¹ : ↥H) : GL ι F)).isUnit
  have hsub : A * B * A⁻¹ - 1 = A * (B - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hAC]
  rw [hcoe, hsub, Matrix.rank_mul_eq_left_of_isUnit_det A⁻¹ (A * (B - 1)) hdetC,
    Matrix.rank_mul_eq_right_of_isUnit_det A (B - 1) hdetA]

private theorem spUCited_spEnd_injective_core {k : ℕ} {F : Type} [Field F]
    (g : ↥(StatedSp k F)) : Function.Injective (spEnd g) := by
  intro x y h
  have h1 := congrArg (spEnd g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

private theorem spUCited_flag_one_eq_core {r : ℕ} {K : Type} [Field K] (hr : 2 ≤ r) :
    flag r K 1 = Submodule.span K
      {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} := by
  have hset : (fun j : Fin r =>
        (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) '' {j : Fin r | (j : ℕ) < 1} =
      {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = (⟨0, by omega⟩ : Fin r) := by
        ext
        simp
        omega
      rw [hj0]
    · rintro rfl
      exact ⟨⟨0, by omega⟩, by simp, rfl⟩
  rw [flag, ite_eq_left (by omega), isoFlag, hset]

private theorem spUCited_pointwise_conj {G : Type} [Group G] (S : Subgroup G) (g : G) :
    MulAut.conj g • S = S.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem spUCited_isSymplecticTransvectionIn_conj {k : ℕ} {F : Type} [Field F]
    {g : ↥(StatedSp k F)} (hg : IsSymplecticTransvectionIn k g) (h : ↥(StatedSp k F)) :
    IsSymplecticTransvectionIn k (h * g * h⁻¹) := by
  unfold IsSymplecticTransvectionIn at hg ⊢
  rw [spUCited_rank_sub_one_conj (H := StatedSp k F) g h]
  exact hg

theorem spUCited_exists_rootParabolic_statedSp {k : ℕ} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hk : 2 ≤ k) (R : Subgroup ↥(StatedSp k F))
    (hR : Nat.card R = 2 ^ n) (hRt : ∀ x ∈ R, x ≠ 1 → IsSymplecticTransvectionIn k x)
    {Sy : Subgroup ↥(StatedSp k F)} (hSy : ∃ P : Sylow 2 ↥(StatedSp k F), (P : Subgroup _) = Sy)
    (hRSy : R ≤ Sy) (hSyR : Sy ≤ Subgroup.normalizer (R : Set ↥(StatedSp k F))) :
    ∃ X₂ Pα : Subgroup ↥(StatedSp k F), RootParabolic R Sy X₂ Pα 1 := by
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 ↥(StatedSp k F)) :=
    Finite.of_injective
      (fun P : Sylow 2 ↥(StatedSp k F) => (P : Subgroup ↥(StatedSp k F)))
      (fun P Q h => Sylow.ext h)
  obtain ⟨T, hT⟩ := hSy
  obtain ⟨V, hV⟩ := exists_sylow_unipotent (K := F) 2 k
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSp k F) T V
  let φ : ↥(StatedSp k F) ≃* ↥(StatedSp k F) := MulAut.conj g
  have hφSy : Sy.map φ.toMonoidHom = unipotent k F := by
    have h1 : (↑(g • T) : Subgroup ↥(StatedSp k F)) = Sy.map φ.toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, spUCited_pointwise_conj, hT]
    have h2 : (↑(g • T) : Subgroup ↥(StatedSp k F)) = unipotent k F := by
      rw [hg, hV]
    rw [h1] at h2
    exact h2
  have hR'card : Nat.card (R.map φ.toMonoidHom) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective φ.injective, hR]
  have hR'trans : ∀ x ∈ R.map φ.toMonoidHom, x ≠ 1 → IsSymplecticTransvectionIn k x := by
    intro x hx hx1
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy1 : y ≠ 1 := by
      intro hy1
      exact hx1 (by rw [hy1, map_one])
    change IsSymplecticTransvectionIn k (φ y)
    rw [show (φ : ↥(StatedSp k F) → ↥(StatedSp k F)) y = g * y * g⁻¹ from
      MulAut.conj_apply g y]
    exact spUCited_isSymplecticTransvectionIn_conj (hRt y hy hy1) g
  have hR'U : R.map φ.toMonoidHom ≤ unipotent k F := by
    rw [← hφSy]
    exact Subgroup.map_mono hRSy
  have hUR'N : unipotent k F ≤
      Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup ↥(StatedSp k F)) : Set _) := by
    rw [← hφSy, ← Subgroup.map_equiv_normalizer_eq R φ]
    exact Subgroup.map_mono hSyR
  obtain ⟨a, ha, hRa⟩ :=
    exists_eq_spUFixRootSp (k := k) hF (R.map φ.toMonoidHom) hR'card hR'trans
  have hfix : ∀ u ∈ unipotent k F, spEnd u a = a := by
    intro u hu
    have huN : u ∈ Subgroup.normalizer
        ((R.map φ.toMonoidHom : Subgroup ↥(StatedSp k F)) : Set _) := hUR'N hu
    have hmap : (R.map φ.toMonoidHom).map (MulAut.conj u).toMonoidHom =
        R.map φ.toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
    have hroot : spUFixRootSp (spEnd u a) = spUFixRootSp a := by
      rw [← map_conj_spUFixRootSp u a, ← hRa]
      exact hmap
    have hspne : spEnd u a ≠ 0 := by
      intro h0
      exact ha (spUCited_spEnd_injective_core u (by rw [h0, map_zero]))
    obtain ⟨c, hc⟩ :=
      exists_smul_of_spUFixRootSp_eq (k := k) (F := F) (v := a) (w := spEnd u a)
        ha hspne hroot.symm
    have hU2 : IsPGroup 2 ↥(unipotent k F) := hV ▸ V.isPGroup'
    obtain ⟨m, hm⟩ :=
      hU2.exists_orderOf_eq_pow (⟨u, hu⟩ : ↥(unipotent k F))
    have hu2 : u ^ (2 ^ m) = 1 := by
      have h1 : (⟨u, hu⟩ : ↥(unipotent k F)) ^ (2 ^ m) = 1 := by
        rw [← hm]
        exact pow_orderOf_eq_one _
      simpa using congrArg (Subtype.val) h1
    have hsp : spEnd u ^ (2 ^ m) = 1 := by
      simpa using spEnd_pow (p := 2 ^ m) (x := u) hu2
    have hpow : ∀ t : ℕ, (spEnd u ^ t) a = c ^ t • a := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          rw [pow_succ, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
            mul_comm c (c ^ t)]
    have hcpow : c ^ (2 ^ m) = 1 := by
      have h1 : (spEnd u ^ (2 ^ m)) a = (1 : Module.End F (Fin k ⊕ Fin k → F)) a := by
        rw [hsp]
      rw [hpow (2 ^ m)] at h1
      simp only [Module.End.one_apply] at h1
      have h2 : (c ^ (2 ^ m) - 1) • a = 0 := by
        rw [sub_smul, one_smul, h1, sub_self]
      have h3 : c ^ (2 ^ m) - 1 = 0 := by
        rcases smul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h ha
      exact sub_eq_zero.mp h3
    have hc1 : c = 1 := by
      have hzero : (c - 1) ^ (2 ^ m) = 0 := by
        rw [sub_pow_char_pow (p := 2) (x := c) (y := 1) (n := m), hcpow, one_pow, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
    rw [hc, hc1, one_smul]
  have ha_flag : a ∈ flag k F 1 := by
    change a ∈ (flag k F 1 : Set (Fin k ⊕ Fin k → F))
    rw [← (unitriangular_invariant_isotropic_subspaces (r := k) (K := F)).1]
    intro u hu
    rw [← spEnd_apply]
    exact hfix u hu
  have hspan : a ∈ Submodule.span F
      {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin k)) (1 : F)} := by
    rw [← spUCited_flag_one_eq_core (r := k) (K := F) hk]
    exact ha_flag
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hspan
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    apply ha
    rw [← hc₀, h0, zero_smul]
  have hRa' : R.map φ.toMonoidHom = spUCitedRoot k F ⟨0, by omega⟩ := by
    rw [hRa, ← hc₀, spUFixRootSp_smul hc₀ne]
    rfl
  refine rootParabolic_exists_of_mulEquiv φ ?_
  refine ⟨spUCitedRoot k F ⟨1, by omega⟩, spUCitedPar k F, ?_⟩
  rw [hφSy, hRa']
  exact spUCited_rootParabolic_std (r := k) (K := F) hk

end CFSG.LocalAnalysis.WeakClosure81

end
