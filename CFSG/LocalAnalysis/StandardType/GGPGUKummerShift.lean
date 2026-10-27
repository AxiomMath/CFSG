module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.StandardType.KummerShift

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin
  CFSG.LocalAnalysis.RankThreeUC.S15

theorem exists_shift_fun {m p : ℕ} (hp : p.Prime) {σ : Equiv.Perm (Fin m)} (hσp : σ ^ p = 1)
    (hfix : ∀ i, σ i ≠ i) : ∃ c : Fin m → ZMod p, ∀ j, c (σ j) = c j + 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hσz : σ ^ (p : ℤ) = 1 := by rw [_root_.zpow_natCast, hσp]
  have hdvd : ∀ (y : Fin m) (k : ℤ), (σ ^ k) y = y → (k : ZMod p) = 0 := by
    intro y k hk
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a : ZMod p, a * k = 1 := ⟨(k : ZMod p)⁻¹, inv_mul_cancel₀ hne⟩
    have hdiv : (p : ℤ) ∣ (a.val : ℤ) * k - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, ha, sub_self]
    obtain ⟨j, hj⟩ := hdiv
    have h1 : σ ^ ((a.val : ℤ) * k) = σ := by
      have e : (a.val : ℤ) * k = p * j + 1 := by linarith
      rw [e, _root_.zpow_add, _root_.zpow_mul, hσz, _root_.one_zpow, one_mul, _root_.zpow_one]
    have h2 : (σ ^ ((a.val : ℤ) * k)) y = y := by
      rw [mul_comm, _root_.zpow_mul]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hk _
    rw [h1] at h2
    exact hfix y h2
  let r : Fin m → Fin m := fun x => (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x).out
  have hr : ∀ x, ∃ k : ℤ, (σ ^ k) (r x) = x := fun x =>
    Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid σ) x
  have hrσ : ∀ x, r (σ x) = r x := fun x => by
    simp only [r]
    congr 1
    exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl σ x))
  choose k hk using hr
  refine ⟨fun x => (k x : ZMod p), fun j => ?_⟩
  have h1 : (σ ^ (k (σ j))) (r j) = (σ ^ (1 + k j)) (r j) := by
    have e := hk (σ j)
    rw [hrσ] at e
    rw [e, _root_.zpow_one_add, Equiv.Perm.mul_apply, hk j]
  have h2 : (σ ^ (-(1 + k j) + k (σ j))) (r j) = r j := by
    rw [_root_.zpow_add, Equiv.Perm.mul_apply, h1, _root_.zpow_neg]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have h3 := hdvd _ _ h2
  push_cast at h3
  change (k (σ j) : ZMod p) = (k j : ZMod p) + 1
  linear_combination h3

theorem sum_eq_zero_of_shift {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Equiv.Perm (Fin m)}
    {c : Fin m → ZMod p} (hc : ∀ j, c (σ j) = c j + 1) : ∑ j, c j = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ∑ j, c (σ j) = ∑ j, c j := Equiv.sum_comp σ c
  have h2 : ∑ j, c (σ j) ^ 2 = ∑ j, c j ^ 2 := Equiv.sum_comp σ (fun j => c j ^ 2)
  have e1 : ∑ j, c (σ j) = ∑ j, c j + ∑ _j : Fin m, (1 : ZMod p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hc j
  have e2 : ∑ j, c (σ j) ^ 2 =
      ∑ j, c j ^ 2 + 2 * ∑ j, c j + ∑ _j : Fin m, (1 : ZMod p) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hc j]; ring
  have h3 : (2 : ZMod p) * ∑ j, c j = 0 := by linear_combination h2 - h1 - e2 + e1
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
  exact (mul_eq_zero.mp h3).resolve_left h20

variable {K : Type} [Field K] {n : ℕ}

theorem statedGU_le_primeFormUnitary (h : UnitaryFieldData 2 n K) (m : ℕ) :
    StatedGU m (2 ^ n) K ≤ primeFormUnitary h (idGram K m) := by
  rw [StatedGU, Subgroup.closure_le]
  intro A hA
  change ((A : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * ((1 : GL (Fin m) K) :
    Matrix (Fin m) (Fin m) K) * A = ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  rw [Units.val_one, Matrix.mul_one]
  exact hA

theorem mem_statedGU_of_mem_primeFormUnitary (h : UnitaryFieldData 2 n K) {m : ℕ}
    {A : GL (Fin m) K} (hA : A ∈ primeFormUnitary h (idGram K m)) :
    A ∈ StatedGU m (2 ^ n) K := by
  apply Subgroup.subset_closure
  have e : ((A : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * ((1 : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) * A = ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := hA
  rw [Units.val_one, Matrix.mul_one] at e
  exact e

theorem diagHom_const (m : ℕ) (ζ : Kˣ) :
    SectionRank.OddCover.diagHom m (fun _ => ζ) = GeneralLinearGroup.scalar (Fin m) ζ := by
  apply Units.ext
  rw [SectionRank.OddCover.coe_diagHom, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem exists_unitarySU_conj_eq_scalar_mul [Finite K] (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {m : ℕ} {X : GL (Fin m) K} (hXU : X ∈ primeFormUnitary h (idGram K m)) {b : ℕ}
    (hXb : X ^ p ^ b = 1) {l : Kˣ} (hXp : X ^ p = GeneralLinearGroup.scalar (Fin m) l)
    (hl : ∀ μ : Kˣ, μ ^ p ≠ l) :
    ∃ E ∈ unitarySU 2 n K m, E * X * E⁻¹ = GeneralLinearGroup.scalar (Fin m) ζ * X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : Fintype K := Fintype.ofFinite K
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    apply Units.ext
    ext i
    exact i.elim0
  have hF : Fintype.card K = (2 ^ n) ^ 2 := by
    rw [Fintype.card_eq_nat_card, h.card, ← pow_mul, mul_comm]
  have hXG : X ∈ StatedGU m (2 ^ n) K := mem_statedGU_of_mem_primeFormUnitary h hXU
  have hH : IsPGroup p (Subgroup.zpowers X) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hXb)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨g, hg, hgX⟩ := ACore.exists_conj_monomial_GU hp2 hF hpq hm (Subgroup.zpowers X)
    (Subgroup.zpowers_le.mpr hXG) hH
  obtain ⟨x, hx⟩ := hgX X (Subgroup.mem_zpowers X)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hlP : l ∈ ACore.unitsPPart K p := by
    refine ⟨b, TypeA.PGLTor.scalar_injective (ι := Fin m) ?_⟩
    rw [map_pow, ← hXp, ← pow_mul, mul_comm, pow_mul, hXb, one_pow, map_one]
  have hxp : x ^ p = ACore.monScalar _ m ⟨l, hlP⟩ := by
    apply ACore.monEmb_injective (F := K) (Subgroup.subtype_injective _) m
    rw [map_pow, hx, conj_pow, hXp, ACore.monEmb_monScalar,
      ← (TypeA.PGLTor.commute_scalar l g).eq, mul_inv_cancel_right]
    rfl
  set σ := x.right with hσ
  have hσp : σ ^ p = 1 := by
    have e := congrArg SemidirectProduct.right hxp
    rw [ACore.monScalar_apply, ACore.monT, SemidirectProduct.right_inl] at e
    rw [hσ, ← SemidirectProduct.rightHom_eq_right, ← map_pow, SemidirectProduct.rightHom_eq_right,
      e]
  have hfix : ∀ i, σ i ≠ i := by
    intro i hi
    have hk : ∀ k : ℕ, (x ^ k).left i = x.left i ^ k ∧ (x ^ k).right = σ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, SemidirectProduct.mul_left, SemidirectProduct.mul_right, ih.2, pow_succ,
          pow_succ]
        refine ⟨?_, rfl⟩
        rw [Pi.mul_apply, ih.1, ACore.permAct_apply]
        congr 2
        rw [show (σ ^ k)⁻¹ i = i from Equiv.Perm.inv_eq_iff_eq.mpr
          (Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hi k).symm]
    have e := congrArg (fun y : ACore.Mon (ACore.unitsPPart K p) m => y.left i) hxp
    simp only [ACore.monScalar_apply, ACore.monT, SemidirectProduct.left_inl] at e
    rw [(hk p).1] at e
    apply hl (x.left i : Kˣ)
    have e2 := congrArg Subtype.val e
    rwa [Subgroup.coe_pow] at e2
  obtain ⟨c, hc⟩ := exists_shift_fun hp hσp hfix
  have hsum := sum_eq_zero_of_shift hp hp2 hc
  have hpowval : ∀ a b : ZMod p, ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := fun a b => by
    rw [ZMod.val_add, ← pow_add, ← pow_mod_orderOf ζ (a.val + b.val), ← hζ.eq_orderOf]
  set w : Fin m → Kˣ := fun i => ζ ^ (c i).val with hw
  set u : GL (Fin m) K := SectionRank.OddCover.diagHom m w with hu
  have huG : u ∈ StatedGU m (2 ^ n) K := by
    refine ACore.diagHom_mem_statedGU (by positivity) fun i => ?_
    obtain ⟨j, hj⟩ := hpq
    rw [hw, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hj, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, Units.val_one]
  have hdetu : (u : Matrix (Fin m) (Fin m) K).det = 1 := by
    rw [hu, SectionRank.OddCover.det_diagHom, ← Units.coe_prod, hw,
      Finset.prod_pow_eq_pow_sum, hζ.pow_eq_one_iff_dvd _ |>.mpr, Units.val_one]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact hsum
  set Y : GL (Fin m) K := g * X * g⁻¹ with hY
  set T : Fin m → Kˣ := fun i => (x.left i : Kˣ) with hT
  set P : GL (Fin m) K := ACore.monPermGL m σ with hP
  have hYmon : Y = SectionRank.OddCover.diagHom m T * P := by
    rw [← hx, ACore.monEmb_apply]
    rfl
  have huY : u * Y * u⁻¹ = GeneralLinearGroup.scalar (Fin m) ζ * Y := by
    have e1 : u * (SectionRank.OddCover.diagHom m T * P) * u⁻¹ =
        u * SectionRank.OddCover.diagHom m T * (P * u⁻¹ * P⁻¹) * P := by group
    have e2 : w * T * (w⁻¹ ∘ σ.symm) = (fun _ => ζ) * T := by
      funext i
      have hci : c i = c (σ.symm i) + 1 := by rw [← hc, Equiv.apply_symm_apply]
      simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply, hw]
      rw [hci, hpowval, ZMod.val_one, pow_one, mul_inv_eq_iff_eq_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hYmon, e1, hu, ← map_inv, hP, ACore.monPermGL_conj_diagHom, ← hP, ← map_mul, ← map_mul,
      e2, map_mul, diagHom_const, mul_assoc]
  refine ⟨g⁻¹ * u * g, ?_, ?_⟩
  · rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdetu, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    · have hE : g⁻¹ * u * g ∈ primeFormUnitary h (idGram K m) :=
        statedGU_le_primeFormUnitary h m
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) huG) hg)
      have e : ((((g⁻¹ * u * g : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ *
          ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
          ((g⁻¹ * u * g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
          ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := hE
      rw [Units.val_one, Matrix.mul_one] at e
      exact e
  · have hcom := (TypeA.PGLTor.commute_scalar ζ g⁻¹).eq
    calc g⁻¹ * u * g * X * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * Y * u⁻¹) * g := by rw [hY]; group
      _ = g⁻¹ * GeneralLinearGroup.scalar (Fin m) ζ * Y * g := by rw [huY]; group
      _ = GeneralLinearGroup.scalar (Fin m) ζ * X := by rw [← hcom, hY]; group

end CFSG.StandardType.KummerShift
