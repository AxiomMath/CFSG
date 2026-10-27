module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeRep
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeSpInv
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeSpFix
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Walter.W67.CentralExt
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.RankThree.SubgroupLists.SL2Perfect
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.OddSolvableUnitary
open scoped Matrix commutatorElement

theorem exists_isElemAbelian_succ {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.Open.IsElemAbelian 3 K) {k : ℕ} (hKc : Nat.card K = 3 ^ k) {g : G}
    (hg3 : g ^ 3 = 1) (hgK : g ∉ K) (hcomm : ∀ a ∈ K, g * a = a * g) :
    ∃ L : Subgroup G, CFSG.Open.IsElemAbelian 3 L ∧ Nat.card L = 3 ^ (k + 1) ∧
      L ≤ K ⊔ Subgroup.zpowers g := by
  have hg1 : g ≠ 1 := fun h => hgK (h ▸ K.one_mem)
  have hog : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hc : ∀ (a : K) (m : Subgroup.zpowers g),
      Commute (K.subtype a) ((Subgroup.zpowers g).subtype m) := by
    rintro ⟨a, ha⟩ ⟨_, n, rfl⟩
    exact (Commute.zpow_left (hcomm a ha) n).symm
  set f : K × Subgroup.zpowers g →* G := MonoidHom.noncommCoprod K.subtype
    (Subgroup.zpowers g).subtype hc with hf
  have hfapp : ∀ q : K × Subgroup.zpowers g, f q = (q.1 : G) * (q.2 : G) := fun q => rfl
  have hmK : ∀ m ∈ Subgroup.zpowers g, m ∈ K → m = 1 := by
    rintro _ ⟨n, rfl⟩ hn
    have hmod : g ^ n = g ^ (n % 3) := by
      have := zpow_mod_orderOf g n
      rw [hog] at this
      exact this.symm
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with h0 | h1 | h2
    · simp only at hn ⊢
      rw [hmod, h0, zpow_zero]
    · exfalso
      simp only at hn
      rw [hmod, h1, zpow_one] at hn
      exact hgK hn
    · exfalso
      simp only at hn
      rw [hmod, h2] at hn
      have : g = (g ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
          show g ^ (3 : ℤ) = 1 by exact_mod_cast hg3, one_mul]
      exact hgK (this ▸ K.zpow_mem hn 2)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, m⟩ h1
    rw [hfapp] at h1
    have hm : (m : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hm1 : (m : G) = 1 := hmK m m.2 (hm ▸ K.inv_mem a.2)
    have ha1 : (a : G) = 1 := by rw [hm1, mul_one] at h1; exact h1
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hm1)
  have hcommA : ∀ q q' : K × Subgroup.zpowers g, q * q' = q' * q := by
    rintro ⟨a, m⟩ ⟨a', m'⟩
    have := hK.1
    refine Prod.ext (mul_comm' a a') (Subtype.ext ?_)
    obtain ⟨_, n, rfl⟩ := m
    obtain ⟨_, n', rfl⟩ := m'
    change g ^ n * g ^ n' = g ^ n' * g ^ n
    rw [← zpow_add, ← zpow_add, add_comm]
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := x.2
    obtain ⟨q', hq'⟩ := y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← hq, ← hq', ← map_mul, ← map_mul, hcommA]
  · obtain ⟨⟨a, m⟩, rfl⟩ := hy
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hK.2 a a.2)
    have hm3 : m ^ 3 = 1 := by
      obtain ⟨_, n, rfl⟩ := m
      apply Subtype.ext
      change (g ^ n) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    rw [show ((a, m) : K × Subgroup.zpowers g) ^ 3 = (a ^ 3, m ^ 3) from rfl, ha3, hm3]
    exact map_one f
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hKc,
      Nat.card_zpowers, hog, pow_succ]
  · rintro _ ⟨⟨a, m⟩, rfl⟩
    rw [hfapp]
    exact Subgroup.mul_mem_sup a.2 m.2

theorem conj_eq_self_of_card_eq_three {Y : Type*} [Group Y] (hperf : Group.IsPerfect Y)
    {Z : Subgroup Y} [Z.Normal] (hZ : Nat.card Z = 3) (y : Y) {c : Y} (hc : c ∈ Z) :
    y * c * y⁻¹ = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic Z := isCyclic_of_prime_card hZ
  set e := IsCyclic.mulAutMulEquiv Z
  have hφ := perfect_hom_eq_one_of_commute hperf (MulAut.conjNormal : Y →* MulAut Z)
    (fun a _ b _ => e.injective (by rw [map_mul, map_mul, mul_comm]))
  have := congrArg (fun φ : Y →* MulAut Z => ((φ y ⟨c, hc⟩ : Z) : Y)) hφ
  simpa only [MulAut.conjNormal_apply, MonoidHom.one_apply, MulAut.one_apply] using this

theorem conjD_center_eq {Y : Type*} [Group Y] (hperf : Group.IsPerfect Y) {D : Subgroup Y}
    (h : CriticalAt 3 D) (hZ3 : Nat.card (Subgroup.center D) = 3) (y : Y) {c : D}
    (hc : c ∈ Subgroup.center D) : h.conjD y c = c := by
  have : D.Normal := h.normal
  have hcard : Nat.card ((Subgroup.center D).map D.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective, hZ3]
  apply Subtype.ext
  rw [h.conjD_apply]
  exact conj_eq_self_of_card_eq_three hperf hcard y ⟨c, hc, rfl⟩

theorem eq_of_commute_inv {D : Type*} [Group D] (hexp : ∀ d : D, d ^ 3 = 1) {σ τ : MulAut D}
    (hστ : σ * τ = τ * σ) (hσZ : ∀ c ∈ Subgroup.center D, σ c = c)
    (hτZ : ∀ c ∈ Subgroup.center D, τ c = c) (hτ : ∀ d : D, τ d * d ∈ Subgroup.center D)
    {d : D} (hσd : σ d * d⁻¹ ∈ Subgroup.center D) : σ d = d := by
  set c := σ d * d⁻¹ with hc
  set e := τ d * d with he
  have hσ : σ d = c * d := by rw [hc]; group
  have hτd : τ d = e * d⁻¹ := by rw [he]; group
  have heZ : e ∈ Subgroup.center D := hτ d
  clear_value c e
  have h1 : σ (τ d) = τ (σ d) := by
    have := congrArg (fun φ : MulAut D => φ d) hστ
    simpa only [MulAut.mul_apply] using this
  rw [hτd, map_mul, map_inv, hσZ e heZ, hσ, map_mul, hτZ c hσd, hτd] at h1
  have hcc : c * c = 1 := by
    have hcz := Subgroup.mem_center_iff.mp hσd
    have hez := Subgroup.mem_center_iff.mp heZ
    have h2 : e * d⁻¹ * c⁻¹ = e * d⁻¹ * c := by
      calc e * d⁻¹ * c⁻¹ = e * (c * d)⁻¹ := by
            rw [mul_inv_rev, ← mul_assoc]
        _ = c * (e * d⁻¹) := h1
        _ = e * d⁻¹ * c := (hcz (e * d⁻¹)).symm
    have h3 : c⁻¹ = c := mul_left_cancel h2
    calc c * c = c * c⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel c
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hexp c, hcc, inv_one, one_mul]
  rw [hσ, hc1, one_mul]

theorem exists_commute_lift {Y G : Type*} [Group Y] [Group G] (ρ : Y →* G)
    (hker : ∀ u, ρ u = 1 → ∃ k : ℕ, u ^ 3 ^ k = 1) {z : Y} (hz2 : z * z = 1)
    (hzc : ∀ g, ρ z * g = g * ρ z) (hzz : ρ z * ρ z = 1) (y : Y) :
    ∃ c : Y, c * z = z * c ∧ ρ c = ρ y := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set w := y * z * y⁻¹ with hw
  set u := w * z with hu
  have hρu : ρ u = 1 := by
    rw [hu, hw, map_mul, map_mul, map_mul, map_inv, ← hzc (ρ y), mul_inv_cancel_right, hzz]
  obtain ⟨k, hk⟩ := hker u hρu
  set N := 3 ^ k with hN
  have hNodd : N % 2 = 1 := by
    rw [hN, Nat.pow_mod]
    norm_num
  set j := (N + 1) / 2 with hj
  have h2j : 2 * j = N + 1 := by omega
  have hww : w * w = 1 := by
    rw [hw]
    calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have huz : u * z = z * u⁻¹ := by
    rw [hu, mul_inv_rev, hzi, hwi, mul_assoc, hz2, mul_one, ← mul_assoc, hz2, one_mul]
  have hpow : ∀ n : ℕ, u ^ n * z = z * u⁻¹ ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, one_mul, mul_one]
    | succ n ih =>
      rw [pow_succ, mul_assoc, huz, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  set s := u ^ j with hs
  have hszs : s * z * s⁻¹ = w := by
    have h1 : s * z * s⁻¹ = z * u⁻¹ ^ (2 * j) := by
      rw [hs, hpow, mul_assoc, ← inv_pow, two_mul, pow_add]
    have h2 : u⁻¹ ^ (2 * j) = u⁻¹ := by
      rw [h2j, pow_succ, inv_pow, hk, inv_one, one_mul]
    rw [h1, h2]
    calc z * u⁻¹ = u * z := huz.symm
      _ = w * (z * z) := by rw [hu, mul_assoc]
      _ = w := by rw [hz2, mul_one]
  refine ⟨s⁻¹ * y, ?_, ?_⟩
  · have : s⁻¹ * y * z * (s⁻¹ * y)⁻¹ = z := by
      calc s⁻¹ * y * z * (s⁻¹ * y)⁻¹ = s⁻¹ * (y * z * y⁻¹) * s := by group
        _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [← hw, hszs]
        _ = z := by group
    calc s⁻¹ * y * z = s⁻¹ * y * z * (s⁻¹ * y)⁻¹ * (s⁻¹ * y) := by group
      _ = z * (s⁻¹ * y) := by rw [this]
  · rw [map_mul, map_inv, hs, map_pow, hρu, one_pow, inv_one, one_mul]

theorem eq_one_of_mem_commutator_commutator {C G : Type*} [Group C] [Finite C] [Group G]
    (ρ : C →* G) (hker : IsPGroup 3 ρ.ker)
    (hcyc : ∀ P : Subgroup C, IsPGroup 3 P → IsCyclic P) {g : C}
    (hg : g ∈ ⁅commutator C, commutator C⁆) (hρg : ρ g = 1) : g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := ρ.ker with hR
  have hRn : R.Normal := MonoidHom.normal_ker ρ
  have hRc : IsCyclic R := hcyc R hker
  set e := IsCyclic.mulAutMulEquiv R
  have hF : ∀ a ∈ commutator C, ∀ r ∈ R, a * r * a⁻¹ = r := by
    have hle : commutator C ≤ (MulAut.conjNormal : C →* MulAut R).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact e.injective (by rw [map_mul, map_mul, mul_comm])
    intro a ha r hr
    have := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : C)) (MonoidHom.mem_ker.mp (hle ha))
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using this
  set F := commutator C with hFdef
  obtain ⟨P⟩ : Nonempty (Sylow 3 F) := inferInstance
  have hPc : IsMulCommutative (P : Subgroup F) := by
    have hPp : IsPGroup 3 ((P : Subgroup F).map F.subtype) := P.isPGroup'.map _
    have := hcyc _ hPp
    have hcomm : IsMulCommutative ((P : Subgroup F).map F.subtype) := inferInstance
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := hcomm.is_comm.comm ⟨(a : F), ⟨a, a.2, rfl⟩⟩ ⟨(b : F), ⟨b, b.2, rfl⟩⟩
    have h2 : ((a : F) : C) * ((b : F) : C) = ((b : F) : C) * ((a : F) : C) :=
      congrArg Subtype.val h1
    exact Subtype.ext (Subtype.ext h2)
  set Z := R.subgroupOf F with hZdef
  have hZc : Z ≤ Subgroup.center F := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    have := hF a a.2 r hr
    change (a : C) * r = r * a
    calc (a : C) * r = a * r * (a : C)⁻¹ * a := by group
      _ = r * a := by rw [this]
  have hZp : IsPGroup 3 Z := by
    intro r
    obtain ⟨k, hk⟩ := hker ⟨(r : F), r.2⟩
    have h2 : ((r : F) : C) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h2
  have hbot := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup P hPc hZc hZp
  have hg' : g ∈ (commutator F).map F.subtype := by
    rw [Subgroup.map_subtype_commutator]
    exact hg
  obtain ⟨g', hg'c, rfl⟩ := hg'
  have hg'Z : g' ∈ Z := by
    rw [hZdef, Subgroup.mem_subgroupOf]
    exact hρg
  have : g' ∈ Z ⊓ commutator F := ⟨hg'Z, hg'c⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [this]
  rfl

theorem spForm_eq_neg {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    {B : LinearMap.BilinForm (ZMod 3) V} (b : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 3) V)
    (hb : LinearMap.BilinForm.toMatrix b B = Matrix.J (Fin 2) (ZMod 3))
    (x y : Fin 2 ⊕ Fin 2 → ZMod 3) :
    spForm 2 (ZMod 3) x y = -B (b.equivFun.symm x) (b.equivFun.symm y) := by
  rw [← LinearMap.BilinForm.dotProduct_toMatrix_mulVec b B x y, hb, spForm,
    Matrix.toBilin'_apply', ← dotProduct_neg, ← Matrix.neg_mulVec]
  congr 2
  rw [Matrix.J, Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem fromBlocks_eq_neg_J :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) =
      -Matrix.J (Fin 2) (ZMod 3) := by
  rw [Matrix.J, Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem eq_top_of_extraspecial {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    {D : Subgroup Y} (h : CriticalAt 3 D)
    (hC : Subgroup.centralizer (pCore 3 Y : Set Y) ≤ pCore 3 Y)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    (hZ : Subgroup.center D = commutator D) (hZ3 : Nat.card (Subgroup.center D) = 3)
    (hD5 : Nat.card D = 3 ^ 5) : pCore 3 Y = ⊤ := by
  have hne3 : (-1 : ZMod 3) ≠ 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hperf
  by_contra hQ
  have hexpD : ∀ x : D, x ^ 3 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, h.exp x x.2, Subgroup.coe_one])
  let _ : Module (ZMod 3) (Additive (Abelianization D)) :=
    AddCommGroup.zmodModule (nsmul_abelianization_eq_zero hexpD)
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod 3) (Additive (Abelianization D)) := Module.Finite.of_finite
  obtain ⟨ε⟩ := nonempty_center_mulEquiv hZ3
  obtain ⟨B, hBa, hBn, hB⟩ := exists_commForm hZ ε
  have hfixZ : ∀ (y : Y) (c : D), c ∈ Subgroup.center D → h.conjD y c = c :=
    fun y c hc => conjD_center_eq hperf h hZ3 y hc
  have hBinv : ∀ (y : Y) (u v : Additive (Abelianization D)),
      B (abEnd h y u) (abEnd h y v) = B u v := by
    intro y u v
    obtain ⟨u', rfl⟩ : ∃ u', Additive.ofMul u' = u := ⟨Additive.toMul u, rfl⟩
    obtain ⟨v', rfl⟩ : ∃ v', Additive.ofMul v' = v := ⟨Additive.toMul v, rfl⟩
    induction u' using QuotientGroup.induction_on with
    | H x =>
      induction v' using QuotientGroup.induction_on with
      | H x' =>
        change B (abEnd h y (Additive.ofMul (Abelianization.of x)))
            (abEnd h y (Additive.ofMul (Abelianization.of x'))) =
          B (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of x'))
        rw [abEnd_of, abEnd_of, hB, hB]
        congr 2
        apply Subtype.ext
        change ⁅h.conjD y x, h.conjD y x'⁆ = ⁅x, x'⁆
        rw [← map_commutatorElement]
        exact hfixZ y _ (commutatorElement_mem_center hZ x x')
  have hcardV : Nat.card (Additive (Abelianization D)) = 3 ^ 4 := by
    have h1 := card_eq_card_abelianization_mul hZ hZ3
    rw [hD5] at h1
    change Nat.card (Abelianization D) = 3 ^ 4
    norm_num at h1 ⊢
    omega
  have hfin : Module.finrank (ZMod 3) (Additive (Abelianization D)) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive (Abelianization D))
    rw [hcardV, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num)) h1).symm
  obtain ⟨m, b, hb⟩ := hBa.exists_basis_toMatrix_eq_J hBn
  have hm : m = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hfin, Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  have hSp : ∀ y, abMat h b y ∈ StatedSp 2 (ZMod 3) := by
    intro y
    apply Subgroup.subset_closure
    show (↑(abMat h b y) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 *
        (↑(abMat h b y) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) =
      Matrix.fromBlocks 0 1 (-1) 0
    have hcomp := LinearMap.BilinForm.toMatrix_comp b b B (abEnd h y) (abEnd h y)
    have hinv : B.comp (abEnd h y) (abEnd h y) = B := LinearMap.ext₂ fun u v => hBinv y u v
    rw [hinv, hb] at hcomp
    rw [fromBlocks_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, abMat_coe, ← hcomp]
  have hker3 : ∀ y, abMat h b y = 1 → ∃ k : ℕ, y ^ 3 ^ k = 1 := fun y hy =>
    exists_pow_eq_one_of_mem_frattiniKer h hC
      (mem_frattiniKer_of_abEnd_eq_one h ((abMat_eq_one_iff h b y).mp hy))
  have hDker : ∀ y ∈ D, abMat h b y = 1 := fun y hy =>
    (abMat_eq_one_iff h b y).mpr (abEnd_eq_one_of_mem h hy)
  set H := (abMat h b).range with hHdef
  have hHS : H ≤ StatedSp 2 (ZMod 3) := by
    rintro _ ⟨y, rfl⟩
    exact hSp y
  have hHperf : Group.IsPerfect H := Group.IsPerfect.range _
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hQ
    refine top_le_iff.mp (le_sSup ⟨inferInstance, fun y => ?_⟩)
    have hy : abMat h b y = 1 := by
      have : abMat h b y ∈ H := ⟨y, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    obtain ⟨k, hk⟩ := hker3 y hy
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩
  obtain ⟨y₀, hy₀⟩ : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ H :=
    neg_one_mem_of_isPerfect hHS hHperf hHne
  obtain ⟨z, hz2, hzρ⟩ : ∃ z : Y, z * z = 1 ∧ abMat h b z = -1 := by
    obtain ⟨a, m, hm2, hn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 2 (by norm_num)
    have hmodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)
    refine ⟨y₀ ^ m, ?_, ?_⟩
    · have hρ2 : abMat h b ((y₀ ^ m) ^ 2) = 1 := by
        rw [map_pow, map_pow, hy₀, ← pow_mul, Even.neg_one_pow ⟨m, by ring⟩]
      obtain ⟨k, hk⟩ := hker3 _ hρ2
      have h2a : ((y₀ ^ m) ^ 2) ^ 2 ^ a = 1 := by
        rw [← pow_mul, ← pow_mul, show m * (2 * 2 ^ a) = 2 ^ a * m * 2 by ring, pow_mul, ← hn,
          pow_orderOf_eq_one, one_pow]
      have hg := pow_gcd_eq_one.mpr ⟨hk, h2a⟩
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k a (by norm_num)), pow_one] at hg
      rw [← sq]
      exact hg
    · rw [map_pow, hy₀, Odd.neg_one_pow hmodd]
  have hzinv : ∀ x : D, Abelianization.of (h.conjD z x) = (Abelianization.of x)⁻¹ :=
    (abEnd_eq_neg_one_iff h z).mp ((abMat_eq_neg_one_iff h b z).mp hzρ)
  have hτ : ∀ d : D, h.conjD z d * d ∈ Subgroup.center D := by
    intro d
    rw [hZ, ← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, hzinv, inv_mul_cancel]
  have hCz : ∀ d : D, h.conjD z d = d → d ∈ Subgroup.center D := by
    intro d hd
    have h1 := hτ d
    rw [hd] at h1
    have : d = (d * d)⁻¹ := by
      calc d = d ^ 3 * (d * d)⁻¹ := by group
        _ = (d * d)⁻¹ := by rw [hexpD d, one_mul]
    rw [this]
    exact Subgroup.inv_mem _ h1
  have hzc : ∀ g, abMat h b z * g = g * abMat h b z := fun g => by
    rw [hzρ, neg_one_mul, mul_neg_one]
  have hzz : abMat h b z * abMat h b z = 1 := by rw [hzρ, neg_mul_neg, mul_one]
  have hFrat := exists_commute_lift (abMat h b) hker3 hz2 hzc hzz
  have hP : ∃ x : Y, x * z = z * x ∧ x ^ 3 = 1 ∧ x ∉ (Subgroup.center D).map D.subtype := by
    by_contra hnP
    push Not at hnP
    set Cz := Subgroup.centralizer ({z} : Set Y) with hCzdef
    have hcyc : ∀ P : Subgroup Cz, IsPGroup 3 P → IsCyclic P := by
      intro P hP3
      by_contra hnc
      have : Fact (IsPGroup 3 P) := ⟨hP3⟩
      obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := P) (p := 3) (by norm_num) hnc
      have hmem : ∀ s : S, (((s : P) : Cz) : Y) ∈ (Subgroup.center D).map D.subtype := by
        intro s
        refine hnP _ (Subgroup.mem_centralizer_singleton_iff.mp ((s : P) : Cz).2) ?_
        have := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := S) (s : P) s.2
        have h1 := congrArg (fun t : P => ((t : Cz) : Y)) this
        simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h1
      have hle : Nat.card S ≤ Nat.card ((Subgroup.center D).map D.subtype) :=
        Nat.card_le_card_of_injective (fun s => ⟨_, hmem s⟩) fun s s' hss' => by
          have := congrArg Subtype.val hss'
          exact Subtype.ext (Subtype.ext (Subtype.ext this))
      rw [hScard, Subgroup.card_map_of_injective D.subtype_injective, hZ3] at hle
      norm_num at hle
    set ρC := (abMat h b).comp Cz.subtype with hρC
    have hkerC : IsPGroup 3 ρC.ker := by
      intro c
      obtain ⟨k, hk⟩ := hker3 ((c : Cz) : Y) (MonoidHom.mem_ker.mp c.2)
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
    have hrange : ρC.range = H := by
      apply le_antisymm
      · rintro _ ⟨c, rfl⟩
        exact ⟨c, rfl⟩
      · rintro _ ⟨y, rfl⟩
        obtain ⟨c, hcz, hcy⟩ := hFrat y
        exact ⟨⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hcz⟩, hcy⟩
    have hHcomm : ⁅H, H⁆ = H := Subgroup.commutator_eq_self
    have hmap1 : (commutator Cz).map ρC = H := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange,
        hHcomm]
    have hmap2 : (⁅commutator Cz, commutator Cz⁆).map ρC = H := by
      rw [Subgroup.map_commutator, hmap1, hHcomm]
    obtain ⟨h₃, hh₃⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
      (three_dvd_card_of_isPerfect hHS hHperf hHne)
    have hh₃mem : (h₃ : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈
        (⁅commutator Cz, commutator Cz⁆).map ρC := by
      rw [hmap2]
      exact h₃.2
    obtain ⟨g, hg, hgh⟩ := hh₃mem
    have hh3 : h₃ ^ 3 = 1 := by
      have := pow_orderOf_eq_one h₃
      rwa [hh₃] at this
    have hg3 : g ^ 3 = 1 := by
      apply eq_one_of_mem_commutator_commutator ρC hkerC hcyc (Subgroup.pow_mem _ hg 3)
      rw [map_pow, hgh, ← Subgroup.coe_pow, hh3, Subgroup.coe_one]
    have hgZ := hnP (g : Y) (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      (by rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one])
    obtain ⟨c, -, hc⟩ := hgZ
    have h1 : abMat h b (g : Y) = 1 := hDker _ (hc ▸ c.2)
    have h2 : (h₃ : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = 1 := by
      rw [← hgh]
      exact h1
    have h3 : h₃ = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hh₃
    norm_num at hh₃
  obtain ⟨x, hxz, hx3, hxZ⟩ := hP
  have hxρ3 : abMat h b x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨w₁, w₂, hind, hw₁, hw₂, hsp⟩ := exists_fixed_isotropic_pair (hSp x) hxρ3
  set v₁ := b.equivFun.symm w₁ with hv₁
  set v₂ := b.equivFun.symm w₂ with hv₂
  have hfix : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 3,
      (abMat h b x : Matrix _ _ (ZMod 3)) *ᵥ w = w →
        abEnd h x (b.equivFun.symm w) = b.equivFun.symm w := by
    intro w hw
    apply b.equivFun.injective
    rw [← abMat_mulVec, LinearEquiv.apply_symm_apply, hw]
  have hB12 : B v₁ v₂ = 0 := by
    have := spForm_eq_neg b hb w₁ w₂
    rw [hsp] at this
    exact neg_eq_zero.mp this.symm
  have hind' : LinearIndependent (ZMod 3) ![v₁, v₂] := by
    have := hind.map' b.equivFun.symm.toLinearMap (LinearEquiv.ker _)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨d₁, hd₁⟩ : ∃ d : D, Additive.ofMul (Abelianization.of d) = v₁ :=
    ⟨(QuotientGroup.mk_surjective (Additive.toMul v₁)).choose,
      (QuotientGroup.mk_surjective (Additive.toMul v₁)).choose_spec⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : D, Additive.ofMul (Abelianization.of d) = v₂ :=
    ⟨(QuotientGroup.mk_surjective (Additive.toMul v₂)).choose,
      (QuotientGroup.mk_surjective (Additive.toMul v₂)).choose_spec⟩
  have hd12 : d₁ * d₂ = d₂ * d₁ := by
    have h1 := hB d₁ d₂
    rw [hd₁, hd₂, hB12] at h1
    have h2 : ε ⟨⁅d₁, d₂⁆, commutatorElement_mem_center hZ d₁ d₂⟩ = 1 := by
      rw [← toAdd_one, ← Multiplicative.toAdd.injective.eq_iff] at *
      exact h1.symm
    have h3 : ⁅d₁, d₂⁆ = 1 := by
      have := congrArg Subtype.val (ε.injective (h2.trans (map_one ε).symm))
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hστ : h.conjD x * h.conjD z = h.conjD z * h.conjD x := by
    rw [← map_mul, ← map_mul, hxz]
  have hxfix : ∀ d : D, abEnd h x (Additive.ofMul (Abelianization.of d)) =
      Additive.ofMul (Abelianization.of d) → h.conjD x d = d := by
    intro d hd
    refine eq_of_commute_inv hexpD hστ (hfixZ x) (hfixZ z) hτ ?_
    rw [abEnd_of] at hd
    have hd' : Abelianization.of (h.conjD x d) = Abelianization.of d :=
      Additive.ofMul.injective hd
    rw [hZ, ← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hd', mul_inv_cancel]
  have hxd₁ : h.conjD x d₁ = d₁ := hxfix d₁ (by rw [hd₁]; exact hfix w₁ hw₁)
  have hxd₂ : h.conjD x d₂ = d₂ := hxfix d₂ (by rw [hd₂]; exact hfix w₂ hw₂)
  have hxcomm : ∀ d : D, h.conjD x d = d → x * (d : Y) = (d : Y) * x := by
    intro d hd
    have := congrArg Subtype.val hd
    rw [h.conjD_apply] at this
    calc x * (d : Y) = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [this]
  obtain ⟨c₀, hc₀1⟩ : ∃ c₀ : Subgroup.center D, c₀ ≠ 1 := by
    have : Nontrivial (Subgroup.center D) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ3]; norm_num)
    exact exists_ne 1
  have hc₀ : (c₀ : D) ≠ 1 := fun h' => hc₀1 (Subtype.ext h')
  have hc₀Z : (c₀ : D) ∈ Subgroup.center D := c₀.2
  have hc₀c : ∀ d : D, (c₀ : D) * d = d * c₀ := fun d =>
    (Subgroup.mem_center_iff.mp hc₀Z d).symm
  have hK₁ : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (c₀ : D)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨_, n, rfl⟩ := a
      obtain ⟨_, n', rfl⟩ := b
      apply Subtype.ext
      change (c₀ : D) ^ n * (c₀ : D) ^ n' = (c₀ : D) ^ n' * (c₀ : D) ^ n
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := hy
      change ((c₀ : D) ^ n) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hexpD, one_zpow]
  have hK₁c : Nat.card (Subgroup.zpowers (c₀ : D)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexpD _) hc₀, pow_one]
  have hofZ : ∀ d : D, d ∈ Subgroup.center D → Abelianization.of d = 1 := by
    intro d hd
    rw [← MonoidHom.mem_ker, Abelianization.ker_of, ← hZ]
    exact hd
  have hv₁ne : v₁ ≠ 0 := hind'.ne_zero 0
  have hd₁K : d₁ ∉ Subgroup.zpowers (c₀ : D) := by
    intro hmem
    apply hv₁ne
    rw [← hd₁]
    have : d₁ ∈ Subgroup.center D :=
      (Subgroup.zpowers_le.mpr hc₀Z) hmem
    rw [hofZ d₁ this]
    rfl
  obtain ⟨L₂, hL₂, hL₂c, hL₂le⟩ := exists_isElemAbelian_succ hK₁ hK₁c (hexpD d₁) hd₁K
    (fun a ha => by
      obtain ⟨n, rfl⟩ := ha
      exact (Commute.zpow_left (hc₀c d₁) n).symm.eq)
  have hcomm₂ : ∀ a ∈ L₂, d₂ * a = a * d₂ := by
    have hle : Subgroup.zpowers (c₀ : D) ⊔ Subgroup.zpowers d₁ ≤
        Subgroup.centralizer ({d₂} : Set D) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc₀c d₂)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hd12
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hL₂le ha))).symm
  have hd₂L : d₂ ∉ L₂ := by
    intro hmem
    have h1 : Abelianization.of d₂ ∈ Subgroup.zpowers (Abelianization.of d₁) := by
      have h2 := Subgroup.mem_map_of_mem (Abelianization.of : D →* Abelianization D)
        (hL₂le hmem)
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hofZ _ hc₀Z,
        Subgroup.zpowers_one_eq_bot, bot_sup_eq] at h2
      exact h2
    obtain ⟨n, hn⟩ := h1
    have h3 : v₂ = n • v₁ := by
      rw [← hd₁, ← hd₂, ← ofMul_zpow]
      exact congrArg Additive.ofMul hn.symm
    have h4 := LinearIndependent.pair_iff.mp hind' (n : ZMod 3) (-1)
      (by rw [neg_one_smul, Int.cast_smul_eq_zsmul, ← h3, add_neg_cancel])
    exact hne3 h4.2
  obtain ⟨L₃, hL₃, hL₃c, hL₃le⟩ := exists_isElemAbelian_succ hL₂ hL₂c (hexpD d₂) hd₂L hcomm₂
  set K₃ := L₃.map D.subtype with hK₃
  have hK₃e : CFSG.Open.IsElemAbelian 3 K₃ := CFSG.SectionRank.isElemAbelian_map hL₃ D.subtype
  have hK₃c : Nat.card K₃ = 3 ^ 3 := by
    rw [hK₃, Subgroup.card_map_of_injective D.subtype_injective, hL₃c]
  have hxK₃ : x ∉ K₃ := by
    rintro ⟨d, -, hd⟩
    apply hxZ
    have hd' : (d : Y) = x := hd
    have hdx : h.conjD z d = d := by
      apply Subtype.ext
      rw [h.conjD_apply, hd']
      calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [hxz]
        _ = x := by group
    exact ⟨d, hCz d hdx, hd⟩
  have hcommx : ∀ a ∈ K₃, x * a = a * x := by
    have hle : L₃ ≤ (Subgroup.centralizer ({x} : Set Y)).comap D.subtype := by
      refine hL₃le.trans (sup_le (hL₂le.trans (sup_le ?_ ?_)) ?_) <;>
        refine Subgroup.zpowers_le.mpr ?_ <;>
        refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      · exact (hxcomm _ (hfixZ x _ hc₀Z)).symm
      · exact (hxcomm _ hxd₁).symm
      · exact (hxcomm _ hxd₂).symm
    rintro _ ⟨d, hd, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hd)).symm
  obtain ⟨L₄, hL₄, hL₄c, -⟩ := exists_isElemAbelian_succ hK₃e hK₃c hx3 hxK₃ hcommx
  have h4 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : L₄ ≤ ⊤) hL₄ hL₄c
  omega

end CFSG.RankThree.PartTwo.Sec4.Census
