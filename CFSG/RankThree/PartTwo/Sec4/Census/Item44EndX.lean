module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndCrit
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndForm
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSymp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement IsMulCommutative

theorem map_eq_one_of_isPerfect {X Y : Type*} [Group X] [Group.IsPerfect X] [Group Y]
    [Group.IsSolvable Y] (f : X →* Y) (x : X) : f x = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsol : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  by_contra h
  have : Nontrivial f.range :=
    ⟨⟨⟨f x, x, rfl⟩, 1, fun e => h (congrArg Subtype.val e)⟩⟩
  exact Group.IsPerfect.not_isSolvable f.range hsol

theorem sq_mem_center_of_comm {P : Type*} [Group P] {z : P} (hz : z ∈ center P)
    (hz2 : z * z = 1) (hc : ∀ x y : P, ⁅x, y⁆ ∈ zpowers z) (x : P) : x * x ∈ center P := by
  rw [mem_center_iff]
  intro g
  set c := ⁅g, x⁆ with hcdef
  have hcen : c ∈ center P := zpowers_le.mpr hz (hc g x)
  have hcc : c * c = 1 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hc g x)
    rw [hcdef, ← hn, ← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
  have hgx : g * x * g⁻¹ = c * x := by
    rw [hcdef, commutatorElement_def]
    group
  have hxc : x * c = c * x := mem_center_iff.mp hcen x
  have hconj : g * (x * x) * g⁻¹ = x * x := by
    calc g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
      _ = c * (x * c) * x := by rw [hgx]; group
      _ = c * c * (x * x) := by rw [hxc]; group
      _ = x * x := by rw [hcc, one_mul]
  calc g * (x * x) = g * (x * x) * g⁻¹ * g := by group
    _ = x * x * g := by rw [hconj]

theorem symm_of_alt {Q : Type*} [Group Q] (b : Q → Q → ZMod 2)
    (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t) (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (hb₃ : ∀ u, b u u = 0) (u v : Q) : b v u = b u v := by
  have h := hb₃ (u * v)
  rw [hb₁, hb₂, hb₂, hb₃, hb₃] at h
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination h - b u v * h2

theorem exists_symplectic_pairs {Q : Type*} [Group Q] [IsElementaryAbelian 2 Q] [Finite Q]
    {w : ℕ} (hcard : Nat.card Q = 2 ^ (2 * w)) (b : Q → Q → ZMod 2)
    (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t) (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (hb₃ : ∀ u, b u u = 0) (hb₄ : ∀ u, (∀ v, b u v = 0) → u = 1) :
    ∃ e f : Fin w → Q, (∀ i j, b (e i) (e j) = 0) ∧ (∀ i j, b (f i) (f j) = 0) ∧
      ∀ i j, b (e i) (f j) = if i = j then 1 else 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := bilinOf b hb₁ hb₂ with hB
  have hBa : B.IsAlt := fun u => hb₃ _
  have hBn : B.Nondegenerate := by
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · have := hb₄ (Additive.toMul u) fun v => hu (Additive.ofMul v)
      exact congrArg Additive.ofMul this
    · have := hb₄ (Additive.toMul v) fun u => by
        rw [symm_of_alt b hb₁ hb₂ hb₃]
        exact hv (Additive.ofMul u)
      exact congrArg Additive.ofMul this
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive Q) = 2 * w := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [show Nat.card (Additive Q) = 2 ^ (2 * w) from hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  obtain ⟨m, bs₀, hbs₀⟩ := hBa.exists_basis_toMatrix_eq_J hBn
  have hm : m = w := by
    have := Module.finrank_eq_card_basis bs₀
    rw [hfin, Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  have hval : ∀ x y, b (Additive.toMul (bs₀ x)) (Additive.toMul (bs₀ y)) =
      Matrix.J (Fin m) (ZMod 2) x y := by
    intro x y
    rw [← hbs₀, LinearMap.BilinForm.toMatrix_apply]
    rfl
  refine ⟨fun i => Additive.toMul (bs₀ (Sum.inl i)), fun i => Additive.toMul (bs₀ (Sum.inr i)),
    fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [hval, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
  · rw [hval, Matrix.J, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · rw [hval, Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> decide

@[expose] noncomputable def quotConj {X : Type*} [Group X] (S : Subgroup X) [S.Normal] :
    X →* MulAut (S ⧸ center S) :=
  quotAut.comp MulAut.conjNormal

theorem quotConj_mk {X : Type*} [Group X] (S : Subgroup X) [S.Normal] (x : X) (s : S) :
    quotConj S x (s : S ⧸ center S) = ((MulAut.conjNormal x s : S) : S ⧸ center S) :=
  quotAut_mk _ _

theorem quotConj_apply {X : Type*} [Group X] (S : Subgroup X) [S.Normal] (x : X) :
    quotConj S x = quotAut (MulAut.conjNormal x : MulAut S) :=
  rfl

structure PairData {X : Type*} [Group X] (z u₁ v₁ u₂ v₂ : X) : Prop where
  sq_u₁ : u₁ * u₁ = 1 ∨ u₁ * u₁ = z
  sq_v₁ : v₁ * v₁ = 1 ∨ v₁ * v₁ = z
  sq_u₂ : u₂ * u₂ = 1 ∨ u₂ * u₂ = z
  sq_v₂ : v₂ * v₂ = 1 ∨ v₂ * v₂ = z
  comm₁ : u₁ * v₁ = z * (v₁ * u₁)
  comm₂ : u₂ * v₂ = z * (v₂ * u₂)
  uu : u₁ * u₂ = u₂ * u₁
  uv : u₁ * v₂ = v₂ * u₁
  vu : v₁ * u₂ = u₂ * v₁
  vv : v₁ * v₂ = v₂ * v₁

@[expose] def PairBound (X : Type*) [Group X] (z₀ : X) : Prop :=
  ∀ u₁ v₁ u₂ v₂ c c' : X, u₁ ∈ pCore 2 X → v₁ ∈ pCore 2 X → u₂ ∈ pCore 2 X →
    v₂ ∈ pCore 2 X → c ∈ pCore 2 X → c' ∈ pCore 2 X → PairData z₀ u₁ v₁ u₂ v₂ →
    (∀ x ∈ ({u₁, v₁, u₂, v₂} : Set X), c * x = x * c) →
    (∀ x ∈ ({u₁, v₁, u₂, v₂} : Set X), c' * x = x * c') → c ^ 4 = 1 ∧ c * c' = c' * c

section Lifts

variable {P : Type*} [Group P] {z : P}

theorem exists_lift_of_sup {E : Subgroup P} (hEZ : E ⊔ center P = ⊤) (q : P ⧸ center P) :
    ∃ e ∈ E, (e : P ⧸ center P) = q := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  have hs : s ∈ E ⊔ center P := by rw [hEZ]; exact mem_top s
  obtain ⟨e, he, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hs
  refine ⟨e, he, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hc

theorem sq_eq_of_mem (h : CommData P z) {E : Subgroup P} (hEZ' : E ⊓ center P = zpowers z)
    {e : P} (he : e ∈ E) : e * e = 1 ∨ e * e = z := by
  have : e * e ∈ E ⊓ center P := ⟨mul_mem he he, h.sq_mem e⟩
  rw [hEZ'] at this
  exact h.mem_zpowers_iff.mp this

theorem mul_eq_of_commB_eq_one (h : CommData P z) (ε : zpowers z ≃* Multiplicative (ZMod 2))
    {x y : P} (hxy : commB h ε x y = 1) : x * y = z * (y * x) := by
  have hne : ⁅x, y⁆ ≠ 1 := fun h1 => by
    rw [commB_mk, (commVal_eq_zero_iff h ε x y).mpr h1] at hxy
    exact absurd hxy (by decide)
  rcases h.mem_zpowers_iff.mp (h.comm_mem x y) with h1 | h1
  · exact absurd h1 hne
  · rw [commutatorElement_def] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = z * (y * x) := by rw [h1]

theorem mul_comm_of_commB_eq_zero (h : CommData P z) (ε : zpowers z ≃* Multiplicative (ZMod 2))
    {x y : P} (hxy : commB h ε x y = 0) : x * y = y * x := by
  rw [commB_mk, commVal_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm] at hxy
  exact hxy

theorem exists_lift_sq_eq (h : CommData P z) {E : Subgroup P} (hEZ : E ⊔ center P = ⊤)
    (hEZ' : E ⊓ center P = zpowers z) {i : P} (hi : i ∈ center P) (hii : i * i = z)
    (q : P ⧸ center P) : ∃ x : P, (x : P ⧸ center P) = q ∧ x * x = z := by
  obtain ⟨e, he, rfl⟩ := exists_lift_of_sup hEZ q
  rcases sq_eq_of_mem h hEZ' he with h1 | h1
  · refine ⟨e * i, ?_, ?_⟩
    · rw [QuotientGroup.eq]
      simpa using inv_mem hi
    · have hc := mem_center_iff.mp hi e
      calc e * i * (e * i) = e * (i * e) * i := by group
        _ = e * e * (i * i) := by rw [← hc]; group
        _ = z := by rw [h1, hii, one_mul]
  · exact ⟨e, rfl, h1⟩

end Lifts

section Core

variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
  [IsSimpleGroup (X ⧸ K)]

omit [Finite X] [Group.IsPerfect X] in
include K in
theorem nontrivial_of_simple : Nontrivial X :=
  (QuotientGroup.mk'_surjective K).nontrivial

include K in
theorem pCore_two_ne_top : pCore 2 X ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial X := nontrivial_of_simple (K := K)
  intro h
  have h2 : IsPGroup 2 X := fun x => by
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 X)) ⟨x, by rw [h]; exact mem_top x⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact Group.IsPerfect.not_isNilpotent X h2.isNilpotent

theorem not_pCore_two_le_center (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) : ¬ pCore 2 X ≤ center X := by
  intro h
  apply pCore_two_ne_top (K := K)
  refine eq_top_iff.mpr fun x _ => centralizer_pCore_two_le hK hO hq
    (mem_centralizer_iff.mpr fun s hs => ?_)
  exact (mem_center_iff.mp (h hs) x).symm

omit [Finite X] [Group.IsPerfect X] in
theorem mem_pCore_two_of_mem_center {z₀ : X} (hz₀ : z₀ ∈ center X) (hz₀2 : z₀ * z₀ = 1) :
    z₀ ∈ pCore 2 X := by
  have hn : (zpowers z₀).Normal := normal_of_le_center (zpowers_le.mpr hz₀)
  have h2 : IsPGroup 2 (zpowers z₀) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hz₀2, one_zpow]
  exact (le_sSup ⟨hn, h2⟩ : zpowers z₀ ≤ pCore 2 X) (mem_zpowers z₀)

omit [Finite X] [Group.IsPerfect X] in
theorem map_le_center_of_characteristic
    (H1 : ∀ A : Subgroup X, A.Normal → IsPGroup 2 A → IsMulCommutative A → A ≤ center X)
    {A : Subgroup (pCore 2 X)} (hA : A.Characteristic) (hAc : IsMulCommutative A) :
    A.map (pCore 2 X).subtype ≤ center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (A.map (pCore 2 X).subtype).Normal := inferInstance
  exact H1 _ hn (((pCore_isPGroup : IsPGroup 2 (pCore 2 X)).to_subgroup A).map _) inferInstance

theorem structure_pCore_two (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) {z₀ : X} (hz₀ : z₀ ∈ center X) (hz₀1 : z₀ ≠ 1)
    (hz₀2 : z₀ * z₀ = 1)
    (H1 : ∀ A : Subgroup X, A.Normal → IsPGroup 2 A → IsMulCommutative A → A ≤ center X)
    (H2 : ∀ t ∈ center X, t * t = 1 → t = 1 ∨ t = z₀) :
    ∃ hz : z₀ ∈ pCore 2 X, CommData (pCore 2 X) ⟨z₀, hz⟩ ∧ IsCyclic (center (pCore 2 X)) ∧
      (∀ c ∈ center (pCore 2 X), (c : X) ∈ center X) ∧
      (∃ E : Subgroup (pCore 2 X), E ⊔ center (pCore 2 X) = ⊤ ∧
        E ⊓ center (pCore 2 X) = zpowers ⟨z₀, hz⟩) ∧
      ∃ w : ℕ, 1 ≤ w ∧ Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 2 ^ (2 * w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSn : (pCore 2 X).Normal := inferInstance
  have hS2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hz := mem_pCore_two_of_mem_center hz₀ hz₀2
  set z : pCore 2 X := ⟨z₀, hz⟩ with hzdef
  have hcenX : ∀ A : Subgroup (pCore 2 X), A.Characteristic → IsMulCommutative A →
      A.map (pCore 2 X).subtype ≤ center X := fun A hA hAc =>
    map_le_center_of_characteristic H1 hA hAc
  have hcenS : ∀ A : Subgroup (pCore 2 X), A.Characteristic → IsMulCommutative A →
      A ≤ center (pCore 2 X) := by
    intro A hA hAc a ha
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hcenX A hA hAc ⟨a, ha, rfl⟩) g)
  have hsymp : ∀ A : Subgroup (pCore 2 X), A.Characteristic → IsMulCommutative A →
      IsCyclic A := by
    intro A hA hAc
    have key : ∀ u : A, u * u = 1 → u ≠ 1 → ((u : pCore 2 X) : X) = z₀ := by
      intro u hu hu1
      have hc : ((u : pCore 2 X) : X) ∈ center X := hcenX A hA hAc ⟨u, u.2, rfl⟩
      have hu' : ((u : pCore 2 X) : X) * ((u : pCore 2 X) : X) = 1 := by
        have := congrArg (fun v : A => ((v : pCore 2 X) : X)) hu
        simpa using this
      rcases H2 _ hc hu' with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hu1
      · exact h
    exact isCyclic_of_unique_involution (hS2.to_subgroup A) fun s t hs ht hs1 ht1 =>
      Subtype.ext (Subtype.ext ((key s hs hs1).trans (key t ht ht1).symm))
  have hnt : Nontrivial (pCore 2 X) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply not_pCore_two_le_center hK hO hq
    intro s hs
    have : (⟨s, hs⟩ : pCore 2 X) = 1 := Subsingleton.elim _ _
    rw [show s = 1 from congrArg Subtype.val this]
    exact one_mem _
  have hzc : z ∈ center (pCore 2 X) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hz₀ g)
  have hzord : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      exact Subtype.ext hz₀2
    · intro h
      exact hz₀1 (congrArg Subtype.val h)
  have hZX : ∀ c ∈ center (pCore 2 X), (c : X) ∈ center X := fun c hc =>
    hcenX _ inferInstance inferInstance ⟨c, hc, rfl⟩
  rcases structure_of_central hS2 hsymp hcenS with hcyc |
      ⟨z', -, -, hz'u, hcomm, E, hEZ, hEZ', w, hw1, hcard⟩
  · exfalso
    exact not_pCore_two_le_center hK hO hq (H1 _ hSn hS2 inferInstance)
  · have hzz : z' = z := (hz'u z hzc hzord).symm
    rw [hzz] at hcomm hEZ'
    have hcd : CommData (pCore 2 X) z :=
      { mem_center := hzc
        sq_eq_one := Subtype.ext hz₀2
        ne_one := fun h => hz₀1 (congrArg Subtype.val h)
        comm_mem := hcomm
        sq_mem := sq_mem_center_of_comm hzc (Subtype.ext hz₀2) hcomm }
    exact ⟨hz, hcd, hsymp _ inferInstance inferInstance, hZX, ⟨E, hEZ, hEZ'⟩, w, hw1, hcard⟩

theorem ker_quotConj_le (hK : Group.IsSolvable K) (hO : oddCore X = ⊥) (hq : ¬ IsQuasisimple X)
    (hZ : ∀ c ∈ center (pCore 2 X), (c : X) ∈ center X) :
    (quotConj (pCore 2 X)).ker ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSn : (pCore 2 X).Normal := inferInstance
  have hS2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hCS := centralizer_pCore_two_le hK hO hq
  set C := (quotConj (pCore 2 X)).ker with hCdef
  have hCn : C.Normal := MonoidHom.normal_ker _
  have hcen : ∀ g ∈ C, Odd (orderOf g) → g ∈ centralizer (pCore 2 X : Set X) := by
    intro g hg hodd
    rw [mem_centralizer_iff]
    intro s hs
    have hζS : s⁻¹ * (g * s * g⁻¹) ∈ pCore 2 X := mul_mem (inv_mem hs) (hSn.conj_mem s hs g)
    have hζ : s⁻¹ * (g * s * g⁻¹) ∈ center X := by
      have h1 := congrArg (fun σ : MulAut (pCore 2 X ⧸ center (pCore 2 X)) =>
        σ ((⟨s, hs⟩ : pCore 2 X) : pCore 2 X ⧸ center (pCore 2 X))) (MonoidHom.mem_ker.mp hg)
      simp only [quotConj_mk, MulAut.one_apply] at h1
      exact hZ _ (QuotientGroup.eq.mp h1.symm)
    set ζ := s⁻¹ * (g * s * g⁻¹) with hζdef
    have hgs : g * s * g⁻¹ = s * ζ := by
      rw [hζdef]
      group
    have hpow : ∀ n : ℕ, g ^ n * s * (g ^ n)⁻¹ = s * ζ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hc : g * ζ ^ n * g⁻¹ = ζ ^ n := by
          rw [mem_center_iff.mp (pow_mem hζ n) g]
          group
        calc g ^ (n + 1) * s * (g ^ (n + 1))⁻¹ = g * (g ^ n * s * (g ^ n)⁻¹) * g⁻¹ := by group
          _ = (g * s * g⁻¹) * (g * ζ ^ n * g⁻¹) := by rw [ih]; group
          _ = s * ζ ^ (n + 1) := by rw [hgs, hc, pow_succ', mul_assoc]
    have hζ1 : ζ ^ orderOf g = 1 := by
      have h := hpow (orderOf g)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
      calc ζ ^ orderOf g = s⁻¹ * (s * ζ ^ orderOf g) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hS2 ⟨ζ, hζS⟩
    have hk' : ζ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hζ1' : ζ = 1 := by
      have h1 : orderOf ζ ∣ orderOf g := orderOf_dvd_of_pow_eq_one hζ1
      have h2 : orderOf ζ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    rw [hζ1', mul_one] at hgs
    calc s * g = g * s * g⁻¹ * g := by rw [hgs]
      _ = g * s := by group
  have hodd : ∀ g ∈ C, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf g = r → False := by
    intro g hg r hr hr2 hgr
    have hgS := hCS (hcen g hg (hgr ▸ hr.odd_of_ne_two hr2))
    obtain ⟨k, hk⟩ := hS2 ⟨g, hgS⟩
    have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : r ∣ 2 ^ k := hgr ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
  have hC2 : IsPGroup 2 C := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos).ne' fun {r} hr hrC => ?_⟩
    by_contra hr2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) r hrC
    exact hodd c c.2 r hr hr2 (by rw [Subgroup.orderOf_coe]; exact hc)
  exact le_sSup ⟨hCn, hC2⟩

include K in
theorem eq_two_of_pairBound {z₀ : X} (hz : z₀ ∈ pCore 2 X)
    (h : CommData (pCore 2 X) ⟨z₀, hz⟩) {E : Subgroup (pCore 2 X)}
    (hEZ : E ⊔ center (pCore 2 X) = ⊤) (hEZ' : E ⊓ center (pCore 2 X) = zpowers ⟨z₀, hz⟩)
    {w : ℕ} (hcard : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 2 ^ (2 * w))
    (hC2 : (quotConj (pCore 2 X)).ker ≤ pCore 2 X) (H3 : PairBound X z₀) :
    w = 2 ∧ ∀ c ∈ center (pCore 2 X), c ^ 4 = 1 := by
  set z : pCore 2 X := ⟨z₀, hz⟩ with hzdef
  have : IsElementaryAbelian 2 (pCore 2 X ⧸ center (pCore 2 X)) := isElementaryAbelian_quot h
  obtain ⟨ε⟩ := h.nonempty_mulEquiv
  set b := commB h ε with hbdef
  have hlift := exists_lift_of_sup hEZ
  have hsq : ∀ e ∈ E, e * e = 1 ∨ e * e = z := fun e he => sq_eq_of_mem h hEZ' he
  have hrel1 : ∀ x y : pCore 2 X, b x y = 1 → x * y = z * (y * x) := fun x y hxy =>
    mul_eq_of_commB_eq_one h ε hxy
  have hrel0 : ∀ x y : pCore 2 X, b x y = 0 → x * y = y * x := fun x y hxy =>
    mul_comm_of_commB_eq_zero h ε hxy
  have hsymm := symm_of_alt b (commB_mul_left h ε) (commB_mul_right h ε) (commB_self h ε)
  obtain ⟨e, f, hee, hff, hef⟩ := exists_symplectic_pairs hcard b (commB_mul_left h ε)
    (commB_mul_right h ε) (commB_self h ε) (eq_one_of_commB h ε)
  choose eL heLE heL using fun i => hlift (e i)
  choose fL hfLE hfL using fun i => hlift (f i)
  have hEE : ∀ i j, eL i * eL j = eL j * eL i := fun i j =>
    hrel0 _ _ (by rw [heL, heL]; exact hee i j)
  have hFF : ∀ i j, fL i * fL j = fL j * fL i := fun i j =>
    hrel0 _ _ (by rw [hfL, hfL]; exact hff i j)
  have hEF : ∀ i j, i ≠ j → eL i * fL j = fL j * eL i := fun i j hij =>
    hrel0 _ _ (by rw [heL, hfL, hef]; simp [hij])
  have hFE : ∀ i j, i ≠ j → fL i * eL j = eL j * fL i := fun i j hij =>
    hrel0 _ _ (by rw [heL, hfL, hsymm, hef]; simp [Ne.symm hij])
  have hEF1 : ∀ i, eL i * fL i = z * (fL i * eL i) := fun i =>
    hrel1 _ _ (by rw [heL, hfL, hef]; simp)
  have hcoe : ∀ x y : pCore 2 X, x * y = y * x → (x : X) * y = y * x := fun x y hxy =>
    congrArg Subtype.val hxy
  have hsqX : ∀ i, ((eL i : X) * eL i = 1 ∨ (eL i : X) * eL i = z₀) ∧
      ((fL i : X) * fL i = 1 ∨ (fL i : X) * fL i = z₀) := fun i =>
    ⟨(hsq _ (heLE i)).imp (congrArg Subtype.val) (congrArg Subtype.val),
      (hsq _ (hfLE i)).imp (congrArg Subtype.val) (congrArg Subtype.val)⟩
  have hw2 : 2 ≤ w := by
    by_contra hlt
    have hcard4 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) ≤ 4 := by
      rw [hcard]
      interval_cases w <;> norm_num
    have : Group.IsSolvable (Equiv.Perm (pCore 2 X ⧸ center (pCore 2 X))) :=
      Equiv.Perm.isSolvable hcard4
    apply pCore_two_ne_top (K := K)
    refine eq_top_iff.mpr fun x _ => hC2 (MonoidHom.mem_ker.mpr ?_)
    have h1 := map_eq_one_of_isPerfect ((MulAut.toPerm _).comp (quotConj (pCore 2 X))) x
    ext q
    exact congrArg (fun π : Equiv.Perm _ => π q) h1
  set i₀ : Fin w := ⟨0, by omega⟩
  set i₁ : Fin w := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h' => by simpa [i₀, i₁] using congrArg Fin.val h'
  have hpd : PairData z₀ (eL i₀ : X) (fL i₀) (eL i₁) (fL i₁) :=
    { sq_u₁ := (hsqX i₀).1
      sq_v₁ := (hsqX i₀).2
      sq_u₂ := (hsqX i₁).1
      sq_v₂ := (hsqX i₁).2
      comm₁ := congrArg Subtype.val (hEF1 i₀)
      comm₂ := congrArg Subtype.val (hEF1 i₁)
      uu := hcoe _ _ (hEE i₀ i₁)
      uv := hcoe _ _ (hEF i₀ i₁ h01)
      vu := hcoe _ _ (hFE i₀ i₁ h01)
      vv := hcoe _ _ (hFF i₀ i₁) }
  have hmem : ∀ x : pCore 2 X, (x : X) ∈ pCore 2 X := fun x => x.2
  set T : Set X := {(eL i₀ : X), (fL i₀ : X), (eL i₁ : X), (fL i₁ : X)} with hT
  refine ⟨?_, fun c hc => ?_⟩
  ·
    by_contra hne
    set i₂ : Fin w := ⟨2, by omega⟩
    have h02 : i₀ ≠ i₂ := fun h' => by simpa [i₀, i₂] using congrArg Fin.val h'
    have h12 : i₁ ≠ i₂ := fun h' => by simpa [i₁, i₂] using congrArg Fin.val h'
    have hcu : ∀ x ∈ T, (eL i₂ : X) * x = x * eL i₂ := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact hcoe _ _ (hEE i₂ i₀)
      · exact hcoe _ _ (hEF i₂ i₀ h02.symm)
      · exact hcoe _ _ (hEE i₂ i₁)
      · exact hcoe _ _ (hEF i₂ i₁ h12.symm)
    have hcv : ∀ x ∈ T, (fL i₂ : X) * x = x * fL i₂ := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact hcoe _ _ (hFE i₂ i₀ h02.symm)
      · exact hcoe _ _ (hFF i₂ i₀)
      · exact hcoe _ _ (hFE i₂ i₁ h12.symm)
      · exact hcoe _ _ (hFF i₂ i₁)
    have hc := (H3 _ _ _ _ _ _ (hmem _) (hmem _) (hmem _) (hmem _) (hmem _) (hmem _) hpd hcu
      hcv).2
    have h2 := congrArg Subtype.val (hEF1 i₂)
    simp only [Subgroup.coe_mul] at h2
    rw [hc] at h2
    apply h.ne_one
    apply Subtype.ext
    change z₀ = 1
    calc z₀ = z₀ * ((fL i₂ : X) * eL i₂) * ((fL i₂ : X) * eL i₂)⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  ·
    have hcx : ∀ x ∈ T, (c : X) * x = x * c := by
      have hcS : ∀ y : pCore 2 X, (c : X) * y = y * c := fun y =>
        (congrArg Subtype.val (mem_center_iff.mp hc y)).symm
      rintro x (rfl | rfl | rfl | rfl) <;> exact hcS _
    have h4 := (H3 _ _ _ _ _ _ (hmem _) (hmem _) (hmem _) (hmem _) (hmem c) (hmem c) hpd hcx
      hcx).1
    exact Subtype.ext (by simpa using h4)

end Core

end CFSG.RankThree.PartTwo.Sec4.Census
