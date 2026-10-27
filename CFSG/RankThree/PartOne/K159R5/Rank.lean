module

public import CFSG.RankThree.PartOne.S15K.L0cCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartOne.K159R5

open CFSG CFSG.RankThree.PartOne.S15K
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

@[expose] def SylAb (p : ℕ) (Y : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ Y → IsPGroup p ↥P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x

@[expose] def MaxEA (p : ℕ) (Y P : Subgroup G) : Prop :=
  P ≤ Y ∧ IsElementaryAbelian p ↥P ∧
    ∀ P' : Subgroup G, P ≤ P' → P' ≤ Y → IsElementaryAbelian p ↥P' → P' = P

theorem isElementaryAbelian_of_forall {p : ℕ} {H : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hp : ∀ x ∈ H, x ^ p = 1) : IsElementaryAbelian p ↥H := CFSG.IsElementaryAbelian.of_forall hc hp

theorem ea_comm {p : ℕ} {H : Subgroup G} (hH : IsElementaryAbelian p ↥H) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem ea_pow_eq_one {p : ℕ} {H : Subgroup G} (hH : IsElementaryAbelian p ↥H) {x : G}
    (hx : x ∈ H) : x ^ p = 1 :=
  CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) x hx

theorem card_sup_eq_mul {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hi : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K →* G :=
    { toFun := fun a => (a.1 : G) * (a.2 : G)
      map_one' := by simp
      map_mul' := fun a b => by
        have := hc (b.1 : G) b.1.2 (a.2 : G) a.2.2
        calc ((a.1 : G) * (b.1 : G)) * ((a.2 : G) * (b.2 : G))
            = (a.1 : G) * ((b.1 : G) * (a.2 : G)) * (b.2 : G) := by group
          _ = (a.1 : G) * ((a.2 : G) * (b.1 : G)) * (b.2 : G) := by rw [this]
          _ = ((a.1 : G) * (a.2 : G)) * ((b.1 : G) * (b.2 : G)) := by group }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ h
    have h1 : x * y = 1 := h
    have hxy : x = y⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : x ∈ H ⊓ K := ⟨hx, by rw [hxy]; exact K.inv_mem hy⟩
    rw [hi, Subgroup.mem_bot] at hmem
    subst hmem
    have : y = 1 := by simpa using hxy
    subst this
    rfl
  have hrange : (⊤ : Subgroup (↥H × ↥K)).map f = H ⊔ K := by
    apply le_antisymm
    · rintro _ ⟨a, -, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.1.2) (Subgroup.mem_sup_right a.2.2)
    · refine sup_le (fun x hx => ⟨(⟨x, hx⟩, 1), trivial, by simp [f]⟩) (fun y hy => ⟨(1, ⟨y, hy⟩), trivial, by simp [f]⟩)
  rw [← hrange, Subgroup.card_map_of_injective hinj, Subgroup.card_top, Nat.card_prod]

end Basic

section Equal

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mem_smul_sylow_iff {p : ℕ} (S : Sylow p Γ) (g x : Γ) :
    x ∈ ((g • S : Sylow p Γ) : Subgroup Γ) ↔ g⁻¹ * x * g ∈ (S : Subgroup Γ) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.smul_def, mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.smul_def, mul_assoc]

omit [Finite Γ] in
theorem inv_conj_pow (g x : Γ) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

theorem card_eq_of_abelian_sylow {p : ℕ} (hp : p.Prime)
    (hab : ∀ T : Subgroup Γ, IsPGroup p ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {P₁ P₂ : Subgroup Γ} (h₁ : IsElementaryAbelian p ↥P₁)
    (m₁ : ∀ P' : Subgroup Γ, P₁ ≤ P' → IsElementaryAbelian p ↥P' → P' = P₁)
    (h₂ : IsElementaryAbelian p ↥P₂)
    (m₂ : ∀ P' : Subgroup Γ, P₂ ≤ P' → IsElementaryAbelian p ↥P' → P' = P₂) :
    Nat.card ↥P₁ = Nat.card ↥P₂ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ (P T : Subgroup Γ), IsElementaryAbelian p ↥P →
      (∀ P' : Subgroup Γ, P ≤ P' → IsElementaryAbelian p ↥P' → P' = P) → P ≤ T → IsPGroup p ↥T →
      ∀ x : Γ, x ∈ P ↔ x ∈ T ∧ x ^ p = 1 := by
    intro P T hP hmax hPT hT x
    constructor
    · intro hx
      exact ⟨hPT hx, ea_pow_eq_one hP hx⟩
    · rintro ⟨hxT, hxp⟩
      have hzc : Subgroup.zpowers x ≤ Subgroup.centralizer (P : Set Γ) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro g hg
        exact hab T hT g (hPT hg) x hxT
      have hz := IsElementaryAbelian.zpowers_of_pow_eq_one (p := p) hxp
      have hF := IsElementaryAbelian.sup_of_le_centralizer (p := p) (E := P) (C := Subgroup.zpowers x) hzc
      have := hmax _ le_sup_left hF
      rw [← this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨S₁, hS₁⟩ := h₁.isPGroup.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := h₂.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S₁ S₂
  have k₁ := key P₁ (S₁ : Subgroup Γ) h₁ m₁ hS₁ S₁.isPGroup'
  have k₂ := key P₂ (S₂ : Subgroup Γ) h₂ m₂ hS₂ S₂.isPGroup'
  have hg' : ∀ x : Γ, x ∈ (S₂ : Subgroup Γ) ↔ g⁻¹ * x * g ∈ (S₁ : Subgroup Γ) := by
    intro x
    rw [← hg]
    exact mem_smul_sylow_iff S₁ g x
  let e : ↥P₁ ≃ ↥P₂ :=
    { toFun := fun x => ⟨g * x * g⁻¹, by
        rw [k₂]
        have hx := (k₁ x).1 x.2
        refine ⟨?_, ?_⟩
        · rw [hg']
          simpa [mul_assoc] using hx.1
        · rw [conj_pow, hx.2]
          simp⟩
      invFun := fun y => ⟨g⁻¹ * y * g, by
        rw [k₁]
        have hy := (k₂ y).1 y.2
        refine ⟨?_, ?_⟩
        · exact (hg' _).1 hy.1
        · rw [inv_conj_pow, hy.2]
          simp⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  exact Nat.card_congr e

end Equal

section Wrap

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_sylAb {p : ℕ} (hp : p.Prime) {Y P₁ P₂ : Subgroup G} (hY : SylAb p Y)
    (h₁ : MaxEA p Y P₁) (h₂ : MaxEA p Y P₂) : Nat.card ↥P₁ = Nat.card ↥P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hab : ∀ T : Subgroup ↥Y, IsPGroup p ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro T hT x hx y hy
    have hTm : IsPGroup p ↥(T.map Y.subtype) :=
      hT.of_equiv (Subgroup.equivMapOfInjective T Y.subtype Y.subtype_injective)
    have := hY (T.map Y.subtype) (Subgroup.map_subtype_le T) hTm (x : G) (Subgroup.mem_map_of_mem _ hx) (y : G)
      (Subgroup.mem_map_of_mem _ hy)
    exact Subtype.ext this
  have key : ∀ P : Subgroup G, MaxEA p Y P → IsElementaryAbelian p ↥(P.subgroupOf Y) ∧
      ∀ P' : Subgroup ↥Y, P.subgroupOf Y ≤ P' → IsElementaryAbelian p ↥P' → P' = P.subgroupOf Y := by
    intro P hP
    obtain ⟨hPY, hPel, hPmax⟩ := hP
    have := hPel
    refine ⟨IsElementaryAbelian.subgroupOf hPY, ?_⟩
    intro P' hP' hel
    have := hel
    have hQel : IsElementaryAbelian p ↥(P'.map Y.subtype) := IsElementaryAbelian.map_subtype
    have hPQ : P ≤ P'.map Y.subtype := by
      intro x hx
      exact ⟨⟨x, hPY hx⟩, hP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hQ := hPmax _ hPQ (Subgroup.map_subtype_le P') hQel
    refine le_antisymm (fun t ht => ?_) hP'
    rw [Subgroup.mem_subgroupOf, ← hQ]
    exact Subgroup.mem_map_of_mem _ ht
  have e1 := key P₁ h₁
  have e2 := key P₂ h₂
  have hc := card_eq_of_abelian_sylow (Γ := ↥Y) hp hab e1.1 e1.2 e2.1 e2.2
  have hcard : ∀ P : Subgroup G, P ≤ Y → Nat.card ↥(P.subgroupOf Y) = Nat.card ↥P := fun P hP =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  rw [← hcard P₁ h₁.1, ← hcard P₂ h₂.1]
  exact hc

end Wrap

section Inner

variable {G : Type} [Group G] [Finite G]

def innerSub (Y : Subgroup G) : Subgroup G where
  carrier := {g | ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), g = x * y}
  one_mem' := ⟨1, Y.one_mem, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨xa, hxa, ya, hya, rfl⟩ ⟨xb, hxb, yb, hyb, rfl⟩
    refine ⟨xa * xb, Y.mul_mem hxa hxb, ya * yb, mul_mem hya hyb, ?_⟩
    have h : ya * xb = xb * ya := (Subgroup.mem_centralizer_iff.1 hya xb hxb).symm
    calc xa * ya * (xb * yb) = xa * (ya * xb) * yb := by group
      _ = xa * (xb * ya) * yb := by rw [h]
      _ = xa * xb * (ya * yb) := by group
  inv_mem' := by
    rintro a ⟨x, hx, y, hy, rfl⟩
    refine ⟨x⁻¹, Y.inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
    have h : x * y = y * x := Subgroup.mem_centralizer_iff.1 hy x hx
    calc (x * y)⁻¹ = (y * x)⁻¹ := by rw [h]
      _ = x⁻¹ * y⁻¹ := by group

omit [Finite G] in
theorem le_innerSub_left (Y : Subgroup G) : Y ≤ innerSub Y := fun x hx =>
  ⟨x, hx, 1, one_mem _, by simp⟩

omit [Finite G] in
theorem le_innerSub_right (Y : Subgroup G) : Subgroup.centralizer (Y : Set G) ≤ innerSub Y := fun y hy =>
  ⟨1, Y.one_mem, y, hy, by simp⟩

theorem inner_split {p : ℕ} (hp : p.Prime) {E Y : Subgroup G} (hE : IsElementaryAbelian p ↥E)
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hinn : ∀ e ∈ E, ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y)
    (hZ : ¬ p ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G))) :
    MaxEA p Y (E ⊓ Y) ∧
      Nat.card ↥E = Nat.card ↥(E ⊓ Y) * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => ea_comm hE hx hy
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => ea_pow_eq_one hE hx
  obtain ⟨P, hPY, hPcomm, hPpow, hPC, hPE, -⟩ := exists_complement_of_inner hp hEcomm hEpow hinn hZ
  have hPel : IsElementaryAbelian p ↥P := isElementaryAbelian_of_forall hPcomm hPpow
  have hCmem : ∀ y ∈ Subgroup.centralizer (Y : Set G), ∀ w ∈ Y, w * y = y * w :=
    fun y hy w hw => Subgroup.mem_centralizer_iff.1 hy w hw
  have hPcent : P ≤ Subgroup.centralizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨x, hxP, y, hyC, rfl⟩ := hPE e he
    calc x * y * a = x * (y * a) := by group
      _ = x * (a * y) := by rw [← hCmem y hyC a (hPY ha)]
      _ = (x * a) * y := by group
      _ = (a * x) * y := by rw [hPcomm x hxP a ha]
      _ = a * (x * y) := by group
  have hPE_le : P ≤ E := by
    have hF := IsElementaryAbelian.sup_of_le_centralizer (p := p) (E := E) (C := P) hPcent
    have := hEmax _ hF le_sup_left
    rw [← this]
    exact le_sup_right
  have hEY : E ⊓ Y = P := by
    refine le_antisymm (fun a ha => ?_) (le_inf hPE_le hPY)
    obtain ⟨x, hxP, y, hyC, rfl⟩ := hPE a ha.1
    have hyY : y ∈ Y := by
      have : y = x⁻¹ * (x * y) := by group
      rw [this]
      exact Y.mul_mem (Y.inv_mem (hPY hxP)) ha.2
    have hcommxy : Commute x y := (hCmem y hyC x (hPY hxP))
    have hyp : y ^ p = 1 := by
      have h1 : (x * y) ^ p = x ^ p * y ^ p := hcommxy.mul_pow p
      rw [hEpow _ ha.1, hPpow x hxP, one_mul] at h1
      exact h1.symm
    have hy1 : y = 1 := by
      by_contra hne
      have hord : orderOf y = p := orderOf_eq_prime hyp hne
      have hmem : y ∈ Y ⊓ Subgroup.centralizer (Y : Set G) := ⟨hyY, hyC⟩
      apply hZ
      rw [← hord]
      have := orderOf_dvd_natCard (⟨y, hmem⟩ : ↥(Y ⊓ Subgroup.centralizer (Y : Set G)))
      simpa using this
    rw [hy1, mul_one]
    exact hxP
  refine ⟨⟨inf_le_right, ?_, ?_⟩, ?_⟩
  · exact isElementaryAbelian_of_forall (fun x hx y hy => hEcomm x hx.1 y hy.1) (fun x hx => hEpow x hx.1)
  · intro P' hP'1 hP'2 hP'el
    have := hP'el
    have hDel : IsElementaryAbelian p ↥(E ⊓ Subgroup.centralizer (Y : Set G)) :=
      isElementaryAbelian_of_forall (fun x hx y hy => hEcomm x hx.1 y hy.1) (fun x hx => hEpow x hx.1)
    have hDcent : E ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer (P' : Set G) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hCmem d hd.2 h (hP'2 hh)
    have hF := IsElementaryAbelian.sup_of_le_centralizer (p := p) (E := P') (C := E ⊓ Subgroup.centralizer (Y : Set G))
      hDcent
    have hEle : E ≤ P' ⊔ (E ⊓ Subgroup.centralizer (Y : Set G)) := by
      intro e he
      obtain ⟨x, hxP, y, hyC, rfl⟩ := hPE e he
      have hxE : x ∈ E := hPE_le hxP
      have hyE : y ∈ E := by
        have : y = x⁻¹ * (x * y) := by group
        rw [this]
        exact E.mul_mem (E.inv_mem hxE) he
      exact Subgroup.mul_mem_sup (hP'1 ⟨hxE, hPY hxP⟩) ⟨hyE, hyC⟩
    have hEq := hEmax _ hF hEle
    refine le_antisymm (fun t ht => ⟨?_, hP'2 ht⟩) hP'1
    rw [← hEq]
    exact Subgroup.mem_sup_left ht
  · have hsup : (E ⊓ Y) ⊔ (E ⊓ Subgroup.centralizer (Y : Set G)) = E := by
      refine le_antisymm (sup_le inf_le_left inf_le_left) (fun e he => ?_)
      obtain ⟨x, hxP, y, hyC, rfl⟩ := hPE e he
      have hxE : x ∈ E := hPE_le hxP
      have hyE : y ∈ E := by
        have : y = x⁻¹ * (x * y) := by group
        rw [this]
        exact E.mul_mem (E.inv_mem hxE) he
      exact Subgroup.mul_mem_sup ⟨hxE, hPY hxP⟩ ⟨hyE, hyC⟩
    have hi : (E ⊓ Y) ⊓ (E ⊓ Subgroup.centralizer (Y : Set G)) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have hgP : g ∈ P ⊓ Subgroup.centralizer (Y : Set G) := ⟨by rw [← hEY]; exact hg.1, hg.2.2⟩
      rw [hPC] at hgP
      exact hgP
    have hcc : ∀ x ∈ E ⊓ Y, ∀ y ∈ E ⊓ Subgroup.centralizer (Y : Set G), x * y = y * x :=
      fun x hx y hy => hCmem y hy.2 x hx.2
    have := card_sup_eq_mul hcc hi
    rw [hsup] at this
    exact this

end Inner

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_prime_commute {p : ℕ} (hp : p.Prime) {X : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (X : Set G)) (hep : e ^ p = 1) (hpX : p ∣ Nat.card ↥X) :
    ∃ u ∈ X, e * u = u * e ∧ orderOf u = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ↥X := Fintype.ofFinite _
  have hmem : ∀ x : G, x ∈ X → e * x * e⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.1 he x).1 hx
  let f : Function.End ↥X := fun x => ⟨e * x * e⁻¹, hmem x x.2⟩
  have hiter : ∀ (n : ℕ) (x : ↥X), (((f ^ n) x : ↥X) : G) = e ^ n * x * (e ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro x
      have h0 : (f ^ 0) x = x := rfl
      rw [h0]
      simp
    | succ n ih =>
      intro x
      have h1 : (f ^ (n + 1)) x = (f ^ n) (f x) := rfl
      rw [h1, ih]
      show e ^ n * (e * (x : G) * e⁻¹) * (e ^ n)⁻¹ = e ^ (n + 1) * x * (e ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  have hf : f ^ p ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [hiter, pow_one, hep]
    simp
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hmod' : Nat.card ↥X ≡ Nat.card ↥(Function.fixedPoints f) [MOD p] := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    convert hmod
  set K : Subgroup G := X ⊓ Subgroup.centralizer ({e} : Set G) with hK
  have hKcard : Nat.card ↥K = Nat.card ↥(Function.fixedPoints f) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨⟨u, u.2.1⟩, ?_⟩
        invFun := fun x => ⟨(x.1 : G), x.1.2, ?_⟩
        left_inv := fun u => rfl
        right_inv := fun x => rfl }
    · apply Subtype.ext
      show e * (u : G) * e⁻¹ = u
      have h := Subgroup.mem_centralizer_singleton_iff.1 u.2.2
      rw [← h]
      group
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h := congrArg Subtype.val x.2
      have h' : e * (x.1 : G) * e⁻¹ = x.1 := h
      calc (x.1 : G) * e = e * (x.1 : G) * e⁻¹ * e := by rw [h']
        _ = e * x.1 := by group
  have hpK : p ∣ Nat.card ↥K := by
    rw [hKcard]
    exact (Nat.modEq_zero_iff_dvd.1 (hmod'.symm.trans (Nat.modEq_zero_iff_dvd.2 hpX)))
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  refine ⟨(k : G), k.2.1, ?_, ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.1 k.2.2
    exact h.symm
  · rw [← hk]
    exact (Subgroup.orderOf_coe k)

end Fixed

section Core

variable {G : Type} [Group G]

theorem exists_card_eq_pow {p n : ℕ} (hp : p.Prime) {E H : Subgroup G} (hE : Nat.card ↥E = p ^ n)
    (hH : H ≤ E) : ∃ k, k ≤ n ∧ Nat.card ↥H = p ^ k := by
  have := Subgroup.card_dvd_of_le hH
  rw [hE] at this
  exact (Nat.dvd_prime_pow hp).1 this

theorem card_lt_of_lt [Finite G] {H K : Subgroup G} (h : H < K) : Nat.card ↥H < Nat.card ↥K := by
  refine lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq => ?_
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

theorem eq_of_lt_of_pow [Finite G] {p : ℕ} (hp : p.Prime) {E C D : Subgroup G} (hE : Nat.card ↥E = p ^ 4)
    (hCD : C < D) (hDE : D ≤ E) (hC : p ^ 3 ≤ Nat.card ↥C) : D = E := by
  obtain ⟨m, hm, hDm⟩ := exists_card_eq_pow hp hE hDE
  obtain ⟨k, hk, hCk⟩ := exists_card_eq_pow hp hE (hCD.le.trans hDE)
  have h1 : Nat.card ↥C < Nat.card ↥D := card_lt_of_lt hCD
  rw [hCk] at hC h1
  rw [hDm] at h1
  have h3 : 3 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hC
  have h4 : k < m := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  have hm4 : m = 4 := by omega
  subst hm4
  exact Subgroup.eq_of_le_of_card_ge hDE (by rw [hE, hDm])

end Core

section Final

variable {G : Type} [Group G] [Finite G]

theorem no_commuting_conjugate {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElementaryAbelian p ↥E)
    (hE4 : Nat.card ↥E = p ^ 4)
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E)
    (hrank : ∀ F : Subgroup G, IsElementaryAbelian p ↥F →
      (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ F ≤ Subgroup.normalizer (S : Set G)) →
        Nat.card ↥F ≤ p ^ 3)
    {Y X : Subgroup G}
    (hYin : ∀ e ∈ E, ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y)
    (hYZ : ¬ p ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G)))
    {B S : Subgroup G} (hBE : B ≤ E) (hB3 : Nat.card ↥B = p ^ 3) (hSY : S ≤ Y) (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 ↥S) (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hSB : S = ⁅S, B⁆)
    (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hXZ : ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set G)))
    (hXsyl : SylAb p X)
    (htr : ∀ P : Subgroup G, MaxEA p Y P →
      ∃ P' : Subgroup G, MaxEA p X P' ∧ Nat.card ↥P' = Nat.card ↥P)
    (hXY : X ≤ Subgroup.centralizer (Y : Set G))
    {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) (hbY : Y ≤ Subgroup.centralizer ({b} : Set G))
    (hbX : X ≤ Subgroup.centralizer ({b} : Set G)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => ea_comm hE hx hy
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => ea_pow_eq_one hE hx
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨hmaxY, hcardY⟩ := inner_split hp hE hEmax hYin hYZ
  have hCY : Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set G)) ≤ p ^ 2 := by
    have hFE : B ⊔ (E ⊓ Subgroup.centralizer (Y : Set G)) ≤ E := sup_le hBE inf_le_left
    have hFel : IsElementaryAbelian p ↥(B ⊔ (E ⊓ Subgroup.centralizer (Y : Set G))) :=
      isElementaryAbelian_of_forall (fun x hx y hy => hEcomm x (hFE hx) y (hFE hy))
        (fun x hx => hEpow x (hFE hx))
    have hCN : E ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (S : Set G) := fun d hd =>
      Subgroup.centralizer_le_normalizer (S : Set G) (Subgroup.centralizer_le hSY hd.2)
    have hFn : B ⊔ (E ⊓ Subgroup.centralizer (Y : Set G)) ≤ Subgroup.normalizer (S : Set G) :=
      sup_le hBS hCN
    have hF3 := hrank _ hFel ⟨S, hS1, hS2, hFn⟩
    have hBF : B = B ⊔ (E ⊓ Subgroup.centralizer (Y : Set G)) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hB3]; exact hF3)
    have hDB : E ⊓ Subgroup.centralizer (Y : Set G) ≤ B := le_sup_right.trans hBF.symm.le
    by_contra hgt
    push Not at hgt
    obtain ⟨i, hi, hDi⟩ := exists_card_eq_pow hp hB3 hDB
    rw [hDi] at hgt
    have hi3 : i = 3 := by
      have : 2 < i := (Nat.pow_lt_pow_iff_right hp1).1 hgt
      omega
    subst hi3
    have hDB' : E ⊓ Subgroup.centralizer (Y : Set G) = B :=
      Subgroup.eq_of_le_of_card_ge hDB (by rw [hDi, hB3])
    have hBC : B ≤ Subgroup.centralizer (Y : Set G) := by rw [← hDB']; exact inf_le_right
    have hSC : S ≤ Subgroup.centralizer (B : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.1 (hBC hh) s (hSY hs)).symm
    apply hS1
    rw [hSB]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hSC
  obtain ⟨j, hj2, hj4, hjc⟩ : ∃ j, 2 ≤ j ∧ j ≤ 4 ∧ Nat.card ↥(E ⊓ Y) = p ^ j := by
    obtain ⟨j, hj, hjc⟩ := exists_card_eq_pow hp hE4 (inf_le_left : E ⊓ Y ≤ E)
    refine ⟨j, ?_, hj, hjc⟩
    have h1 : p ^ 4 ≤ p ^ j * p ^ 2 := by
      calc p ^ 4 = Nat.card ↥(E ⊓ Y) * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set G)) := by
            rw [← hE4]; exact hcardY
        _ ≤ p ^ j * p ^ 2 := by rw [hjc]; exact Nat.mul_le_mul_left _ hCY
    have h2 : p ^ 4 ≤ p ^ (j + 2) := by rw [pow_add]; exact h1
    have := (Nat.pow_le_pow_iff_right hp1).1 h2
    omega
  have hbnY : b ∉ Y := by
    intro hbY'
    have hbC : b ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.1 (hbY hg)
    have hmem : b ∈ Y ⊓ Subgroup.centralizer (Y : Set G) := ⟨hbY', hbC⟩
    apply hYZ
    have hord : orderOf b = p := orderOf_eq_prime (hEpow b hb) hb1
    rw [← hord]
    have := orderOf_dvd_natCard (⟨b, hmem⟩ : ↥(Y ⊓ Subgroup.centralizer (Y : Set G)))
    simpa using this
  have hCge : p ^ 3 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (X : Set G)) := by
    have hYC : E ⊓ Y ≤ E ⊓ Subgroup.centralizer (X : Set G) := by
      intro x hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      exact (Subgroup.mem_centralizer_iff.1 (hXY hg) x hx.2).symm
    have hbC : b ∈ E ⊓ Subgroup.centralizer (X : Set G) := by
      refine ⟨hb, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.1 (hbX hg)
    have hlt : E ⊓ Y < E ⊓ Subgroup.centralizer (X : Set G) :=
      lt_of_le_of_ne hYC fun h => by
        have : b ∈ E ⊓ Y := by rw [h]; exact hbC
        exact hbnY this.2
    have hcl := card_lt_of_lt hlt
    obtain ⟨k, hk, hkc⟩ :=
      exists_card_eq_pow hp hE4 (inf_le_left : E ⊓ Subgroup.centralizer (X : Set G) ≤ E)
    rw [hjc, hkc] at hcl
    have := (Nat.pow_lt_pow_iff_right hp1).1 hcl
    rw [hkc]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨P', hmaxX', hP'card⟩ := htr (E ⊓ Y) hmaxY
  have hpX : p ∣ Nat.card ↥X := by
    have h1 : p ∣ Nat.card ↥P' := by
      rw [hP'card, hjc]
      exact dvd_pow_self p (by omega)
    exact h1.trans (Subgroup.card_dvd_of_le hmaxX'.1)
  have hXin : ∀ e ∈ E, ∃ x ∈ X, ∃ y ∈ Subgroup.centralizer (X : Set G), e = x * y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, heE, hexy⟩ := hcon
    have heW : e ∉ innerSub X := fun h => by
      obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact hexy x hx y hy hxy
    obtain ⟨u, huX, hue, huord⟩ := exists_orderOf_prime_commute hp (hEX heE) (hEpow e heE) hpX
    have hCW : E ⊓ Subgroup.centralizer (X : Set G) ≤ innerSub X := inf_le_right.trans (le_innerSub_right X)
    have heC : e ∉ E ⊓ Subgroup.centralizer (X : Set G) := fun h => heW (hCW h)
    have hDE : (E ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers e = E := by
      refine eq_of_lt_of_pow hp hE4 (lt_of_le_of_ne le_sup_left fun h => heC ?_)
        (sup_le inf_le_left ((Subgroup.zpowers_le).2 heE)) hCge
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    have huE : E ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [← hDE]
      refine sup_le (fun c hc => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc.2 u huX).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hue
    have hupow : u ^ p = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
    have huC : u ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.1 (huE hg)
    have hzel := IsElementaryAbelian.zpowers_of_pow_eq_one (p := p) hupow
    have hFel := IsElementaryAbelian.sup_of_le_centralizer (p := p) (E := E) (C := Subgroup.zpowers u)
      ((Subgroup.zpowers_le).2 huC)
    have huEq := hEmax _ hFel le_sup_left
    have huinE : u ∈ E := by
      rw [← huEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have huCX : u ∉ Subgroup.centralizer (X : Set G) := by
      intro hu
      apply hXZ
      rw [← huord]
      have hmem : u ∈ X ⊓ Subgroup.centralizer (X : Set G) := ⟨huX, hu⟩
      have := orderOf_dvd_natCard (⟨u, hmem⟩ : ↥(X ⊓ Subgroup.centralizer (X : Set G)))
      simpa using this
    have huC' : u ∉ E ⊓ Subgroup.centralizer (X : Set G) := fun h => huCX h.2
    have hDE' : (E ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers u = E := by
      refine eq_of_lt_of_pow hp hE4 (lt_of_le_of_ne le_sup_left fun h => huC' ?_)
        (sup_le inf_le_left ((Subgroup.zpowers_le).2 huinE)) hCge
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have hEW : E ≤ innerSub X := by
      rw [← hDE']
      exact sup_le hCW ((Subgroup.zpowers_le).2 (le_innerSub_left X huX))
    exact heW (hEW heE)
  obtain ⟨hmaxX, hcardX⟩ := inner_split hp hE hEmax hXin hXZ
  have hEq : Nat.card ↥(E ⊓ X) = Nat.card ↥P' := card_eq_of_sylAb hp hXsyl hmaxX hmaxX'
  rw [hEq, hP'card, hjc] at hcardX
  have h1 : p ^ 2 * p ^ 3 ≤ p ^ 4 := by
    calc p ^ 2 * p ^ 3 ≤ p ^ j * Nat.card ↥(E ⊓ Subgroup.centralizer (X : Set G)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos hj2) hCge
      _ = p ^ 4 := by rw [← hE4]; exact hcardX.symm
  have h5 : p ^ 2 * p ^ 3 = p ^ 5 := by ring
  rw [h5] at h1
  have := (Nat.pow_le_pow_iff_right hp1).1 h1
  omega

end Final

section Map

variable {G : Type} [Group G]

theorem mem_of_map_mem {φ : G ≃* G} {Y : Subgroup G} {t : G} (ht : φ t ∈ Y.map φ.toMonoidHom) : t ∈ Y := by
  obtain ⟨u, hu, hut⟩ := ht
  have : u = t := φ.injective hut
  exact this ▸ hu

theorem SylAb.map {p : ℕ} (φ : G ≃* G) {Y : Subgroup G} (h : SylAb p Y) :
    SylAb p (Y.map φ.toMonoidHom) := by
  intro Q hQ hQp x hx y hy
  have hQY : Q.comap φ.toMonoidHom ≤ Y := fun t ht => mem_of_map_mem (hQ ht)
  have hpg : IsPGroup p ↥(Q.comap φ.toMonoidHom) := by
    intro g
    obtain ⟨k, hk⟩ := hQp ⟨φ g, g.2⟩
    refine ⟨k, Subtype.ext (φ.injective ?_)⟩
    have h1 : (φ (g : G)) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact h1
  have hcomm := h _ hQY hpg (φ.symm x) (by simpa using hx) (φ.symm y) (by simpa using hy)
  have := congrArg φ hcomm
  simpa using this

theorem MaxEA.map {p : ℕ} (φ : G ≃* G) {Y P : Subgroup G} (h : MaxEA p Y P) :
    MaxEA p (Y.map φ.toMonoidHom) (P.map φ.toMonoidHom) := by
  obtain ⟨hPY, hPel, hmax⟩ := h
  refine ⟨Subgroup.map_mono hPY, ?_, ?_⟩
  · refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp [← map_mul, ea_comm hPel hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      simp [← map_pow, ea_pow_eq_one hPel hx]
  · intro P' hPP' hP'Y hP'el
    have hP'' : P'.comap φ.toMonoidHom = P := by
      refine hmax _ (fun x hx => hPP' ⟨x, hx, rfl⟩) (fun t ht => mem_of_map_mem (hP'Y ht)) ?_
      refine isElementaryAbelian_of_forall (fun x hx y hy => φ.injective ?_) (fun x hx => φ.injective ?_)
      · simpa [map_mul] using ea_comm hP'el hx hy
      · simpa [map_pow] using ea_pow_eq_one hP'el hx
    rw [← hP'']
    exact (Subgroup.map_comap_eq_self_of_surjective φ.surjective P').symm

end Map

end CFSG.RankThree.PartOne.K159R5
