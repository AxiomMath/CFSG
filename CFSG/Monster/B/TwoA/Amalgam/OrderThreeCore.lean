module

public import CFSG.Monster.B.E6.StdF4Opposite
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoStd

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup card_betaGroup)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt isoGraph LBeta extAct)

theorem clabel_mem_Shat
    (v : CVert) : clabel v ∈ Shat := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  rw [clabel_cvOf]
  exact Shat.mul_mem (Shat.mul_mem (Shat.inv_mem g.2) cQ_mem_Shat) g.2

@[expose] def clabelS
    (v : CVert) : Shat := ⟨clabel v, clabel_mem_Shat v⟩

theorem coe_clabelS
    (v : CVert) : ((clabelS v : Shat) : Dfull) = clabel v := rfl

theorem commute_conj_inv_iff {M : Type*} [Group M] (g p q : M) :
    Commute (g⁻¹ * p * g) (g⁻¹ * q * g) ↔ Commute p q := by
  constructor
  · intro h
    have h' : g⁻¹ * p * g * (g⁻¹ * q * g) = g⁻¹ * q * g * (g⁻¹ * p * g) := h
    have e1 : g⁻¹ * p * g * (g⁻¹ * q * g) = g⁻¹ * (p * q) * g := by group
    have e2 : g⁻¹ * q * g * (g⁻¹ * p * g) = g⁻¹ * (q * p) * g := by group
    rw [e1, e2] at h'
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    show g⁻¹ * p * g * (g⁻¹ * q * g) = g⁻¹ * q * g * (g⁻¹ * p * g)
    calc g⁻¹ * p * g * (g⁻¹ * q * g) = g⁻¹ * (p * q) * g := by group
      _ = g⁻¹ * (q * p) * g := by rw [h.eq]
      _ = g⁻¹ * q * g * (g⁻¹ * p * g) := by group

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem conj_inv_eq_one_iff {M : Type*} [Group M] (g r : M) : g⁻¹ * r * g = 1 ↔ r = 1 := by
  constructor
  · intro h
    calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · intro h
    rw [h, mul_one, inv_mul_cancel]

theorem conj_fix_of_commute {M : Type*} [Group M] {g r z p c : M} (hc : r * p = p * r)
    (hp : p = g * z * g⁻¹) (hcr : c = g⁻¹ * r * g) : c * z * c⁻¹ = z := by
  subst hp hcr
  calc g⁻¹ * r * g * z * (g⁻¹ * r * g)⁻¹ = g⁻¹ * (r * (g * z * g⁻¹)) * r⁻¹ * g := by group
    _ = g⁻¹ * (g * z * g⁻¹ * r) * r⁻¹ * g := by rw [hc]
    _ = z := by group

theorem conj_inv_conj_of_eq {M : Type*} [Group M] {g r s : M} (h : r = g * s * g⁻¹) :
    g⁻¹ * r * g = s := by
  subst h
  group

theorem map_conj_of_eq {N M : Type*} [Group N] [Group M] (ψ : N →* M) {x g z : N}
    (h : x = g * z * g⁻¹) : ψ x = ψ g * ψ z * (ψ g)⁻¹ := by
  subst h
  simp only [map_mul, map_inv]

theorem map_conj_conj {N M : Type*} [Group N] [Group M] (ψ : N →* M) (g x x' : N) (r : M)
    (h : ψ x' = r⁻¹ * ψ x * r) :
    ψ (g⁻¹ * x' * g) = ((ψ g)⁻¹ * r * ψ g)⁻¹ * ψ (g⁻¹ * x * g) * ((ψ g)⁻¹ * r * ψ g) := by
  simp only [map_mul, map_inv, h]
  group

theorem inv_conj_eq_of_eq {M : Type*} [Group M] {c C p q : M} (hc : c = C) (hp : p = q) :
    C⁻¹ * q * C = c⁻¹ * p * c⁻¹⁻¹ := by
  subst hc hp
  rw [inv_inv]

theorem card_leviStar :
    Nat.card E6.StdF4.leviStar = 18393661440 := by
  have hle : ∀ {x : ModGL Tag.E6 K}, x ∈ stdLevi firstJ → x ∈ stdGroup := fun hx =>
    ((stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ)) hx
  let e : E6.StdF4.leviStar ≃ stdLevi firstJ × betaGroup :=
    { toFun := fun γ => (⟨(((γ : GStar).left : stdGroup) : ModGL Tag.E6 K), γ.2⟩,
        (γ : GStar).right)
      invFun := fun p => ⟨⟨⟨p.1, hle p.1.2⟩, p.2⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_stdLevi_firstJ, card_betaGroup]

structure LocalHom
    (u : CVert) where
  stab : Subgroup Shat
  mem_stab : ∀ y : Shat, y ∈ stab ↔ cvMul u y = u
  iv : cgraph.neighborSet u ≃ rootClass
  rho : stab →* GStar
  adj_iff : ∀ a b : cgraph.neighborSet u, a ≠ b →
    (cgraph.Adj a b ↔ Commute (iv a : stdGroup) (iv b))
  act : ∀ (y : stab) (a : cgraph.neighborSet u) (h : cvMul a y ∈ cgraph.neighborSet u),
    SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) =
      (rho y)⁻¹ * SemidirectProduct.inl (iv a : stdGroup) * rho y
  surj : Function.Surjective rho
  ker : ∀ y : Shat, (cvMul u y = u ∧ ∀ a ∈ cgraph.neighborSet u, cvMul a y = a) ↔
    (y : Dfull) ∈ Subgroup.zpowers (clabel u)
  orderOf_clabel : orderOf (clabel u) = 2
  rho_clabel : ∀ (a : cgraph.neighborSet u) (y : stab), ((y : Shat) : Dfull) = clabel a →
    rho y = SemidirectProduct.inl (iv a : stdGroup)

namespace LocalHom

variable {u : CVert} (L : LocalHom u)

abbrev pt (a : cgraph.neighborSet u) : GStar := SemidirectProduct.inl (L.iv a : stdGroup)

theorem pt_injective : Function.Injective L.pt := fun _ _ h =>
  L.iv.injective (Subtype.ext (SemidirectProduct.inl_injective h))

theorem pt_mem (a : cgraph.neighborSet u) : L.pt a ∈ rootClassStar := by
  rw [mem_rootClassStar_iff]
  exact ⟨_, (L.iv a).2, rfl⟩

theorem cvMul_mem (y : L.stab) {a : CVert} (ha : a ∈ cgraph.neighborSet u) :
    cvMul a y ∈ cgraph.neighborSet u := by
  have h := (cgraph_adj_cvMul u a y).2 ha
  rwa [(L.mem_stab y).1 y.2] at h

theorem cvMul_eq_self_iff (y : L.stab) (a : cgraph.neighborSet u) :
    cvMul (a : CVert) y = a ↔ L.rho y * L.pt a = L.pt a * L.rho y := by
  have e : L.pt ⟨cvMul a y, L.cvMul_mem y a.2⟩ = (L.rho y)⁻¹ * L.pt a * L.rho y :=
    L.act y a _
  constructor
  · intro h
    have h' : L.pt ⟨cvMul a y, L.cvMul_mem y a.2⟩ = L.pt a := congrArg L.pt (Subtype.ext h)
    rw [h'] at e
    calc L.rho y * L.pt a = L.rho y * ((L.rho y)⁻¹ * L.pt a * L.rho y) := by rw [← e]
      _ = L.pt a * L.rho y := by group
  · intro h
    have e2 : (L.rho y)⁻¹ * L.pt a * L.rho y = L.pt a := by
      rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2] at e
    exact congrArg Subtype.val (L.pt_injective e)

theorem mem_zpowers_of_rho_eq_one {y : L.stab} (h : L.rho y = 1) :
    ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u) :=
  (L.ker y).1 ⟨(L.mem_stab y).1 y.2, fun a ha =>
    (L.cvMul_eq_self_iff y ⟨a, ha⟩).2 (by rw [h, one_mul, mul_one])⟩

theorem adj_iff_commute {a b : cgraph.neighborSet u} (hne : a ≠ b) :
    cgraph.Adj a b ↔ Commute (L.pt a) (L.pt b) := by
  rw [L.adj_iff a b hne]
  constructor
  · intro h
    exact h.map SemidirectProduct.inl
  · intro h
    exact Commute.of_map (f := (SemidirectProduct.inl : stdGroup →* GStar))
      SemidirectProduct.inl_injective h

theorem adj_iff' (a b : cgraph.neighborSet u) :
    cgraph.Adj a b ↔ a ≠ b ∧ Commute (L.iv a : stdGroup) (L.iv b) := by
  by_cases h : a = b
  · subst h
    exact iff_of_false (cgraph.irrefl) fun h => h.1 rfl
  · rw [L.adj_iff a b h]
    exact ⟨fun hc => ⟨h, hc⟩, fun hc => hc.2⟩

theorem mem_commonNeighbors_iff (a b x : cgraph.neighborSet u) :
    (x : CVert) ∈ cgraph.commonNeighbors a b ↔
      (L.iv x : stdGroup) ∈ commonNbrs (L.iv a) (L.iv b) := by
  have hne : ∀ y z : cgraph.neighborSet u, y ≠ z ↔ (L.iv y : stdGroup) ≠ L.iv z := fun y z =>
    not_congr ⟨fun h => by rw [h], fun h => L.iv.injective (Subtype.ext h)⟩
  rw [SimpleGraph.mem_commonNeighbors, L.adj_iff', L.adj_iff', commonNbrs, Set.mem_ofPred_eq,
    hne, hne]
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨(L.iv x).2, h1.symm, h2.symm, h3.symm, h4.symm⟩,
    fun ⟨_, h1, h2, h3, h4⟩ => ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩⟩

end LocalHom

section Labels

variable (H : ∀ x : CVert, LocalHom x)
include H

theorem clabelS_mem_stab {u a : CVert} (ha : a ∈ cgraph.neighborSet u) :
    clabelS a ∈ (H u).stab := by
  rw [(H u).mem_stab]
  exact (((H a).ker (clabelS a)).2 (Subgroup.mem_zpowers _)).2 u
    ((cgraph.mem_neighborSet u a).1 ha).symm

theorem rho_clabelS {u a : CVert} (ha : a ∈ cgraph.neighborSet u) :
    (H u).rho ⟨clabelS a, clabelS_mem_stab H ha⟩ = (H u).pt ⟨a, ha⟩ :=
  (H u).rho_clabel ⟨a, ha⟩ _ rfl

theorem cvMul_clabelS_self (v : CVert) : cvMul v (clabelS v) = v :=
  (((H v).ker (clabelS v)).2 (Subgroup.mem_zpowers _)).1

theorem cvMul_clabelS_of_mem {v x : CVert} (hx : x ∈ cgraph.neighborSet v) :
    cvMul x (clabelS v) = x :=
  (((H v).ker (clabelS v)).2 (Subgroup.mem_zpowers _)).2 x hx

theorem orderOf_pt_mul_pt_eq_three {u : CVert} {a b : cgraph.neighborSet u} (hne : a ≠ b)
    (hna : ¬cgraph.Adj a b)
    (h3 : orderOf (clabel a * clabel b) = 3 ∨ orderOf (clabel a * clabel b) = 6) :
    orderOf ((H u).pt a * (H u).pt b) = 3 := by
  have hrz : (H u).rho (⟨clabelS a, clabelS_mem_stab H a.2⟩ * ⟨clabelS b, clabelS_mem_stab H b.2⟩)
      = (H u).pt a * (H u).pt b := by
    rw [map_mul, rho_clabelS H a.2, rho_clabelS H b.2]
  have hoz : orderOf (clabel a * clabel b) = orderOf
      ((⟨clabelS a, clabelS_mem_stab H a.2⟩ * ⟨clabelS b, clabelS_mem_stab H b.2⟩ :
        (H u).stab)) := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rfl
  have hdvd : orderOf ((H u).pt a * (H u).pt b) ∣ orderOf (clabel a * clabel b) := by
    rw [← hrz, hoz]
    exact orderOf_map_dvd (H u).rho _
  have hnc : ¬((H u).pt a * (H u).pt b) ^ 2 = 1 := by
    rw [← commute_iff_sq_eq_one (mul_self_of_mem_rootClassStar ((H u).pt_mem a))
      (mul_self_of_mem_rootClassStar ((H u).pt_mem b))]
    exact fun h => hna (((H u).adj_iff_commute hne).2 h)
  obtain ⟨i, -, ho⟩ := exists_orbSize_eq ((H u).pt_mem a) ((H u).pt_mem b)
  rw [← orderOf_dvd_iff_pow_eq_one, ho] at hnc
  rw [ho] at hdvd ⊢
  have key : ∀ j : Fin 5, ¬repOrder j ∣ 2 → (repOrder j ∣ 3 ∨ repOrder j ∣ 6) →
      repOrder j = 3 := by decide
  rcases h3 with e | e <;> rw [e] at hdvd
  · exact key i hnc (Or.inl hdvd)
  · exact key i hnc (Or.inr hdvd)

end Labels

theorem exists_opposite
    {u : CVert} (L : LocalHom u) {a b : cgraph.neighborSet u}
    (horder : orderOf (L.pt a * L.pt b) = 3) :
    ∃ g : stdGroup, g * rootInv * g⁻¹ = L.iv a ∧ g * tMinus * g⁻¹ = L.iv b ∧
      Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) =
        E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom ∧
      commonNbrs (L.iv a) (L.iv b) = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus := by
  have h' : orderOf ((L.iv a : stdGroup) * L.iv b) = 3 := by
    rw [← orderOf_injective (SemidirectProduct.inl : stdGroup →* GStar)
      SemidirectProduct.inl_injective, map_mul]
    exact horder
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hconj⟩ :=
    standard_F4_opposite_root_common_neighbor_geometry
  exact hconj _ _ (L.iv a).2 (L.iv b).2 h'

section Slice

variable {u : CVert} (L : LocalHom u) {a b : cgraph.neighborSet u} {g : stdGroup}

theorem exists_isoPt_map
    (hcn : commonNbrs (L.iv a) (L.iv b) = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus) :
    ∃ f : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b) → IsoPt,
      Function.Bijective f ∧ (∀ x, rootPt (f x) = g⁻¹ * L.iv ⟨x, x.2.1⟩ * g) ∧
      ∀ x x' : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b),
        cgraph.Adj x x' ↔ isoGraph.Adj (f x) (f x') := by
  have hrange := standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.1
  have hrinj := standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.1
  have hadjU := standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.2.2.2.1
  have hex : ∀ x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b),
      ∃ P : IsoPt, rootPt P = g⁻¹ * L.iv ⟨x, x.2.1⟩ * g := by
    intro x
    have h1 := (L.mem_commonNeighbors_iff a b ⟨x, x.2.1⟩).1 x.2.2
    rw [hcn] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [hrange] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, (conj_inv_conj_of_eq hyx.symm).symm⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro x x' h
    have e := congrArg rootPt h
    rw [hf, hf] at e
    have e2 : (L.iv ⟨x, x.2.1⟩ : stdGroup) = L.iv ⟨x', x'.2.1⟩ :=
      mul_left_cancel (mul_right_cancel e)
    exact Subtype.ext (congrArg (fun z : cgraph.neighborSet u => (z : CVert))
      (L.iv.injective (Subtype.ext e2)))
  have hfsurj : Function.Surjective f := by
    intro P
    have hP : rootPt P ∈ commonNbrs rootInv tMinus := by
      rw [hrange]
      exact ⟨P, rfl⟩
    have hmem : g * rootPt P * g⁻¹ ∈ commonNbrs (L.iv a) (L.iv b) := by
      rw [hcn]
      exact ⟨_, hP, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : cgraph.neighborSet u, y = L.iv.symm ⟨_, hmem.1⟩ := ⟨_, rfl⟩
    have hyv : (L.iv y : stdGroup) = g * rootPt P * g⁻¹ := by
      rw [hy, Equiv.apply_symm_apply]
    have hyC : (y : CVert) ∈ cgraph.commonNeighbors a b := by
      rw [L.mem_commonNeighbors_iff a b y, hyv]
      exact hmem
    exact ⟨⟨y, y.2, hyC⟩, hrinj ((hf _).trans (conj_inv_conj_of_eq hyv))⟩
  refine ⟨f, ⟨hfinj, hfsurj⟩, hf, fun x x' => ?_⟩
  refine (L.adj_iff' ⟨x, x.2.1⟩ ⟨x', x'.2.1⟩).trans ?_
  rw [hadjU, hf, hf, commute_conj_inv_iff, hfinj.ne_iff]
  refine and_congr_left' (not_congr ⟨fun h => Subtype.ext
    (congrArg (fun z : cgraph.neighborSet u => (z : CVert)) h), fun h => by rw [h]⟩)

variable (T : Subgroup Shat) (hT : ∀ y, y ∈ T ↔ cvMul a y = a ∧ cvMul b y = b ∧ cvMul u y = u)
include hT

theorem le_stab : T ≤ L.stab := fun y hy => (L.mem_stab y).2 ((hT y).1 hy).2.2

theorem rho_mem_centralizer (y : T) :
    L.rho ⟨y, le_stab L T hT y.2⟩ ∈ Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro z (rfl | rfl)
  · exact ((L.cvMul_eq_self_iff ⟨y, le_stab L T hT y.2⟩ a).1 ((hT y).1 y.2).1).symm
  · exact ((L.cvMul_eq_self_iff ⟨y, le_stab L T hT y.2⟩ b).1 ((hT y).1 y.2).2.1).symm

theorem conj_rho_mem_leviStar
    (hcent : Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom)
    (y : T) : (SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ *
      SemidirectProduct.inl g ∈ E6.StdF4.leviStar := by
  have h := rho_mem_centralizer L T hT y
  rw [hcent, Subgroup.mem_map_equiv] at h
  exact h

theorem exists_leviHom₀
    (hcent : Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom) :
    ∃ φ₀ : T →* E6.StdF4.leviStar, ∀ y : T, ((φ₀ y : E6.StdF4.leviStar) : GStar) =
      (SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ * SemidirectProduct.inl g :=
  ⟨MonoidHom.codRestrict ((MulAut.conj (SemidirectProduct.inl g : GStar)).symm.toMonoidHom.comp
      (L.rho.comp (Subgroup.inclusion (le_stab L T hT)))) E6.StdF4.leviStar
      (conj_rho_mem_leviStar L T hT hcent), fun _ => rfl⟩

variable {φ₀ : T →* E6.StdF4.leviStar}
  (hφ₀ : ∀ y : T, ((φ₀ y : E6.StdF4.leviStar) : GStar) =
    (SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ * SemidirectProduct.inl g)
include hφ₀

theorem leviHom₀_eq_one_iff (y : T) : φ₀ y = 1 ↔ L.rho ⟨y, le_stab L T hT y.2⟩ = 1 :=
  ⟨fun h => (conj_inv_eq_one_iff _ _).1
      ((hφ₀ y).symm.trans (congrArg (fun z : E6.StdF4.leviStar => (z : GStar)) h)),
    fun h => Subtype.ext ((hφ₀ y).trans ((conj_inv_eq_one_iff _ _).2 h))⟩

theorem leviHom₀_eq_one_of_fix
    (hcn : commonNbrs (L.iv a) (L.iv b) = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus)
    (y : T) (hfix : ∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors a b, cvMul x y = x) :
    φ₀ y = 1 := by
  apply standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro z hz
  have hmem : g * z * g⁻¹ ∈ commonNbrs (L.iv a) (L.iv b) := by
    rw [hcn]
    exact ⟨z, hz, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : cgraph.neighborSet u, (L.iv x : stdGroup) = g * z * g⁻¹ :=
    ⟨L.iv.symm ⟨_, hmem.1⟩, by rw [Equiv.apply_symm_apply]⟩
  have hxC : (x : CVert) ∈ cgraph.commonNeighbors a b := by
    rw [L.mem_commonNeighbors_iff a b x, hx]
    exact hmem
  exact conj_fix_of_commute
    ((L.cvMul_eq_self_iff ⟨y, le_stab L T hT y.2⟩ x).1 (hfix x ⟨x.2, hxC⟩))
    (map_conj_of_eq SemidirectProduct.inl hx) (hφ₀ y)

theorem rho_eq_one_iff
    (hcn : commonNbrs (L.iv a) (L.iv b) = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus)
    (y : T) : L.rho ⟨y, le_stab L T hT y.2⟩ = 1 ↔
      ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u) := by
  refine ⟨fun h => L.mem_zpowers_of_rho_eq_one h, fun hy => ?_⟩
  have hfix := ((L.ker y).2 hy).2
  exact (leviHom₀_eq_one_iff L T hT hφ₀ y).1
    (leviHom₀_eq_one_of_fix L T hT hφ₀ hcn y fun x hx => hfix x hx.1)

theorem leviHom₀_surjective
    (hcent : Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom) :
    Function.Surjective φ₀ := by
  intro γ
  obtain ⟨y₀, hy₀⟩ := L.surj (MulAut.conj (SemidirectProduct.inl g : GStar) γ)
  have hmem : L.rho y₀ ∈ Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) := by
    rw [hy₀, hcent]
    exact Subgroup.mem_map_of_mem _ γ.2
  rw [Subgroup.mem_centralizer_iff] at hmem
  have hya : cvMul (a : CVert) y₀ = a :=
    (L.cvMul_eq_self_iff y₀ a).2 (hmem _ (Set.mem_insert _ _)).symm
  have hyb : cvMul (b : CVert) y₀ = b :=
    (L.cvMul_eq_self_iff y₀ b).2 (hmem _ (Set.mem_insert_of_mem _ rfl)).symm
  have hyT : (y₀ : Shat) ∈ T := (hT y₀).2 ⟨hya, hyb, (L.mem_stab y₀).1 y₀.2⟩
  exact ⟨⟨y₀, hyT⟩, Subtype.ext ((hφ₀ _).trans (conj_inv_conj_of_eq hy₀))⟩

end Slice

section Slice2

variable {u : CVert} (L : LocalHom u) {a b : cgraph.neighborSet u} {g : stdGroup}
  (T : Subgroup Shat) (hT : ∀ y, y ∈ T ↔ cvMul a y = a ∧ cvMul b y = b ∧ cvMul u y = u)

theorem exists_leviHom
    (hcent : Subgroup.centralizer ({L.pt a, L.pt b} : Set GStar) =
      E6.StdF4.leviStar.map (MulAut.conj (SemidirectProduct.inl g : GStar)).toMonoidHom)
    (hcn : commonNbrs (L.iv a) (L.iv b) = (fun x => g * x * g⁻¹) '' commonNbrs rootInv tMinus) :
    ∃ φ : T →* LBeta, Function.Surjective φ ∧
      (∀ y : T, φ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      (∀ y : T, ((leviStarEquiv.symm (φ y) : E6.StdF4.leviStar) : GStar) =
        (SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ * SemidirectProduct.inl g) ∧
      ∀ s : Shat, (s ∈ T ∧ ∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors a b,
        cvMul x s = x) ↔ (s : Dfull) ∈ Subgroup.zpowers (clabel u) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_leviHom₀ L T hT hcent
  refine ⟨leviStarEquiv.toMonoidHom.comp φ₀, fun β => ?_, fun y => ?_, fun y => ?_,
    fun s => ⟨fun ⟨hsT, hsN⟩ => ?_, fun hs => ?_⟩⟩
  · obtain ⟨y, hy⟩ := leviHom₀_surjective L T hT hφ₀ hcent (leviStarEquiv.symm β)
    exact ⟨y, (congrArg leviStarEquiv hy).trans (leviStarEquiv.apply_symm_apply β)⟩
  · exact (MulEquiv.map_eq_one_iff leviStarEquiv).trans
      ((leviHom₀_eq_one_iff L T hT hφ₀ y).trans (rho_eq_one_iff L T hT hφ₀ hcn y))
  · exact (congrArg (fun z : E6.StdF4.leviStar => (z : GStar))
      (leviStarEquiv.symm_apply_apply (φ₀ y))).trans (hφ₀ y)
  · exact (rho_eq_one_iff L T hT hφ₀ hcn ⟨s, hsT⟩).1 ((leviHom₀_eq_one_iff L T hT hφ₀ ⟨s, hsT⟩).1
      (leviHom₀_eq_one_of_fix L T hT hφ₀ hcn ⟨s, hsT⟩ hsN))
  · have hfix := (L.ker s).2 hs
    exact ⟨(hT s).2 ⟨hfix.2 a a.2, hfix.2 b b.2, hfix.1⟩, fun x hx => hfix.2 x hx.1⟩

theorem slice_equivariant
    {f : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b) → IsoPt}
    (hf : ∀ x, rootPt (f x) = g⁻¹ * L.iv ⟨x, x.2.1⟩ * g) {φ : T →* LBeta}
    (hφg : ∀ y : T, ((leviStarEquiv.symm (φ y) : E6.StdF4.leviStar) : GStar) =
      (SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ * SemidirectProduct.inl g)
    (y : T) (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b))
    (h : cvMul x y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors a b) :
    f ⟨_, h⟩ = (extAct (φ y))⁻¹ (f x) := by
  apply standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.1
  apply E6.StdF4.inl_injective
  have hact : SemidirectProduct.inl (L.iv ⟨cvMul x y, h.1⟩ : stdGroup) =
      (L.rho ⟨y, le_stab L T hT y.2⟩)⁻¹ * SemidirectProduct.inl (L.iv ⟨x, x.2.1⟩ : stdGroup) *
        L.rho ⟨y, le_stab L T hT y.2⟩ :=
    L.act ⟨y, le_stab L T hT y.2⟩ ⟨x, x.2.1⟩ h.1
  have he : extAct (leviStarEquiv (leviStarEquiv.symm (φ y))⁻¹) = (extAct (φ y))⁻¹ := by
    rw [map_inv, MulEquiv.apply_symm_apply, map_inv]
  calc SemidirectProduct.inl (rootPt (f ⟨_, h⟩))
      = SemidirectProduct.inl (g⁻¹ * (L.iv ⟨cvMul x y, h.1⟩ : stdGroup) * g) :=
        congrArg _ (hf _)
    _ = ((SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ *
          SemidirectProduct.inl g)⁻¹ *
        SemidirectProduct.inl (g⁻¹ * (L.iv ⟨x, x.2.1⟩ : stdGroup) * g) *
        ((SemidirectProduct.inl g)⁻¹ * L.rho ⟨y, le_stab L T hT y.2⟩ *
          SemidirectProduct.inl g) :=
        map_conj_conj SemidirectProduct.inl g _ _ _ hact
    _ = (((leviStarEquiv.symm (φ y))⁻¹ : E6.StdF4.leviStar) : GStar) *
        SemidirectProduct.inl (rootPt (f x)) *
        (((leviStarEquiv.symm (φ y))⁻¹ : E6.StdF4.leviStar) : GStar)⁻¹ :=
        inv_conj_eq_of_eq (hφg y) (congrArg SemidirectProduct.inl (hf x))
    _ = SemidirectProduct.inl
          (rootPt (extAct (leviStarEquiv (leviStarEquiv.symm (φ y))⁻¹) (f x))) :=
        standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _
    _ = SemidirectProduct.inl (rootPt ((extAct (φ y))⁻¹ (f x))) := by rw [he]

include L hT in
theorem natCard_slice_stab {φ : T →* LBeta} (hφsurj : Function.Surjective φ)
    (hφker : ∀ y : T, φ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) :
    Nat.card T = 36787322880 := by
  have hker2 : Nat.card φ.ker = Nat.card (Subgroup.zpowers (clabel u)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨(((y : T) : Shat) : Dfull), (hφker y).1 (MonoidHom.mem_ker.1 y.2)⟩) ⟨?_, ?_⟩)
    · intro y y' h
      have h' : (((y : T) : Shat) : Dfull) = (((y' : T) : Shat) : Dfull) :=
        congrArg (fun z : Subgroup.zpowers (clabel u) => (z : Dfull)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    · rintro ⟨z, hz⟩
      have hzS : z ∈ Shat := Subgroup.zpowers_le.2 (clabel_mem_Shat u) hz
      have hfix := (L.ker ⟨z, hzS⟩).2 hz
      have hzT : (⟨z, hzS⟩ : Shat) ∈ T :=
        (hT _).2 ⟨hfix.2 a a.2, hfix.2 b b.2, hfix.1⟩
      exact ⟨⟨⟨⟨z, hzS⟩, hzT⟩, MonoidHom.mem_ker.2 ((hφker _).2 hz)⟩, rfl⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv,
    ← Nat.card_congr leviStarEquiv.toEquiv, card_leviStar, hker2, Nat.card_zpowers,
    L.orderOf_clabel]

end Slice2

theorem order_three_local
    {u : CVert} (L : LocalHom u) {a b : cgraph.neighborSet u}
    (horder : orderOf (L.pt a * L.pt b) = 3) (T : Subgroup Shat)
    (hT : ∀ y, y ∈ T ↔ cvMul a y = a ∧ cvMul b y = b ∧ cvMul u y = u) :
    (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b).ncard = 693 ∧
    (∀ s : Shat, (s ∈ T ∧ ∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors a b,
        cvMul x s = x) ↔ (s : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
    Nat.card T = 36787322880 ∧
    ∃ (ι : cgraph.induce (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b) ≃g isoGraph)
      (φ : T →* LBeta), Function.Surjective φ ∧
      (∀ y : T, φ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      ∀ (y : T) (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors a b))
        (h : cvMul x y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors a b),
        ι ⟨_, h⟩ = (extAct (φ y))⁻¹ (ι x) := by
  have hop := exists_opposite L horder
  have hiso := exists_isoPt_map L hop.choose_spec.2.2.2
  have hlv := exists_leviHom L T hT hop.choose_spec.2.2.1 hop.choose_spec.2.2.2
  refine ⟨?_, hlv.choose_spec.2.2.2,
    natCard_slice_stab L T hT hlv.choose_spec.1 hlv.choose_spec.2.1,
    { toEquiv := Equiv.ofBijective hiso.choose hiso.choose_spec.1
      map_rel_iff' := fun {x x'} => (hiso.choose_spec.2.2 x x').symm }, hlv.choose,
    hlv.choose_spec.1, hlv.choose_spec.2.1,
    slice_equivariant L T hT hiso.choose_spec.2.1 hlv.choose_spec.2.2.1⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofBijective _ hiso.choose_spec.1),
    Nat.card_eq_fintype_card, standard_F4_opposite_root_common_neighbor_geometry.2.2.2.2.2.2.2.2.1]

section Common

variable (H : ∀ x : CVert, LocalHom x)
include H

theorem exists_stab3 (v w u : CVert) :
    ∃ T : Subgroup Shat, ∀ y, y ∈ T ↔ cvMul v y = v ∧ cvMul w y = w ∧ cvMul u y = u :=
  ⟨(H v).stab ⊓ (H w).stab ⊓ (H u).stab, fun y => by
    simp only [Subgroup.mem_inf, (H v).mem_stab, (H w).mem_stab, (H u).mem_stab, and_assoc]⟩

theorem order_three_at
    {v w u : CVert} (hvw : v ≠ w) (hna : ¬cgraph.Adj v w)
    (h3 : orderOf (clabel v * clabel w) = 3 ∨ orderOf (clabel v * clabel w) = 6)
    (hu : u ∈ cgraph.commonNeighbors v w) (T : Subgroup Shat)
    (hT : ∀ y, y ∈ T ↔ cvMul v y = v ∧ cvMul w y = w ∧ cvMul u y = u) :
    (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 693 ∧
    (∀ s : Shat, (s ∈ T ∧ ∀ x ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w,
        cvMul x s = x) ↔ (s : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
    Nat.card T = 36787322880 ∧
    ∃ (ι : cgraph.induce (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ≃g isoGraph)
      (φ : T →* LBeta), Function.Surjective φ ∧
      (∀ y : T, φ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel u)) ∧
      ∀ (y : T) (x : ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w))
        (h : cvMul x y ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w),
        ι ⟨_, h⟩ = (extAct (φ y))⁻¹ (ι x) := by
  have hvu : v ∈ cgraph.neighborSet u := ((cgraph.mem_commonNeighbors).1 hu).1.symm
  have hwu : w ∈ cgraph.neighborSet u := ((cgraph.mem_commonNeighbors).1 hu).2.symm
  have hne : (⟨v, hvu⟩ : cgraph.neighborSet u) ≠ ⟨w, hwu⟩ := fun h =>
    hvw (congrArg Subtype.val h)
  exact order_three_local (H u) (orderOf_pt_mul_pt_eq_three H hne hna h3) T hT

theorem mem_zpowers_of_fix
    {v w u : CVert} (hvw : v ≠ w) (hna : ¬cgraph.Adj v w)
    (h3 : orderOf (clabel v * clabel w) = 3 ∨ orderOf (clabel v * clabel w) = 6)
    (hu : u ∈ cgraph.commonNeighbors v w) {s : Shat} (hv : cvMul v s = v) (hw : cvMul w s = w)
    (hs : ∀ x ∈ cgraph.commonNeighbors v w, cvMul x s = x) :
    (s : Dfull) ∈ Subgroup.zpowers (clabel u) := by
  obtain ⟨T, hT⟩ := exists_stab3 H v w u
  obtain ⟨-, hker, -⟩ := order_three_at H hvw hna h3 hu T hT
  exact (hker s).1 ⟨(hT s).2 ⟨hv, hw, hs u hu⟩, fun x hx => hs x hx.2⟩

theorem exists_commonNeighbor_adj
    {v w u : CVert} (hvw : v ≠ w) (hna : ¬cgraph.Adj v w)
    (h3 : orderOf (clabel v * clabel w) = 3 ∨ orderOf (clabel v * clabel w) = 6)
    (hu : u ∈ cgraph.commonNeighbors v w) :
    ∃ u' ∈ cgraph.commonNeighbors v w, u' ≠ u ∧ cgraph.Adj u u' := by
  obtain ⟨T, hT⟩ := exists_stab3 H v w u
  obtain ⟨hN, -⟩ := order_three_at H hvw hna h3 hu T hT
  have hne : (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hN]; decide)
  obtain ⟨u', hu'1, hu'2⟩ := hne
  exact ⟨u', hu'2, fun h => cgraph.irrefl (h ▸ hu'1), hu'1⟩

theorem order_three_common
    {v w : CVert} (hvw : v ≠ w) (hna : ¬cgraph.Adj v w)
    (h3 : orderOf (clabel v * clabel w) = 3 ∨ orderOf (clabel v * clabel w) = 6)
    (hC : (cgraph.commonNeighbors v w).Nonempty) :
    694 ≤ (cgraph.commonNeighbors v w).ncard ∧
    ∀ s : Shat, cvMul v s = v → cvMul w s = w →
      (∀ x ∈ cgraph.commonNeighbors v w, cvMul x s = x) → s = 1 := by
  obtain ⟨u, hu⟩ := hC
  obtain ⟨T, hT⟩ := exists_stab3 H v w u
  obtain ⟨hN, -⟩ := order_three_at H hvw hna h3 hu T hT
  refine ⟨?_, fun s hv hw hs => ?_⟩
  · have hnot : u ∉ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w := fun h =>
      cgraph.irrefl h.1
    have hsub : insert u (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) ⊆
        cgraph.commonNeighbors v w := Set.insert_subset hu Set.inter_subset_right
    calc 694 = 693 + 1 := rfl
      _ = (insert u (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)).ncard := by
          rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), hN]
      _ ≤ (cgraph.commonNeighbors v w).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  · obtain ⟨u', hu', hne, -⟩ := exists_commonNeighbor_adj H hvw hna h3 hu
    have h1 := mem_zpowers_of_fix H hvw hna h3 hu hv hw hs
    have h2 := mem_zpowers_of_fix H hvw hna h3 hu' hv hw hs
    have hvu : u ∈ cgraph.neighborSet v := ((cgraph.mem_commonNeighbors).1 hu).1
    have hvu' : u' ∈ cgraph.neighborSet v := ((cgraph.mem_commonNeighbors).1 hu').1
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf (H u).orderOf_clabel h1 with e1 | e1
    · exact Subtype.ext e1
    · rcases eq_one_or_eq_of_mem_zpowers_of_orderOf (H u').orderOf_clabel h2 with e2 | e2
      · exact Subtype.ext e2
      · exact absurd (clabel_injOn_neighborSet v hvu' hvu (e2.symm.trans e1)) hne

end Common

end CFSG.Monster.B.TwoA.Amalgam
