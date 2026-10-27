module

public import CFSG.Walter.AStar.Components
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

@[expose] def IsTypeL2Even (L : Type*) [Group L] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))

@[expose] def IsTypeL2Odd (L : Type*) [Group L] : Prop :=
  ∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
    (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f))

theorem isTypeL2_iff {L : Type*} [Group L] : IsTypeL2 L ↔ IsTypeL2Even L ∨ IsTypeL2Odd L :=
  Iff.rfl

theorem IsTypeL2.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : IsTypeL2 A) :
    IsTypeL2 B := by
  rcases h with ⟨f, hf, ⟨φ⟩⟩ | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨φ⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e.symm.trans φ⟩⟩

theorem map_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (S : Set A) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h' := h x hx
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact h'
  · intro h x hx
    have h' := h (e x) ⟨x, hx, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h'

theorem map_centralizer_singleton_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (a : A) : (Subgroup.centralizer ({a} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set B) := by
  rw [map_centralizer_mulEquiv, Set.image_singleton]

theorem IsTypeJR.of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B)
    (h : IsTypeJR A) : IsTypeJR B := by
  obtain ⟨hs, hab, hc⟩ := h
  have : IsSimpleGroup A := hs
  refine ⟨e.symm.isSimpleGroup, hab.of_surjective (f := e.toMonoidHom) e.surjective, ?_⟩
  intro t ht
  have ht' : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨hco, p, f, hp, L, hpodd, hf, h5, hLC, hLn, ⟨φ⟩, hCL⟩ := hc (e.symm t) ht'
  have hC : (Subgroup.centralizer ({e.symm t} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({t} : Set B) := by
    rw [map_centralizer_singleton_mulEquiv, MulEquiv.apply_symm_apply]
  have hLC' : L.map e.toMonoidHom ≤ Subgroup.centralizer ({t} : Set B) :=
    hC ▸ Subgroup.map_mono hLC
  refine ⟨?_, p, f, hp, L.map e.toMonoidHom, hpodd, hf, h5, hLC', ?_, ⟨?_⟩, ?_⟩
  · rw [← hC]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).mpr hco
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLC', ← hC,
      ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLn)
  · exact (L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans φ
  · rw [← hC, Subgroup.coe_map, MulEquiv.coe_toMonoidHom, ← map_centralizer_mulEquiv,
      ← Subgroup.map_inf_eq _ _ _ e.injective, hCL, MonoidHom.map_zpowers,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : GorensteinWalter.IsQuasisimple A) : GorensteinWalter.IsQuasisimple B := by
  obtain ⟨hnt, hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  let e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B := QuotientGroup.congr _ _ e hc
  refine ⟨e.symm.toEquiv.nontrivial, ?_, e'.symm.isSimpleGroup⟩
  rw [commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

theorem IsQuasisimple.exists_mul_ne_mul {Q : Type*} [Group Q]
    (hQ : GorensteinWalter.IsQuasisimple Q) :
    ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨hnt, hperf, -⟩ := hQ
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h _ _
  rw [hperf] at hle
  have hbot : commutator Q = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp (hle (Subgroup.mem_top y)) x).symm
  rw [hperf] at hbot
  obtain ⟨a, b, hab⟩ := hnt
  exact hab ((Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a)).trans
    (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top b)).symm)

theorem IsQuasisimple.two_dvd_card {Q : Type*} [Group Q] [Finite Q]
    (hQ : GorensteinWalter.IsQuasisimple Q) :
    2 ∣ Nat.card Q := by
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.2
  exact (even_card_of_isSimpleGroup (IsQuasisimple.exists_mul_ne_mul hQ)).two_dvd.trans
    (Subgroup.card_quotient_dvd_card _)

theorem odd_card_center_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : GorensteinWalter.IsQuasisimple Q)
    (hab : HasAbelianSylowTwo Q) : Odd (Nat.card (Subgroup.center Q)) :=
  odd_card_center_of_perfect hQ.2.1 hab

theorem commutatorElement_mul_left_of_commute' {G : Type*} [Group G] {a c y : G}
    (h : Commute c y) : ⁅a * c, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_commute' {G : Type*} [Group G] {x b d : G}
    (h : Commute d x) : ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (b * d) * x⁻¹ * (d⁻¹ * b⁻¹) = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [h.inv_right.eq, mul_inv_cancel_right]

theorem mem_centralizer_of_commutator_mem_center {G : Type*} [Group G] {K : Subgroup G}
    (hK : commutator K = ⊤) {c : G}
    (hc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ (Subgroup.center K).map K.subtype) :
    c ∈ Subgroup.centralizer (K : Set G) := by
  have hcz : ∀ x ∈ K, ∃ z ∈ K, c * x * c⁻¹ = z * x ∧ ∀ y ∈ K, z * y = y * z := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hc x hx
    refine ⟨z, z.2, ?_, fun y hy => ?_⟩
    · rw [Subgroup.coe_subtype] at hzx
      rw [hzx, inv_mul_cancel_right]
    · exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm)
  set A : Subgroup K := (Subgroup.centralizer ({c} : Set G)).subgroupOf K
  have hA : (⊤ : Subgroup K) ≤ A := by
    rw [← hK, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    change c * ⁅(x : G), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * c
    obtain ⟨z, hzK, hzx0, hz⟩ := hcz x x.2
    obtain ⟨w, hwK, hwy0, hw⟩ := hcz y y.2
    have h1 : c * ⁅(x : G), (y : G)⁆ * c⁻¹ = ⁅z * (x : G), w * (y : G)⁆ := by
      rw [← hzx0, ← hwy0]
      group
    have hzw : Commute z w := hz w hwK
    have hzy : Commute z y := hz y y.2
    have hzx : Commute z x := hz x x.2
    have hwx : Commute w x := hw x x.2
    have hwy : Commute w y := hw y y.2
    have h2 : ⁅z * (x : G), w * (y : G)⁆ = ⁅(x : G), (y : G)⁆ := by
      rw [hzx.eq, hwy.eq, commutatorElement_mul_left_of_commute' (hzy.mul_right hzw),
        commutatorElement_mul_right_of_commute' hwx]
    have h3 := h1.trans h2
    calc c * ⁅(x : G), (y : G)⁆ = c * ⁅(x : G), (y : G)⁆ * c⁻¹ * c := by group
      _ = ⁅(x : G), (y : G)⁆ * c := by rw [h3]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxA := hA (Subgroup.mem_top ⟨x, hx⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hxA
  exact (hxA c rfl).symm

section Components

variable {Y : Type*} [Group Y] [Finite Y]

theorem sylow_le_normalizer_of_isComponentOf' (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    (S : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_card_center_of_isQuasisimple hK.2.2 (hY.subgroup K)
  have hS := hY S
  have hKc : CFSG.IsComponent K := (isComponent_iff_isComponentOf_top K).mpr hK
  obtain ⟨⟨t, htS, htK⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (sylow_inf_ne_bot_of_isSubnormal S (isSubnormal_of_isComponentOf hK)
      (IsQuasisimple.two_dvd_card hK.2.2))
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  set K' := K.map (MulAut.conj s).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hKc
  rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with heq | hcomm
  · intro h
    constructor
    · intro hh
      rw [heq]
      exact ⟨h, hh, MulAut.conj_apply s h⟩
    · intro hh
      rw [heq] at hh
      obtain ⟨k, hk, hkeq⟩ := hh
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkeq
      have : k = h := by simpa using hkeq
      rwa [← this]
  · exfalso
    have hst : s * t * s⁻¹ = t := by
      rw [setLike_mul_comm hs htS, mul_inv_cancel_right]
    have htK' : t ∈ K' := ⟨t, htK, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hst]⟩
    have hcent : (⟨t, htK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hkC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm k.2
      exact ((Subgroup.mem_centralizer_iff.mp hkC) t htK').symm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨t, htS⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact ht1' (congrArg Subtype.val hk)
    have h2 : 2 ∣ orderOf (⟨⟨t, htK⟩, hcent⟩ : Subgroup.center K) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rw [Subgroup.orderOf_mk] at hk
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (h2.trans (orderOf_dvd_natCard _)))

theorem le_normalizer_of_isPGroup_of_isComponentOf (hY : HasAbelianSylowTwo Y) {P : Subgroup Y}
    (hP : IsPGroup 2 P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    P ≤ Subgroup.normalizer (K : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact hS.trans (sylow_le_normalizer_of_isComponentOf' hY S hK)

end Components

section Inner

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_inner_of_isQuasisimple (hY : HasAbelianSylowTwo Y) (K : Subgroup Y)
    (hK : GorensteinWalter.IsQuasisimple K) (S : Sylow 2 Y)
    (hSK : (S : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y)) :
    ∀ s ∈ (S : Subgroup Y), ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Y := K ⊔ (S : Subgroup Y) with hH
  have hKH : K ≤ H := le_sup_left
  have hSH : (S : Subgroup Y) ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (K : Set Y) := sup_le Subgroup.le_normalizer hSK
  set K' : Subgroup H := K.subgroupOf H with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  set S' : Sylow 2 H := S.subtype hSH with hS'
  set C : Subgroup H := Subgroup.centralizer (K' : Set H) with hC
  have : C.Normal := Subgroup.normal_centralizer
  set π : H →* H ⧸ C := QuotientGroup.mk' C with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C
  set SW : Sylow 2 (H ⧸ C) := S'.mapSurjective hπ with hSW
  set LW : Subgroup (H ⧸ C) := K'.map π with hLW
  let eK : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  have hK'q : GorensteinWalter.IsQuasisimple K' := isQuasisimple_of_mulEquiv' eK.symm hK
  set ψ : K' →* H ⧸ C := π.comp K'.subtype with hψ
  have hψker : ψ.ker = Subgroup.center K' := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_center_iff, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx g
      exact Subtype.ext (hx g g.2)
    · intro hx g hg
      exact congrArg Subtype.val (hx ⟨g, hg⟩)
  have hψrange : ψ.range = LW := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  let eL : LW ≃* K' ⧸ Subgroup.center K' :=
    (MulEquiv.subgroupCongr hψrange).symm.trans
      ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hψker))
  have : IsSimpleGroup (K' ⧸ Subgroup.center K') := hK'q.2.2
  have : IsSimpleGroup LW := eL.isSimpleGroup
  have hLWnonab : ∃ a b : LW, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsQuasisimple.exists_mul_ne_mul hK'q
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    simpa using congrArg eL h
  have : LW.Normal := hK'n.map π hπ
  have hCW : Subgroup.centralizer (LW : Set (H ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨h, rfl⟩ := hπ w
    rw [Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply mem_centralizer_of_commutator_mem_center hK'q.2.1
    intro k hk
    have h1 := (Subgroup.mem_centralizer_iff.mp hw) (π k) ⟨k, hk, rfl⟩
    have hc1 : h * k * h⁻¹ * k⁻¹ ∈ C := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef]
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    have hc2 : h * k * h⁻¹ * k⁻¹ ∈ K' := K'.mul_mem (hK'n.conj_mem k hk h) (K'.inv_mem hk)
    refine ⟨⟨_, hc2⟩, ?_, rfl⟩
    change (⟨_, hc2⟩ : K') ∈ Subgroup.center K'
    rw [← hψker, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, hπdef,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc1
  have hsup : LW ⊔ (SW : Subgroup (H ⧸ C)) = ⊤ := by
    rw [hSW, Sylow.coe_mapSurjective, hLW, ← Subgroup.map_sup, hS', Sylow.coe_subtype, hK',
      ← Subgroup.subgroupOf_sup hKH hSH, ← hH, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ hπ]
  have hSWab : IsMulCommutative (SW : Subgroup (H ⧸ C)) := by
    rw [hSW, Sylow.coe_mapSurjective]
    have : IsMulCommutative (S' : Subgroup H) := by
      rw [hS', Sylow.coe_subtype]
      have := hY S
      exact Subgroup.comap_injective_isMulCommutative (S : Subgroup Y) H.subtype_injective
    exact Subgroup.map_isMulCommutative _ _
  have hmain := sylow_le_of_centralizer_eq_bot SW hSWab LW hLWnonab hCW hsup
  intro s hs
  have hs' : (⟨s, hSH hs⟩ : H) ∈ (S' : Subgroup H) := by
    rw [hS', Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hs
  have hmem : π ⟨s, hSH hs⟩ ∈ LW := by
    apply hmain
    rw [hSW, Sylow.coe_mapSurjective]
    exact ⟨_, hs', rfl⟩
  obtain ⟨k', hk', hk'eq⟩ := hmem
  have hkc : k'⁻¹ * ⟨s, hSH hs⟩ ∈ C := QuotientGroup.eq.mp hk'eq
  refine ⟨(k' : Y), Subgroup.mem_subgroupOf.mp hk', ?_⟩
  intro x hx
  have h' := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hkc) ⟨x, hKH hx⟩
    (Subgroup.mem_subgroupOf.mpr hx))
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h'
  calc s * x * s⁻¹ = (k' : Y) * ((k' : Y)⁻¹ * s * x) * s⁻¹ := by group
    _ = (k' : Y) * (x * ((k' : Y)⁻¹ * s)) * s⁻¹ := by rw [h']
    _ = (k' : Y) * x * (k' : Y)⁻¹ := by group

theorem exists_inner_of_isComponentOf (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) {s : Y} (hs : s ∈ (S : Subgroup Y)) :
    ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ :=
  exists_inner_of_isQuasisimple hY K hK.2.2 S (sylow_le_normalizer_of_isComponentOf' hY S hK) s hs

theorem exists_inner_of_isPGroup (hY : HasAbelianSylowTwo Y) {P : Subgroup Y}
    (hP : IsPGroup 2 P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) {s : Y} (hs : s ∈ P) :
    ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact exists_inner_of_isComponentOf hY S hK (hS hs)

theorem exists_mem_componentLayerOf_conj_eq' (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {s : Y}
    (hs : s ∈ (S : Subgroup Y)) :
    ∃ e ∈ componentLayerOf (⊤ : Subgroup Y), ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      ∀ x ∈ K, e * x * e⁻¹ = s * x * s⁻¹ := by
  classical
  have hinner : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := fun K hK =>
    exists_inner_of_isComponentOf hY S hK hs
  have hfin : Set.Finite {K : Subgroup Y | IsComponentOf K ⊤} := Set.toFinite _
  suffices h : ∀ F : Finset (Subgroup Y), (∀ K ∈ F, IsComponentOf K ⊤) →
      ∃ e ∈ (⨆ K ∈ F, K), ∀ K ∈ F, ∀ x ∈ K, e * x * e⁻¹ = s * x * s⁻¹ by
    obtain ⟨e, he, hconj⟩ := h hfin.toFinset (fun K hK => hfin.mem_toFinset.mp hK)
    refine ⟨e, ?_, fun K hK => hconj K (hfin.mem_toFinset.mpr hK)⟩
    have hle : (⨆ K ∈ hfin.toFinset, K) ≤ componentLayerOf (⊤ : Subgroup Y) :=
      iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.mp hK)
    exact hle he
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_mem _, fun K hK => absurd hK (Finset.notMem_empty K)⟩
  | insert K₀ F hK₀F ih =>
    intro hF
    obtain ⟨e', he', hconj'⟩ := ih (fun K hK => hF K (Finset.mem_insert_of_mem hK))
    have hK₀ := hF K₀ (Finset.mem_insert_self K₀ F)
    obtain ⟨k₀, hk₀, hk₀conj⟩ := hinner K₀ hK₀
    have hcommF : ∀ K ∈ F, K ≤ Subgroup.centralizer (K₀ : Set Y) := by
      intro K hK
      rcases CFSG.LocalCores.distinct_components_commute
          ((isComponent_iff_isComponentOf_top K).mpr (hF K (Finset.mem_insert_of_mem hK)))
          ((isComponent_iff_isComponentOf_top K₀).mpr hK₀) with h | h
      · exact absurd (h ▸ hK) hK₀F
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have he'C : e' ∈ Subgroup.centralizer (K₀ : Set Y) := (iSup₂_le hcommF) he'
    refine ⟨e' * k₀, ?_, ?_⟩
    · apply mul_mem
      · have hle : (⨆ K ∈ F, K) ≤ (⨆ K ∈ insert K₀ F, K) :=
          iSup₂_le fun K hK => le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => K) K
            (Finset.mem_insert_of_mem hK)
        exact hle he'
      · exact (le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => K) K₀
          (Finset.mem_insert_self K₀ F)) hk₀
    · intro K hK x hx
      rcases Finset.mem_insert.mp hK with rfl | hKF
      · rw [hk₀conj x hx]
        have hy : k₀ * x * k₀⁻¹ ∈ K := mul_mem (mul_mem hk₀ hx) (inv_mem hk₀)
        have hc := (Subgroup.mem_centralizer_iff.mp he'C) _ hy
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = k₀ * x * k₀⁻¹ := by rw [← hc, mul_inv_cancel_right]
      · have hxC := hcommF K hKF hx
        have hc := (Subgroup.mem_centralizer_iff.mp hxC) k₀ hk₀
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = e' * x * e'⁻¹ := by rw [hc, mul_inv_cancel_right]
          _ = s * x * s⁻¹ := hconj' K hKF x hx

end Inner

section AStar

variable {X : Type*} [Group X] [Finite X]

theorem IsAStar.component_image (hX : IsAStar X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsComponentOf (K.map (QuotientGroup.mk' (pPrimeCore 2 X))) ⊤ ∧
      Subgroup.center K = (pPrimeCore 2 X).subgroupOf K ∧
      Nonempty (K ⧸ Subgroup.center K ≃* K.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 X with hO
  set q := QuotientGroup.mk' O with hq
  set Kb := K.map q with hKbdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hnle : ¬ K ≤ q.ker := by
    intro h
    rw [hq, QuotientGroup.ker_mk'] at h
    have h2 := (IsQuasisimple.two_dvd_card hK.2.2).trans (Subgroup.card_dvd_of_le h)
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have hKc : CFSG.IsComponent K := (isComponent_iff_isComponentOf_top K).mpr hK
  have hKbc : CFSG.IsComponent Kb :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKc.1 q hnle,
      hKc.2.map (QuotientGroup.mk'_surjective O)⟩
  have hKb : IsComponentOf Kb ⊤ := (isComponent_iff_isComponentOf_top Kb).mp hKbc
  obtain ⟨hZb, -⟩ := hX.2.2 Kb hKb
  set φ := q.subgroupMap K with hφdef
  have hφ : Function.Surjective φ := q.subgroupMap_surjective K
  have hker : φ.ker = O.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hcenter : Subgroup.center K = O.subgroupOf K := by
    apply le_antisymm
    · intro z hz
      rw [← hker, MonoidHom.mem_ker]
      have h1 : φ z ∈ Subgroup.center Kb := Subgroup.map_center_le_center hφ ⟨z, hz, rfl⟩
      rw [hZb, Subgroup.mem_bot] at h1
      exact h1
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hKc.1 (N := O.subgroupOf K)
        inferInstance with h | h
      · exfalso
        apply hnle
        rw [hq, QuotientGroup.ker_mk']
        intro x hx
        have h1 : (⟨x, hx⟩ : K) ∈ O.subgroupOf K := h ▸ Subgroup.mem_top _
        exact h1
      · exact h
  exact ⟨hKb, hcenter, ⟨(QuotientGroup.quotientMulEquivOfEq (hcenter.trans hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩⟩

theorem IsAStar.center_le_pPrimeCore (hX : IsAStar X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : (Subgroup.center K).map K.subtype ≤ pPrimeCore 2 X := by
  rw [(hX.component_image hK).2.1]
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem IsAStar.isTypeL2_or_isTypeJR (hX : IsAStar X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    IsTypeL2 (K ⧸ Subgroup.center K) ∨ IsTypeJR (K ⧸ Subgroup.center K) := by
  obtain ⟨hKb, -, ⟨e⟩⟩ := hX.component_image hK
  rcases (hX.2.2 _ hKb).2 with h | h
  · exact Or.inl (h.of_mulEquiv e.symm)
  · exact Or.inr (h.of_mulEquiv e.symm)

end AStar

end CFSG.Walter
