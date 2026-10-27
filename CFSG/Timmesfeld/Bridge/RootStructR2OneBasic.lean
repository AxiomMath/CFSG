module

public import CFSG.Timmesfeld.Bridge.RootStructWTIModuleProps
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyCore
public import CFSG.Timmesfeld.Bridge.RootStructWTIQuot
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanLin

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

section Core

variable {a d : G}

theorem lineN₀_le_Nd : lineN₀ D a d ≤ nCore D d ⊓ Subgroup.centralizer {a} := fun _ hk =>
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hk).2, Subgroup.mem_centralizer_singleton_iff.2
    (commute_of_mem_nCore (Subgroup.mem_inf.1 hk).1).eq⟩

theorem lineN₀_le_Na : lineN₀ D a d ≤ nCore D a ⊓ Subgroup.centralizer {d} := fun _ hk =>
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hk).1, Subgroup.mem_centralizer_singleton_iff.2
    (commute_of_mem_nCore (Subgroup.mem_inf.1 hk).2).eq⟩

theorem mem_lineN₀_of_mem {k : G} (hka : k ∈ nCore D a ⊓ Subgroup.centralizer {d})
    (hkd : k ∈ nCore D d ⊓ Subgroup.centralizer {a}) : k ∈ lineN₀ D a d :=
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hka).1, (Subgroup.mem_inf.1 hkd).1⟩

end Core

structure LineConf (D : Set G) (a d x y : G) : Prop where
  setting : LineSetting G D
  ha : a ∈ D
  hd : d ∈ D
  had : Commute a d
  hadD : a * d ∈ D
  hdT : d ∉ rootSet D a
  hx : x ∈ D
  hax : Commute a x
  haxD : a * x ∈ D
  hxT : x ∉ rootGroup D a ⊔ rootGroup D d
  hy : y ∈ D
  hdy : Commute d y
  hdyD : d * y ∈ D
  hyT : y ∉ rootGroup D a ⊔ rootGroup D d

namespace LineConf

variable {a d x y : G} (C : LineConf D a d x y)
include C

theorem finite : Finite G := C.setting.hyp.finite

theorem root : IsRootInvolutionSet D := C.setting.hyp.root

theorem isClass : ∃ d₀ : G, D = {g | IsConj d₀ g} := C.setting.hyp.isClass

theorem hdaD : d * a ∈ D := by rw [← C.had.eq]; exact C.hadD

theorem haT : a ∉ rootSet D d := fun h => C.hdT (mem_rootSet_comm C.hd h)

theorem hxTa : x ∉ rootSet D a := fun h =>
  C.hxT (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h))

theorem mem_rootLines_a : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a :=
  ⟨d, C.hd, C.had, C.hadD, C.hdT, rfl⟩

theorem mem_rootLines_d : rootGroup D a ⊔ rootGroup D d ∈ rootLines D d :=
  ⟨a, C.ha, C.had.symm, C.hdaD, C.haT, sup_comm _ _⟩

theorem mem_rootLines_x : rootGroup D a ⊔ rootGroup D x ∈ rootLines D a :=
  ⟨x, C.hx, C.hax, C.haxD, C.hxTa, rfl⟩

theorem lineTI : LineTI D a d := C.setting.lineTI C.ha C.hd C.had C.hadD C.hdT

theorem lineTI_x : LineTI D a x := C.setting.lineTI C.ha C.hx C.hax C.haxD C.hxTa

theorem orderOf_xd : orderOf (x * d) = 4 :=
  orderOf_mul_eq_four_of_not_mem_line C.root C.setting.lineCentralizerEq C.ha C.hd C.had C.hadD
    C.hdT C.lineTI C.hx C.hax C.hxT

theorem orderOf_ya : orderOf (y * a) = 4 :=
  orderOf_mul_eq_four_of_not_mem_line' C.root C.setting.lineCentralizerEq C.ha C.hd C.had C.hadD
    C.hdT C.lineTI C.hy C.hdy C.hyT

theorem not_commute_xd : ¬ Commute x d :=
  not_commute_of_orderOf_mul_eq_four (C.root.mul_self_eq_one C.hx) (C.root.mul_self_eq_one C.hd)
    C.orderOf_xd

theorem not_commute_ya : ¬ Commute y a :=
  not_commute_of_orderOf_mul_eq_four (C.root.mul_self_eq_one C.hy) (C.root.mul_self_eq_one C.ha)
    C.orderOf_ya

theorem commute_of_mem_Na {k : G} (hk : k ∈ nCore D a ⊓ Subgroup.centralizer {d}) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute k t := by
  rw [sup_comm] at ht
  exact C.setting.commute_of_mem_nCore_of_commute C.hd C.ha C.had.symm C.hdaD C.haT
    (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2)
    ht

theorem commute_of_mem_Nd {k : G} (hk : k ∈ nCore D d ⊓ Subgroup.centralizer {a}) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute k t :=
  C.setting.commute_of_mem_nCore_of_commute C.ha C.hd C.had C.hadD C.hdT
    (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2)
    ht

theorem commute_of_mem_lineN {n : G} (hn : n ∈ lineN D a d) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute n t := by
  have hle : lineN D a d ≤
      Subgroup.centralizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro t ht
    · exact (C.commute_of_mem_Na hk ht).symm.eq
    · exact (C.commute_of_mem_Nd hk ht).symm.eq
  exact ((Subgroup.mem_centralizer_iff.1 (hle hn)) t ht).symm

theorem conj_mem_Na {k : G} (hk : k ∈ nCore D d ⊓ Subgroup.centralizer {a}) {n : G}
    (hn : n ∈ nCore D a ⊓ Subgroup.centralizer {d}) :
    k * n * k⁻¹ ∈ nCore D a ⊓ Subgroup.centralizer {d} := by
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
  obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
  have hka : k * a * k⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hk2, mul_inv_cancel_right]
  have hkd : k * d * k⁻¹ = d := by
    rw [(commute_of_mem_nCore hk1).eq, mul_inv_cancel_right]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have := conj_mem_nCore_conj C.isClass hn1 k
    rwa [hka] at this
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : Commute (k * n * k⁻¹) (k * d * k⁻¹) :=
      (Commute.conj_iff k).2 (Subgroup.mem_centralizer_singleton_iff.1 hn2)
    rw [hkd] at h1
    exact h1.eq

theorem Nd_le_normalizer : nCore D d ⊓ Subgroup.centralizer {a} ≤
    Subgroup.normalizer ((nCore D a ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => C.conj_mem_Na hk hn, fun hn => ?_⟩
  have := C.conj_mem_Na (Subgroup.inv_mem _ hk) hn
  rwa [show k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n by group] at this

theorem exists_mul_eq {n : G} (hn : n ∈ lineN D a d) :
    ∃ na ∈ nCore D a ⊓ Subgroup.centralizer {d}, ∃ nd ∈ nCore D d ⊓ Subgroup.centralizer {a},
      na * nd = n := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left _ _ C.Nd_le_normalizer
  have hn' : n ∈ ((lineN D a d : Subgroup G) : Set G) := hn
  rw [lineN, h] at hn'
  obtain ⟨na, hna, nd, hnd, rfl⟩ := hn'
  exact ⟨na, hna, nd, hnd, rfl⟩

theorem isPGroup_lineN : IsPGroup 2 (lineN D a d) := by
  have := C.finite
  rw [lineN, sup_comm]
  refine IsPGroup.to_sup_of_normal_right' ((isPGroup_nCore D d).to_le inf_le_left)
    ((isPGroup_nCore D a).to_le inf_le_left) C.Nd_le_normalizer

theorem map_conj_eq_of_mem_nCore {k : G} (hk : k ∈ nCore D a) :
    (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj k).toMonoidHom =
      rootGroup D a ⊔ rootGroup D x :=
  C.setting.map_conj_eq_of_mem_closure C.ha (nCore_le_closure_commute D a hk) C.mem_rootLines_x

theorem mem_Na_of_map_conj_eq {c : G} (hc : c ∈ lineN D a d)
    (hcL : (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj c).toMonoidHom =
      rootGroup D a ⊔ rootGroup D x) : c ∈ nCore D a ⊓ Subgroup.centralizer {d} := by
  obtain ⟨na, hna, nd, hnd, rfl⟩ := C.exists_mul_eq hc
  have hna' := C.map_conj_eq_of_mem_nCore (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hna).1)
  have hndL : (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj nd).toMonoidHom =
      rootGroup D a ⊔ rootGroup D x := by
    have h1 := RankOne.map_conj_mul (rootGroup D a ⊔ rootGroup D x) na⁻¹ (na * nd)
    rw [inv_mul_cancel_left, hcL, hna'] at h1
    exact h1
  have hndM := ((rootLinesRegularStep G D C.setting a C.ha d C.hd C.had C.hadD C.hdT x C.hx C.hax
    C.haxD C.hxT x C.hx C.hax C.haxD C.hxT).2 nd hnd hndL)
  have hnd' : nd ∈ nCore D a ⊓ Subgroup.centralizer {d} :=
    Subgroup.mem_inf.2 ⟨hndM, Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem_nCore (Subgroup.mem_inf.1 hnd).1).eq⟩
  exact Subgroup.mul_mem _ hna hnd'

theorem mem_Na_of_commute {c : G} (hc : c ∈ lineN D a d) (hcx : Commute x (c * x * c⁻¹)) :
    c ∈ nCore D a ⊓ Subgroup.centralizer {d} := by
  have := C.finite
  have hclass := C.isClass
  have hD := C.root
  have hca : Commute c a := C.commute_of_mem_lineN hc (left_mem_line C.ha)
  have hca' : c * a * c⁻¹ = a := by rw [hca.eq, mul_inv_cancel_right]
  set x' := c * x * c⁻¹ with hx'
  have hx'D : x' ∈ D := conj_mem_of_isClass hclass c C.hx
  have hax' : Commute a x' := by
    have := (Commute.conj_iff c).2 C.hax
    rwa [hca'] at this
  have hax'D : a * x' ∈ D := by
    have := conj_mem_of_isClass hclass c C.haxD
    rwa [show c * (a * x) * c⁻¹ = c * a * c⁻¹ * (c * x * c⁻¹) by group, hca'] at this
  have hx'T : x' ∉ rootSet D a := by
    intro h
    apply C.hxTa
    have h1 : x' ∈ rootSet D (c * a * c⁻¹) := by rw [hca']; exact h
    rw [rootSet_conj hclass] at h1
    obtain ⟨e, he, he'⟩ := h1
    have : e = x := by simpa [hx'] using he'
    exact this ▸ he
  have hx'L : x' ∈ rootGroup D a ⊔ rootGroup D x := by
    rcases C.setting.mem_rootSet_or_collinear C.hx hx'D hcx.symm with h | ⟨h1, h2⟩
    · exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D x h)
    · exact mem_sup_of_collinear_of_lineTI C.setting.hyp C.setting.closure C.setting.special C.ha
        C.hx C.hax C.haxD C.hxTa C.lineTI_x hx'D hax'.symm (by rw [← hax'.eq]; exact hax'D) h1.symm
        (by rw [← h1.eq]; exact h2)
  have hLeq := C.setting.sup_rootGroup_eq_of_mem_sup C.ha hx'D C.hx hax' hx'T C.hax C.haxD C.hxTa
    hx'L
  refine C.mem_Na_of_map_conj_eq hc ?_
  rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, hca', ← hx', hLeq]

theorem orderOf_mul_conj_eq_four {P : Subgroup G} (hP : IsPGroup 2 P) {c : G} (hcP : c ∈ P)
    (hxcP : x * c * x⁻¹ ∈ P) (hc : c ∈ lineN D a d)
    (hcN : c ∉ nCore D a ⊓ Subgroup.centralizer {d}) : orderOf (x * (c * x * c⁻¹)) = 4 := by
  have hD := C.root
  have hx'D : c * x * c⁻¹ ∈ D := conj_mem_of_isClass C.isClass c C.hx
  have hw : x * (c * x * c⁻¹) ∈ P := by
    rw [show x * (c * x * c⁻¹) = x * c * x⁻¹ * c⁻¹ by rw [hD.inv_eq C.hx]; group]
    exact Subgroup.mul_mem _ hxcP (Subgroup.inv_mem _ hcP)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD C.hx hx'D with h | h | ⟨hodd, hnc⟩
  · exact absurd (C.mem_Na_of_commute hc h) hcN
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨_, hw⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 : orderOf (x * (c * x * c⁻¹)) = 1 := by
      rcases k.eq_zero_or_pos with h0 | h0
      · rw [hk, h0, pow_zero]
      · rw [hk] at hodd
        exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, h0.ne'⟩))
    rw [orderOf_eq_one_iff] at h1
    have : c * x * c⁻¹ = x := (eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq C.hx)
    exact hnc (by rw [this])

theorem le_Na_of_forall_mem {P : Subgroup G} (hPN : P ≤ lineN D a d)
    (hxP : ∀ c ∈ P, x * c * x⁻¹ ∈ P)
    (hPT : ∀ t ∈ P, t ∈ rootGroup D a ⊔ rootGroup D d → t = 1) :
    P ≤ nCore D a ⊓ Subgroup.centralizer {d} := by
  intro c hc
  by_contra hcN
  have hD := C.root
  have hx'D : c * x * c⁻¹ ∈ D := conj_mem_of_isClass C.isClass c C.hx
  have h4 := C.orderOf_mul_conj_eq_four (C.isPGroup_lineN.to_le hPN) hc (hxP c hc) (hPN hc) hcN
  have hw : x * (c * x * c⁻¹) ∈ P := by
    rw [show x * (c * x * c⁻¹) = x * c * x⁻¹ * c⁻¹ by rw [hD.inv_eq C.hx]; group]
    exact Subgroup.mul_mem _ (hxP c hc) (Subgroup.inv_mem _ hc)
  have hw2D := hD.sq_mem C.hx hx'D h4
  have hw2P : (x * (c * x * c⁻¹)) ^ 2 ∈ P := Subgroup.pow_mem _ hw 2
  have hw2T : (x * (c * x * c⁻¹)) ^ 2 ∈ rootGroup D a ⊔ rootGroup D d :=
    C.setting.lineCentralizerEq a C.ha d C.hd C.had C.hadD C.hdT C.lineTI _ hw2D
      (C.commute_of_mem_lineN (hPN hw2P) (left_mem_line C.ha))
      (C.commute_of_mem_lineN (hPN hw2P) (right_mem_line C.hd))
  exact hD.ne_one hw2D (hPT _ hw2P hw2T)

theorem exists_mem_Nd_not_mem (h3 : 3 ≤ (rootLines D a).ncard) :
    ∃ k ∈ nCore D d ⊓ Subgroup.centralizer {a}, k ∉ nCore D a := by
  obtain ⟨L₃, hL₃, h1, h2⟩ := exists_mem_rootLines_ne_ne (L₁ := rootGroup D a ⊔ rootGroup D d)
    (L₂ := rootGroup D a ⊔ rootGroup D x) h3
  obtain ⟨c, hc, hac, hacD, hcT, rfl⟩ := hL₃
  have hcL : c ∉ rootGroup D a ⊔ rootGroup D d := fun h =>
    h1 (C.setting.sup_rootGroup_eq_of_mem_sup C.ha hc C.hd hac hcT C.had C.hadD C.hdT h)
  obtain ⟨⟨k, hk, hkL⟩, -⟩ := rootLinesRegularStep G D C.setting a C.ha d C.hd C.had C.hadD C.hdT
    x C.hx C.hax C.haxD C.hxT c hc hac hacD hcL
  refine ⟨k, hk, fun hkM => h2 ?_⟩
  rw [← hkL, C.map_conj_eq_of_mem_nCore hkM]

theorem T_le_lineN₀ : rootGroup D a ⊔ rootGroup D d ≤ lineN₀ D a d := by
  refine le_inf (C.setting.sup_rootGroup_le_nCore C.ha C.hd C.had) ?_
  rw [sup_comm]
  exact C.setting.sup_rootGroup_le_nCore C.hd C.ha C.had.symm

theorem conj_mem_T {g : G} (hg : g ∈ rootGroup D x ⊔ rootGroup D y) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : g * t * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have hle : rootGroup D x ⊔ rootGroup D y ≤
      Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_ <;> rw [rootGroup, Subgroup.closure_le] <;> intro e he
    · have hae : Commute a e := ((he.2 a C.ha).2 C.hax.symm).symm
      exact RootSubgroup.mem_normalizer_of_map_eq
        (C.setting.map_conj_eq_of_commute C.ha he.1 hae C.mem_rootLines_a)
    · have hde : Commute d e := ((he.2 d C.hd).2 C.hdy.symm).symm
      exact RootSubgroup.mem_normalizer_of_map_eq
        (C.setting.map_conj_eq_of_commute C.hd he.1 hde C.mem_rootLines_d)
  exact (Subgroup.mem_normalizer_iff.1 (hle hg) t).1 ht

theorem mem_rootGroup_a_of_commute {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d)
    (htx : Commute t x) : t ∈ rootGroup D a := by
  rw [sup_comm] at ht
  exact mem_rootGroup_of_mem_line_of_commute C.root C.setting.closure C.hd C.ha C.had.symm C.hx
    C.hax (fun h => C.not_commute_xd h.symm) ht htx

theorem mem_rootGroup_d_of_commute {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d)
    (hty : Commute t y) : t ∈ rootGroup D d :=
  mem_rootGroup_of_mem_line_of_commute C.root C.setting.closure C.ha C.hd C.had C.hy C.hdy
    (fun h => C.not_commute_ya h.symm) ht hty

theorem card_T : Nat.card (rootGroup D a ⊔ rootGroup D d : Subgroup G) =
    Nat.card (rootGroup D a) ^ 2 := by
  have := C.finite
  rw [card_sup_rootGroup C.setting.hyp C.setting.closure C.ha C.hd C.had C.hdT,
    card_rootGroup_eq C.isClass C.root C.setting.closure C.ha C.hd, sq]

theorem exists_natural {K : Type*} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2]
    (hK : Nat.card K = Nat.card (rootGroup D a))
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφx : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      upperUnipotent K)
    (hφy : ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      lowerUnipotent K) :
    ∃ θ₀ : (Fin 2 → K) → G, ARS.IsNaturalModule φ θ₀ ∧
      (∀ t, t ∈ rootGroup D a ⊔ rootGroup D d ↔ ∃ v, θ₀ v = t) ∧
      (∀ s : K, θ₀ ![s, 0] ∈ rootGroup D a) ∧ (∀ s : K, θ₀ ![0, s] ∈ rootGroup D d) := by
  classical
  have := C.finite
  have hD := C.root
  have hc := C.setting.closure
  have hxX : x ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D x (mem_rootSet_self C.hx))
  have hyX : y ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self C.hy))
  have hN : ∀ n ∈ rootGroup D a ⊔ rootGroup D d, ∀ m ∈ rootGroup D a ⊔ rootGroup D d,
      Commute n m := fun n hn m hm => commute_of_mem_sup_rootGroup C.ha C.hd C.had hn hm
  have hXN : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ n ∈ rootGroup D a ⊔ rootGroup D d,
      g * n * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := fun g hg n hn => C.conj_mem_T hg hn
  have hne : rootSet D a ≠ rootSet D d := fun h => C.hdT (h ▸ mem_rootSet_self C.hd)
  have hfix : ∀ n ∈ rootGroup D a ⊔ rootGroup D d,
      (∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute g n) → n = 1 := by
    intro n hn hnX
    have h1 := C.mem_rootGroup_a_of_commute hn (hnX x hxX).symm
    have h2 := C.mem_rootGroup_d_of_commute hn (hnX y hyX).symm
    have h3 : n ∈ rootGroup D a ⊓ rootGroup D d := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rwa [rootGroup_inf_eq_bot_of_rootClosure hD hc C.ha C.hd hne, Subgroup.mem_bot] at h3
  have hxM : rootGroup D x ≤ nCore D a :=
    le_sup_right.trans (C.setting.sup_rootGroup_le_nCore C.ha C.hx C.hax)
  have hTM : rootGroup D a ⊔ rootGroup D d ≤ nCore D a :=
    C.setting.sup_rootGroup_le_nCore C.ha C.hd C.had
  have hquad : ∀ n ∈ rootGroup D a ⊔ rootGroup D d, ∀ g ∈ rootGroup D x, ∀ g' ∈ rootGroup D x,
      Commute g' ⁅g, n⁆ := by
    intro n hn g hg g' hg'
    have h1 : ⁅g, n⁆ ∈ rootGroup D a := by
      rw [commutatorElement_def]
      exact nCoreCommutatorInRoot_of_hyp C.setting.hyp hc a C.ha g (hxM hg) n (hTM hn)
    exact commute_of_mem_rootGroup_of_commute' C.ha hg' h1 C.hax.symm
  have hwA : ∀ g ∈ rootGroup D x, Commute g a := fun g hg =>
    commute_of_mem_rootGroup_of_commute hg C.ha C.hax.symm
  obtain ⟨θ, hθ, hrange, -⟩ := ARS.exists_natural_of_quadratic_conj φ hφx hN hXN hfix hquad
    (left_mem_line C.ha) hwA (hD.ne_one C.ha)
  have hsub : Set.range θ ⊆ ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    rw [hrange]
    refine (Subgroup.closure_le (rootGroup D a ⊔ rootGroup D d)).2 ?_
    rintro _ ⟨g, rfl⟩
    exact hXN g g.2 a (left_mem_line C.ha)
  have hcardK : Nat.card (Fin 2 → K) = Nat.card (rootGroup D a ⊔ rootGroup D d : Subgroup G) := by
    rw [Nat.card_fun, Nat.card_fin, hK, C.card_T]
  have hrange' : Set.range θ = ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_range_of_injective hθ.injective, hcardK]
    exact (Nat.card_coe_set_eq ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G)).ge
  refine ⟨θ, hθ, fun t => ?_, fun s => ?_, fun s => ?_⟩
  · rw [← SetLike.mem_coe, ← hrange']
    exact Iff.rfl
  · have hmem : θ ![s, 0] ∈ rootGroup D a ⊔ rootGroup D d := hsub ⟨_, rfl⟩
    refine C.mem_rootGroup_a_of_commute hmem ?_
    have hφ : φ ⟨x, hxX⟩ ∈ upperUnipotent K :=
      (ARS.NaturalModule.coe_mem_iff hφx ⟨x, hxX⟩).1
        (rootSet_subset_rootGroup D x (mem_rootSet_self C.hx))
    obtain ⟨u, hu⟩ := RankOne.mem_upperUnipotent_iff K |>.1 hφ
    have h1 := hθ.map_mulVec ⟨x, hxX⟩ ![s, 0]
    rw [hu, Higman.upperElt_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      add_zero] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
  · have hmem : θ ![0, s] ∈ rootGroup D a ⊔ rootGroup D d := hsub ⟨_, rfl⟩
    refine C.mem_rootGroup_d_of_commute hmem ?_
    have hφ : φ ⟨y, hyX⟩ ∈ lowerUnipotent K :=
      (ARS.NaturalModule.coe_mem_iff hφy ⟨y, hyX⟩).1
        (rootSet_subset_rootGroup D y (mem_rootSet_self C.hy))
    obtain ⟨u, hu⟩ := RankOne.mem_lowerUnipotent_iff K |>.1 hφ
    have h1 := hθ.map_mulVec ⟨y, hyX⟩ ![0, s]
    rw [hu, Higman.lowerElt_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      zero_add] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm

end LineConf

theorem card_dvd_ncard_of_centralizes (C : ThinGateCounter G D) {a d : G} (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (P : Subgroup G) (hPT : ∀ g ∈ P, ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute g t) :
    Nat.card P ∣ (oneOmega D a \ gatedPoints D a (rootGroup D a ⊔ rootGroup D d)).ncard := by
  classical
  have := C.hyp.finite
  have hD := C.hyp.root
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hPa : ∀ g ∈ P, Commute g a := fun g hg => hPT g hg a (left_mem_line ha)
  set Ω : Set (Subgroup G) := oneOmega D a \ gatedPoints D a (rootGroup D a ⊔ rootGroup D d)
    with hΩ
  have hmapΩ : ∀ g ∈ P, ∀ B ∈ Ω, B.map (MulAut.conj g).toMonoidHom ∈ Ω := by
    intro g hg B hB
    refine ⟨RootMany.map_conj_mem_oneOmega C (hPa g hg) hB.1, fun hgB => hB.2 ?_⟩
    have h := RootMany.map_conj_mem_gatedPoints C (hPa g⁻¹ (P.inv_mem hg))
      (hPT g⁻¹ (P.inv_mem hg)) hgB
    rwa [map_conj_inv_map_conj_eq] at h
  let _ : MulAction P Ω :=
    { smul := fun g B => ⟨B.1.map (MulAut.conj (g : G)).toMonoidHom, hmapΩ g g.2 B B.2⟩
      one_smul := fun B => Subtype.ext (RankOne.map_conj_one B.1)
      mul_smul := fun g g' B => Subtype.ext (RankOne.map_conj_mul B.1 g g') }
  have hdvd := RootMany.card_dvd_of_free (P := P) (β := Ω) fun g B hgB => ?_
  · rwa [Nat.card_coe_set_eq] at hdvd
  obtain ⟨⟨u, hu, hBu, hau, hoddau, hu1⟩, hBg⟩ := B.2
  have hnogate : ∀ p ∈ D, p ∈ rootGroup D a ⊔ rootGroup D d → orderOf (u * p) ≠ 4 :=
    fun p hp hpT h4 => hBg ⟨B.2.1, u, hu, hBu, p, hp, hpT, h4⟩
  have hgB' : (B : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = B :=
    congrArg Subtype.val hgB
  have huA : u ∈ rootGroup D u := rootSet_subset_rootGroup D u (mem_rootSet_self hu)
  have hguA : (g : G) * u * (g : G)⁻¹ ∈ rootGroup D u := by
    have : (g : G) * u * (g : G)⁻¹ ∈ (B : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [hBu]
      exact ⟨u, huA, rfl⟩
    rwa [hgB', hBu] at this
  have hguT : (g : G) * u * (g : G)⁻¹ ∈ rootSet D u :=
    mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure hu hguA (fun h => hD.ne_one hu (by
      have := congrArg (fun w => (g : G)⁻¹ * w * g) h
      simpa [mul_assoc] using this))
  have hga' : ∀ a' ∈ rootSet D a, Commute (g : G) a' := fun a' h' =>
    hPT g g.2 a' (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hgu := fun {w : G} (hw : w ∈ rootGroup D u) =>
    commute_of_conj_mem_rootSet_of_centralizes' C.hyp C.closure C.special ha hu hau hoddau hu1
      hga' hguT hw
  have htop := C.gen a ha d hd u hu had hadD hdT hau hoddau hu1 hnogate
  have hcen : (g : G) ∈ Subgroup.center G := by
    have hle : rootGroup D a ⊔ rootGroup D d ⊔ rootGroup D u ≤
        Subgroup.centralizer ({(g : G)} : Set G) := by
      refine sup_le (fun t ht => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hPT g g.2 t ht).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hgu hw).eq.symm
    rw [htop] at hle
    rw [Subgroup.mem_center_iff]
    intro h'
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top h'))
  rw [C.hyp.center_eq_bot, Subgroup.mem_bot] at hcen
  exact Subtype.ext hcen

theorem exists_lineConf (C : ThinGateCounter G D) : ∃ a d x y : G, LineConf D a d x y := by
  have hLS := RootMany.lineSetting_of_counter C
  obtain ⟨b, hb, c₁, hc₁, c₂, hc₂, c₃, -, hc, h2, -, -⟩ := C.three
  obtain ⟨hbc₁, hbc₁D, hc₁T⟩ := hc c₁ (by simp)
  obtain ⟨hbc₂, hbc₂D, hc₂T⟩ := hc c₂ (by simp)
  have hc₁bD : c₁ * b ∈ D := by rw [← hbc₁.eq]; exact hbc₁D
  have hbT : b ∉ rootSet D c₁ := fun h => hc₁T (mem_rootSet_comm hc₁ h)
  have hT : rootGroup D b ⊔ rootGroup D c₁ ∈ rootLines D c₁ :=
    ⟨b, hb, hbc₁.symm, hc₁bD, hbT, sup_comm _ _⟩
  obtain ⟨L, ⟨y, hy, hc₁y, hc₁yD, hyT, rfl⟩, hLT⟩ := hLS.exists_ne_mem_rootLines hc₁ hT
  refine ⟨b, c₁, c₂, y, hLS, hb, hc₁, hbc₁, hbc₁D, hc₁T, hc₂, hbc₂, hbc₂D, h2, hy, hc₁y, hc₁yD,
    fun hyL => hLT ?_⟩
  rw [sup_comm (rootGroup D b)] at hyL ⊢
  exact hLS.sup_rootGroup_eq_of_mem_sup hc₁ hy hb hc₁y hyT hbc₁.symm hc₁bD hbT hyL

end RootOne

end CFSG.Timmesfeld.Bridge
