module

public import CFSG.Quasithin.H13.U3Codim3
public import CFSG.Quasithin.H13.U3Hyp1223
public import CFSG.Quasithin.H13.U3HullData
public import CFSG.Quasithin.H13.U3HullAbs
public import CFSG.Quasithin.H13.A6F91General
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Transport

variable {V : Subgroup G} [IsElementaryAbelian 2 V] {Φ : Additive V ≃ₗ[ZMod 2] W6}

theorem phi_mul' {x y : G} (hx : x ∈ V) (hy : y ∈ V) :
    Φ (Additive.ofMul (⟨x * y, V.mul_mem hx hy⟩ : V)) =
      Φ (Additive.ofMul (⟨x, hx⟩ : V)) + Φ (Additive.ofMul (⟨y, hy⟩ : V)) := by
  rw [← map_add]
  rfl

theorem phi_inv' {x : G} (hx : x ∈ V) :
    Φ (Additive.ofMul (⟨x⁻¹, V.inv_mem hx⟩ : V)) = -Φ (Additive.ofMul (⟨x, hx⟩ : V)) := by
  rw [← map_neg]
  rfl

theorem phi_injective' {x y : G} (hx : x ∈ V) (hy : y ∈ V)
    (h : Φ (Additive.ofMul (⟨x, hx⟩ : V)) = Φ (Additive.ofMul (⟨y, hy⟩ : V))) : x = y :=
  congrArg Subtype.val (Additive.ofMul.injective (Φ.injective h))

noncomputable def elOf (Φ : Additive V ≃ₗ[ZMod 2] W6) (w : W6) : G :=
  ((Additive.toMul (Φ.symm w) : V) : G)

theorem elOf_mem (w : W6) : elOf Φ w ∈ V := (Additive.toMul (Φ.symm w)).2

theorem phi_elOf (w : W6) : Φ (Additive.ofMul (⟨elOf Φ w, elOf_mem w⟩ : V)) = w := by
  change Φ (Additive.ofMul (Additive.toMul (Φ.symm w))) = w
  rw [ofMul_toMul, LinearEquiv.apply_symm_apply]

theorem elOf_mem_pullSub {P : Submodule (ZMod 2) W6} {w : W6} :
    elOf Φ w ∈ pullSub Φ P ↔ w ∈ P := by
  rw [mem_pullSub]
  constructor
  · rintro ⟨h, hP⟩
    rwa [show (⟨elOf Φ w, h⟩ : V) = ⟨elOf Φ w, elOf_mem w⟩ from rfl, phi_elOf] at hP
  · intro hw
    exact ⟨elOf_mem w, by rw [phi_elOf]; exact hw⟩

theorem pullSub_le_iff {P Q : Submodule (ZMod 2) W6} : pullSub Φ P ≤ pullSub Φ Q ↔ P ≤ Q := by
  refine ⟨fun h w hw => ?_, pullSub_mono⟩
  have := h (elOf_mem_pullSub.2 hw)
  exact elOf_mem_pullSub.1 this

theorem pullSub_top : pullSub Φ ⊤ = V :=
  le_antisymm (pullSub_le _) fun _ hx => mem_pullSub.2 ⟨hx, Submodule.mem_top⟩

noncomputable def subSpace (Φ : Additive V ≃ₗ[ZMod 2] W6) (X : Subgroup G) :
    Submodule (ZMod 2) W6 :=
  (subOf V X).map (Φ : Additive V →ₗ[ZMod 2] W6)

theorem pullSub_subSpace {X : Subgroup G} (hXV : X ≤ V) : pullSub Φ (subSpace Φ X) = X :=
  pullSub_map_subOf hXV

theorem mem_subSpace {X : Subgroup G} {x : G} (hx : x ∈ V) :
    Φ (Additive.ofMul (⟨x, hx⟩ : V)) ∈ subSpace Φ X ↔ x ∈ X := by
  rw [subSpace, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  exact mem_subOf

theorem phi_conj' {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {x : G} (hx : x ∈ V) :
    Φ (Additive.ofMul (⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn x).1 hx⟩ : V)) =
      glLin k (Φ (Additive.ofMul (⟨x, hx⟩ : V))) :=
  phi_conj hn hk hx

theorem comm_mem_pullSub {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {v : G} (hv : v ∈ V) (P : Submodule (ZMod 2) W6) :
    v * n * v⁻¹ * n⁻¹ ∈ pullSub Φ P ↔
      glLin k (Φ (Additive.ofMul (⟨v, hv⟩ : V))) - Φ (Additive.ofMul (⟨v, hv⟩ : V)) ∈ P := by
  have hv' : v⁻¹ ∈ V := V.inv_mem hv
  have hnv : n * v⁻¹ * n⁻¹ ∈ V := (mem_normalizer_iff.1 hn _).1 hv'
  have e : v * n * v⁻¹ * n⁻¹ = v * (n * v⁻¹ * n⁻¹) := by group
  have hmem : v * n * v⁻¹ * n⁻¹ ∈ V := by rw [e]; exact V.mul_mem hv hnv
  have hphi : Φ (Additive.ofMul (⟨v * n * v⁻¹ * n⁻¹, hmem⟩ : V)) =
      -(glLin k (Φ (Additive.ofMul (⟨v, hv⟩ : V))) - Φ (Additive.ofMul (⟨v, hv⟩ : V))) := by
    have h1 : (⟨v * n * v⁻¹ * n⁻¹, hmem⟩ : V) = ⟨v * (n * v⁻¹ * n⁻¹), V.mul_mem hv hnv⟩ :=
      Subtype.ext e
    rw [h1, phi_mul' hv hnv, phi_conj' hn hk hv', phi_inv' hv, map_neg]
    abel
  rw [mem_pullSub]
  constructor
  · rintro ⟨h, hP⟩
    rw [show (⟨v * n * v⁻¹ * n⁻¹, h⟩ : V) = ⟨v * n * v⁻¹ * n⁻¹, hmem⟩ from rfl, hphi,
      neg_mem_iff] at hP
    exact hP
  · intro hP
    exact ⟨hmem, by rw [hphi]; exact P.neg_mem hP⟩

theorem conj_mem_pullSub {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {x : G} (hx : x ∈ V) (P : Submodule (ZMod 2) W6) :
    n * x * n⁻¹ ∈ pullSub Φ P ↔ glLin k (Φ (Additive.ofMul (⟨x, hx⟩ : V))) ∈ P := by
  rw [mem_pullSub]
  constructor
  · rintro ⟨h, hP⟩
    rwa [phi_conj' hn hk hx] at hP
  · intro hP
    exact ⟨(mem_normalizer_iff.1 hn x).1 hx, by rw [phi_conj' hn hk hx]; exact hP⟩

theorem mem_centralizer_pullSub_iff {n : G} (hn : n ∈ normalizer (V : Set G))
    {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    (P : Submodule (ZMod 2) W6) :
    n ∈ centralizer (pullSub Φ P : Set G) ↔ ∀ w ∈ P, glLin k w = w := by
  rw [mem_centralizer_iff]
  constructor
  · intro h w hw
    have hx := elOf_mem (Φ := Φ) w
    have h1 := h _ (elOf_mem_pullSub.2 hw)
    have h2 : n * elOf Φ w * n⁻¹ = elOf Φ w := by rw [← h1, mul_inv_cancel_right]
    have h3 := phi_conj' hn hk hx
    rw [show (⟨n * elOf Φ w * n⁻¹, (mem_normalizer_iff.1 hn _).1 hx⟩ : V) = ⟨elOf Φ w, hx⟩ from
      Subtype.ext h2, phi_elOf] at h3
    exact h3.symm
  · intro h x hx
    obtain ⟨hxV, hxP⟩ := mem_pullSub.1 hx
    have h3 := phi_conj' hn hk hxV
    rw [h _ hxP] at h3
    have h4 := phi_injective' _ hxV h3
    calc x * n = n * x * n⁻¹ * n := by rw [h4]
      _ = n * x := by group

theorem mem_centralizer_V_iff {n : G} (hn : n ∈ normalizer (V : Set G))
    {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k) :
    n ∈ centralizer (V : Set G) ↔ k = 1 := by
  rw [← u3ConjLin_eq_one_iff (H := normalizer (V : Set G)) (hH := le_rfl) ⟨n, hn⟩]
  constructor
  · intro h
    rw [h, map_one] at hk
    exact glLin.injective (by rw [← hk, map_one])
  · intro h
    rw [h, map_one] at hk
    exact (linConj Φ).injective (by rw [hk, map_one])

theorem mem_normalizer_pullSub {n : G} (hn : n ∈ normalizer (V : Set G))
    {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    {P : Submodule (ZMod 2) W6} (hP : P.map (glLin k : W6 →ₗ[ZMod 2] W6) = P) :
    n ∈ normalizer (pullSub Φ P : Set G) := by
  have h := pullSub_map_glLin hn hk P
  rw [hP] at h
  have := mem_normalizer_of_conjugate_eq h.symm
  exact inv_inv n ▸ (normalizer (pullSub Φ P : Set G)).inv_mem this

theorem subSpace_invariant {X : Subgroup G} {n : G}
    (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    (hnX : n ∈ normalizer (X : Set G)) : ∀ w ∈ subSpace Φ X, glLin k w ∈ subSpace Φ X := by
  intro w hw
  have hx := elOf_mem (Φ := Φ) w
  have hwX : elOf Φ w ∈ X := by
    rw [← mem_subSpace hx, phi_elOf]
    exact hw
  have h1 := phi_conj' hn hk hx
  rw [phi_elOf] at h1
  rw [← h1, mem_subSpace]
  exact (mem_normalizer_iff.1 hnX _).1 hwX

theorem J6_le_N6 : J6 ≤ N6 := le_sup_right

omit [IsElementaryAbelian 2 V] in
theorem isElemAbelian_of_isElementaryAbelian' (V : Subgroup G) [IsElementaryAbelian 2 V] :
    IsElemAbelian 2 V := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr inferInstance

theorem sq_eq_one_of_fixes
    {k : GL (Fin 6) (ZMod 2)} (hk : k ∈ N6)
    (hfix : ∀ w ∈ V3sub, glLin k w = w) : k * k = 1 := by
  apply glLin.injective
  ext w : 1
  have hu := sub_V3sub_of_fixes hk hfix w
  have h1 := hfix _ hu
  rw [map_sub] at h1
  have h2 : glLin k (glLin k w) = glLin k w - w + glLin k w := by
    rw [← h1]
    abel
  rw [map_mul, LinearEquiv.mul_apply, h2,
    show glLin k w - w + glLin k w = glLin k w + glLin k w - w by abel, W6_add_self, zero_sub,
    neg_eq_of_add_eq_zero_left (W6_add_self w), map_one]
  rfl

theorem xGL_pow_two_pow (a : ℕ) : xGL ^ 2 ^ a = xGL ∨ xGL ^ 2 ^ a = xGL * xGL := by
  induction a with
  | zero => left; rw [pow_zero, pow_one]
  | succ a ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · right; rw [h, pow_two]
    · left; rw [h, pow_two, xGL_pow_four]

end Transport

structure HullSetting
    (G : Type) [Group G] [Finite G] (T L V : Subgroup G)
    [IsElementaryAbelian 2 V] (z : G) where
  h1332 : Stmt13_3_2
  hH : QTH13 G T L
  hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1
  hF : QTU3InternalFrame T L V z
  Φ : Additive V ≃ₗ[ZMod 2] W6
  hL : ∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j
  hLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j
  hN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
    linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k
  hT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}
variable
  (S : HullSetting G T L V z)
include S

theorem hLV : L ≤ normalizer (V : Set G) := S.hF.2.2.2.2.2.2.1

theorem hTV : T ≤ normalizer (V : Set G) := S.hF.2.2.2.2.2.2.2.1

theorem hVT : V ≤ T := S.hF.2.1

theorem hV64 : Nat.card V = 64 := S.hF.2.2.2.1

theorem hTL : T ≤ normalizer (L : Set G) := S.hF.1

theorem hz2 : orderOf z = 2 := S.hF.2.2.2.2.2.2.2.2.2.2.2.2

theorem hVz : V ⊓ centralizer (T : Set G) = zpowers z := S.hF.2.2.2.2.2.2.2.2.2.2.2.1

theorem hzVT : z ∈ V ⊓ centralizer (T : Set G) := by
  rw [S.hVz]
  exact mem_zpowers z

theorem hzV : z ∈ V := S.hzVT.1

theorem hz1 : z ≠ 1 := by
  intro h
  have := S.hz2
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

noncomputable def rho : normalizer (V : Set G) →* GL (Fin 6) (ZMod 2) :=
  glLin.symm.toMonoidHom.comp
    ((linConj S.Φ).toMonoidHom.comp (u3ConjLin V (normalizer (V : Set G)) le_rfl))

theorem rho_spec (n : normalizer (V : Set G)) :
    linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin (S.rho n) := by
  simp only [rho, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]

theorem rho_mem_N6 (n : normalizer (V : Set G)) : S.rho n ∈ N6 := by
  obtain ⟨k, hk, hkn⟩ := S.hN n
  rw [show S.rho n = k from glLin.injective (by rw [← S.rho_spec, hkn])]
  exact hk

theorem phi_z
    : S.Φ (Additive.ofMul (⟨z, S.hzV⟩ : V)) = vecOf 15 := by
  classical
  set g15 := elOf S.Φ (vecOf 15) with hg15
  have hg15V : g15 ∈ V := elOf_mem _
  have hg : S.Φ (Additive.ofMul (⟨g15, hg15V⟩ : V)) = vecOf 15 := phi_elOf _
  have hg15C : g15 ∈ V ⊓ centralizer (T : Set G) := by
    refine ⟨hg15V, mem_centralizer_iff.2 fun t ht => ?_⟩
    obtain ⟨s, hs, hst⟩ := S.hT t ht
    obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
    have h2 : S.Φ (Additive.ofMul ⟨t * g15 * t⁻¹,
        (mem_normalizer_iff.1 (S.hTV ht) g15).1 hg15V⟩) = vecOf 15 := by
      rw [phi_conj (S.hTV ht) hst hg15V, hg, glLin_apply, coe_s0GL hi, colMat_mulVec_vecOf,
        s0c_fix_fifteen _ (by
          rw [s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; exact hi)]
          exact List.getElem_mem _)]
    have h4 : t * g15 * t⁻¹ = g15 := phi_injective' _ hg15V (h2.trans hg.symm)
    calc t * g15 = t * g15 * t⁻¹ * t := by group
      _ = g15 * t := by rw [h4]
  rw [S.hVz] at hg15C
  have hg151 : g15 ≠ 1 := by
    intro h
    have h1 : S.Φ (Additive.ofMul (⟨g15, hg15V⟩ : V)) = 0 := by
      rw [show (⟨g15, hg15V⟩ : V) = 1 from Subtype.ext h]
      exact map_zero _
    rw [hg] at h1
    exact absurd (vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
      (h1.trans vecOf_zero.symm)) (by norm_num)
  have hgz : g15 = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, S.hz2, Finset.mem_image] at hg15C
    obtain ⟨k, hk, hkz⟩ := hg15C
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hkz
      exact absurd hkz.symm hg151
    · rw [pow_one] at hkz
      exact hkz.symm
  have : (⟨z, S.hzV⟩ : V) = ⟨g15, hg15V⟩ := Subtype.ext hgz.symm
  rw [this, hg]

noncomputable def V₁ : Subgroup G := pullSub S.Φ V1sub
noncomputable def V₂ : Subgroup G := pullSub S.Φ V2sub
noncomputable def V₃ : Subgroup G := pullSub S.Φ V3sub
noncomputable def V₅ : Subgroup G := pullSub S.Φ V5sub

theorem card_V₁ : Nat.card S.V₁ = 2 := by rw [V₁, card_pullSub, card_V1sub]
theorem card_V₂ : Nat.card S.V₂ = 4 := by rw [V₂, card_pullSub, card_V2sub]
theorem card_V₃ : Nat.card S.V₃ = 8 := by rw [V₃, card_pullSub, card_V3sub]
theorem card_V₅ : Nat.card S.V₅ = 32 := by rw [V₅, card_pullSub, card_V5sub]

theorem z_mem_V₁
    : z ∈ S.V₁ := mem_pullSub.2 ⟨S.hzV, by rw [S.phi_z]; exact vecOf_fifteen_mem_V1sub⟩

theorem V₁_eq :
    S.V₁ = zpowers z := by
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 S.z_mem_V₁) ?_).symm
  rw [S.card_V₁, Nat.card_zpowers, S.hz2]

theorem le12 : S.V₁ ≤ S.V₂ := pullSub_mono V1sub_le_V2sub
theorem le23 : S.V₂ ≤ S.V₃ := pullSub_mono V2sub_le_V3sub
theorem le35 : S.V₃ ≤ S.V₅ := pullSub_mono V3sub_le_V5sub
theorem le5 : S.V₅ ≤ V := pullSub_le _
theorem le3 : S.V₃ ≤ V := pullSub_le _

noncomputable def H : Subgroup G := centralizer (S.V₁ : Set G)

theorem H_eq :
    S.H = centralizer ({z} : Set G) := by
  rw [H, V₁_eq, zpowers_eq_closure, centralizer_closure]

theorem mem_H_iff
    {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k) :
    n ∈ S.H ↔ glLin k (vecOf 15) = vecOf 15 := by
  rw [H_eq, mem_centralizer_singleton_iff]
  have h1 := phi_conj' hn hk S.hzV
  rw [S.phi_z] at h1
  constructor
  · intro h
    have h2 : n * z * n⁻¹ = z := by rw [h, mul_inv_cancel_right]
    rw [← h1, ← S.phi_z]
    congr 2
    exact Subtype.ext h2
  · intro h
    have h2 := phi_injective' _ S.hzV (h1.trans (h.trans S.phi_z.symm))
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h2]

theorem V₁_le_V₃ : S.V₁ ≤ S.V₃ := S.le12.trans S.le23

theorem exists_lift {j : GL (Fin 6) (ZMod 2)} (hj : j ∈ J6) :
    ∃ l ∈ L, ∃ hl : l ∈ normalizer (V : Set G),
      linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hl⟩) = glLin j := by
  obtain ⟨l, hl, hlj⟩ := S.hLs j hj
  exact ⟨l, hl, S.hLV hl, hlj⟩

noncomputable def l₁ : G := (S.exists_lift xGL_mem).choose
theorem l₁_mem : S.l₁ ∈ L := (S.exists_lift xGL_mem).choose_spec.1
theorem l₁_N : S.l₁ ∈ normalizer (V : Set G) := (S.exists_lift xGL_mem).choose_spec.2.choose
theorem l₁_spec : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨S.l₁, S.l₁_N⟩) =
    glLin xGL := (S.exists_lift xGL_mem).choose_spec.2.choose_spec

noncomputable def l₂ : G := (S.exists_lift g2GL_mem).choose
theorem l₂_mem : S.l₂ ∈ L := (S.exists_lift g2GL_mem).choose_spec.1
theorem l₂_N : S.l₂ ∈ normalizer (V : Set G) := (S.exists_lift g2GL_mem).choose_spec.2.choose
theorem l₂_spec : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨S.l₂, S.l₂_N⟩) =
    glLin g2GL := (S.exists_lift g2GL_mem).choose_spec.2.choose_spec

noncomputable def l₃ : G := (S.exists_lift yGL_mem).choose
theorem l₃_N : S.l₃ ∈ normalizer (V : Set G) := (S.exists_lift yGL_mem).choose_spec.2.choose
theorem l₃_spec : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨S.l₃, S.l₃_N⟩) =
    glLin yGL := (S.exists_lift yGL_mem).choose_spec.2.choose_spec

theorem l₁_H
    : S.l₁ ∈ S.H := (S.mem_H_iff S.l₁_N S.l₁_spec).2 xGL_fix

theorem l₂_H
    : S.l₂ ∈ S.H := (S.mem_H_iff S.l₂_N S.l₂_spec).2 g2GL_fix

theorem l₁_V₃ : S.l₁ ∈ normalizer (S.V₃ : Set G) :=
  mem_normalizer_pullSub S.l₁_N S.l₁_spec (map_V3sub_of_fix (J6_le_N6 xGL_mem) xGL_fix)

theorem spec_mul {a b : G} {ha : a ∈ normalizer (V : Set G)} {hb : b ∈ normalizer (V : Set G)}
    {ka kb : GL (Fin 6) (ZMod 2)}
    (hka : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨a, ha⟩) = glLin ka)
    (hkb : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨b, hb⟩) = glLin kb) :
    linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨a * b, mul_mem ha hb⟩) =
      glLin (ka * kb) := by
  rw [map_mul, show (⟨a * b, mul_mem ha hb⟩ : normalizer (V : Set G)) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
    map_mul, map_mul, hka, hkb]

theorem spec_inv {a : G} {ha : a ∈ normalizer (V : Set G)} {ka : GL (Fin 6) (ZMod 2)}
    (hka : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨a, ha⟩) = glLin ka) :
    linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨a⁻¹, inv_mem ha⟩) =
      glLin ka⁻¹ := by
  rw [map_inv, show (⟨a⁻¹, inv_mem ha⟩ : normalizer (V : Set G)) = (⟨a, ha⟩)⁻¹ from rfl,
    map_inv, map_inv, hka]

theorem comm_V₃_of {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k)
    (h : ∀ c ∈ S.V₃, c * n * c⁻¹ * n⁻¹ ∈ S.V₁) : ∀ w ∈ V3sub, glLin k w - w ∈ V1sub := by
  intro w hw
  have hc := (elOf_mem_pullSub (Φ := S.Φ) (P := V3sub)).2 hw
  have := (comm_mem_pullSub hn hk (elOf_mem w) V1sub).1 (h _ hc)
  rwa [phi_elOf] at this

theorem wa :
    ∀ n ∈ T, (∀ c ∈ S.V₃, c * n * c⁻¹ * n⁻¹ ∈ S.V₁) →
    n ^ 2 ∈ centralizer (V : Set G) →
    n * (S.l₁ * n * S.l₁⁻¹) * n⁻¹ * (S.l₁ * n * S.l₁⁻¹)⁻¹ ∈ centralizer (V : Set G) →
    n * (S.l₂ * n * S.l₂⁻¹) * n⁻¹ * (S.l₂ * n * S.l₂⁻¹)⁻¹ ∈ centralizer (V : Set G) →
    n ∈ centralizer (S.V₃ : Set G) ∧ (∀ v ∈ V, v * n * v⁻¹ * n⁻¹ ∈ S.V₃) ∧
      (n ∉ centralizer (V : Set G) → ∃ v ∈ V, v * n * v⁻¹ * n⁻¹ ∉ S.V₁) := by
  intro n hn h1 h2 h3 h4
  have hnN := S.hTV hn
  obtain ⟨s, hs, hst⟩ := S.hT n hn
  have hst' : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hnN⟩) = glLin s := hst
  have k1 := S.comm_V₃_of hnN hst' h1
  have k2 : s * s = 1 := by
    have h := S.spec_mul hst' hst'
    exact (mem_centralizer_V_iff (mul_mem hnN hnN) h).1 (by rw [← pow_two]; exact h2)
  have hcomm : ∀ {l : G} {hl : l ∈ normalizer (V : Set G)} {j : GL (Fin 6) (ZMod 2)},
      linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hl⟩) = glLin j →
      n * (l * n * l⁻¹) * n⁻¹ * (l * n * l⁻¹)⁻¹ ∈ centralizer (V : Set G) →
      s * (j * s * j⁻¹) = j * s * j⁻¹ * s := by
    intro l hl j hj hc
    have hm := S.spec_mul hj hst'
    have hm2 := S.spec_mul hm (S.spec_inv hj)
    have hm3 := S.spec_mul hst' hm2
    have hm4 := S.spec_mul hm3 (S.spec_inv hst')
    have hm5 := S.spec_mul hm4 (S.spec_inv hm2)
    have h1' := (mem_centralizer_V_iff _ hm5).1 hc
    calc s * (j * s * j⁻¹) = (s * (j * s * j⁻¹) * s⁻¹ * (j * s * j⁻¹)⁻¹) * (j * s * j⁻¹ * s) := by
          group
      _ = j * s * j⁻¹ * s := by rw [h1', one_mul]
  obtain ⟨c1, c2, c3⟩ := s0_hull_a hs k1 k2 (hcomm S.l₁_spec h3) (hcomm S.l₂_spec h4)
  refine ⟨(mem_centralizer_pullSub_iff hnN hst' V3sub).2 c1, fun v hv =>
    (comm_mem_pullSub hnN hst' hv V3sub).2 (c2 _), fun hnC => ?_⟩
  have hs1 : s ≠ 1 := fun h => hnC ((mem_centralizer_V_iff hnN hst').2 h)
  obtain ⟨w, hw⟩ := c3 hs1
  refine ⟨elOf S.Φ w, elOf_mem w, fun hmem => hw ?_⟩
  have := (comm_mem_pullSub hnN hst' (elOf_mem w) V1sub).1 hmem
  rwa [phi_elOf] at this

theorem wb :
    ∀ n ∈ T, (∀ c ∈ S.V₃, c * n * c⁻¹ * n⁻¹ ∈ S.V₁) →
    n ∉ centralizer (S.V₃ : Set G) →
    ∃ w ∈ S.V₅, w * n * w⁻¹ * n⁻¹ ∈ S.V₃ ∧ w * n * w⁻¹ * n⁻¹ ∉ S.V₁ := by
  intro n hn h1 h2
  have hnN := S.hTV hn
  obtain ⟨s, hs, hst⟩ := S.hT n hn
  have hst' : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hnN⟩) = glLin s := hst
  have k2 : ∃ w ∈ V3sub, glLin s w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact h2 ((mem_centralizer_pullSub_iff hnN hst' V3sub).2 hcon)
  obtain ⟨w, hw5, hw3, hw1⟩ := s0_hull_b hs (S.comm_V₃_of hnN hst' h1) k2
  refine ⟨elOf S.Φ w, elOf_mem_pullSub.2 hw5, ?_, fun hmem => hw1 ?_⟩
  · refine (comm_mem_pullSub hnN hst' (elOf_mem w) V3sub).2 ?_
    rwa [phi_elOf]
  · have := (comm_mem_pullSub hnN hst' (elOf_mem w) V1sub).1 hmem
    rwa [phi_elOf] at this

theorem wc : ∀ n ∈ normalizer (V : Set G), n ∈ centralizer (S.V₃ : Set G) →
    ∀ v ∈ V, v * n * v⁻¹ * n⁻¹ ∈ S.V₃ := by
  intro n hn hnC v hv
  have hk := S.rho_spec ⟨n, hn⟩
  have hfix := (mem_centralizer_pullSub_iff hn hk V3sub).1 hnC
  exact (comm_mem_pullSub hn hk hv V3sub).2
    (sub_V3sub_of_fixes (S.rho_mem_N6 ⟨n, hn⟩) hfix _)

theorem wd : ∀ X : Subgroup G, S.V₁ ≤ X → X ≤ S.V₃ → S.l₁ ∈ normalizer (X : Set G) →
    X = S.V₁ ∨ X = S.V₃ := by
  intro X h1 h3 hl
  have hXV : X ≤ V := h3.trans S.le3
  have hX := pullSub_subSpace (Φ := S.Φ) hXV
  have hP1 : V1sub ≤ subSpace S.Φ X := pullSub_le_iff.1 (by rw [hX]; exact h1)
  have hP3 : subSpace S.Φ X ≤ V3sub := pullSub_le_iff.1 (by rw [hX]; exact h3)
  rcases eq_of_V1_le_le_V3 hP1 hP3 (subSpace_invariant S.l₁_N S.l₁_spec hl) with h | h
  · left
    rw [← hX, h]
    rfl
  · right
    rw [← hX, h]
    rfl

theorem we : ∀ X : Subgroup G, S.V₃ ≤ X → X ≤ V → S.l₁ ∈ normalizer (X : Set G) →
    S.l₂ ∈ normalizer (X : Set G) → X = S.V₃ ∨ X = S.V₅ ∨ X = V := by
  intro X h3 hXV hl₁ hl₂
  have hX := pullSub_subSpace (Φ := S.Φ) hXV
  have hP3 : V3sub ≤ subSpace S.Φ X := pullSub_le_iff.1 (by rw [hX]; exact h3)
  rcases eq_of_V3_le hP3 (subSpace_invariant S.l₁_N S.l₁_spec hl₁)
      (subSpace_invariant S.l₂_N S.l₂_spec hl₂) with h | h | h
  · left
    rw [← hX, h]
    rfl
  · right; left
    rw [← hX, h]
    rfl
  · right; right
    rw [← hX, h, pullSub_top]

theorem wf : ∀ c ∈ S.V₃, c ∉ S.V₁ →
    ∃ l ∈ S.H, l ∈ normalizer (V : Set G) ∧ l * c * l⁻¹ ∈ S.V₂ := by
  intro c hc hc1
  obtain ⟨hcV, hw3⟩ := mem_pullSub.1 hc
  have hw1 : S.Φ (Additive.ofMul (⟨c, hcV⟩ : V)) ∉ V1sub := fun h =>
    hc1 (mem_pullSub.2 ⟨hcV, h⟩)
  rcases exists_fusion hw3 hw1 with h | h | h
  · refine ⟨1, S.H.one_mem, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_pullSub.2 ⟨hcV, h⟩
  · exact ⟨S.l₁, S.l₁_H, S.l₁_N, (conj_mem_pullSub S.l₁_N S.l₁_spec hcV V2sub).2 h⟩
  · have hm := S.spec_mul S.l₁_spec S.l₁_spec
    exact ⟨S.l₁ * S.l₁, S.H.mul_mem S.l₁_H S.l₁_H, mul_mem S.l₁_N S.l₁_N,
      (conj_mem_pullSub (mul_mem S.l₁_N S.l₁_N) hm hcV V2sub).2 h⟩

theorem wg : ∃ l ∈ normalizer (S.V₂ : Set G), l ∈ normalizer (V : Set G) ∧
    ∃ w ∈ S.V₅, l * w * l⁻¹ ∉ S.V₅ := by
  refine ⟨S.l₃, mem_normalizer_pullSub S.l₃_N S.l₃_spec map_V2sub_yGL, S.l₃_N,
    elOf S.Φ (vecOf 4), elOf_mem_pullSub.2 yGL_moves_V5sub.1, fun hmem => ?_⟩
  have := (conj_mem_pullSub S.l₃_N S.l₃_spec (elOf_mem _) V5sub).1 hmem
  rw [phi_elOf] at this
  exact yGL_moves_V5sub.2 this

theorem normalizer_V₁ : normalizer (S.V₁ : Set G) = S.H :=
  normalizer_eq_centralizer_of_card_eq_two S.card_V₁

theorem T_le_H : T ≤ S.H := by
  rw [H_eq]
  intro t ht
  exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 S.hzVT.2) t ht)

theorem T_le_N_V₁ :
    T ≤ normalizer (S.V₁ : Set G) := by
  rw [S.normalizer_V₁]
  exact S.T_le_H

theorem pCoreOf_H_ne_bot :
    pCoreOf 2 S.H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2' : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.hz2]; norm_num)
  have hzH : zpowers z ≤ S.H := by
    rw [H_eq, zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have hN : S.H ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    rw [← S.V₁_eq, S.normalizer_V₁]
  have hle : zpowers z ≤ pCoreOf 2 S.H :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzH hN hz2'
  intro h
  rw [h, le_bot_iff, zpowers_eq_bot] at hle
  exact S.hz1 hle

theorem L₁T_le_H :
    L₁Of L S.V₁ ⊔ T ≤ S.H := by
  refine sup_le ((oTwoRes_le (L ⊓ normalizer (S.V₁ : Set G))).trans ?_) S.T_le_H
  rw [← S.normalizer_V₁]
  exact inf_le_right

theorem inH
    : InH (L₁Of L S.V₁ ⊔ T) S.H := ⟨S.L₁T_le_H, S.pCoreOf_H_ne_bot⟩

theorem charTwo_H :
    CFSG.QuasithinUnique.CharTwo S.H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hH.sylow
  exact CFSG.Quasithin.charTwo_of_inH S.hH.qtke.2.1 P ⟨hP ▸ S.T_le_H, S.pCoreOf_H_ne_bot⟩

theorem uniqueM : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) := by
  obtain ⟨-, -, -, ⟨hMmax, hLT, huniq⟩, -⟩ :=
    u3_original_local_maximality_and_unique_normalizer_of_1332 S.h1332 S.hH
  exact ⟨⟨hMmax, hLT⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

theorem normalizer_V_le : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  (u3_selected_local_normalizer_and_TI_of_1332 S.h1332 S.hH S.hF).2.1

theorem pCoreOf_L_le : pCoreOf 2 L ≤ T ⊓ centralizer (V : Set G) := by
  rw [S.hF.2.2.2.2.2.2.2.2.2.2.1]
  exact A6.pCoreOf_le_pCoreOf_sup S.hTL

theorem isSimple_quot : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel S.hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact (MulEquiv.isSimpleGroup_congr (e1.trans e2.symm)).2 this

theorem inf_centralizer_le : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := S.isSimple_quot
  set K : Subgroup ↥L := (centralizer (V : Set G)).subgroupOf L with hK
  have hKn : K.Normal := by
    constructor
    intro k hk l
    rw [mem_subgroupOf] at hk ⊢
    exact (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (S.hLV l.2)) k).1 hk
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hmapn : (K.map π).Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  have hO2C : ∀ o : ↥L, o ∈ CFSG.pCore 2 ↥L → (o : G) ∈ centralizer (V : Set G) := fun o ho =>
    (S.pCoreOf_L_le ⟨o, mem_open_pCore_of_mem_pCore ho, rfl⟩).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with h | h
  · rintro x ⟨hxL, hxC⟩
    have hxK : (⟨x, hxL⟩ : ↥L) ∈ K := hxC
    have h1 : π ⟨x, hxL⟩ ∈ K.map π := ⟨_, hxK, rfl⟩
    rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨x, hxL⟩, mem_open_pCore_of_mem_pCore h1, rfl⟩
  · exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := S.hF.2.2.2.2.2.2.2.2.2.1
    have h1 : π ⟨l, hl⟩ ∈ K.map π := h ▸ mem_top _
    obtain ⟨k, hk, hkl⟩ := h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
    have hkC : (k : G) ∈ centralizer (V : Set G) := hk
    have hoC := hO2C _ hkl
    have hlC : l ∈ centralizer (V : Set G) := by
      have := mul_mem hkC hoC
      rwa [show (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) = l by simp] at this
    exact hlv (by rw [← (mem_centralizer_iff.1 hlC) v hv, mul_inv_cancel_right])

theorem comm_mem_pCoreOf_L : ∀ y ∈ normalizer (L : Set G) ⊓ centralizer (V : Set G),
    ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  rintro y ⟨hyM, hyC⟩ l hl
  refine S.inf_centralizer_le ⟨?_, ?_⟩
  · rw [show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) by group]
    exact L.mul_mem hl ((mem_normalizer_iff.1 hyM _).1 (L.inv_mem hl))
  · have h1 : l * y * l⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (S.hLV hl)) y).1 hyC
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hyC)

theorem odd_centralizes (hB : centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G)) :
    ∀ y ∈ S.H, y ∈ centralizer (S.V₃ : Set G) → (∃ m : ℕ, Odd m ∧ y ^ m = 1) →
      y ∈ centralizer (V : Set G) := by
  rintro y - hyC ⟨m, hm, hym⟩
  have hyN := hB hyC
  have hk := S.rho_spec ⟨y, hyN⟩
  have hfix := (mem_centralizer_pullSub_iff hyN hk V3sub).1 hyC
  have hsq := sq_eq_one_of_fixes (S.rho_mem_N6 _) hfix
  rw [mem_centralizer_V_iff hyN hk]
  have h1 : S.rho ⟨y, hyN⟩ ^ m = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : normalizer (V : Set G)) ^ m = 1 := Subtype.ext (by simpa using hym)
    rw [this, map_one]
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul] at h1
  exact h1

theorem L₁T_normalizes_V₃
    : L₁Of L S.V₁ ⊔ T ≤ normalizer (S.V₃ : Set G) := by
  refine sup_le ((oTwoRes_le (L ⊓ normalizer (S.V₁ : Set G))).trans fun l ⟨hl, hlN⟩ => ?_)
    fun t ht => ?_
  · obtain ⟨j, hj, hlj⟩ := S.hL l hl
    rw [S.normalizer_V₁] at hlN
    have hfix := (S.mem_H_iff (S.hLV hl) hlj).1 hlN
    exact mem_normalizer_pullSub (S.hLV hl) hlj (map_V3sub_of_fix (J6_le_N6 hj) hfix)
  · obtain ⟨s, hs, hst⟩ := S.hT t ht
    exact mem_normalizer_pullSub (S.hTV ht) hst (map_V3sub_of_mem_S0 hs)

theorem T_normalizes_V₂ : T ≤ normalizer (S.V₂ : Set G) := fun t ht => by
  obtain ⟨s, hs, hst⟩ := S.hT t ht
  exact mem_normalizer_pullSub (S.hTV ht) hst (map_V2sub_of_mem_S0 hs)

theorem T_normalizes_V₃ :
    T ≤ normalizer (S.V₃ : Set G) :=
  le_sup_right.trans S.L₁T_normalizes_V₃

theorem irred :
    ∀ W : Subgroup G, S.V₁ ≤ W → W ≤ S.V₃ →
    L₁Of L S.V₁ ⊔ T ≤ normalizer (W : Set G) → W = S.V₁ ∨ W = S.V₃ := by
  intro W h1 h3 hW
  have hWV : W ≤ V := h3.trans S.le3
  have h0 : orderOf S.l₁ ≠ 0 := (orderOf_pos S.l₁).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd h0
  set l₀ := S.l₁ ^ 2 ^ a with hl₀
  have hl₀N : l₀ ∈ normalizer (V : Set G) := pow_mem S.l₁_N _
  have hl₀L : l₀ ∈ L ⊓ normalizer (S.V₁ : Set G) := by
    rw [S.normalizer_V₁]
    exact ⟨pow_mem S.l₁_mem _, pow_mem S.l₁_H _⟩
  have hl₀m : l₀ ^ m = 1 := by
    rw [hl₀, ← pow_mul, ← ham, pow_orderOf_eq_one]
  have hl₀W : l₀ ∈ normalizer (W : Set G) :=
    hW (le_sup_left (a := L₁Of L S.V₁) (Subgroup.subset_closure ⟨hl₀L, m, hm, hl₀m⟩))
  have hspec : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l₀, hl₀N⟩) =
      glLin (xGL ^ 2 ^ a) := by
    rw [show (⟨l₀, hl₀N⟩ : normalizer (V : Set G)) = ⟨S.l₁, S.l₁_N⟩ ^ 2 ^ a from rfl,
      map_pow (u3ConjLin V (normalizer (V : Set G)) le_rfl), map_pow (linConj S.Φ), S.l₁_spec,
      map_pow glLin]
  have hinv := subSpace_invariant hl₀N hspec hl₀W
  have hx : ∀ w ∈ subSpace S.Φ W, glLin xGL w ∈ subSpace S.Φ W := by
    rcases xGL_pow_two_pow a with h | h
    · rw [h] at hinv
      exact hinv
    · rw [h] at hinv
      intro w hw
      have := hinv _ (hinv w hw)
      rwa [← LinearEquiv.mul_apply, ← map_mul, xGL_pow_four] at this
  have hX := pullSub_subSpace (Φ := S.Φ) hWV
  have hP1 : V1sub ≤ subSpace S.Φ W := pullSub_le_iff.1 (by rw [hX]; exact h1)
  have hP3 : subSpace S.Φ W ≤ V3sub := pullSub_le_iff.1 (by rw [hX]; exact h3)
  rcases eq_of_V1_le_le_V3 hP1 hP3 hx with h | h
  · left
    rw [← hX, h]
    rfl
  · right
    rw [← hX, h]
    rfl

theorem conj_V₁_of_H {g e : G} (hg : g ∈ S.H) (he : e ∈ S.V₁) : g * e * g⁻¹ = e := by
  have := (mem_centralizer_iff.1 hg) e he
  rw [← this, mul_inv_cancel_right]

theorem V₃_le_closure :
    S.V₃ ≤ closure ({z, elOf S.Φ (vecOf 18), elOf S.Φ (vecOf 39)} : Set G) := by
  set X := closure ({z, elOf S.Φ (vecOf 18), elOf S.Φ (vecOf 39)} : Set G) with hXdef
  have hzX : z ∈ X := subset_closure (by simp)
  have h18X : elOf S.Φ (vecOf 18) ∈ X := subset_closure (by simp)
  have h39X : elOf S.Φ (vecOf 39) ∈ X := subset_closure (by simp)
  have hXV : X ≤ V := (closure_le _).2 (by
    rintro _ (rfl | rfl | rfl)
    · exact S.hzV
    · exact elOf_mem _
    · exact elOf_mem _)
  have hX := pullSub_subSpace (Φ := S.Φ) hXV
  rw [← hX]
  refine pullSub_mono fun w hw => ?_
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  refine mem_of_spanL [15, 18, 39] (fun a ha => ?_) c hc
    (hexL_fifteen.2.2.2.2.2.2 c hc ((hasMask_V3sub' c hc).1 hw))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · refine ⟨by norm_num, ?_⟩
    rw [← S.phi_z, mem_subSpace]
    exact hzX
  · refine ⟨by norm_num, ?_⟩
    rw [← phi_elOf (Φ := S.Φ) (vecOf 18), mem_subSpace]
    exact h18X
  · refine ⟨by norm_num, ?_⟩
    rw [← phi_elOf (Φ := S.Φ) (vecOf 39), mem_subSpace]
    exact h39X

theorem H_inf_normalizer_V₃_le
    (hB : centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G)) :
    S.H ⊓ normalizer (S.V₃ : Set G) ≤ normalizer (V : Set G) := by
  rintro g ⟨hgH, hg3⟩
  set x18 := elOf S.Φ (vecOf 18) with hx18
  set x39 := elOf S.Φ (vecOf 39) with hx39
  have hm18 : x18 ∈ S.V₃ := elOf_mem_pullSub.2 ((hasMask_V3sub' 18 (by norm_num)).2 (by decide))
  have hm39 : x39 ∈ S.V₃ := elOf_mem_pullSub.2 ((hasMask_V3sub' 39 (by norm_num)).2 (by decide))
  have hp18 : S.Φ (Additive.ofMul (⟨x18, elOf_mem _⟩ : V)) = vecOf 18 := phi_elOf _
  have hp39 : S.Φ (Additive.ofMul (⟨x39, elOf_mem _⟩ : V)) = vecOf 39 := phi_elOf _
  have hgz : g * z * g⁻¹ = z := S.conj_V₁_of_H hgH S.z_mem_V₁
  obtain ⟨he18V, hw18⟩ := mem_pullSub.1 ((mem_normalizer_iff.1 hg3 _).1 hm18)
  obtain ⟨he39V, hw39⟩ := mem_pullSub.1 ((mem_normalizer_iff.1 hg3 _).1 hm39)
  obtain ⟨a, ha, hav⟩ := exists_vecOf (S.Φ (Additive.ofMul (⟨g * x18 * g⁻¹, he18V⟩ : V)))
  obtain ⟨b, hb, hbv⟩ := exists_vecOf (S.Φ (Additive.ofMul (⟨g * x39 * g⁻¹, he39V⟩ : V)))
  have hinj : ∀ {u v : G}, g * u * g⁻¹ = g * v * g⁻¹ → u = v := fun h => by
    simpa using h
  have hzv : S.Φ (Additive.ofMul (⟨z, S.hzV⟩ : V)) = vecOf 15 := S.phi_z
  have ha3 : v3mask.testBit a = true := (hasMask_V3sub' a ha).1 (hav ▸ hw18)
  have ha1 : v1mask.testBit a = false := by
    cases h : v1mask.testBit a
    · rfl
    · exfalso
      have h1 : g * x18 * g⁻¹ ∈ S.V₁ :=
        mem_pullSub.2 ⟨he18V, by rw [← hav]; exact (hasMask_V1sub a ha).2 h⟩
      have h2 : x18 ∈ S.V₁ := by
        have := S.conj_V₁_of_H (S.H.inv_mem hgH) h1
        rw [inv_inv, show g⁻¹ * (g * x18 * g⁻¹) * g = x18 by group] at this
        rw [this]
        exact h1
      obtain ⟨hx, h3⟩ := mem_pullSub.1 h2
      rw [show (⟨x18, hx⟩ : V) = ⟨x18, elOf_mem _⟩ from rfl, hp18,
        hasMask_V1sub 18 (by norm_num)] at h3
      exact absurd h3 (by decide)
  have hb3 : v3mask.testBit b = true := (hasMask_V3sub' b hb).1 (hbv ▸ hw39)
  have hne : ∀ {y : G} (hy : y ∈ V), g * x39 * g⁻¹ = g * y * g⁻¹ →
      S.Φ (Additive.ofMul (⟨y, hy⟩ : V)) = vecOf 39 := by
    intro y hy h
    have := hinj h
    subst this
    exact hp39
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h1 : g * x39 * g⁻¹ = g * 1 * g⁻¹ := by
      rw [mul_one, mul_inv_cancel]
      exact phi_injective' he39V (one_mem _) (by rw [← hbv, vecOf_zero]; exact (map_zero _).symm)
    have := hne (one_mem _) h1
    rw [show Additive.ofMul (⟨1, one_mem V⟩ : V) = 0 from rfl, map_zero] at this
    exact absurd (vecOf_injective (by norm_num) (by norm_num) (this.symm.trans vecOf_zero.symm))
      (by norm_num)
  have hb15 : b ≠ 15 := by
    rintro rfl
    have h1 : g * x39 * g⁻¹ = g * z * g⁻¹ := by
      rw [hgz]
      exact phi_injective' he39V S.hzV (by rw [← hbv, hzv])
    have := hne S.hzV h1
    rw [hzv] at this
    exact absurd (vecOf_injective (by norm_num) (by norm_num) this) (by norm_num)
  have hba : b ≠ a := by
    rintro rfl
    have h1 : g * x39 * g⁻¹ = g * x18 * g⁻¹ :=
      phi_injective' he39V he18V (by rw [← hbv, ← hav])
    have := hne (elOf_mem _) h1
    rw [hp18] at this
    exact absurd (vecOf_injective (by norm_num) (by norm_num) this) (by norm_num)
  have hba' : b ≠ a ^^^ 15 := by
    rintro rfl
    have hxz : x18 * z ∈ V := V.mul_mem (elOf_mem _) S.hzV
    have h1 : g * x39 * g⁻¹ = g * (x18 * z) * g⁻¹ := by
      rw [show g * (x18 * z) * g⁻¹ = (g * x18 * g⁻¹) * (g * z * g⁻¹) by group, hgz]
      refine phi_injective' (Φ := S.Φ) he39V (V.mul_mem he18V S.hzV) ?_
      rw [phi_mul' he18V S.hzV, ← hbv, ← hav, hzv, vecOf_xor]
    have := hne hxz h1
    rw [phi_mul' (elOf_mem _) S.hzV, hp18, hzv, ← vecOf_xor] at this
    exact absurd (vecOf_injective (by norm_num) (by norm_num) this) (by norm_num)
  obtain ⟨j, hj, hj15, hj18, hj39⟩ := exists_real ha hb ha3 ha1 hb3 hb0 hb15 hba hba'
  obtain ⟨l, -, hlN, hlj⟩ := S.exists_lift hj
  have hl18 : l * x18 * l⁻¹ = g * x18 * g⁻¹ :=
    phi_injective' _ he18V (by rw [phi_conj' hlN hlj (elOf_mem _), hp18, hj18, hav])
  have hl39 : l * x39 * l⁻¹ = g * x39 * g⁻¹ :=
    phi_injective' _ he39V (by rw [phi_conj' hlN hlj (elOf_mem _), hp39, hj39, hbv])
  have hlz : l * z * l⁻¹ = z :=
    phi_injective' _ S.hzV (by rw [phi_conj' hlN hlj S.hzV, hzv, hj15])
  have hfix : ∀ {x : G}, l * x * l⁻¹ = g * x * g⁻¹ → (l⁻¹ * g) * x = x * (l⁻¹ * g) := by
    intro x h
    calc l⁻¹ * g * x = l⁻¹ * (g * x * g⁻¹) * g := by group
      _ = l⁻¹ * (l * x * l⁻¹) * g := by rw [h]
      _ = x * (l⁻¹ * g) := by group
  have hC : l⁻¹ * g ∈ centralizer (S.V₃ : Set G) := by
    have h1 : l⁻¹ * g ∈ centralizer ({z, x18, x39} : Set G) := by
      rw [mem_centralizer_iff]
      rintro x (rfl | rfl | rfl)
      · exact (hfix (by rw [hlz, hgz])).symm
      · exact (hfix hl18).symm
      · exact (hfix hl39).symm
    rw [← centralizer_closure] at h1
    exact Subgroup.centralizer_le S.V₃_le_closure h1
  have := mul_mem hlN (hB hC)
  rwa [mul_inv_cancel_left] at this

theorem V₁_lt_V₃ : S.V₁ < S.V₃ := by
  refine lt_of_le_of_ne S.V₁_le_V₃ fun h => ?_
  have := S.card_V₁
  rw [h, S.card_V₃] at this
  norm_num at this

theorem isTwoReducedIn : IsTwoReducedIn (L ⊔ T) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.hLV S.hTV
  have hLTL : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer S.hTL
  refine ⟨S.hVT.trans le_sup_right, hLTN, isElemAbelian_of_isElementaryAbelian' V,
    fun D hD hDn hD2 => ?_⟩
  have hrhoL : ∀ {l : G} (hl : l ∈ L), S.rho ⟨l, S.hLV hl⟩ ∈ J6 := by
    intro l hl
    obtain ⟨j, hj, hlj⟩ := S.hL l hl
    rw [show S.rho ⟨l, S.hLV hl⟩ = j from glLin.injective (by rw [← S.rho_spec, hlj])]
    exact hj
  have hrhoLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), S.rho ⟨l, S.hLV hl⟩ = j := by
    intro j hj
    obtain ⟨l, hl, hlj⟩ := S.hLs j hj
    exact ⟨l, hl, glLin.injective (by rw [← S.rho_spec, hlj])⟩
  set N : Subgroup (GL (Fin 6) (ZMod 2)) :=
    (D.subgroupOf (normalizer (V : Set G))).map S.rho ⊓ J6 with hNdef
  have hN : N = ⊥ := by
    refine eq_bot_of_isPGroup_of_normal_J6 inf_le_right ?_ ?_
    · rintro ⟨n, ⟨d, hd, rfl⟩, -⟩
      obtain ⟨k, hk⟩ := hD2 d hd
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := (mem_centralizer_V_iff (d ^ 2 ^ k).2 (S.rho_spec (d ^ 2 ^ k))).1 hk
      rw [map_pow] at h1
      simpa using h1
    · intro σ hσ n hn
      obtain ⟨⟨d, hd, rfl⟩, hnJ⟩ := mem_inf.1 hn
      obtain ⟨l, hl, rfl⟩ := hrhoLs σ hσ
      rw [SetLike.mem_coe, mem_subgroupOf] at hd
      refine mem_inf.2 ⟨⟨⟨l, S.hLV hl⟩ * d * ⟨l, S.hLV hl⟩⁻¹, ?_, by rw [map_mul, map_mul,
        map_inv]⟩, mul_mem (mul_mem (hrhoL hl) hnJ) (inv_mem (hrhoL hl))⟩
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact (mem_normalizer_iff.1 (hDn (le_sup_left (b := T) hl)) d).1 hd
  intro d hd
  have hdN : d ∈ normalizer (V : Set G) := hLTN (hD hd)
  rw [mem_centralizer_V_iff hdN (S.rho_spec ⟨d, hdN⟩)]
  refine eq_one_of_commute_J6 fun j hj => ?_
  obtain ⟨l, hl, rfl⟩ := hrhoLs j hj
  set c : normalizer (V : Set G) :=
    ⟨d, hdN⟩ * ⟨l, S.hLV hl⟩ * ⟨d, hdN⟩⁻¹ * ⟨l, S.hLV hl⟩⁻¹ with hc
  have hcD : (c : G) ∈ D := by
    rw [hc]
    show d * l * d⁻¹ * l⁻¹ ∈ D
    rw [show d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) by group]
    exact D.mul_mem hd ((mem_normalizer_iff.1 (hDn (le_sup_left (b := T) hl)) _).1
      (D.inv_mem hd))
  have hcL : (c : G) ∈ L := by
    rw [hc]
    show d * l * d⁻¹ * l⁻¹ ∈ L
    exact L.mul_mem ((mem_normalizer_iff.1 (hLTL (hD hd)) l).1 hl) (L.inv_mem hl)
  have hcN : S.rho c ∈ N := by
    refine mem_inf.2 ⟨⟨c, hcD, rfl⟩, ?_⟩
    have := hrhoL hcL
    exact this
  rw [hN, mem_bot, hc, map_mul, map_mul, map_mul, map_inv, map_inv] at hcN
  calc S.rho ⟨l, S.hLV hl⟩ * S.rho ⟨d, hdN⟩ =
      (S.rho ⟨d, hdN⟩ * S.rho ⟨l, S.hLV hl⟩ * (S.rho ⟨d, hdN⟩)⁻¹ *
        (S.rho ⟨l, S.hLV hl⟩)⁻¹)⁻¹ * (S.rho ⟨d, hdN⟩ * S.rho ⟨l, S.hLV hl⟩) := by group
    _ = S.rho ⟨d, hdN⟩ * S.rho ⟨l, S.hLV hl⟩ := by rw [hcN, inv_one, one_mul]

theorem weak_e
    (h1317 : ∀ g ∈ S.H, ⁅V, conjSub g V⁆ ≤ V ⊓ conjSub g V → ⁅V, conjSub g V⁆ = ⊥) :
    ∀ g ∈ S.H, ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V → ⁅S.V₃, conjSub g⁻¹ V⁆ ≤ S.V₁ →
      ⁅conjSub g⁻¹ S.V₃, V⁆ ≤ S.V₁ →
        ⁅S.V₃, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ S.V₃, V⁆ = ⊥ := by
  intro g hg h1 _ _
  have h2 := h1317 g⁻¹ (S.H.inv_mem hg) h1
  refine ⟨le_bot_iff.1 ((commutator_mono S.le3 le_rfl).trans h2.le),
    le_bot_iff.1 ((commutator_mono (conjSub_mono _ S.le3) le_rfl).trans ?_)⟩
  rw [commutator_comm]
  exact h2.le

theorem hypF91
    (hB : centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G))
    (h1317 : ∀ g ∈ S.H, ⁅V, conjSub g V⁆ ≤ V ⊓ conjSub g V → ⁅V, conjSub g V⁆ = ⊥)
    (hHM : ¬ S.H ≤ normalizer (L : Set G)) : HypF91 T V L S.V₁ S.V₃ S.H :=
  A6.hypF91_of S.hH.sylow S.hH.faithful S.hH.qtke.2.1 S.hTL S.isTwoReducedIn
    S.hF.2.2.2.2.2.2.2.2.2.2.1 S.uniqueM S.card_V₁ S.V₁_lt_V₃ S.le3 S.T_le_N_V₁ S.inH le_rfl hHM
    (A6.coreIn_le_pCoreOf_of S.uniqueM S.T_le_H hHM S.charTwo_H le_rfl
      (F7.isElemAbelian_mono (isElemAbelian_of_isElementaryAbelian' V) S.le3) S.V₁_le_V₃
      ((Subgroup.centralizer_le_normalizer _).trans S.normalizer_V_le)
      (S.pCoreOf_L_le.trans inf_le_left) S.comm_mem_pCoreOf_L (S.odd_centralizes hB))
    S.L₁T_normalizes_V₃ S.irred (S.H_inf_normalizer_V₃_le hB) (S.weak_e h1317)

theorem hullHyp
    (hB : centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G))
    (h1317 : ∀ g ∈ S.H, ⁅V, conjSub g V⁆ ≤ V ⊓ conjSub g V → ⁅V, conjSub g V⁆ = ⊥)
    (hHM : ¬ S.H ≤ normalizer (L : Set G))
    (h13314 : ¬ pCoreOf 2 S.H ≤ centralizer (S.V₂ : Set G))
    (h13315 : pCoreOf 2 S.H ⊓ centralizer (S.V₂ : Set G) ≤
      pCoreOf 2 (normalizer (S.V₂ : Set G)))
    (hcod : ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
      centralizer (F : Set G) ≤ normalizer (V : Set G)) :
    HullHyp T V L S.V₁ S.V₂ S.V₃ S.V₅ S.H S.l₁ S.l₂ where
  f91 := S.hypF91 hB h1317 hHM
  le12 := S.le12
  le23 := S.le23
  le35 := S.le35
  le5 := S.le5
  card2 := S.card_V₂
  card3 := S.card_V₃
  card5 := S.card_V₅
  card := S.hV64
  l₁H := S.l₁_H
  l₂H := S.l₂_H
  l₁V := S.l₁_N
  l₂V := S.l₂_N
  l₁V₃ := S.l₁_V₃
  wa := S.wa
  wb := S.wb
  wc := S.wc
  wd := S.wd
  we := S.we
  wf := S.wf
  wg := S.wg
  s1317 := h1317
  s13314 := h13314
  s13315 := h13315
  cod := hcod

end HullSetting

end CFSG.Quasithin.H13.U3
