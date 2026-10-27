module

public import CFSG.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Ctx764 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp147 G T L V
  hMod : StmtL32NModule
  h63 : Thm14_7_63
  hF : HypF98 T V L (fsuV1 T V) V (hz T V)
  h1222 : Stmt12_2_2
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4

omit [Finite G] in
theorem comm_mul {U : Subgroup G} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {s : G}
    (hs : s ∈ Subgroup.normalizer (U : Set G)) {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) :
    u * u' * s * (u * u')⁻¹ * s⁻¹ = (u * s * u⁻¹ * s⁻¹) * (u' * s * u'⁻¹ * s⁻¹) := by
  have h1 : s * u⁻¹ * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hs _).mp (inv_mem hu)
  have h2 : s * u'⁻¹ * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hs _).mp (inv_mem hu')
  have e : u' * (s * u'⁻¹ * s⁻¹) * (s * u⁻¹ * s⁻¹) = (s * u⁻¹ * s⁻¹) * (u' * (s * u'⁻¹ * s⁻¹)) :=
    hUc _ (mul_mem hu' h2) _ h1
  calc u * u' * s * (u * u')⁻¹ * s⁻¹ = u * (u' * (s * u'⁻¹ * s⁻¹) * (s * u⁻¹ * s⁻¹)) := by group
    _ = u * ((s * u⁻¹ * s⁻¹) * (u' * (s * u'⁻¹ * s⁻¹))) := by rw [e]
    _ = (u * s * u⁻¹ * s⁻¹) * (u' * s * u'⁻¹ * s⁻¹) := by group

@[expose] def dS (T V : Subgroup G) (s : G) : Subgroup G :=
  Subgroup.closure {w | ∃ u ∈ fsuU T V, w = u * s * u⁻¹ * s⁻¹} ⊔ fsuV1 T V

omit [Finite G] in
theorem mem_dS_iff (hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a) {s : G}
    (hs : s ∈ Subgroup.normalizer (fsuU T V : Set G)) {x : G} :
    x ∈ dS T V s ↔ ∃ u ∈ fsuU T V, ∃ c ∈ fsuV1 T V, x = u * s * u⁻¹ * s⁻¹ * c := by
  have hV1U : fsuV1 T V ≤ fsuU T V := (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  have hcU : ∀ u ∈ fsuU T V, u * s * u⁻¹ * s⁻¹ ∈ fsuU T V := by
    intro u hu
    rw [show u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) by group]
    exact mul_mem hu ((Subgroup.mem_normalizer_iff.mp hs _).mp (inv_mem hu))
  have hinv : ∀ u ∈ fsuU T V, (u * s * u⁻¹ * s⁻¹)⁻¹ = u⁻¹ * s * u⁻¹⁻¹ * s⁻¹ := by
    intro u hu
    have e := comm_mul hUc hs hu (inv_mem hu)
    have e' : (u * s * u⁻¹ * s⁻¹) * (u⁻¹ * s * u⁻¹⁻¹ * s⁻¹) = 1 := by rw [← e]; group
    exact inv_eq_of_mul_eq_one_right e'
  let W : Subgroup G :=
    { carrier := {x | ∃ u ∈ fsuU T V, ∃ c ∈ fsuV1 T V, x = u * s * u⁻¹ * s⁻¹ * c}
      mul_mem' := by
        rintro _ _ ⟨u, hu, c, hc, rfl⟩ ⟨u', hu', c', hc', rfl⟩
        refine ⟨u * u', mul_mem hu hu', c * c', mul_mem hc hc', ?_⟩
        have e := hUc c (hV1U hc) _ (hcU u' hu')
        rw [comm_mul hUc hs hu hu']
        calc u * s * u⁻¹ * s⁻¹ * c * (u' * s * u'⁻¹ * s⁻¹ * c') =
            u * s * u⁻¹ * s⁻¹ * (c * (u' * s * u'⁻¹ * s⁻¹)) * c' := by group
          _ = u * s * u⁻¹ * s⁻¹ * ((u' * s * u'⁻¹ * s⁻¹) * c) * c' := by rw [e]
          _ = u * s * u⁻¹ * s⁻¹ * (u' * s * u'⁻¹ * s⁻¹) * (c * c') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by group⟩
      inv_mem' := by
        rintro _ ⟨u, hu, c, hc, rfl⟩
        refine ⟨u⁻¹, inv_mem hu, c⁻¹, inv_mem hc, ?_⟩
        rw [mul_inv_rev, hinv u hu]
        exact hUc _ (inv_mem (hV1U hc)) _ (hcU _ (inv_mem hu)) }
  constructor
  · intro hx
    have hle : dS T V s ≤ W := by
      refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact ⟨u, hu, 1, one_mem _, by group⟩
      · intro c hc
        exact ⟨1, one_mem _, c, hc, by group⟩
    exact hle hx
  · rintro ⟨u, hu, c, hc, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩))
      (Subgroup.mem_sup_right hc)

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a :=
  (F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of C.hyp C.hMod)).1

theorem hUe : ∀ u ∈ fsuU T V, u ^ 2 = 1 :=
  (F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of C.hyp C.hMod)).2

theorem U_le_H : fsuU T V ≤ hz T V := by
  rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
  exact C.hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)

theorem H_le_normalizer_U : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  hz_le_normalizer_U C.hyp C.hMod

theorem R1_le_H : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ hz T V :=
  (pCoreOf_le 2 _).trans C.hF.L₁T_le_H

theorem comm_Q {q u : G} (hq : q ∈ pCoreOf 2 (hz T V)) (hu : u ∈ fsuU T V) :
    q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
    rw [← C.hF.pCoreOf_eq_centralizerMod]
    exact hq
  exact hqC.2.2 u (fsuU_eq_conjClosure_hz C.hMod C.hyp ▸ hu)

theorem exists_comm_of_mem_u0 {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) {u : G} (hu : u ∈ fsuU T V)
    (hus : s * u * s⁻¹ * u⁻¹ ∈ u0 T V) :
    ∃ w ∈ fsuU T V, u * (w * s * w⁻¹ * s⁻¹)⁻¹ ∈ u0 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := C.hyp
  have hMod := C.hMod
  have h63 := C.h63
  have hF := C.hF
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨hR1KQ, -⟩ := R1_le_kz_sup S0 hF h63 C.h1222 C.h1332 C.h1334
  obtain ⟨hKU, π, β, -, hπk, hβs, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hV1U0 := fsuV1_le_u0 h hMod
  have hHV1 : hz T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hHU0 : hz T V ≤ Subgroup.normalizer (u0 T V : Set G) := hz_le_normalizer_u0 h hMod
  have hQR := pCoreOf_hz_le_R1 h hF
  have hKQ : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hs' := hR1KQ hs
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKQ] at hs'
  obtain ⟨k, hk, q, hq, rfl⟩ := hs'
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  have hqu : q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := C.comm_Q hq hu
  have hku : k * u * k⁻¹ * u⁻¹ ∈ u0 T V := by
    have h1 : k * (q * u * q⁻¹ * u⁻¹) * k⁻¹ ∈ u0 T V :=
      (Subgroup.mem_normalizer_iff.mp (hHU0 hkH) _).mp (hV1U0 hqu)
    rw [show k * u * k⁻¹ * u⁻¹ = (k * (q * u * q⁻¹ * u⁻¹) * k⁻¹)⁻¹ *
      (k * q * u * (k * q)⁻¹ * u⁻¹) by group]
    exact mul_mem (inv_mem h1) hus
  have hkR : k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [show k = k * q * q⁻¹ by group]
    exact mul_mem hs (inv_mem (hQR hq))
  have hπ2 : π ⟨k, hk⟩ ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⟨k, hkR⟩
    have hk2 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine sl24_sq_of_two_pow _ n ?_
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk2)
    rw [this, map_one]
  have hπ1 : π ⟨k, hk⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨k, hk⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    have hkQ : k ∈ pCoreOf 2 (hz T V) :=
      A4.pCoreOf_le_of_subnormal 2 (A4.subnormal_of_normal (oTwoUpper_le _)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
          (le_normalizer_oTwoUpper _))) h2
    exact hsQ (mul_mem hkQ hq)
  have hku' : k * u * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp hu
  have hfix : (π ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β ⟨u, hu⟩)) = Multiplicative.toAdd (β ⟨u, hu⟩) := by
    have e1 := hβe ⟨k, hk⟩ ⟨u, hu⟩ ⟨_, hku'⟩ rfl
    have hc : (⟨k * u * k⁻¹, hku'⟩ : ↥(fsuU T V)) =
        ⟨k * u * k⁻¹ * u⁻¹, hU0U hku⟩ * ⟨u, hu⟩ := Subtype.ext (by simp)
    have hc1 : β ⟨k * u * k⁻¹ * u⁻¹, hU0U hku⟩ = 1 := (l24_ker_iff hβk _).mpr hku
    rw [hc, map_mul, hc1, one_mul] at e1
    have := congrArg Multiplicative.toAdd e1
    rw [toAdd_ofAdd] at this
    exact this.symm
  obtain ⟨v, hv⟩ := sl24_fix_comm_exists _ hπ2 hπ1 _ hfix
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd v)
  have hkw' : k * (w : G) * k⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hKU hk) w).mp w.2
  have hmem : u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹ ∈ fsuU T V :=
    mul_mem hu (inv_mem (mul_mem hkw' (inv_mem w.2)))
  have h0 : u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹ ∈ u0 T V := by
    refine (l24_ker_iff hβk ⟨_, hmem⟩).mp ?_
    have e2 := hβe ⟨k, hk⟩ w ⟨_, hkw'⟩ rfl
    have e3 : (⟨u * (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹, hmem⟩ : ↥(fsuU T V)) =
        ⟨u, hu⟩ * (⟨_, hkw'⟩ * w⁻¹)⁻¹ := Subtype.ext (by simp)
    rw [e3, map_mul, map_inv, map_mul, map_inv, e2, hw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one]
    rw [← hv]
    exact f4_key3 _ _
  refine ⟨w, w.2, ?_⟩
  have hwU := w.2
  have hcU : k * (w : G) * k⁻¹ * (w : G)⁻¹ ∈ fsuU T V := mul_mem hkw' (inv_mem hwU)
  have hc1 : (w : G) * q * (w : G)⁻¹ * q⁻¹ ∈ fsuV1 T V := by
    have := inv_mem (C.comm_Q hq hwU)
    rwa [show (q * (w : G) * q⁻¹ * (w : G)⁻¹)⁻¹ = (w : G) * q * (w : G)⁻¹ * q⁻¹ by group]
      at this
  have hc3 : k * ((w : G) * q * (w : G)⁻¹ * q⁻¹) * k⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (hHV1 hkH) _).mp hc1
  have hsq : (k * (w : G) * k⁻¹ * (w : G)⁻¹) * (k * (w : G) * k⁻¹ * (w : G)⁻¹) = 1 := by
    rw [← sq]
    exact C.hUe _ hcU
  have e5 : (k * (w : G) * k⁻¹ * (w : G)⁻¹)⁻¹ = k * (w : G) * k⁻¹ * (w : G)⁻¹ :=
    inv_eq_of_mul_eq_one_right hsq
  have e4 : (w : G) * (k * q) * (w : G)⁻¹ * (k * q)⁻¹ =
      (k * (w : G) * k⁻¹ * (w : G)⁻¹) * (k * ((w : G) * q * (w : G)⁻¹ * q⁻¹) * k⁻¹) := by
    rw [← e5]
    group
  set c := k * (w : G) * k⁻¹ * (w : G)⁻¹ with hcdef
  set X := k * ((w : G) * q * (w : G)⁻¹ * q⁻¹) * k⁻¹ with hXdef
  rw [e4, show u * (c * X)⁻¹ = (u * c⁻¹) * (c * X⁻¹ * c⁻¹) by group]
  exact mul_mem h0 ((Subgroup.mem_normalizer_iff.mp
    (hz_le_normalizer_u0 h hMod (C.U_le_H hcU)) _).mp (hV1U0 (inv_mem hc3)))

end Ctx764

end CFSG.Quasithin.H13.L32A
