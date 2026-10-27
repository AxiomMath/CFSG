module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.ThompsonJ
public import CFSG.SignalizerFunctorTheorem.Quadratic.Ambient

import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Glauberman

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {G : Type*} [Group G] [Finite G]

section Vq

variable {q : ℕ} {U : Subgroup G}

@[expose] def Vq (q : ℕ) (U : Subgroup G) : Subgroup G :=
  ⨆ (S : Subgroup G) (_ : IsSylowOf q S U), omegaCenter q S

omit [Finite G] in
private theorem thm_isSylowOf_iff_max {S : Subgroup G} :
    IsSylowOf q S U ↔ S ≤ U ∧ IsPGroup q S ∧
      ∀ Q : Subgroup G, Q ≤ U → IsPGroup q Q → S ≤ Q → Q = S := by
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map U.subtype, fun Q hQU hQ hle => ?_⟩
    have h1 : (P : Subgroup U) ≤ Q.subgroupOf U := fun x hx => hle ⟨x, hx, rfl⟩
    have h2 : Q.subgroupOf U = P := P.is_maximal' (hQ.comap_subtype) h1
    rw [← inf_eq_left.mpr hQU, ← Subgroup.subgroupOf_map_subtype, h2]
  · rintro ⟨hSU, hS, hmax⟩
    refine ⟨⟨S.subgroupOf U, hS.comap_subtype, fun {Q} hQ hle => ?_⟩, ?_⟩
    · have h1 : S ≤ Q.map U.subtype := by
        intro x hx
        exact ⟨⟨x, hSU hx⟩, hle hx, rfl⟩
      have h2 := hmax (Q.map U.subtype) (Subgroup.map_subtype_le Q) (hQ.map U.subtype) h1
      calc Q = (Q.map U.subtype).comap U.subtype :=
            (Subgroup.comap_map_eq_self_of_injective U.subtype_injective Q).symm
        _ = S.subgroupOf U := by rw [h2]; rfl
    · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSU]

omit [Finite G] in
private theorem thm_isSylowOf_le {S : Subgroup G} (hS : IsSylowOf q S U) : S ≤ U := by
  obtain ⟨P, rfl⟩ := hS
  exact Subgroup.map_subtype_le _

omit [Finite G] in
private theorem thm_map_conj_le {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    {S : Subgroup G} (hS : S ≤ U) : S.map (MulAut.conj g).toMonoidHom ≤ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hS hx)

omit [Finite G] in
private theorem thm_isSylowOf_map_conj {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    {S : Subgroup G} (hS : IsSylowOf q S U) :
    IsSylowOf q (S.map (MulAut.conj g).toMonoidHom) U := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem hg
  rw [thm_isSylowOf_iff_max] at hS ⊢
  obtain ⟨hSU, hSp, hmax⟩ := hS
  refine ⟨thm_map_conj_le hg hSU, hSp.map _, fun Q hQU hQ hle => ?_⟩
  have h1 : S ≤ Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, ?_⟩
    simp
    group
  have h2 := hmax _ (thm_map_conj_le hg' hQU) (hQ.map _) h1
  ext y
  constructor
  · intro hy
    have h3 : g⁻¹ * y * g⁻¹⁻¹ ∈ Q.map (MulAut.conj g⁻¹).toMonoidHom := ⟨y, hy, rfl⟩
    rw [h2] at h3
    exact ⟨_, h3, by simp; group⟩
  · rintro ⟨x, hx, rfl⟩
    exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem Vq_le : Vq q U ≤ U := by
  refine iSup₂_le fun S hS => ?_
  obtain ⟨P, rfl⟩ := hS
  exact (omegaCenter_le q _).trans (Subgroup.map_subtype_le _)

omit [Finite G] in
theorem omegaCenter_le_Vq {T : Subgroup G} (hT : IsSylowOf q T U) : omegaCenter q T ≤ Vq q U :=
  le_iSup₂ (f := fun (S : Subgroup G) (_ : IsSylowOf q S U) => omegaCenter q S) T hT

omit [Finite G] in
theorem normalizes_Vq {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer (Vq q U : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (U : Set G) →
      (Vq q U).map (MulAut.conj g).toMonoidHom ≤ Vq q U := by
    intro g hg
    rw [Vq, Subgroup.map_iSup]
    refine iSup_le fun S => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hS => ?_
    rw [cj_omegaCenter]
    exact omegaCenter_le_Vq (thm_isSylowOf_map_conj hg hS)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key hg ⟨x, hx, rfl⟩
  · intro hx
    have h := key (inv_mem hg) ⟨_, hx, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := by simp; group
    rwa [e] at h

omit [Finite G] in
private theorem thm_isElemAb_of_le_omegaCenter {Q V : Subgroup G} (h : V ≤ omegaCenter q Q) :
    IsElemAb q V := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => (h hx).2.2⟩
  exact (h a.2).2.1 b (h b.2).1

theorem isElemAb_Vq (hq : q.Prime) (hsolv : Group.IsSolvable U)
    (hcore : ∀ M : Subgroup G, M ≤ U → (M.subgroupOf U).Normal → Nat.Coprime q (Nat.card M) →
      M = ⊥) : IsElemAb q (Vq q U) := by
  have : Fact q.Prime := ⟨hq⟩
  have hpp : CFSG.pPrimeCore q U = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    have hKU : (K.map U.subtype).subgroupOf U = K :=
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective K
    have h0 := hcore (K.map U.subtype) (Subgroup.map_subtype_le K) (by rw [hKU]; exact hK)
      (by rwa [Subgroup.card_map_of_injective U.subtype_injective])
    exact (Subgroup.map_eq_bot_iff_of_injective K U.subtype_injective).mp h0
  have hfit : CFSG.fittingSubgroup U = CFSG.pCore q U := CFSG.Fitting_eq_pcore U q hpp
  have hcent : Subgroup.centralizer (CFSG.pCore q U : Set U) ≤ CFSG.pCore q U := by
    have := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := U) hsolv
    rwa [hfit] at this
  refine thm_isElemAb_of_le_omegaCenter (Q := (CFSG.pCore q U).map U.subtype) ?_
  refine iSup₂_le fun S hS => ?_
  obtain ⟨P, rfl⟩ := hS
  rintro z ⟨⟨z0, hz0P, rfl⟩, hzc, hzq⟩
  have hQP : CFSG.pCore q U ≤ (P : Subgroup U) := CFSG.fitting_pCore_le_sylow P
  have hz0Q : z0 ∈ CFSG.pCore q U := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hzc (y : G) ⟨y, hQP hy, rfl⟩).symm
  refine ⟨⟨z0, hz0Q, rfl⟩, fun t ht => ?_, hzq⟩
  obtain ⟨t0, ht0, rfl⟩ := ht
  exact hzc _ ⟨t0, hQP ht0, rfl⟩

private theorem thm_mul_decomp (hq : q.Prime) {J K N P : Subgroup G}
    (hKn : (K.subgroupOf J).Normal) (hNJ : N ≤ J) (hNn : (N.subgroupOf J).Normal)
    (hNq : ∀ n ∈ N, ∃ k : ℕ, n ^ (q ^ k) ∈ K) (hP : IsSylowOf q P J) {n : G} (hn : n ∈ N) :
    ∃ p ∈ P, ∃ k ∈ K, n = p * k := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P', rfl⟩ := hP
  let π : J →* J ⧸ K.subgroupOf J := QuotientGroup.mk' (K.subgroupOf J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNb : ((N.subgroupOf J).map π).Normal := hNn.map π hπ
  have hNbp : IsPGroup q ((N.subgroupOf J).map π) := by
    rintro ⟨_, n', hn', rfl⟩
    obtain ⟨k, hk⟩ := hNq n' hn'
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : n' ^ (q ^ k) ∈ K.subgroupOf J := hk
    change π n' ^ (q ^ k) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have hle := hNbp.le_sylow_of_normal (P'.mapSurjective hπ)
  obtain ⟨p', hp', hpn⟩ := hle ⟨⟨n, hNJ hn⟩, hn, rfl⟩
  have h2 : p'⁻¹ * ⟨n, hNJ hn⟩ ∈ K.subgroupOf J := QuotientGroup.eq.mp hpn
  refine ⟨(p' : G), ⟨p', hp', rfl⟩, (p' : G)⁻¹ * n, h2, ?_⟩
  group

omit [Finite G] in
private theorem thm_conj_mem_centralizer {V₀ : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (V₀ : Set G)) (hk : k ∈ Subgroup.centralizer (V₀ : Set G)) :
    g * k * g⁻¹ ∈ Subgroup.centralizer (V₀ : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro v hv
  have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
  have := hk _ hw
  calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
    _ = g * k * g⁻¹ * v := by group

theorem noP_thompsonJ (hq : q.Prime) :
    ∀ N : Subgroup G, N ≤ thompsonJ q U → (N.subgroupOf (thompsonJ q U)).Normal →
      (∀ n ∈ N, ∃ k : ℕ, n ^ (q ^ k) ∈ Subgroup.centralizer (Vq q U : Set G)) →
      N ≤ Subgroup.centralizer (Vq q U : Set G) := by
  intro N hNJ hNn hNq n hn
  have : Fact q.Prime := ⟨hq⟩
  have hJU : thompsonJ q U ≤ U := thompsonJ_le q U
  have hUJ : U ≤ Subgroup.normalizer (thompsonJ q U : Set G) := fun g hg =>
    mem_normalizer_thompsonJ q (Subgroup.le_normalizer hg)
  have hKn : ((Subgroup.centralizer (Vq q U : Set G) ⊓ thompsonJ q U).subgroupOf
      (thompsonJ q U)).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact ⟨thm_conj_mem_centralizer (normalizes_Vq (Subgroup.le_normalizer (hJU g.2))) hk.1,
      (g * k * g⁻¹).2⟩
  have hcomm : ∀ S : Subgroup G, IsSylowOf q S U → ∀ z ∈ omegaCenter q S, z * n = n * z := by
    intro S hS z hz
    have hP : IsSylowOf q (S ⊓ thompsonJ q U) (thompsonJ q U) :=
      CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (p := q) hS hJU hUJ
    obtain ⟨p, hp, k, hk, rfl⟩ := thm_mul_decomp hq hKn hNJ hNn (fun m hm => by
      obtain ⟨j, hj⟩ := hNq m hm
      exact ⟨j, hj, pow_mem (hNJ hm) _⟩) hP hn
    have hzV : z ∈ Vq q U := omegaCenter_le_Vq hS hz
    have h1 : z * p = p * z := hz.2.1 p hp.1
    have h2 : z * k = k * z := Subgroup.mem_centralizer_iff.mp hk.1 z hzV
    calc z * (p * k) = (z * p) * k := by rw [mul_assoc]
      _ = p * (z * k) := by rw [h1, mul_assoc]
      _ = p * (k * z) := by rw [h2]
      _ = p * k * z := by rw [mul_assoc]
  have hle : Vq q U ≤ Subgroup.centralizer ({n} : Set G) := by
    refine iSup₂_le fun S hS z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (hcomm S hS z hz).symm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hle hv) n rfl).symm

omit [Finite G] in
private theorem thm_elemAb_comm {E : Subgroup G} (hE : IsElemAb q E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have := hE.1
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite G] in
private theorem thm_isElemAb_of_le {A B : Subgroup G} (h : A ≤ B) (hB : IsElemAb q B) :
    IsElemAb q A :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (thm_elemAb_comm hB (h a.2) (h b.2)),
    fun x hx => hB.2 x (h hx)⟩

omit [Finite G] in
private theorem thm_isElemAb_iff {E : Subgroup G} :
    IsElemAb q E ↔ CFSG.IsElementaryAbelian q E :=
  ⟨fun h => { toIsMulCommutative := h.1
              exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
                fun x => Subtype.ext (h.2 x x.2) },
   fun h => ⟨h.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩⟩

omit [Finite G] in
private theorem thm_card_sup_mul_card_inf (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

private theorem thm_qOneAmb_of_max {U V₀ E : Subgroup G} (hV : IsElemAb q V₀) (hVU : V₀ ≤ U)
    (hEU : E ≤ U) (hEa : IsElemAb q E)
    (hmax : ∀ E' : Subgroup G, E' ≤ U → IsElemAb q E' → Nat.card E' ≤ Nat.card E) :
    QOneAmb V₀ E := by
  intro B hBE
  have hBel : IsElemAb q B := thm_isElemAb_of_le hBE hEa
  have hDel : IsElemAb q (V₀ ⊓ Subgroup.centralizer (B : Set G)) :=
    thm_isElemAb_of_le inf_le_left hV
  have hcomm : ∀ x ∈ B, ∀ y ∈ V₀ ⊓ Subgroup.centralizer (B : Set G), x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hy.2) x hx
  have hsup : IsElemAb q (B ⊔ (V₀ ⊓ Subgroup.centralizer (B : Set G))) := by
    have := thm_isElemAb_iff.mp hBel
    have := thm_isElemAb_iff.mp hDel
    exact thm_isElemAb_iff.mpr
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer (E := B) inf_le_right)
  have h1 : Nat.card (B ⊔ (V₀ ⊓ Subgroup.centralizer (B : Set G)) : Subgroup G) ≤ Nat.card E :=
    hmax _ (sup_le (hBE.trans hEU) (inf_le_left.trans hVU)) hsup
  have h2 : Nat.card (B ⊓ (V₀ ⊓ Subgroup.centralizer (B : Set G)) : Subgroup G) ≤
      Nat.card ↥(V₀ ⊓ Subgroup.centralizer (E : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => Subgroup.mem_inf.mpr ⟨hx.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact thm_elemAb_comm hEa hy (hBE hx.1)
  calc Nat.card B * Nat.card ↥(V₀ ⊓ Subgroup.centralizer (B : Set G))
      = Nat.card (B ⊔ (V₀ ⊓ Subgroup.centralizer (B : Set G)) : Subgroup G) *
        Nat.card (B ⊓ (V₀ ⊓ Subgroup.centralizer (B : Set G)) : Subgroup G) :=
        (thm_card_sup_mul_card_inf _ _ hcomm).symm
    _ ≤ Nat.card E * Nat.card ↥(V₀ ⊓ Subgroup.centralizer (E : Set G)) := Nat.mul_le_mul h1 h2

theorem gen_thompsonJ (hV : IsElemAb q (Vq q U)) :
    (⨆ (E : Subgroup G) (_ : E ≤ thompsonJ q U ∧ IsElemAb q E ∧ QOneAmb (Vq q U) E), E) =
      thompsonJ q U := by
  refine le_antisymm (iSup₂_le fun E hE => hE.1) (sSup_le fun E hE => ?_)
  obtain ⟨hEU, hEa, hmax⟩ := hE
  exact le_iSup₂_of_le E ⟨le_sSup ⟨hEU, hEa, hmax⟩, hEa,
    thm_qOneAmb_of_max hV Vq_le hEU hEa hmax⟩ le_rfl

private theorem thm_frattini (hq : q.Prime) {Y R U : Subgroup G} (hYU : Y ≤ U)
    (hn : U ≤ Subgroup.normalizer (Y : Set G)) (hR : IsSylowOf q R Y) :
    (U ⊓ Subgroup.normalizer (R : Set G)) ⊔ Y = U := by
  have : Fact q.Prime := ⟨hq⟩
  have hRY : R ≤ Y := thm_isSylowOf_le hR
  have hRU : R ≤ U := hRY.trans hYU
  have h1 : CFSG.ABGLocalTools.IsSylowOf q (R.subgroupOf U) (Y.subgroupOf U) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff U, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRU, inf_eq_left.mpr hYU]
    exact hR
  obtain ⟨P, hP⟩ := h1
  have hN : (Y.subgroupOf U).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYU).mpr hn
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP, ← Subgroup.subgroupOf_normalizer_eq hRU] at hfr
  have h2 := congrArg (Subgroup.map U.subtype) hfr
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.mpr hYU, inf_comm] at h2
  exact h2

omit [Finite G] in
private theorem thm_mem_normalizer_centralizer {V₀ : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V₀ : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (V₀ : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => thm_conj_mem_centralizer hg hx, fun hx => ?_⟩
  have := thm_conj_mem_centralizer (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem factorizable_of_le (hq : q.Prime) {T : Subgroup G} (hT : IsSylowOf q T U)
    (hJ : thompsonJ q U ≤ Subgroup.centralizer (Vq q U : Set G)) :
    (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) = U := by
  have : Fact q.Prime := ⟨hq⟩
  have hTU : T ≤ U := thm_isSylowOf_le hT
  have hYn : U ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (Vq q U : Set G) : Subgroup G) :
      Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x
    have h2 := Subgroup.mem_normalizer_iff.mp
      (thm_mem_normalizer_centralizer (normalizes_Vq (q := q) (Subgroup.le_normalizer hg))) x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hR : IsSylowOf q (T ⊓ Subgroup.centralizer (Vq q U : Set G))
      (U ⊓ Subgroup.centralizer (Vq q U : Set G)) := by
    have := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (p := q) hT inf_le_left hYn
    rwa [← inf_assoc, inf_eq_left.mpr hTU] at this
  have hfr := thm_frattini hq inf_le_left hYn hR
  have hJT : thompsonJ q T ≤ T ⊓ Subgroup.centralizer (Vq q U : Set G) :=
    le_inf (thompsonJ_le q T) ((thompsonJ_le_of_isSylowOf q hq hT).trans hJ)
  have hJeq := thompsonJ_eq_of_le q hJT inf_le_left
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  conv_lhs => rw [← hfr]
  refine sup_le_sup (inf_le_inf_left U fun g hg => ?_)
    (inf_le_inf_left U
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (omegaCenter_le_Vq hT))))
  rw [← hJeq]
  exact mem_normalizer_thompsonJ q hg

end Vq

structure Reduced (q r : ℕ) (U A T : Subgroup G) : Prop where
  prime_q : q.Prime
  prime_r : r.Prime
  solvable : Group.IsSolvable U
  noCore : ∀ M : Subgroup G, M ≤ U → (M.subgroupOf U).Normal → Nat.Coprime q (Nat.card M) →
    M = ⊥
  elem : IsElemAbelian r A
  cop : Nat.Coprime r (Nat.card U)
  normU : A ≤ Subgroup.normalizer (U : Set G)
  sylow : IsSylowOf q T U
  normT : A ≤ Subgroup.normalizer (T : Set G)

private theorem thm_core {q r : ℕ} {U A T : Subgroup G} (h : Reduced q r U A T)
    (hnot : ¬ ThompsonFactorizable q U T) :
    (q = 2 ∨ q = 3) ∧
    (∀ P : Subgroup G, IsSyl q P (thompsonJ q U) →
      thompsonJ q U ≤ (thompsonJ q U ⊓ Subgroup.centralizer (A : Set G)) ⊔ P ⊔
        (thompsonJ q U ⊓ Subgroup.centralizer (Vq q U : Set G))) ∧
    (q = 2 → ∃ W : Subgroup G, W ≤ Vq q U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ thompsonJ q U ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) ∧
    (q = 3 → ∃ W : Subgroup G, W ≤ Vq q U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAb 3 W ∧
      Nat.card W = 9 ∧ ∃ D : Subgroup G, D ≤ thompsonJ q U ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ) := by
  have hq := h.prime_q
  have hV := isElemAb_Vq hq h.solvable h.noCore
  have hJU : thompsonJ q U ≤ U := thompsonJ_le q U
  have hUV : U ≤ Subgroup.normalizer (Vq q U : Set G) := fun g hg =>
    normalizes_Vq (Subgroup.le_normalizer hg)
  have hne : ¬ thompsonJ q U ≤ Subgroup.centralizer (Vq q U : Set G) := by
    intro hJ
    apply hnot
    have hfac := factorizable_of_le hq h.sylow hJ
    refine le_antisymm (sup_le (sup_le (Subgroup.map_subtype_le _) inf_le_left) inf_le_left) ?_
    calc U = _ := hfac.symm
      _ ≤ _ := sup_le_sup_right le_sup_right _
  have hsolvJ : Group.IsSolvable (thompsonJ q U) := by
    have := h.solvable
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJU)
  exact core_ambient hq h.prime_r hV (fun g hg => hUV (hJU hg))
    (fun a ha => normalizes_Vq (h.normU ha)) hsolvJ (noP_thompsonJ hq) (gen_thompsonJ hV) hne
    h.elem (fun a ha => mem_normalizer_thompsonJ q (h.normU ha))
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJU) h.cop)

theorem reduced_factorizable {q r : ℕ} {U A T : Subgroup G} (h : Reduced q r U A T)
    (hnot : ¬ ThompsonFactorizable q U T) : q = 2 ∨ q = 3 :=
  (thm_core h hnot).1

theorem reduced_generation {q r : ℕ} {U A T : Subgroup G} (h : Reduced q r U A T) :
    primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (A : Set G)) = U := by
  have hq := h.prime_q
  have : Fact q.Prime := ⟨hq⟩
  have hTU : T ≤ U := thm_isSylowOf_le h.sylow
  refine le_antisymm (sup_le (sup_le (sup_le (Subgroup.map_subtype_le _) inf_le_left) inf_le_left)
    inf_le_left) ?_
  by_cases hfac : ThompsonFactorizable q U T
  · exact (le_of_eq hfac.symm).trans le_sup_left
  · have hJU : thompsonJ q U ≤ U := thompsonJ_le q U
    have hUJ : U ≤ Subgroup.normalizer (thompsonJ q U : Set G) := fun g hg =>
      mem_normalizer_thompsonJ q (Subgroup.le_normalizer hg)
    have hP : IsSylowOf q (T ⊓ thompsonJ q U) (thompsonJ q U) :=
      CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (p := q) h.sylow hJU hUJ
    have hfr := thm_frattini hq hJU hUJ hP
    have hgen := (thm_core h hfac).2.1 _ hP
    have hJT : thompsonJ q T ≤ T ⊓ thompsonJ q U :=
      le_inf (thompsonJ_le q T) (thompsonJ_le_of_isSylowOf q hq h.sylow)
    have hJeq := thompsonJ_eq_of_le q hJT inf_le_left
    have hN : U ⊓ Subgroup.normalizer ((T ⊓ thompsonJ q U : Subgroup G) : Set G) ≤
        U ⊓ Subgroup.normalizer (thompsonJ q T : Set G) := inf_le_inf_left U fun g hg => by
      rw [← hJeq]
      exact mem_normalizer_thompsonJ q hg
    have hV : thompsonJ q U ⊓ Subgroup.centralizer (Vq q U : Set G) ≤
        U ⊓ Subgroup.centralizer (omegaCenter q T : Set G) :=
      inf_le_inf hJU (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (omegaCenter_le_Vq h.sylow)))
    have hA : thompsonJ q U ⊓ Subgroup.centralizer (A : Set G) ≤
        U ⊓ Subgroup.centralizer (A : Set G) := inf_le_inf_right _ hJU
    have hPN : T ⊓ thompsonJ q U ≤ U ⊓ Subgroup.normalizer (thompsonJ q T : Set G) :=
      fun x hx => ⟨hTU hx.1, mem_normalizer_thompsonJ q (Subgroup.le_normalizer hx.1)⟩
    calc U = (U ⊓ Subgroup.normalizer ((T ⊓ thompsonJ q U : Subgroup G) : Set G)) ⊔
          thompsonJ q U := hfr.symm
      _ ≤ _ := sup_le ((hN.trans le_sup_right).trans (le_sup_left.trans le_sup_left)) (hgen.trans
        (sup_le (sup_le (hA.trans le_sup_right) ((hPN.trans le_sup_right).trans
          (le_sup_left.trans le_sup_left))) ((hV.trans le_sup_right).trans le_sup_left)))

theorem reduced_two {r : ℕ} {U A T : Subgroup G} (h : Reduced 2 r U A T)
    (hnot : ¬ ThompsonFactorizable 2 U T) :
    ∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 := by
  obtain ⟨W, hW, hWe, hWc, d, hd, hd3, hdW, hdw⟩ := (thm_core h hnot).2.2.1 rfl
  exact ⟨W, hW.trans (inf_le_inf_right _ Vq_le), hWe, hWc, d,
    ⟨thompsonJ_le 2 U hd.1, hd.2⟩, hd3, hdW, hdw⟩

theorem reduced_three {r : ℕ} {U A T : Subgroup G} (h : Reduced 3 r U A T)
    (hnot : ¬ ThompsonFactorizable 3 U T) :
    (∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup G, D ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ := by
  obtain ⟨W, hW, hWe, hWc, D, hD, φ, hφ⟩ := (thm_core h hnot).2.2.2 rfl
  exact ⟨⟨W, hW.trans (inf_le_inf_right _ Vq_le), hWe, hWc⟩, D,
    hD.trans (inf_le_inf_right _ (thompsonJ_le 3 U)), φ, hφ⟩

end CFSG.SignalizerFunctorTheorem.Quadratic
