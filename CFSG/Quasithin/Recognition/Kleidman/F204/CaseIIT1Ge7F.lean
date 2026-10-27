module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7A
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7B
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7C

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
private theorem comm_of_elem' {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

private theorem vtype_of_mem_nbrs' {H M : Subgroup G} {u v : Geo H M} (h : v ∈ nbrs u) :
    vtype v = !vtype u := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
  cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem exists_k0 {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α')
    (hμβ : ¬ Zv μ ≤ Qv β) : ∃ k₀ ∈ Vn β ⊓ Qv α', k₀ ∉ Qv μ := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  obtain ⟨t, ht, htQ⟩ : ∃ t ∈ Zv μ, t ∉ Qv β := by
    by_contra h; push Not at h; exact hμβ fun t ht => h t ht
  have htβ : t ∈ stab β := hWβ (hA.Zv_le_Vn hμ ht)
  have hT := lemmaT_Vn F hb3 hβ htβ htQ (k := 1)
    (by rw [pow_one, (hA.isElemAbelian_Zv μ).2 t ht]; exact one_mem _)
  by_contra hK
  push Not at hK
  have hV2 := hA.isElemAbelian_Vn hb3 β
  have h2 := relIndex_inf_Qv_le_two F hα' hVβ hV2
  have hle : Vn β ⊓ Qv α' ≤ Vn β ⊓ Subgroup.centralizer {t} := by
    refine le_inf inf_le_left fun v hv => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ ht).2 v (hK v hv))
  have h3 := (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans h2
  omega

variable (hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
include hb7

theorem comm_mem_Zv_of_full {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α') {a b : G}
    (ha : a ∈ Vball 3 β ⊓ Qv α') (hb : b ∈ Vball 3 β ⊓ Qv α') (haQ : a ∉ Qv μ) (hbQ : b ∉ Qv μ)
    (habQ : a⁻¹ * b ∉ Qv μ) {y z : G} (hy : y ∈ Vball 3 β ⊓ Qv α') (hz : z ∈ Zv μ) :
    y * z * y⁻¹ * z⁻¹ ∈ Zv α' := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨-, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hμt : vtype μ = true := by rw [vtype_of_mem_nbrs' hμ, hα']; rfl
  have hα'μ : α' ∈ nbrs μ := mem_nbrs_symm hμ
  have hU2 := hA.isElemAbelian_Vball (n := 3) (by omega) β
  obtain ⟨hyU, hyQ⟩ := Subgroup.mem_inf.mp hy
  have hyμ : y ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ hyQ
  have hzβ : z ∈ stab β := hWβ (hA.Zv_le_Vn hμ hz)
  set w := y * z * y⁻¹ * z⁻¹ with hw
  have hwZ : w ∈ Zv μ := (Zv μ).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv μ hyμ) z).mp hz) ((Zv μ).inv_mem hz)
  have hwU : w ∈ Vball 3 β := by
    have h1 : z * y⁻¹ * z⁻¹ ∈ Vball 3 β :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vball 3 β hzβ) _).mp
        ((Vball 3 β).inv_mem hyU)
    have e : w = y * (z * y⁻¹ * z⁻¹) := by rw [hw]; group
    rw [e]; exact (Vball 3 β).mul_mem hyU h1
  rw [Zv_eq_inf_centralizer F hT1 hμt hα'μ]
  refine Subgroup.mem_inf.mpr ⟨hwZ, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  have key : ∀ e ∈ Vball 3 β, ∀ m ∈ Qv μ, (e * m) * w = w * (e * m) := by
    intro e he m hm
    have h1 : e * w = w * e := comm_of_elem' hU2 he hwU
    have h2 : m * w = w * m := Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hwZ).2 m hm
    calc e * m * w = e * (m * w) := by group
      _ = e * (w * m) := by rw [h2]
      _ = (e * w) * m := by group
      _ = (w * e) * m := by rw [h1]
      _ = w * (e * m) := by group
  have hdec : ∀ e ∈ Vball 3 β, e⁻¹ * q ∈ Qv μ → q * w = w * q := by
    intro e he hm
    have := key e he _ hm
    rwa [mul_inv_cancel_left] at this
  rcases mem_Qv_of_four F hμt hα'μ ha.2 hb.2 haQ hbQ habQ hq with h | h | h | h
  · exact hdec 1 (Vball 3 β).one_mem (by rwa [inv_one, one_mul])
  · exact hdec a ha.1 h
  · exact hdec b hb.1 h
  · exact hdec (a * b) ((Vball 3 β).mul_mem ha.1 hb.1) h

variable (hF1 : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → ∀ d ∈ nbrs x,
  ∀ d' ∈ nbrs x, d ≠ d' → Zv d ⊓ Zv d' = ⊥)
include hF1

theorem Zv_le_Vn_of_full {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α') {k₀ : G}
    (hk : k₀ ∈ Vn β ⊓ Qv α') (hkQ : k₀ ∉ Qv μ)
    (hfull : ∀ y ∈ Vball 3 β ⊓ Qv α', ∀ z ∈ Zv μ, y * z * y⁻¹ * z⁻¹ ∈ Zv α') :
    Zv α' ≤ Vn β := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨-, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hμt : vtype μ = true := by rw [vtype_of_mem_nbrs' hμ, hα']; rfl
  have hα'μ : α' ∈ nbrs μ := mem_nbrs_symm hμ
  obtain ⟨hkV, hkα'⟩ := Subgroup.mem_inf.mp hk
  have hkU : k₀ ∈ Vball 3 β := (Vn_le_Vball_one β).trans (Vball_mono (by norm_num) β) hkV
  have hkμ : k₀ ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ hkα'
  have hkα's : k₀ ∈ stab α' := pCoreOf_le 2 _ hkα'
  have hk2 : k₀ ^ 2 ^ 1 = 1 := by rw [pow_one]; exact (hA.isElemAbelian_Vn hb3 β).2 k₀ hkV
  have hcard := hA.card_nbrs μ
  have : Finite ↥(nbrs μ) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial ↥(nbrs μ) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (⟨α', hα'μ⟩ : ↥(nbrs μ))
  have hdα' : d ≠ α' := fun h => hne (Subtype.ext h)
  have hdf : vtype d = false := by rw [vtype_of_mem_nbrs' hd, hμt]; rfl
  have hkd : k₀ ∉ stab d := fun h => hkQ (mem_Qv_of_fix_two F hμt hα'μ hd hdα' hkμ hkα's h hk2)
  set kk : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨k₀, (mem_stab.mp hkμ).1⟩ with hkk
  have hkkμ : kk • μ = μ := smul_eq_of_mem_stab (g := kk) hkμ
  have hd' : kk • d ∈ nbrs μ := by
    have := (smul_adj kk).mpr (show (graph _ _ _).Adj μ d from hd)
    rwa [hkkμ] at this
  have hdd' : d ≠ kk • d := fun h => hkd (mem_stab_of_smul_eq (g := kk) h.symm)
  have hbot := hF1 μ hμt d hd (kk • d) hd' hdd'
  have hZdμ : Zv d ≤ Zv μ := by rw [Zv_eq_inf_centralizer F hT1 hμt hd]; exact inf_le_left
  have hZab : ∀ a ∈ Zv μ, ∀ b ∈ Zv μ, a * b = b * a := fun a ha b hb =>
    comm_of_elem' (hA.isElemAbelian_Zv μ) ha hb
  have hkN : k₀ ∈ Subgroup.normalizer (Zv μ : Set G) := hA.stab_le_normalizer_Zv μ hkμ
  set σ := commMap hZab hkN with hσ
  let f : ↥(Zv d) → ↥(Zv α') := fun z =>
    ⟨k₀ * z * k₀⁻¹ * (z : G)⁻¹, hfull k₀ ⟨hkU, hkα'⟩ z (hZdμ z.2)⟩
  have hfinj : Function.Injective f := by
    intro z₁ z₂ h
    have h' : k₀ * z₁ * k₀⁻¹ * (z₁ : G)⁻¹ = k₀ * z₂ * k₀⁻¹ * (z₂ : G)⁻¹ := congrArg Subtype.val h
    set u : G := (z₁ : G) * (z₂ : G)⁻¹ with hu
    have huZd : u ∈ Zv d := (Zv d).mul_mem z₁.2 ((Zv d).inv_mem z₂.2)
    have huμ : u ∈ Zv μ := hZdμ huZd
    have hσu : σ ⟨u, huμ⟩ = 1 := by
      have e : (⟨u, huμ⟩ : ↥(Zv μ)) = ⟨z₁, hZdμ z₁.2⟩ * (⟨z₂, hZdμ z₂.2⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv]
      apply Subtype.ext
      show k₀ * z₁ * k₀⁻¹ * (z₁ : G)⁻¹ * (k₀ * z₂ * k₀⁻¹ * (z₂ : G)⁻¹)⁻¹ = 1
      rw [h', mul_inv_cancel]
    have hfix : k₀ * u * k₀⁻¹ = u := by
      have := congrArg Subtype.val hσu
      rw [commMap_apply, Subgroup.coe_one] at this
      calc k₀ * u * k₀⁻¹ = (k₀ * u * k₀⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [this, one_mul]
    have hu' : u ∈ Zv (kk • d) := by
      rw [Zv_smul, mem_conjSub]
      show k₀⁻¹ * u * k₀ ∈ Zv d
      have e : k₀⁻¹ * u * k₀ = u := by
        calc k₀⁻¹ * u * k₀ = k₀⁻¹ * (k₀ * u * k₀⁻¹) * k₀ := by rw [hfix]
          _ = u := by group
      rw [e]; exact huZd
    have hu1 : u = 1 := by
      have : u ∈ Zv d ⊓ Zv (kk • d) := Subgroup.mem_inf.mpr ⟨huZd, hu'⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    apply Subtype.ext
    calc (z₁ : G) = u * z₂ := by rw [hu]; group
      _ = z₂ := by rw [hu1, one_mul]
  have hcardeq : Nat.card (Zv α') ≤ Nat.card (Zv d) :=
    (card_Zv_eq_of_vtype_false F hdf hα').ge
  have hfsurj := (hfinj.bijective_of_nat_card_le hcardeq).2
  intro w hw
  obtain ⟨z, hz⟩ := hfsurj ⟨w, hw⟩
  have hzw : k₀ * z * k₀⁻¹ * (z : G)⁻¹ = w := congrArg Subtype.val hz
  rw [← hzw]
  have hzβ : (z : G) ∈ stab β := hWβ (hA.Zv_le_Vn hμ (hZdμ z.2))
  have h1 : (z : G) * k₀⁻¹ * (z : G)⁻¹ ∈ Vn β :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hzβ) _).mp ((Vn β).inv_mem hkV)
  have e : k₀ * z * k₀⁻¹ * (z : G)⁻¹ = k₀ * ((z : G) * k₀⁻¹ * (z : G)⁻¹) := by group
  rw [e]
  exact (Vn β).mul_mem hkV h1

end CaseII

end CFSG.Quasithin.Kleidman.F204
