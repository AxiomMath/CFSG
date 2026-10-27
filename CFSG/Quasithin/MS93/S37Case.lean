module

public import CFSG.Quasithin.MS93.S37Off
public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Geo

variable {F : Type} [Field F]

theorem fixSp_eq_perp_commSp (A : Subgroup (Sp4 F)) : fixSp A = perp (commSp A) := by
  ext w
  rw [mem_fixSp]
  constructor
  · intro hw
    refine mem_perp.2 fun c hc => ?_
    have hle : commSp A ≤ perp (F ∙ w) := commSp_le_iff.2 fun a ha v => by
      have e : form F w (mat a *ᵥ v) = form F w v := by
        calc form F w (mat a *ᵥ v) = form F (mat a *ᵥ w) (mat a *ᵥ v) := by rw [hw a ha]
          _ = form F w v := form_mat a w v
      rw [mem_perp_span, map_sub, e, sub_self]
    rw [form_swap, mem_perp_span.1 (hle hc), neg_zero]
  · intro hw a ha
    have h0 : ∀ v : V4 F, form F v (mat a *ᵥ w - w) = 0 := fun v => by
      have := mem_perp.1 hw _ (sub_mem_commSp (inv_mem ha) v)
      rw [map_sub, LinearMap.sub_apply, ← form_mat a (mat a⁻¹ *ᵥ v) w, mat_mulVec_inv] at this
      rw [map_sub, this]
    have h1 := form_nondegenerate.1 (mat a *ᵥ w - w) fun v => by
      rw [form_swap, h0 v, neg_zero]
    exact sub_eq_zero.1 h1

theorem two_le_finrank_fixSp_of_quad {A : Subgroup (Sp4 F)} (h : commSp A ≤ fixSp A) :
    2 ≤ Module.finrank F (fixSp A) := by
  have h1 := finrank_perp (commSp A)
  rw [← fixSp_eq_perp_commSp] at h1
  have h2 := Submodule.finrank_mono h
  omega

end Geo

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

noncomputable abbrev rhoIm (X : Subgroup G) : Subgroup (Sp4 F) :=
  (X.subgroupOf (L ⊔ pCoreOf 2 M)).map C.rho

theorem mem_rhoIm {X : Subgroup G} {g : Sp4 F} :
    g ∈ C.rhoIm X ↔ ∃ (x : G) (hx : x ∈ L ⊔ pCoreOf 2 M), x ∈ X ∧ C.rho ⟨x, hx⟩ = g := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
    exact ⟨x, hx, hxX, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem conj_eq_of_mem_A {x : G} (hx : x ∈ L ⊔ pCoreOf 2 M) {a : G}
    (ha : a ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)) : x * a * x⁻¹ = a := by
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_sup hx
  have h1 : q * a * q⁻¹ = a := by
    rw [comm_of_mem_Uq C.h ha.1 hq, mul_inv_cancel_right]
  have h2 : l * a * l⁻¹ = a := by
    rw [Subgroup.mem_centralizer_iff.1 ha.2 l hl, mul_inv_cancel_right]
  calc l * q * a * (l * q)⁻¹ = l * (q * a * q⁻¹) * l⁻¹ := by group
    _ = a := by rw [h1, h2]

theorem co_mem_fixSp_iff {X : Subgroup G} (hX : X ≤ L ⊔ pCoreOf 2 M) (u : ↥(Uq M T L)) :
    C.N.co u ∈ fixSp (C.rhoIm X) ↔ (u : G) ∈ Subgroup.centralizer (X : Set G) := by
  rw [mem_fixSp, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := C.conj_eq_of_fix ⟨x, hX hx⟩ u.2 (h _ ((C.mem_rhoIm).2 ⟨x, hX hx, hx, rfl⟩))
    calc x * (u : G) = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [this]
  · intro h g hg
    obtain ⟨x, hxK, hxX, rfl⟩ := (C.mem_rhoIm).1 hg
    have hxu : x * (u : G) * x⁻¹ = u := by rw [h x hxX, mul_inv_cancel_right]
    rw [← C.co_conj ⟨x, hxK⟩ (u := u) (v := u) hxu.symm]

theorem card_inf_centralizer {X : Subgroup G} (hX : X ≤ L ⊔ pCoreOf 2 M) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card ↥(fixSp (C.rhoIm X)) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
  set A := Uq M T L ⊓ Subgroup.centralizer (L : Set G) with hA
  set W : Subgroup ↥(Uq M T L) :=
    (Uq M T L ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (Uq M T L) with hW
  let f : ↥W →* Multiplicative (V4 F) := C.N.β.comp W.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hWc : Nat.card ↥W = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (X : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : Nat.card f.ker = Nat.card ↥A := by
    refine Nat.card_congr ⟨fun w => ⟨((w : ↥W) : G), (C.N.β_ker _).1 (w.2 : f (w : ↥W) = 1)⟩,
      fun a => ⟨⟨⟨a, a.2.1⟩, ?_⟩, ?_⟩, fun w => rfl, fun a => rfl⟩
    · rw [Subgroup.mem_subgroupOf]
      refine ⟨a.2.1, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have := C.conj_eq_of_mem_A (hX hx) a.2
      calc x * (a : G) = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [this]
    · show C.N.β ⟨a, a.2.1⟩ = 1
      exact (C.N.β_ker _).2 a.2
  have hrange : Nat.card f.range = Nat.card ↥(fixSp (C.rhoIm X)) := by
    refine Nat.card_congr ⟨fun r => ⟨Multiplicative.toAdd (r : _), ?_⟩,
      fun v => ⟨Multiplicative.ofAdd (v : V4 F), ?_⟩, fun r => rfl, fun v => rfl⟩
    · obtain ⟨w, hw⟩ := r.2
      rw [← hw]
      exact (C.co_mem_fixSp_iff hX _).2 (Subgroup.mem_subgroupOf.1 w.2).2
    · obtain ⟨u, hu⟩ := C.N.co_surj (v : V4 F)
      have hu' : (u : G) ∈ Subgroup.centralizer (X : Set G) :=
        (C.co_mem_fixSp_iff hX u).1 (hu ▸ v.2)
      refine ⟨⟨u, Subgroup.mem_subgroupOf.2 ⟨u.2, hu'⟩⟩, ?_⟩
      show C.N.β u = Multiplicative.ofAdd (v : V4 F)
      rw [← hu]
      rfl
  rw [← hWc, ← h1, hker, hrange, mul_comm]

theorem card_rhoIm {X : Subgroup G} (hX : X ≤ L ⊔ pCoreOf 2 M) :
    Nat.card ↥(C.rhoIm X) = (pCoreOf 2 M).relIndex X := by
  have h1 := Subgroup.card_ker_mul_card_range (C.rho.comp (X.subgroupOf (L ⊔ pCoreOf 2 M)).subtype)
  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 M) X
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hX' : Nat.card ↥(X.subgroupOf (L ⊔ pCoreOf 2 M)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hker : Nat.card ↥(C.rho.comp (X.subgroupOf (L ⊔ pCoreOf 2 M)).subtype).ker =
      Nat.card ↥(pCoreOf 2 M ⊓ X) := by
    refine Nat.card_congr ⟨fun w => ⟨(((w : ↥(X.subgroupOf (L ⊔ pCoreOf 2 M))) :
          ↥(L ⊔ pCoreOf 2 M)) : G),
        (C.rho_eq_one_iff _).1 (by
          have := MonoidHom.mem_ker.1 w.2
          rwa [MonoidHom.comp_apply] at this),
        (Subgroup.mem_subgroupOf.1 (w : ↥(X.subgroupOf (L ⊔ pCoreOf 2 M))).2)⟩,
      fun y => ⟨⟨⟨y, hX y.2.2⟩, Subgroup.mem_subgroupOf.2 y.2.2⟩,
        (C.rho_eq_one_iff ⟨y, hX y.2.2⟩).2 y.2.1⟩, fun w => rfl, fun y => rfl⟩
  rw [hX', hker] at h1
  have hpos : 0 < Nat.card ↥(pCoreOf 2 M ⊓ X) := Nat.card_pos
  rw [← h1] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at h2; linarith)

section Off

variable {S : Subgroup G}

theorem card_V4_eq (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hU : Ut M T L θ ≤ T1 M T L) :
    Nat.card (V4 F) = (Qt M θ).relIndex (Uq M T L) * Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) := by
  have h1 := C.card_Uq
  have h2 := Subgroup.relIndex_mul_card (Qt M θ) (Uq M T L)
  have h3 := C.card_inf_centralizer (hU.trans T1_le_sup)
  have he : Qt M θ ⊓ Uq M T L = Uq M T L ⊓ Subgroup.centralizer (Ut M T L θ : Set G) := by
    rw [C.Qt_eq hQS hST, inf_comm, ← inf_assoc, inf_eq_left.2 (C.Uq_le_S hQS)]
  rw [he, h3, h1] at h2
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← h2]; ring)

theorem commSp_le_fixSp (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S) :
    commSp (C.rhoIm (Ut M T L θ)) ≤ fixSp (C.rhoIm (Ut M T L θ)) := by
  refine commSp_le_iff.2 fun a ha v => ?_
  obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 ha
  refine mem_fixSp.2 fun b hb => ?_
  obtain ⟨y, hyK, hy, rfl⟩ := (C.mem_rhoIm).1 hb
  have h := C.act_quad hQS hST θ hx hy v
  rw [show C.act (C.Ut_le_M hST θ hx) = C.act (C.sup_le_M hxK) from rfl, C.rho_spec ⟨x, hxK⟩,
    show C.act (C.Ut_le_M hST θ hy) = C.act (C.sup_le_M hyK) from rfl,
    C.rho_spec ⟨y, hyK⟩] at h
  exact h

theorem case_I_or_II (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hcrit : ¬ Uq M T L ≤ Qt M θ) (hU : Ut M T L θ ≤ T1 M T L)
    (hle : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L θ)) :
    (∃ p : Submodule F (V4 F), IsPoint p ∧ C.rhoIm (Ut M T L θ) = xPoint p) ∨
      (IsLine (fixSp (C.rhoIm (Ut M T L θ))) ∧
        C.rhoIm (Ut M T L θ) ≤ qLine (fixSp (C.rhoIm (Ut M T L θ)))) := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hcardE : Nat.card ↥(C.rhoIm (Ut M T L θ)) = (pCoreOf 2 M).relIndex (Ut M T L θ) :=
    C.card_rhoIm (hU.trans T1_le_sup)
  have hV := C.card_V4_eq hQS hST θ hU
  rw [C.relIndex_Qt_eq hQS θ] at hV
  have hVle : Nat.card (V4 F) ≤
      Nat.card ↥(C.rhoIm (Ut M T L θ)) * Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) := by
    rw [hV, hcardE]
    exact Nat.mul_le_mul_right _ hle
  have hE2 : IsPGroup 2 (C.rhoIm (Ut M T L θ)) := by
    have h2 : IsPGroup 2 ↥(Ut M T L θ) := C.h.isPGroup.to_le ((tImage_le θ _).trans hST)
    have h3 : IsPGroup 2 ↥((Ut M T L θ).subgroupOf (L ⊔ pCoreOf 2 M)) :=
      h2.of_equiv (Subgroup.subgroupOfEquivOfLe (hU.trans T1_le_sup)).symm
    exact h3.map C.rho
  have hE1 : C.rhoIm (Ut M T L θ) ≠ ⊥ := by
    intro hbot
    apply hcrit
    rw [C.le_Qt_iff hQS hST θ]
    intro x hx
    have hxK := (hU.trans T1_le_sup) hx
    have h1 : C.rho ⟨x, hxK⟩ ∈ C.rhoIm (Ut M T L θ) := (C.mem_rhoIm).2 ⟨x, hxK, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, C.rho_eq_one_iff] at h1
    exact h1
  have hquad := C.commSp_le_fixSp hQS hST θ
  have hd2 := two_le_finrank_fixSp_of_quad hquad
  have hd4 : Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ))) ≤ 4 := by
    have := Submodule.finrank_le (fixSp (C.rhoIm (Ut M T L θ)))
    simpa using this
  have hdne : Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ))) ≠ 4 := fun h4 => by
    refine hE1 (fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq ?_))
    rw [h4]
    simp
  rcases (show Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ))) = 2 ∨
      Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ))) = 3 by omega) with h2 | h3
  · exact Or.inr (isLine_fixSp_of_finrank_two hE2 h2)
  · left
    refine eq_xPoint_of_finrank_fixSp_three h3 ?_
    rw [MSP.card_V4 (F := F), MSP.card_fixSp, h3] at hVle
    have hq : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(C.rhoIm (Ut M T L θ)) * Nat.card F ^ 3 < Nat.card F * Nat.card F ^ 3 :=
      Nat.mul_lt_mul_of_pos_right hlt hq
    have e4 : Nat.card F * Nat.card F ^ 3 = Nat.card F ^ 4 := by ring
    rw [e4] at this
    omega

end Off

end Cfg

end CFSG.Quasithin.MS93.S37
