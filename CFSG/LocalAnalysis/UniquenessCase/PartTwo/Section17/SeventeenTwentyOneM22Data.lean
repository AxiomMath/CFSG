module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22HexadLocal
public import CFSG.LocalAnalysis.WeakClosure81.NineThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_21_irr (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥

@[expose] def Gap17_21_M22HexadPair (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    ∃ E X₁ X₂ : Subgroup G,
      E ≤ D.M ∧ Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
        X₁ ≤ D.M ∧ X₂ ≤ D.M ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
          Permutes X₁ D.T ∧ Permutes X₂ D.T ∧
            E ≤ X₁ ⊔ X₂ ⊔ D.T ∧ X₁ ⊔ X₂ ⊔ D.T ≤ D.M

theorem exists_hexad_pair_of_calC {D : Data G} {V₀ V L : Subgroup G} (hV : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hspor : IsSpor (BarInf L) .M22) (hK : Inputs1719.K_M22HexadPair) :
    ∃ E X₁ X₂ : Subgroup G,
      E ≤ D.M ∧ Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
        X₁ ≤ D.M ∧ X₂ ≤ D.M ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
          Permutes X₁ D.T ∧ Permutes X₂ D.T ∧
            E ≤ X₁ ⊔ X₂ ⊔ D.T ∧ X₁ ⊔ X₂ ⊔ D.T ≤ D.M := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hHM : L ⊔ D.T ≤ D.M := sup_le hLM hTM
  obtain ⟨Y, hYgrp, hYfin, KY, SY, f', hky, hKYe, hf'surj, hker2, hker_le, hTmap, -⟩ :=
    exists_twoQuotient_lift hL hnorm
  have hshape : IsSpor (↥KY ⧸ Subgroup.center ↥KY) .M22 := by
    obtain ⟨eK⟩ := hKYe
    obtain ⟨eI⟩ := uc22p21k_barInf_equiv_of_calC hL
    obtain ⟨eB⟩ := hspor
    exact ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (eI.symm.trans eB)⟩
  obtain ⟨EY, X1Y, X2Y, -, hEYcard, hEYel, hX1YK, hX2YK, hX1Ycard, hX2Ycard,
    hX1Yperm, hX2Yperm, hEYsub⟩ := hK Y KY SY hky hshape
  let H : Subgroup G := L ⊔ D.T
  have hST : IsPGroup 2 (D.T.subgroupOf H) :=
    D.sylowM.isPGroup.comap_subtype (K := H)
  have hX1Yp : IsPGroup 3 ↥X1Y := IsPGroup.of_card (n := 1) (by rw [hX1Ycard]; norm_num)
  have hX2Yp : IsPGroup 3 ↥X2Y := IsPGroup.of_card (n := 1) (by rw [hX2Ycard]; norm_num)
  obtain ⟨X1H, hX1Hp, hX1Hmap, ⟨eX1⟩, hX1Hperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3) f' hf'surj hST hker_le
      (by norm_num : (3 : ℕ) ≠ 2) hX1Yp (by rw [hTmap]; exact hX1Yperm)
  obtain ⟨X2H, hX2Hp, hX2Hmap, ⟨eX2⟩, hX2Hperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3) f' hf'surj hST hker_le
      (by norm_num : (3 : ℕ) ≠ 2) hX2Yp (by rw [hTmap]; exact hX2Yperm)
  let R : Subgroup ↥H := EY.comap f'
  let W : Subgroup ↥H := X1H ⊔ X2H ⊔ D.T.subgroupOf H
  have hWmap : W.map f' = X1Y ⊔ X2Y ⊔ SY := by
    show ((X1H ⊔ X2H ⊔ D.T.subgroupOf H).map f') = X1Y ⊔ X2Y ⊔ SY
    rw [Subgroup.map_sup, Subgroup.map_sup, hX1Hmap, hX2Hmap, hTmap]
  have hRleW : R ≤ W := by
    intro r hr
    have hsub : f' r ∈ X1Y ⊔ X2Y ⊔ SY := hEYsub hr
    rw [← hWmap] at hsub
    obtain ⟨w, hw, hwr⟩ := Subgroup.mem_map.mp hsub
    have hdiff : r * w⁻¹ ∈ f'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwr, mul_inv_cancel]
    have hdiffT : r * w⁻¹ ∈ D.T.subgroupOf H := hker_le hdiff
    have hrw : r = (r * w⁻¹) * w := by group
    rw [hrw]
    exact W.mul_mem (Subgroup.mem_sup_right hdiffT) hw
  have hker_le_R : f'.ker ≤ R := by
    intro x hx
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact EY.one_mem)
  let gR : ↥R →* ↥EY :=
    { toFun := fun r => ⟨f' (r : ↥H), r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hgR : Function.Surjective gR := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf'surj y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker_gR : gR.ker = f'.ker.subgroupOf R := by
    ext r
    constructor
    · intro hr
      rw [MonoidHom.mem_ker] at hr
      refine Subgroup.mem_subgroupOf.mpr ?_
      show f' (r : ↥H) = 1
      have hval : ((gR r : ↥EY) : Y) = 1 := congrArg (fun z : ↥EY => (z : Y)) hr
      exact hval
    · intro hr
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (Subgroup.mem_subgroupOf.mp hr)
  have hker_card : Nat.card gR.ker = Nat.card f'.ker := by
    rw [hker_gR]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_R).toEquiv
  have hRcard : Nat.card R = Nat.card f'.ker * 9 := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := gR) hgR
    rw [hker_card, hEYcard] at h
    exact h.symm
  obtain ⟨KR, hKRcard⟩ := Sylow.exists_subgroup_card_pow_prime (p := 3) (n := 2)
    (by rw [hRcard, show 3 ^ 2 = 9 by norm_num]; exact dvd_mul_left 9 (Nat.card f'.ker))
  have hKR3 : IsPGroup 3 ↥KR := IsPGroup.of_card (n := 2) hKRcard
  have hker2R : IsPGroup 2 (f'.ker.subgroupOf R) := hker2.comap_subtype
  have hdisj : KR ⊓ f'.ker.subgroupOf R = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) KR
      (f'.ker.subgroupOf R) hKR3 hker2R)
  let κ : ↥KR →* ↥EY := gR.comp KR.subtype
  have hκinj : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxR : (x : ↥R) ∈ gR.ker := hx
    rw [hker_gR] at hxR
    have hxinf : (x : ↥R) ∈ KR ⊓ f'.ker.subgroupOf R := ⟨x.2, hxR⟩
    rw [hdisj] at hxinf
    exact Subtype.ext (Subgroup.mem_bot.mp hxinf)
  have hcardKR : Nat.card ↥KR = Nat.card ↥EY := by
    rw [hKRcard, hEYcard]
    norm_num
  have hκsurj : Function.Surjective κ := by
    obtain ⟨e_card⟩ := (Finite.card_eq (α := ↥KR) (β := ↥EY)).1 hcardKR
    exact Function.Injective.surjective_of_finite e_card hκinj
  let eK : ↥KR ≃* ↥EY := MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩
  let EH : Subgroup ↥H := KR.map R.subtype
  have hEHleW : EH ≤ W := (Subgroup.map_subtype_le KR).trans hRleW
  let eEH : ↥EH ≃* ↥KR :=
    (Subgroup.equivMapOfInjective KR R.subtype R.subtype_injective).symm
  let eEK : ↥EH ≃* ↥EY := eEH.trans eK
  have hEHel : IsElemAbelian 3 EH := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · exact eEK.injective (by
        rw [map_mul, map_mul]
        exact hEYel.1.is_comm.comm (eEK a) (eEK b))
    · intro x hx
      have h1 : (⟨x, hx⟩ : ↥EH) ^ 3 = 1 :=
        eEK.injective (by
          rw [map_pow, map_one]
          exact Subtype.ext (hEYel.2 _ (eEK ⟨x, hx⟩).2))
      have h2 : x ^ 3 = 1 := by
        have h2' := congrArg (fun z : ↥EH => (z : ↥H)) h1
        simpa [map_pow] using h2'
      exact h2
  have hEHcard : Nat.card EH = 9 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hKRcard]
    norm_num
  refine ⟨EH.map H.subtype, X1H.map H.subtype, X2H.map H.subtype, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le EH).trans hHM
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hEHcard]
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.mp b.2
      rw [← haa, ← hbb]
      exact congrArg (fun z : ↥EH => (z : G)) (hEHel.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : x ^ 3 = 1 := hEHel.2 x hx
      simpa using congrArg (fun z : ↥H => (z : G)) h1
  · exact (Subgroup.map_subtype_le X1H).trans hHM
  · exact (Subgroup.map_subtype_le X2H).trans hHM
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Nat.card_congr eX1.toEquiv, hX1Ycard]
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Nat.card_congr eX2.toEquiv, hX2Ycard]
  ·
    show ((X1H.map H.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((X1H.map H.subtype : Subgroup G) : Set G)
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      have hbH : b ∈ H := Subgroup.mem_sup_right hb
      have hmem : (a' * ⟨b, hbH⟩ : ↥H) ∈ (X1H : Set ↥H) * (D.T.subgroupOf H : Set ↥H) :=
        Set.mem_mul.mpr ⟨a', ha', ⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      rw [hX1Hperm] at hmem
      obtain ⟨s, hs, x, hx, hsx⟩ := Set.mem_mul.mp hmem
      refine Set.mem_mul.mpr ⟨((s : ↥H) : G), Subgroup.mem_subgroupOf.mp hs, ((x : ↥H) : G),
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      have := congrArg (fun y : ↥H => (y : G)) hsx
      simpa [Subgroup.coe_mul] using this
    · rintro ⟨b, hb, a, ha, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      have hbH : b ∈ H := Subgroup.mem_sup_right hb
      have hmem : (⟨b, hbH⟩ * a' : ↥H) ∈ (D.T.subgroupOf H : Set ↥H) * (X1H : Set ↥H) :=
        Set.mem_mul.mpr ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, a', ha', rfl⟩
      rw [← hX1Hperm] at hmem
      obtain ⟨x, hx, s, hs, hxs⟩ := Set.mem_mul.mp hmem
      refine Set.mem_mul.mpr ⟨((x : ↥H) : G), Subgroup.mem_map.mpr ⟨x, hx, rfl⟩,
        ((s : ↥H) : G), Subgroup.mem_subgroupOf.mp hs, ?_⟩
      have := congrArg (fun y : ↥H => (y : G)) hxs
      simpa [Subgroup.coe_mul] using this
  ·
    show ((X2H.map H.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((X2H.map H.subtype : Subgroup G) : Set G)
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      have hbH : b ∈ H := Subgroup.mem_sup_right hb
      have hmem : (a' * ⟨b, hbH⟩ : ↥H) ∈ (X2H : Set ↥H) * (D.T.subgroupOf H : Set ↥H) :=
        Set.mem_mul.mpr ⟨a', ha', ⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      rw [hX2Hperm] at hmem
      obtain ⟨s, hs, x, hx, hsx⟩ := Set.mem_mul.mp hmem
      refine Set.mem_mul.mpr ⟨((s : ↥H) : G), Subgroup.mem_subgroupOf.mp hs, ((x : ↥H) : G),
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      have := congrArg (fun y : ↥H => (y : G)) hsx
      simpa [Subgroup.coe_mul] using this
    · rintro ⟨b, hb, a, ha, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      have hbH : b ∈ H := Subgroup.mem_sup_right hb
      have hmem : (⟨b, hbH⟩ * a' : ↥H) ∈ (D.T.subgroupOf H : Set ↥H) * (X2H : Set ↥H) :=
        Set.mem_mul.mpr ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, a', ha', rfl⟩
      rw [← hX2Hperm] at hmem
      obtain ⟨x, hx, s, hs, hxs⟩ := Set.mem_mul.mp hmem
      refine Set.mem_mul.mpr ⟨((x : ↥H) : G), Subgroup.mem_map.mpr ⟨x, hx, rfl⟩,
        ((s : ↥H) : G), Subgroup.mem_subgroupOf.mp hs, ?_⟩
      have := congrArg (fun y : ↥H => (y : G)) hxs
      simpa [Subgroup.coe_mul] using this
  ·
    have hmapW : W.map H.subtype = X1H.map H.subtype ⊔ X2H.map H.subtype ⊔ D.T := by
      show ((X1H ⊔ X2H ⊔ D.T.subgroupOf H).map H.subtype) = _
      rw [Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)]
    rw [← hmapW]
    exact Subgroup.map_mono hEHleW
  · exact sup_le (sup_le ((Subgroup.map_subtype_le X1H).trans hHM)
      ((Subgroup.map_subtype_le X2H).trans hHM)) hTM

theorem gap17_21_M22HexadPair_of_K {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_20 : R17_20At D V₀ V) (hK : Inputs1719.K_M22HexadPair) :
    Gap17_21_M22HexadPair D V₀ V hV := by
  intro L c hspor
  obtain ⟨-, hN, -⟩ := h17_20 L c
  exact exists_hexad_pair_of_calC hV c.mem_calC (Tbar_le_normalizer_K1 hN) hspor hK

@[expose] def Gap17_21_M22Module (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    IsSpor (barSub V₀ V hV.isElemAbelian L) .M22 ∧
      Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10 ∧
        IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥ ∧
          Subgroup.centralizer
            (barSub V₀ V hV.isElemAbelian L : Set (MulAut (Vtil V₀ V hV.isElemAbelian))) = ⊥ ∧
            ∀ x : IntMod V hV.isElemAbelian, x.val ∉ V₀ →
              1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ x.val)

@[expose] def Gap17_21_M22Todd (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    IsSpor (barSub V₀ V hV.isElemAbelian L) .M22 ∧
      Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10 ∧
        Subgroup.centralizer
          (barSub V₀ V hV.isElemAbelian L : Set (MulAut (Vtil V₀ V hV.isElemAbelian))) = ⊥

@[expose] def Gap17_21_M22Point (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    ∀ x : IntMod V hV.isElemAbelian, x.val ∉ V₀ →
      1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ x.val)

theorem gap17_21_M22Module_of {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (hirr : Gap17_21_irr D V₀ V hV) (hTodd : Gap17_21_M22Todd D V₀ V hV)
    (hPoint : Gap17_21_M22Point D V₀ V hV) :
    Gap17_21_M22Module D V₀ V hV := by
  intro L c hspor
  obtain ⟨hSporL, hcard, hcent⟩ := hTodd L c hspor
  exact ⟨hSporL, hcard, hirr L c hspor, hcent, hPoint L c hspor⟩

theorem card_mulAut_carrier_m22_dvd :
    Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ∣ 887040 := by
  have hM22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Schreier.m22_card
  have hle : Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ≤
      2 * Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Schreier.m22_mulAut_card
  have hdvd : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∣
      Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)) := by
    refine Subgroup.card_dvd_of_injective
      (MulAut.conj : CFSG.Blueprint.NativeSporadic.Carrier .M22 →*
        MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ?_
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hcent : g ∈ Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun f : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22) =>
        f x) hg
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * g = (g * x * g⁻¹) * g := by rw [h]
        _ = g * x := by group
    have hbot : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) = ⊥ :=
      CFSG.Sporadic.Schreier.m22_center_eq_bot'
    rw [hbot] at hcent
    simpa using hcent
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    have hpos : 0 < Nat.card (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :=
      Nat.card_pos
    have : 0 < Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) * k := by
      rw [← hk]; exact hpos
    by_contra hk0
    have h0 : k = 0 := by omega
    rw [h0, mul_zero] at this
    omega
  have hk2 : k ≤ 2 := by
    rw [hk, hM22] at hle
    nlinarith
  rw [hk, hM22]
  interval_cases k
  · norm_num
  · norm_num

theorem pRank_three_mulAut_m22_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22))) ≤ 2 := by
  by_contra h
  push Not at h
  have hdvd := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card 3
    Nat.prime_three (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)))
  rw [Subgroup.card_top] at hdvd
  have h27 : 3 ^ 3 ∣ 887040 :=
    ((pow_dvd_pow 3 h).trans hdvd).trans card_mulAut_carrier_m22_dvd
  norm_num at h27

theorem not_sq_dvd_mulAut_m22 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 887040 := by
  intro h
  have hfac : 887040 = 2 ^ 8 * (3 ^ 2 * 5 * 7 * 11) := by norm_num
  have h' : p ^ 2 ∣ 2 ^ 8 * (3 ^ 2 * 5 * 7 * 11) := by simpa [hfac] using h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 8) :=
    (Nat.Coprime.pow_left 2 (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2))).pow_right 8
  have hrest : p ^ 2 ∣ 3 ^ 2 * 5 * 7 * 11 := hcop.dvd_of_dvd_mul_left h'
  have hle : p ^ 2 ≤ 3465 := Nat.le_of_dvd (by norm_num) hrest
  have hp_dvd : p ∣ 3 ^ 2 * 5 * 7 * 11 := by
    have h := hrest
    rw [pow_two] at h
    exact (dvd_mul_right p p).trans h
  have hp_dvd' : p ∣ 3 ^ 2 * (5 * (7 * 11)) := by
    simpa only [show 3 ^ 2 * (5 * (7 * 11)) = 3 ^ 2 * 5 * 7 * 11 by ring] using hp_dvd
  have hp_cases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    rcases (Nat.Prime.dvd_mul hp).1 hp_dvd' with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
  rcases hp_cases with rfl | rfl | rfl | rfl
  · exact hp3 rfl
  · norm_num at hrest
  · norm_num at hrest
  · norm_num at hrest

theorem pRank_mulAut_m22_le_one
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22))) ≤ 1 := by
  by_contra h
  push Not at h
  have hdvd := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp
    (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22)))
  rw [Subgroup.card_top] at hdvd
  exact not_sq_dvd_mulAut_m22 hp hp2 hp3
    (((pow_dvd_pow p h).trans hdvd).trans card_mulAut_carrier_m22_dvd)

theorem pRank_mbar_le_mulAut_m22 {D : Data G} {V₀ V L : Subgroup G}
    (hV : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hSpor : IsSpor (barSub V₀ V hV.isElemAbelian L) .M22)
    (hcent : Subgroup.centralizer
      (barSub V₀ V hV.isElemAbelian L : Set (MulAut (Vtil V₀ V hV.isElemAbelian))) = ⊥)
    {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) ≤
      CFSG.Open.pRank p
        (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22))) := by
  let W := Vtil V₀ V hV.isElemAbelian
  let Lb : Subgroup (MulAut W) := barSub V₀ V hV.isElemAbelian L
  let Mb : Subgroup (MulAut W) := Mbar D.M V₀ V hV.isElemAbelian
  have hLbMb : Lb ≤ Mb := barSub_mono V₀ V hV.isElemAbelian hL.1.le
  have hNbar : (Lb.subgroupOf Mb).Normal :=
    barSub_subgroupOf_mbar_normal hV.isElemAbelian hL.1.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN)
  have hMbN : Mb ≤ Subgroup.normalizer (Lb : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbMb).1 hNbar
  let f : Mb →* MulAut Lb :=
    (Subgroup.normalizerMonoidHom (H := Lb)).comp (Subgroup.inclusion hMbN)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hc : (m : MulAut W) ∈ Subgroup.centralizer (Lb : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun g : MulAut Lb => ((g ⟨x, hx⟩ : Lb) : MulAut W)) hm
      have hval : ((f m ⟨x, hx⟩ : Lb) : MulAut W) = (m : MulAut W) * x * (m : MulAut W)⁻¹ := by
        simp [f, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      rw [hval, MulAut.one_apply] at h
      calc x * (m : MulAut W) = ((m : MulAut W) * x * (m : MulAut W)⁻¹) * (m : MulAut W) := by
            rw [h]
        _ = (m : MulAut W) * x := by group
    rw [hcent] at hc
    simpa using hc
  have hbound := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt f hinj
  obtain ⟨eL⟩ := hSpor
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eL)
  calc CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian)
      = CFSG.Open.pRank p (⊤ : Subgroup Mb) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Mb)
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut Lb)) := hbound
    _ = CFSG.Open.pRank p
        (⊤ : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .M22))) := heq

theorem card_vzero_le_four_of_hexad {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hPair : Gap17_21_M22HexadPair D V₀ V hV) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h127One : R127One D)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) {L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hspor : IsSpor (BarInf L) .M22) :
    Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hpair := hV.pairFacts
  have hV₀p : IsPGroup 2 V₀ := IsElemAbelian.isPGroup hpair.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV hV hne
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := hyp125_isTI hV hne
  have h9 : CFSG.LocalAnalysis.WeakClosure81.Hyp9 V₀ D.T :=
    hyp9_of_hyp125 hTim hcat D hV h8
  have hN : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have hz : ∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ D.M := fun z hz hzc hz1 =>
    hyp125_centralizer_le hV hne hz hzc hz1
  obtain ⟨E, X₁, X₂, hEM, hEcard, hEel, hX₁M, hX₂M, hX₁card, hX₂card,
    hX₁perm, hX₂perm, hEsub, hXsubM⟩ := hPair L c hspor
  have hEp : IsPGroup 3 ↥E := hEel.isPGroup
  have hEnc : ¬ IsCyclic ↥E :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.not_isCyclic_of_elemAbelian_nine hEel hEcard
  have hΓE : rankThreeGamma 1 3 E ≤ D.M :=
    ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hsp3 hEM hEp
  have hUE : UniqueMax D.M E :=
    uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_three (by norm_num) hEM hEp hEnc
      (Or.inl hΓE)
  have hU : UniqueMax D.M (X₁ ⊔ X₂ ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D hEsub hXsubM hUE
  have hX₁exp : ∀ x ∈ X₁, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ Nat.card ↥X₁ := Subgroup.orderOf_dvd_natCard X₁ hx
    rw [hX₁card] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hX₂exp : ∀ x ∈ X₂, x ^ 3 = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ Nat.card ↥X₂ := Subgroup.orderOf_dvd_natCard X₂ hx
    rw [hX₂card] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hX₁p : IsPGroup 3 ↥X₁ :=
    IsPGroup.of_card (n := 1) (by rw [hX₁card]; norm_num)
  have hX₂p : IsPGroup 3 ↥X₂ :=
    IsPGroup.of_card (n := 1) (by rw [hX₂card]; norm_num)
  have hΓ₁ : rankThreeGamma 1 3 X₁ ≤ D.M :=
    ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hsp3 hX₁M hX₁p
  have hΓ₂ : rankThreeGamma 1 3 X₂ ≤ D.M :=
    ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hsp3 hX₂M hX₂p
  have hXM₁ : ∀ g : G, g ∉ D.M → V₀ ≤ CFSG.Quasithin.conjSubgroup D.M g →
      X₁ ⊓ CFSG.Quasithin.conjSubgroup D.M g = ⊥ := by
    intro g hg _
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hxX : x ∈ X₁ := (Subgroup.mem_inf.1 hx).1
    have hxM : x ∈ D.M := hX₁M hxX
    have hxConj : x ∈ CFSG.Quasithin.conjSubgroup D.M g := (Subgroup.mem_inf.1 hx).2
    let K : Subgroup G := D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom
    have hxInt : x ∈ K := ⟨hxM, hxConj⟩
    have hord : orderOf x = 3 := orderOf_eq_prime (hX₁exp x hxX) hx1
    have h3 : 3 ∣ Nat.card ↥K := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard K hxInt
    exact hsp3.2.2 g⁻¹ (by simpa using hg) h3
  have hXM₂ : ∀ g : G, g ∉ D.M → V₀ ≤ CFSG.Quasithin.conjSubgroup D.M g →
      X₂ ⊓ CFSG.Quasithin.conjSubgroup D.M g = ⊥ := by
    intro g hg _
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hxX : x ∈ X₂ := (Subgroup.mem_inf.1 hx).1
    have hxM : x ∈ D.M := hX₂M hxX
    have hxConj : x ∈ CFSG.Quasithin.conjSubgroup D.M g := (Subgroup.mem_inf.1 hx).2
    let K : Subgroup G := D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom
    have hxInt : x ∈ K := ⟨hxM, hxConj⟩
    have hord : orderOf x = 3 := orderOf_eq_prime (hX₂exp x hxX) hx1
    have h3 : 3 ∣ Nat.card ↥K := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard K hxInt
    exact hsp3.2.2 g⁻¹ (by simpa using hg) h3
  have hcalP₁ : X₁ ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ :=
    TwelveSixteen.mem_calP D hW hTI Nat.prime_three (by norm_num) hX₁p hXM₁ hΓ₁
  have hcalP₂ : X₂ ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ :=
    TwelveSixteen.mem_calP D hW hTI Nat.prime_three (by norm_num) hX₂p hXM₂ hΓ₂
  rcases CFSG.LocalAnalysis.WeakClosure81.nine_thirteen h9 h93 hcalP₁ hX₁perm with h1 | h2
  · exact twelve_seven_three_one hTim hcat D h66 h88 hV.2 hW hTI h8 hz (h1.trans hN.le)
  rcases CFSG.LocalAnalysis.WeakClosure81.nine_thirteen h9 h93 hcalP₂ hX₂perm with h3 | h4
  · exact twelve_seven_three_one hTim hcat D h66 h88 hV.2 hW hTI h8 hz (h3.trans hN.le)
  · have hXW : X₁ ⊔ X₂ ⊔ D.T ≤
        Subgroup.normalizer (CFSG.Quasithin.E3.wClos V₀ 0 D.T : Set G) := by
      refine sup_le (sup_le (le_trans le_sup_left h2) (le_trans le_sup_left h4))
        (le_trans le_sup_right h2)
    have hU0 : UniqueMax D.M
        (D.M ⊓ Subgroup.normalizer (CFSG.Quasithin.E3.wClos V₀ 0 D.T : Set G)) := by
      unfold UniqueMax at hU ⊢
      refine Set.Subset.antisymm ?_ ?_
      · intro N hN
        have hmem : N ∈ calMOf (X₁ ⊔ X₂ ⊔ D.T) :=
          ⟨hN.1, le_trans (le_inf hXsubM hXW) hN.2⟩
        rwa [hU] at hmem
      · rintro N rfl
        exact ⟨D.maxLocal, inf_le_left⟩
    exact h127One hV.2 V₀ hW hTI h8 hU0

theorem pRank_mbar_ge_two_of_mem_sig {D : Data G} {V₀ V : Subgroup G}
    [hN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal]
    (hV : Hyp125 D V₀ V) (hH11 : F11.Hyp11 D V₀ V)
    (hcard4 : Nat.card V₀ ≤ 4) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {p : ℕ} (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) := by
  have hpair := hV.pairFacts
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hpair.le_normalizer hpair.le_normalizer₀
  have h115 := uc22p22q_r115_of D hx h61
  obtain ⟨-, hle, -⟩ := h115 V₀ V hH11 hcard4 p hp
  have hle' : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have hEq : CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) =
      CFSG.Open.pRank p (⊤ : Subgroup (Mbar D.M V₀ V hV.isElemAbelian)) :=
    s15_Three_pRank_MBar11 (D := D) (V₀ := V₀) (V := V) hV.isElemAbelian hMs (p := p)
  have hleM : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (Mbar D.M V₀ V hV.isElemAbelian), ← hEq]
    exact hle'
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hp
  omega

theorem gap17_21_M22Data_of
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hMod : Gap17_21_M22Module D V₀ V hV) (hHex : Gap17_21_M22HexadPair D V₀ V hV)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h127One : R127One D) (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h17_20 : R17_20At D V₀ V) (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) :
    Gap17_21_M22Data D V₀ V hV := by
  intro L c hspor
  obtain ⟨hSporL, _hRank10, _hirrL, hcentL, hpoint⟩ := hMod L c hspor
  obtain ⟨-, hN, -⟩ := h17_20 L c
  have hcard4 : Nat.card V₀ ≤ 4 :=
    card_vzero_le_four_of_hexad hV hHex h61 h63 hsp3 hTim hcat h66 h88 h127One h93 c hspor
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 c.hyp125
  have hsig : D.sig = {3} := by
    have hkey : ∀ p ∈ D.sig, p = 3 := by
      intro p hp
      by_contra hp3
      obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
      have hge : 2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) :=
        pRank_mbar_ge_two_of_mem_sig (hN := cTilde_normal_of_hyp11 hH11) hV hH11 hcard4 hx h61 hp
      have hleAut := pRank_mbar_le_mulAut_m22 hV c.mem_calC hN hSporL hcentL (p := p) hpP
      have hle1 := pRank_mulAut_m22_le_one hpP hp2 hp3
      omega
    obtain ⟨p, hp⟩ := hx.sig_nonempty
    have hp3 : p = 3 := hkey p hp
    subst hp3
    ext q
    constructor
    · intro hq
      exact hkey q hq
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hp
  have hbar3 : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) ≤ 2 := by
    have h := pRank_mbar_le_mulAut_m22 hV c.mem_calC hN hSporL hcentL
      (p := 3) Nat.prime_three
    exact h.trans pRank_three_mulAut_m22_le
  exact ⟨hcard4, hsig, hbar3, hpoint⟩

theorem gap17_21_M22Data_of_split
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hirr : Gap17_21_irr D V₀ V hV) (hTodd : Gap17_21_M22Todd D V₀ V hV)
    (hPoint : Gap17_21_M22Point D V₀ V hV)
    (hKHex : Inputs1719.K_M22HexadPair)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D)
    (h127One : R127One D) (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h17_20 : R17_20At D V₀ V) (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) :
    Gap17_21_M22Data D V₀ V hV :=
  gap17_21_M22Data_of D V₀ V hV
    (gap17_21_M22Module_of hirr hTodd hPoint)
    (gap17_21_M22HexadPair_of_K hV h17_20 hKHex) hx h61 h63 h127 h127One hsp3 hTim hcat h66
    h88 h17_20 h93

section Certified


theorem seventeen_twentyone_of_M22Module (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_4 : R17_4AtA D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (hKS5 : Inputs1719.K_SporadicNine)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (hB21 : B17_21Bound D V₀ V hV)
    (hKS6 : Inputs1719.K_M12SThreePair)
    (hKS7 : Inputs1719.K_HSRuParabolics)
    (hirr : Gap17_21_irr D V₀ V hV) (hTodd : Gap17_21_M22Todd D V₀ V hV)
    (hPoint : Gap17_21_M22Point D V₀ V hV) (hKHex : Inputs1719.K_M22HexadPair)
    (h127One : R127One D) (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_6 D) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) :
    R17_21At D V₀ V :=
  seventeen_twentyone_of_data D V₀ V hV h17_1 h17_4 h17_20 h869 hC117 hKS5 hx h61 h127 h1114
    h162 hTor h1482 h126 h111 hB21 hKS6 hKS7
    (gap17_21_M22Data_of_split D V₀ V hV hirr hTodd hPoint hKHex hx h61 h63 h127 h127One
      hsp3 hTim hcat h66 h88 h17_20 h93)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
