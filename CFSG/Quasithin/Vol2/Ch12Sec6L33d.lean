module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33c
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126g
public import CFSG.Quasithin.Vol2.Ch12Sec6L33t

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits S126 F126
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Translate

variable {T V L V₁ Vp H : Subgroup G}

abbrev tW (V₁ Vp H A : Subgroup G) : Subgroup ↥(UT V₁ Vp H) :=
  (tildeOf V₁ A).subgroupOf (UT V₁ Vp H)

noncomputable abbrev thX (h : HypF91 T V L V₁ Vp H) (X : Subgroup G) :
    Subgroup (MulAut ↥(UT V₁ Vp H)) :=
  (X.subgroupOf H).map (thetaH h)

omit [Finite G] in
theorem tW_mono {A B : Subgroup G} (hAB : A ≤ B) : tW V₁ Vp H A ≤ tW V₁ Vp H B :=
  fun _ hw => secImg_mono hAB hw

omit [Finite G] in
theorem tW_top : tW V₁ Vp H (conjClosure Vp H) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  exact w.2

omit [Finite G] in
theorem tW_eq_bot_of_le {A : Subgroup G} (hA : A ≤ V₁) : tW V₁ Vp H A = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨⟨a, haN⟩, ha, haw⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hw)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← haw]
  exact secMk_eq_one_iff.2 (hA ha)

omit [Finite G] in
theorem le_of_tW_eq_bot {A : Subgroup G} (hAU : A ≤ conjClosure Vp H) (hAN : A ≤ N1 V₁)
    (hA : tW V₁ Vp H A = ⊥) : A ≤ V₁ := by
  intro a ha
  have hw : secMk (N1 V₁) V₁ ⟨a, hAN ha⟩ ∈ UT V₁ Vp H := secImg_mono hAU (secMk_mem_secImg ha)
  have h1 : (⟨_, hw⟩ : ↥(UT V₁ Vp H)) ∈ tW V₁ Vp H A := secMk_mem_secImg ha
  rw [hA, Subgroup.mem_bot] at h1
  exact secMk_eq_one_iff.1 (congrArg Subtype.val h1)

theorem hWcomm (h : HypF91 T V L V₁ Vp H) : ∀ a b : ↥(UT V₁ Vp H), a * b = b * a :=
  fun a b => h.isElemAbelian_tilde.1.is_comm.comm a b

omit [Finite G] in
theorem commutator_le_conjClosure {A X : Subgroup G} (hAU : A ≤ conjClosure Vp H) (hXH : X ≤ H) :
    ⁅A, X⁆ ≤ conjClosure Vp H := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  rw [commutatorElement_def]
  have h1 : x * a⁻¹ * x⁻¹ ∈ conjClosure Vp H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure Vp H (hXH hx)) _).1
      ((conjClosure Vp H).inv_mem (hAU ha))
  have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
  rw [e]
  exact (conjClosure Vp H).mul_mem (hAU ha) h1

theorem cmSet_thX_tW (h : HypF91 T V L V₁ Vp H) {A X : Subgroup G}
    (hAU : A ≤ conjClosure Vp H) (hXH : X ≤ H) :
    cmSet (thX h X) (tW V₁ Vp H A) = tW V₁ Vp H ⁅A, X⁆ := by
  have hUN : conjClosure Vp H ≤ N1 V₁ :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  apply le_antisymm
  · refine cmSet_le ?_
    rintro _ ⟨x, hx, rfl⟩ w hw
    obtain ⟨⟨a, haN⟩, ha, haw⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hw)
    refine thetaH_mul_inv_mem h x.2 (A := ⁅A, X⁆) haN ?_ w haw
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hx) ha
  · let P : Subgroup G :=
      { carrier := {g | ∃ hg : g ∈ N1 V₁, secMk (N1 V₁) V₁ ⟨g, hg⟩ ∈
          (cmSet (thX h X) (tW V₁ Vp H A)).map (UT V₁ Vp H).subtype}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨(N1 V₁).mul_mem ha hb, ?_⟩
          have : secMk (N1 V₁) V₁ ⟨a * b, (N1 V₁).mul_mem ha hb⟩ =
              secMk (N1 V₁) V₁ ⟨a, ha⟩ * secMk (N1 V₁) V₁ ⟨b, hb⟩ := by
            rw [← map_mul]; rfl
          rw [this]
          exact ((cmSet (thX h X) (tW V₁ Vp H A)).map _).mul_mem ha' hb'
        one_mem' := ⟨(N1 V₁).one_mem, by
          have : secMk (N1 V₁) V₁ ⟨1, (N1 V₁).one_mem⟩ = 1 := map_one _
          rw [this]
          exact ((cmSet (thX h X) (tW V₁ Vp H A)).map _).one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨(N1 V₁).inv_mem ha, ?_⟩
          have : secMk (N1 V₁) V₁ ⟨a⁻¹, (N1 V₁).inv_mem ha⟩ = (secMk (N1 V₁) V₁ ⟨a, ha⟩)⁻¹ := by
            rw [← map_inv]; rfl
          rw [this]
          exact ((cmSet (thX h X) (tW V₁ Vp H A)).map _).inv_mem ha' }
    have hle : ⁅A, X⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have haN : a ∈ N1 V₁ := hUN (hAU ha)
      have hxH : x ∈ H := hXH hx
      have hxN : x ∈ N1 V₁ := le_N1 h hxH
      have hcN : ⁅a, x⁆ ∈ N1 V₁ := by
        rw [commutatorElement_def]
        exact (N1 V₁).mul_mem ((N1 V₁).mul_mem ((N1 V₁).mul_mem haN hxN) ((N1 V₁).inv_mem haN))
          ((N1 V₁).inv_mem hxN)
      refine ⟨hcN, ?_⟩
      have haw : secMk (N1 V₁) V₁ ⟨a, haN⟩ ∈ UT V₁ Vp H := secImg_mono hAU (secMk_mem_secImg ha)
      have hf : thetaH h ⟨x, hxH⟩ ∈ thX h X := Subgroup.mem_map.2 ⟨⟨x, hxH⟩, hx, rfl⟩
      have hs : (⟨_, haw⟩ : ↥(UT V₁ Vp H)) ∈ tW V₁ Vp H A := secMk_mem_secImg ha
      have hmem := (cmSet (thX h X) (tW V₁ Vp H A)).inv_mem
        (mem_cmSet (X := thX h X) (S := tW V₁ Vp H A) hf hs)
      refine ⟨_, hmem, ?_⟩
      rw [Subgroup.subtype_apply, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        thetaH_apply]
      have e : secMk (N1 V₁) V₁ ⟨⁅a, x⁆, hcN⟩ = secMk (N1 V₁) V₁ ⟨a, haN⟩ *
          secMk (N1 V₁) V₁ ⟨x, hxN⟩ * (secMk (N1 V₁) V₁ ⟨a, haN⟩)⁻¹ *
          (secMk (N1 V₁) V₁ ⟨x, hxN⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e]
      show (toSec h ⟨x, hxH⟩ * secMk (N1 V₁) V₁ ⟨a, haN⟩ * (toSec h ⟨x, hxH⟩)⁻¹ *
        (secMk (N1 V₁) V₁ ⟨a, haN⟩)⁻¹)⁻¹ = _
      have ht : toSec h ⟨x, hxH⟩ = secMk (N1 V₁) V₁ ⟨x, hxN⟩ := rfl
      rw [ht]
      group
    intro w hw
    obtain ⟨⟨c, hcN⟩, hc, hcw⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hw)
    obtain ⟨hg, hm⟩ := hle hc
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 hm
    have : s = w := Subtype.ext (hse.trans hcw)
    rw [← this]
    exact hs

end Translate

section CaseA

variable {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem thX_perfect (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} (hXc : X ∈ cComp H) :
    ⁅thX h X, thX h X⁆ = thX h X := by
  rw [thX, ← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hXc),
    perfect_of_mem_cComp hXc]

theorem comm_le_of_claim_a (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K) {t : G}
    (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H)
    (ha1 : ⁅⁅conjClosure Vp H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure I H)
    (ha2 : ⁅⁅conjClosure I H, K⁆, conjSub t⁻¹ K⁆ ≤ V₁) :
    ⁅⁅conjClosure Vp H, K⁆, conjSub t⁻¹ K⁆ ≤ V₁ := by
  set h := h918.toHypF98.toHypF91 with hh
  have hW := hWcomm h
  have hTH : T ≤ H := le_sup_right.trans h.L₁T_le_H
  have htH : t ∈ H := hTH ht
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t⁻¹ K ∈ cComp H := conjSub_mem_cComp hKc (H.inv_mem htH)
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hK₂H : conjSub t⁻¹ K ≤ H := le_of_mem_cComp hK₂c
  have hne : K ≠ conjSub t⁻¹ K := fun he => htK (by
    have h1 : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq he.symm
    simpa using Subgroup.inv_mem _ h1)
  obtain ⟨-, ⟨e₁⟩, -⟩ := h2
  have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
  have hK₂s : S126.star H (conjSub t⁻¹ K) = (S126.star H K).map
      (MulAut.conj (QuotientGroup.mk ⟨t, htH⟩ : S126.HStar H)⁻¹).toMonoidHom := by
    rw [star_conjSub (H.inv_mem htH)]
    rfl
  have hs₂ : IsSimpleGroup ↥(S126.star H (conjSub t⁻¹ K)) :=
    (((S126.star H K).equivMapOfInjective _ (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr hK₂s.symm)).symm.isSimpleGroup
  have hcomm := commute_star hKc hK₂c hne hs hs₂
  have hc : ∀ f ∈ thX h K, ∀ g ∈ thX h (conjSub t⁻¹ K), f * g = g * f := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    rw [← map_mul, ← map_mul, ← psiH_mk, ← psiH_mk, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    congr 1
    exact hcomm _ ⟨k, hk, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
  have hUN : conjClosure Vp H ≤ N1 V₁ :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hIHU : conjClosure I H ≤ conjClosure Vp H := by
    refine conjClosure_le fun x hx i hi => ?_
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure Vp H hx) i).1 (hIU hi)
  have hU1 := commutator_le_conjClosure (Vp := Vp) (H := H) le_rfl hKH
  have hI1 := commutator_le_conjClosure hIHU hKH
  have ha1' : cmSet (thX h (conjSub t⁻¹ K)) (cmSet (thX h K) ⊤) ≤
      tW V₁ Vp H (conjClosure I H) := by
    rw [← tW_top, cmSet_thX_tW h le_rfl hKH, cmSet_thX_tW h hU1 hK₂H]
    exact tW_mono ha1
  have ha2' : cmSet (thX h (conjSub t⁻¹ K)) (cmSet (thX h K) (tW V₁ Vp H (conjClosure I H))) =
      ⊥ := by
    rw [cmSet_thX_tW h hIHU hKH, cmSet_thX_tW h hI1 hK₂H]
    exact tW_eq_bot_of_le ha2
  have hfin := cmSet_eq_bot hW (thX_perfect h hKc) (thX_perfect h hK₂c) hc ha1' ha2'
  rw [← tW_top, cmSet_thX_tW h le_rfl hKH, cmSet_thX_tW h hU1 hK₂H] at hfin
  have hle := commutator_le_conjClosure hU1 hK₂H
  exact le_of_tW_eq_bot hle (hle.trans hUN) hfin

end CaseA

end CFSG.Quasithin.H13.L1233
