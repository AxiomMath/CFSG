module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_trivial_of_hyperplane {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {H : Subgroup (MulAut (Vtil V₀ V hV))} (hNT : OmegaNoTrans H) {U₁ : Subgroup G}
    (hU₁ : U₁ ≤ V) (hcard : Nat.card ↥V = 2 * Nat.card ↥U₁) {t : G}
    (ht : t ∈ stabTil V₀ V) (htH : actTil V₀ V hV ⟨t, ht⟩ ∈ H)
    (hcent : ∀ u ∈ U₁, t * u * t⁻¹ = u) :
    ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ V₀ := by
  haveI : IsMulCommutative ↥V := hV.1
  have htV : t ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V ht
  have hrel : U₁.relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card (H := U₁) (K := V)
    rw [inf_eq_left.2 hU₁] at h
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥U₁)) h
  obtain ⟨a, haV, ha⟩ := (Subgroup.relIndex_eq_two_iff (H := U₁) (K := V)).1 hrel
  set w : G := a⁻¹ with hwdef
  have hwV : w ∈ V := by rw [hwdef]; exact V.inv_mem haV
  have hw_inv : w⁻¹ = a := by rw [hwdef, inv_inv]
  have hw_not : w ∉ U₁ := by
    rw [hwdef]
    intro h
    have hnot : a ∉ U₁ := by
      have h1 : (a ∈ U₁) ↔ False := by
        simpa using (xor_iff_iff_not).1 (ha 1 V.one_mem)
      exact fun ha' => h1.1 ha'
    exact hnot (by simpa using inv_mem h)
  have hvu : ∀ v ∈ V, v ∉ U₁ → v * w⁻¹ ∈ U₁ := by
    intro v hv hvU
    have hiff : (v * a ∈ U₁) ↔ ¬ (v ∈ U₁) := (xor_iff_iff_not).1 (ha v hv)
    rw [hw_inv]
    exact hiff.mpr hvU
  set a0 : G := t * w * t⁻¹ * w⁻¹ with ha0def
  have ha0V : a0 ∈ V := by
    rw [ha0def]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 htV w).1 hwV) (V.inv_mem hwV)
  have hconj : ∀ u ∈ V, u * a0 * u⁻¹ = a0 := by
    intro u hu
    have hmem : (⟨u, hu⟩ : ↥V) * ⟨a0, ha0V⟩ * (⟨u, hu⟩ : ↥V)⁻¹ = ⟨a0, ha0V⟩ := by
      rw [mul_comm' (⟨u, hu⟩ : ↥V) (⟨a0, ha0V⟩ : ↥V)]
      group
    exact congrArg Subtype.val hmem
  have hcomm : ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ = 1 ∨ t * v * t⁻¹ * v⁻¹ = a0 := by
    intro v hv
    by_cases hvU : v ∈ U₁
    · left
      rw [hcent v hvU, mul_inv_cancel]
    · right
      have hu : v * w⁻¹ ∈ U₁ := hvu v hv hvU
      have hcu : t * (v * w⁻¹) * t⁻¹ = v * w⁻¹ := hcent _ hu
      have huV : v * w⁻¹ ∈ V := V.mul_mem hv (V.inv_mem hwV)
      have hv_eq : v = (v * w⁻¹) * w := by group
      rw [hv_eq]
      have step : t * ((v * w⁻¹) * w) * t⁻¹ * ((v * w⁻¹) * w)⁻¹
          = (v * w⁻¹) * a0 * (v * w⁻¹)⁻¹ := by
        rw [ha0def,
          show t * ((v * w⁻¹) * w) * t⁻¹
              = (t * (v * w⁻¹) * t⁻¹) * (t * w * t⁻¹) by group, hcu]
        group
      rw [step, hconj _ huV]
  by_cases ha0V0 : a0 ∈ V₀
  · intro v hv
    rcases hcomm v hv with h | h
    · rw [h]; exact V₀.one_mem
    · rw [h]; exact ha0V0
  · let amk : IntMod V hV := IntMod.mk hV ⟨a0, ha0V⟩
    let c : Vtil V₀ V hV := mkTil V₀ V hV amk
    have hc1 : c ≠ 1 := by
      intro hc
      have h1 : mkTil V₀ V hV amk = mkTil V₀ V hV (1 : IntMod V hV) := by
        rw [map_one]; exact hc
      have hmem : a0 ∈ V₀ := by
        have h := (mkTil_eq_iff V₀ V hV amk 1).1 h1
        have hval : amk.val = a0 := rfl
        rw [hval, IntMod.val_one, inv_one, mul_one] at h
        exact h
      exact ha0V0 hmem
    have hphi : ∀ w' : Vtil V₀ V hV,
        actTil V₀ V hV ⟨t, ht⟩ w' = w' ∨ actTil V₀ V hV ⟨t, ht⟩ w' = w' * c := by
      intro w'
      obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w'
      rcases hcomm y.val y.val_mem with hy | hy
      · left
        have hstab : actStab V₀ V hV ⟨t, ht⟩ y = y := by
          apply IntMod.val_injective
          rw [actStab_apply_val]
          exact (mul_inv_eq_one).1 hy
        rw [actTil_mk, hstab]
      · right
        have hstab : actStab V₀ V hV ⟨t, ht⟩ y = amk * y := by
          apply IntMod.val_injective
          rw [actStab_apply_val, IntMod.val_mul]
          show t * y.val * t⁻¹ = a0 * y.val
          calc t * y.val * t⁻¹ = (t * y.val * t⁻¹ * y.val⁻¹) * y.val := by group
            _ = a0 * y.val := by rw [hy]
        rw [actTil_mk, hstab, map_mul]
        exact mul_comm _ _
    have hphi1 : actTil V₀ V hV ⟨t, ht⟩ = 1 := hNT _ htH c hc1 hphi
    exact (actTil_eq_one_iff V₀ V hV ⟨t, ht⟩).1 hphi1

theorem s16c1_hyp1643_conj_V' (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {h : G}
    (hle : conjSubgroup V h ≤ D.M) : Hyp1643 D V₀ V 0 (conjSubgroup V h) h := by
  have hV2 : IsPGroup 2 V := fun y => ⟨1, Subtype.ext (by simpa using hV.2 y y.2)⟩
  have hpg : IsPGroup 2 (conjSubgroup V h) := IsPGroup.map hV2 _
  exact ⟨Or.inl rfl, ⟨hle, h, le_rfl, (E3.mQuot_eq_zero_iff hpg le_rfl).2 rfl⟩, le_rfl⟩

theorem s16c1_mem_cTilde_of_conjV_le_M (D : Data G) (hkit : OmegaKit) (h43 : R16_43_1 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {U₁ : Subgroup G} (hU₁ : U₁ ≤ V)
    (hcard : Nat.card ↥V = 2 * Nat.card ↥U₁) {h : G} (hhM : conjSubgroup V h ≤ D.M)
    {x : G} (hx : x ∈ conjSubgroup V₀ h) (hxM : x ∈ D.M)
    (hxU : ∀ u ∈ U₁, x * u * x⁻¹ = u) : x ∈ F11.CTilde D.M V₀ V := by
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hxV : x ∈ conjSubgroup V h := E3.conjSubgroup_mono_left h hP.le hx
  have hxs : x ∈ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀ hxM
  have hle : barSub V₀ V hV (conjSubgroup V h) ≤ lBar V₀ V hV L :=
    h43 V₀ V L hV hS hc 0 (conjSubgroup V h) h (s16c1_hyp1643_conj_V' D hV hhM)
  have htH : actTil V₀ V hV ⟨x, hxs⟩ ∈ lBar V₀ V hV L :=
    hle (actTil_mem_barSub V₀ V hV hxV hxs)
  have hNT : OmegaNoTrans (lBar V₀ V hV L) :=
    (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2
  have htriv : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀ :=
    s16c1_trivial_of_hyperplane hNT hU₁ hcard hxs htH hxU
  exact (CFSG.LocalAnalysis.WeakClosure81.mem_cTilde_iff_centralizes hV
    hP.le_normalizer hP.le_normalizer₀).2 ⟨hxM, htriv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
