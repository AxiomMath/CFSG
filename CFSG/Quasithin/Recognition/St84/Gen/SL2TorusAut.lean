module

public import CFSG.CGT.Timmesfeld75.L2Aut

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem exists_torusElt_of_map_utri_of_fix_torus {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (θ : SL(2, F) ≃* SL(2, F))
    (hU : ∀ x, θ x ∈ utri F ↔ x ∈ utri F) (hT : ∀ a : Fˣ, θ (torusElt a) = torusElt a) :
    ∃ a : Fˣ, ∀ x, θ x = torusElt a * x * (torusElt a)⁻¹ := by
  obtain ⟨g, σ, hg⟩ := exists_eq_conj_sl2FieldAut θ
  have hg_borel : g ∈ borel F := by
    rw [mem_borel_iff]
    have h1 : g * utriElt (1 : F) * g⁻¹ ∈ utri F := by
      have h := (hU (utriElt (1 : F))).2 (utriElt_mem_utri 1)
      rw [hg, sl2FieldAut_utriElt] at h
      simpa using h
    have h2 : g 1 0 ^ 2 = 0 := by
      have h := h1.1
      rw [conj_utriElt_apply_10, mul_one] at h
      linear_combination (-1) * h
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  obtain ⟨a, ha⟩ :=
    CFSG.Glauberman.Dickson.eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero g
      (mem_borel_iff.1 hg_borel)
  let s : F := g 0 1 * g 0 0
  have ha' : g = utriElt s * torusElt a := ha
  have hkey : ∀ b : Fˣ, g * torusElt (Units.map (σ : F →* F) b) * g⁻¹ = torusElt b := by
    intro b
    have h := hT b
    rwa [hg, sl2FieldAut_torusElt] at h
  have hconj : ∀ b : Fˣ,
      utriElt s * torusElt (Units.map (σ : F →* F) b) * (utriElt s)⁻¹ = torusElt b := by
    intro b
    have hcomm : torusElt a * torusElt (Units.map (σ : F →* F) b) =
        torusElt (Units.map (σ : F →* F) b) * torusElt a := by
      rw [← torusElt_mul, ← torusElt_mul, mul_comm a (Units.map (σ : F →* F) b)]
    have hcomm' : torusElt a * torusElt (Units.map (σ : F →* F) b) * (torusElt a)⁻¹ =
        torusElt (Units.map (σ : F →* F) b) := by
      rw [hcomm]
      group
    calc utriElt s * torusElt (Units.map (σ : F →* F) b) * (utriElt s)⁻¹
        = utriElt s * (torusElt a * torusElt (Units.map (σ : F →* F) b) * (torusElt a)⁻¹) *
            (utriElt s)⁻¹ := by rw [hcomm']
      _ = (utriElt s * torusElt a) * torusElt (Units.map (σ : F →* F) b) *
            (utriElt s * torusElt a)⁻¹ := by group
      _ = g * torusElt (Units.map (σ : F →* F) b) * g⁻¹ := by rw [← ha']
      _ = torusElt b := hkey b
  have hcb : ∀ b : Fˣ, Units.map (σ : F →* F) b = b := by
    intro b
    have h := congrArg (fun g : SL(2, F) => g 0 0) (hconj b)
    sl2_simp at h
    exact Units.ext (by simpa using h)
  have hσ : σ = RingEquiv.refl F := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have h := congrArg (fun u : Fˣ => (u : F)) (hcb (Units.mk0 x hx))
      simpa using h
  have hconj_b : ∀ b : Fˣ, utriElt s * torusElt b * (utriElt s)⁻¹ = torusElt b := by
    intro b
    simpa only [hcb b] using hconj b
  have hs : s = 0 := by
    have hle : 3 ≤ Nat.card F - 1 := by simpa using Nat.sub_le_sub_right hF 1
    have hlt : 1 < Nat.card Fˣ := by
      rw [Nat.card_units]
      exact lt_of_lt_of_le (by norm_num) hle
    haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlt
    obtain ⟨b, hbne⟩ := exists_ne (1 : Fˣ)
    have h01 := congrArg (fun g : SL(2, F) => g 0 1) (hconj_b b)
    sl2_simp at h01
    rw [Units.val_inv_eq_inv_val] at h01
    rw [CharTwo.neg_eq] at h01
    have h01' : (b : F) * s + s * (b : F)⁻¹ = 0 := by simpa using h01
    have hb1 : (b : F) ≠ 1 := fun h => hbne (Units.ext h)
    have hb2 : (b : F) ^ 2 ≠ 1 := by
      intro h
      exact hb1 (CharTwo.sq_injective (by simpa using h))
    have hbinv : (b : F)⁻¹ - (b : F) ≠ 0 := by
      intro h0
      apply hb2
      have h1 : (b : F)⁻¹ = (b : F) := sub_eq_zero.1 h0
      have h2 : (b : F) * (b : F) = 1 := by
        calc (b : F) * (b : F) = (b : F) * (b : F)⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel₀ (Units.ne_zero b)
      simpa [pow_two] using h2
    have h2 : s * ((b : F)⁻¹ - (b : F)) = 0 := by
      rw [CharTwo.sub_eq_add]
      calc s * ((b : F)⁻¹ + (b : F)) = s * (b : F)⁻¹ + s * (b : F) := by ring
        _ = (b : F) * s + s * (b : F)⁻¹ := by ring
        _ = 0 := h01'
    exact (mul_eq_zero.mp h2).resolve_right hbinv
  have hg_t : g = torusElt a := by
    rw [ha', hs, utriElt_zero, one_mul]
  refine ⟨a, fun x => ?_⟩
  rw [hg x, hσ, sl2FieldAut_refl, hg_t]
  simp

theorem exists_mem_torus_conj_mem_of_normalizes {G : Type*} [Group G] {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) {L Q U' T' : Subgroup G}
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α) (hker : α.ker = Q.subgroupOf L)
    (hU' : (U'.subgroupOf L).map α = utri F) (hT'L : T' ≤ L)
    (hT' : (T'.subgroupOf L).map α = torus F)
    {h : G} (hhL : h ∈ Subgroup.normalizer (L : Set G))
    (hhQ : h ∈ Subgroup.normalizer (Q : Set G))
    (hhU : h ∈ Subgroup.normalizer (U' : Set G))
    (hhT : ∀ t ∈ T', h * t * h⁻¹ = t) :
    ∃ t ∈ T', ∀ l ∈ L, (t⁻¹ * h) * l * (t⁻¹ * h)⁻¹ * l⁻¹ ∈ Q := by
  classical
  let cLHom : ↥L →* ↥L :=
    { toFun := fun l => ⟨h * (l : G) * h⁻¹, (Subgroup.mem_normalizer_iff.1 hhL (l : G)).1 l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show h * ((a * b : ↥L) : G) * h⁻¹ =
          (h * (a : G) * h⁻¹) * (h * (b : G) * h⁻¹)
        rw [Subgroup.coe_mul]
        group }
  let cLInv : ↥L →* ↥L :=
    { toFun := fun l => ⟨h⁻¹ * (l : G) * h, by
        simpa using
          (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhL) (l : G)).1 l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show h⁻¹ * ((a * b : ↥L) : G) * h =
          (h⁻¹ * (a : G) * h) * (h⁻¹ * (b : G) * h)
        rw [Subgroup.coe_mul]
        group }
  have hcL_apply : ∀ l : ↥L, (cLHom l : G) = h * (l : G) * h⁻¹ := fun _ => rfl
  have hcLinv_apply : ∀ l : ↥L, (cLInv l : G) = h⁻¹ * (l : G) * h := fun _ => rfl
  have hcL_id : ∀ l : ↥L, cLHom (cLInv l) = l := by
    intro l
    apply Subtype.ext
    rw [hcL_apply, hcLinv_apply]
    group
  let N : Subgroup ↥L := Q.subgroupOf L
  have hN : α.ker = N := hker
  haveI : N.Normal := by
    rw [← hN]
    exact MonoidHom.normal_ker α
  let β : ↥L →* SL(2, F) := α.comp cLHom
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨l, hl⟩ := hα y
    refine ⟨cLInv l, ?_⟩
    show α (cLHom (cLInv l)) = y
    rw [hcL_id l]
    exact hl
  have hβker : β.ker = N := by
    ext l
    rw [MonoidHom.mem_ker]
    constructor
    · intro hl
      have h1 : cLHom l ∈ α.ker := MonoidHom.mem_ker.mpr hl
      rw [hN] at h1
      have hQ : ((cLHom l : ↥L) : G) ∈ Q := (Subgroup.mem_subgroupOf).mp h1
      have hQ' : (l : G) ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 hhQ (l : G)).2 (by simpa [hcL_apply] using hQ)
      exact (Subgroup.mem_subgroupOf).mpr hQ'
    · intro hl
      have hQ : (l : G) ∈ Q := (Subgroup.mem_subgroupOf).mp hl
      have hQ' : h * (l : G) * h⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hhQ (l : G)).1 hQ
      have h1 : cLHom l ∈ N :=
        (Subgroup.mem_subgroupOf).mpr (by simpa [hcL_apply] using hQ')
      have h2 : cLHom l ∈ α.ker := by rwa [hN]
      exact MonoidHom.mem_ker.mp h2
  let eα : ↥L ⧸ N ≃* SL(2, F) := QuotientGroup.liftEquiv N hα hN.symm
  let eβ : ↥L ⧸ N ≃* SL(2, F) := QuotientGroup.liftEquiv N hβsurj hβker.symm
  let θ : SL(2, F) ≃* SL(2, F) := eα.symm.trans eβ
  have heα : ∀ l : ↥L, eα (QuotientGroup.mk' N l) = α l := fun _ => rfl
  have heβ : ∀ l : ↥L, eβ (QuotientGroup.mk' N l) = β l := fun _ => rfl
  have hθ : ∀ l : ↥L, θ (α l) = β l := by
    intro l
    show eβ (eα.symm (α l)) = β l
    have hsymm : eα.symm (α l) = QuotientGroup.mk' N l := by
      rw [← heα l]
      exact MulEquiv.symm_apply_apply eα _
    rw [hsymm]
    exact heβ l
  have hmapU' : (U'.subgroupOf L).map cLHom = U'.subgroupOf L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hyU : (y : G) ∈ U' := (Subgroup.mem_subgroupOf).mp hy
      have hmem : h * (y : G) * h⁻¹ ∈ U' :=
        (Subgroup.mem_normalizer_iff.1 hhU (y : G)).1 hyU
      exact (Subgroup.mem_subgroupOf).mpr (by simpa [hcL_apply] using hmem)
    · intro x hx
      refine Subgroup.mem_map.2 ⟨cLInv x, ?_, ?_⟩
      · have hxU : (x : G) ∈ U' := (Subgroup.mem_subgroupOf).mp hx
        have hmem : h⁻¹ * (x : G) * h ∈ U' := by
          simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhU) (x : G)).1 hxU
        exact (Subgroup.mem_subgroupOf).mpr (by simpa [hcLinv_apply] using hmem)
      · apply Subtype.ext
        rw [hcL_apply, hcLinv_apply]
        group
  have hcompθα : θ.toMonoidHom.comp α = β := MonoidHom.ext hθ
  have hmap : (utri F).map θ.toMonoidHom = utri F := by
    rw [← hU', Subgroup.map_map, hcompθα]
    change (U'.subgroupOf L).map (α.comp cLHom) = (U'.subgroupOf L).map α
    rw [← Subgroup.map_map, hmapU']
  have hU : ∀ x, θ x ∈ utri F ↔ x ∈ utri F := fun x => mem_iff_of_map_mulEquiv_eq θ hmap x
  have hT : ∀ a : Fˣ, θ (torusElt a) = torusElt a := by
    intro a
    obtain ⟨tL, htL, htα⟩ :=
      Subgroup.mem_map.1 (by rw [hT']; exact torusElt_mem_torus a)
    have hfix : cLHom tL = tL := by
      apply Subtype.ext
      rw [hcL_apply]
      exact hhT (tL : G) ((Subgroup.mem_subgroupOf).mp htL)
    rw [← htα, hθ tL]
    show α (cLHom tL) = α tL
    rw [hfix]
  obtain ⟨a, ha⟩ := exists_torusElt_of_map_utri_of_fix_torus hF θ hU hT
  obtain ⟨tL, htL, htα⟩ :=
    Subgroup.mem_map.1 (by rw [hT']; exact torusElt_mem_torus a)
  refine ⟨(tL : G), (Subgroup.mem_subgroupOf).mp htL, fun l hl => ?_⟩
  let lL : ↥L := ⟨l, hl⟩
  have hmemL : h * l * h⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hhL l).1 hl
  have hconj : α (cLHom lL) = torusElt a * α lL * (torusElt a)⁻¹ := by
    calc α (cLHom lL) = β lL := rfl
      _ = θ (α lL) := (hθ lL).symm
      _ = torusElt a * α lL * (torusElt a)⁻¹ := ha (α lL)
  have htLmem : (tL : G) ∈ L := hT'L ((Subgroup.mem_subgroupOf).mp htL)
  have hgmem : (tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem htLmem) hmemL) htLmem) (L.inv_mem hl)
  have hαg : α ⟨(tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹, hgmem⟩ = 1 := by
    have heq : (⟨(tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹, hgmem⟩ : ↥L) =
        tL⁻¹ * cLHom lL * tL * lL⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hconj, htα]
    group
  have hgQ : (tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹ ∈ Q := by
    have h1 : (⟨(tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹, hgmem⟩ : ↥L) ∈ α.ker :=
      MonoidHom.mem_ker.mpr hαg
    rw [hN] at h1
    exact (Subgroup.mem_subgroupOf).mp h1
  rw [show ((tL : G)⁻¹ * h) * l * ((tL : G)⁻¹ * h)⁻¹ * l⁻¹ =
      (tL : G)⁻¹ * (h * l * h⁻¹) * (tL : G) * l⁻¹ by group]
  exact hgQ

end CFSG.Quasithin.F112R.St84
