module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelOrder3
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelPlane
public import CFSG.RankThree.GF2n.Tim81.Sec2.InvolutionModule
public import CFSG.CGT.Timmesfeld75.L2Basic

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.CGT.Timmesfeld75
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] {l : ℕ}
  {hF : Fintype.card F = 2 ^ (2 * l)} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) SL(2, F) W}

theorem exists_mem_orderOf_mul_eq_three {A A' : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    (hA'2 : ∀ a ∈ A', a * a = 1) (hA' : Nat.card A' = Fintype.card F) (hne : A ≠ A')
    {x : SL(2, F)} (hx : x ∈ A) (hx1 : x ≠ 1) : ∃ y ∈ A', orderOf (x * y) = 3 := by
  have hAeq : Nat.card A = Nat.card F := by rw [hA, Nat.card_eq_fintype_card]
  have hA'eq : Nat.card A' = Nat.card F := by rw [hA', Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := eq_conj_rootGroup A hA2 hAeq
  obtain ⟨b, hb⟩ := eq_conj_rootGroup A' hA'2 hA'eq
  have hAc : A = conjSubgroup a (utri F) := by
    rw [← upperSylow_eq_utri]
    exact eq_map_conj_upperSylow_of_forall_mem_iff ha
  have hA'c : A' = conjSubgroup b (utri F) := by
    rw [← upperSylow_eq_utri]
    exact eq_map_conj_upperSylow_of_forall_mem_iff hb
  have hneconj : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
    intro h
    exact hne (by rw [hAc, hA'c, h])
  obtain ⟨g, hga, hgb⟩ := exists_conj_utri_ltri_of_ne hneconj
  have hxg : g⁻¹ * x * g ∈ utri F := by
    have hxA : x ∈ conjSubgroup a (utri F) := hAc ▸ hx
    rw [hga] at hxA
    exact mem_conjSubgroup.mp hxA
  obtain ⟨s, hs⟩ := mem_utri_iff.mp hxg
  have hs0 : s ≠ 0 := by
    intro h0
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * utriElt s * g⁻¹ := by rw [hs]
      _ = 1 := by rw [h0, utriElt_zero]; group
  refine ⟨g * ltriElt s⁻¹ * g⁻¹, ?_, ?_⟩
  · rw [hA'c, hgb]
    exact conj_mem_conjSubgroup g (ltriElt_mem_ltri s⁻¹)
  · have hxy : x * (g * ltriElt s⁻¹ * g⁻¹) =
        g * (utriElt s * ltriElt s⁻¹) * g⁻¹ := by
      calc x * (g * ltriElt s⁻¹ * g⁻¹)
          = g * (g⁻¹ * x * g) * ltriElt s⁻¹ * g⁻¹ := by group
        _ = g * (utriElt s * ltriElt s⁻¹) * g⁻¹ := by rw [hs]; group
    rw [hxy]
    have hconj : orderOf (g * (utriElt s * ltriElt s⁻¹) * g⁻¹) =
        orderOf (utriElt s * ltriElt s⁻¹) := by
      simpa [MulAut.conj_apply, mul_assoc] using
        (MulEquiv.orderOf_eq (MulAut.conj g) (utriElt s * ltriElt s⁻¹))
    rw [hconj]
    exact orderOf_utriElt_mul_ltriElt (mul_inv_cancel₀ hs0)

theorem IsOrthModule.fixedSub_zpowers_eq_commSub (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    {x : SL(2, F)} (hx : x ∈ A) (hx1 : x ≠ 1) :
    fixedSub ρ (Subgroup.zpowers x) = commSub ρ (Subgroup.zpowers x) ∧
      fixedSub ρ (Subgroup.zpowers x) ≤ commSub ρ A := by
  have hx2 : x * x = 1 := hA2 x hx
  have hl : 1 ≤ l := one_le_of_card hF
  have hWcard : Nat.card W = 2 ^ (4 * l) := by
    obtain ⟨j, β, -⟩ := horth
    rw [Nat.card_congr β.toEquiv]
    exact card_hermA (s := l) hl hF
  have hcardfix : Nat.card ↥(fixedSub ρ (Subgroup.zpowers x)) = 2 ^ (2 * l) :=
    IsOrthModule.card_fixedSub_zpowers hF horth A hA2 hA hx hx1
  have heq : Nat.card W = Nat.card ↥(fixedSub ρ (Subgroup.zpowers x)) ^ 2 := by
    rw [hWcard, hcardfix, ← pow_mul]
    congr 1
    ring
  have hcomm : commSub ρ (Subgroup.zpowers x) = fixedSub ρ (Subgroup.zpowers x) :=
    (natCard_eq_natCard_fixedSub_zpowers_sq_iff ρ hx2).mp heq
  refine ⟨hcomm.symm, ?_⟩
  rw [← hcomm]
  change (⨆ a ∈ Subgroup.zpowers x, LinearMap.range (ρ a - 1)) ≤
    (⨆ a ∈ A, LinearMap.range (ρ a - 1))
  exact iSup₂_le fun a ha =>
    le_iSup₂ (f := fun a (_ : a ∈ A) => LinearMap.range (ρ a - 1)) a
      (Subgroup.zpowers_le.mpr hx ha)

private theorem fixedSub_zpowers_uMat_eq_hermPlane (t : F) (ht : t ≠ 0) :
    fixedSub (hermRep l hF) (Subgroup.zpowers (uMat t)) = hermPlane l t := by
  ext X
  rw [mem_fixedSub_zpowers_uMat_iff_K0 (hF := hF) t ht, mem_hermPlane_iff]
  constructor
  · rintro ⟨h11, c, hc, h01⟩
    exact ⟨h11, c, hc, by rw [h01, mul_comm]⟩
  · rintro ⟨h11, c, hc, h01⟩
    exact ⟨h11, c, hc, by rw [h01, mul_comm]⟩

private theorem m3_setup (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    {x : SL(2, F)} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ (j : ℕ) (β : W ≃+ ↥(hermA l F)) (B : Subgroup SL(2, F)) (c : SL(2, F)) (t : F),
      (∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w)) ∧
        B = A.map (fieldAut F j) ∧
        fieldAut F j x = c * uMat t * c⁻¹ ∧
        B = upperSylow.map (MulAut.conj c).toMonoidHom ∧ t ≠ 0 := by
  obtain ⟨j, β, hβ⟩ := horth
  let B : Subgroup SL(2, F) := A.map (fieldAut F j)
  let xB : SL(2, F) := fieldAut F j x
  have hs := fieldAut_image_sylow A hA2 hA j
  have hB2 : ∀ a ∈ B, a * a = 1 := hs.1
  have hB : Nat.card B = 2 ^ (2 * l) := hs.2
  have hAeq : Nat.card B = Nat.card F := by
    rw [hB, Nat.card_eq_fintype_card, hF]
  obtain ⟨c, hc⟩ := eq_conj_rootGroup B hB2 hAeq
  have hEq : B = upperSylow.map (MulAut.conj c).toMonoidHom :=
    eq_map_conj_upperSylow_of_forall_mem_iff hc
  have hxB_mem : xB ∈ B := Subgroup.mem_map_of_mem _ hx
  have hxB1 : xB ≠ 1 := by
    intro h
    apply hx1
    have h' : (fieldAutEquiv (F := F) j) x = (fieldAutEquiv (F := F) j) 1 := by
      simpa [xB, fieldAutEquiv_apply] using h
    exact (fieldAutEquiv (F := F) j).injective h'
  have hxB' : c⁻¹ * xB * c ∈ upperSylow := by
    have h := hxB_mem
    rw [hEq, CFSG.Timmesfeld.RankOne.mem_map_conj] at h
    exact h
  obtain ⟨t, ht_eq⟩ := mem_upperSylow_iff.mp hxB'
  have hxB_eq : xB = c * uMat t * c⁻¹ := by
    calc xB = c * (c⁻¹ * xB * c) * c⁻¹ := by group
      _ = c * uMat t * c⁻¹ := by rw [ht_eq]
  have ht : t ≠ 0 := by
    intro h0
    apply hxB1
    rw [hxB_eq, h0, uMat_zero]
    group
  exact ⟨j, β, B, c, t, hβ, rfl, hxB_eq, hEq, ht⟩

private theorem m3_fixator_subgroup (hF : Fintype.card F = 2 ^ (2 * l))
    {A : Subgroup SL(2, F)} {j : ℕ} {B : Subgroup SL(2, F)} {c : SL(2, F)} {t : F}
    (hB : B = A.map (fieldAut F j)) (hEq : B = upperSylow.map (MulAut.conj c).toMonoidHom)
    (ht : t ≠ 0) :
    ∃ C : Subgroup SL(2, F), C ≤ A ∧ Nat.card C = 2 ^ l ∧
      (∀ a ∈ A, a ∈ C ↔ c⁻¹ * fieldAut F j a * c ∈ hermPlaneFix l hF t) ∧
      (∀ a ∈ A, c⁻¹ * fieldAut F j a * c ∈ upperSylow) := by
  let C0 : Subgroup SL(2, F) := (hermPlaneFix l hF t).map (MulAut.conj c).toMonoidHom
  let C : Subgroup SL(2, F) := C0.map ((fieldAutEquiv j).symm).toMonoidHom
  have hC0_le_B : C0 ≤ B := by
    rw [hEq]
    exact Subgroup.map_mono (hermPlaneFix_le_upperSylow (hF := hF) t)
  have hC_le_A : C ≤ A := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
    have hbB : b ∈ B := hC0_le_B hb
    rw [hB] at hbB
    obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.mp hbB
    have hae' : (fieldAutEquiv j).symm b = a' := by
      rw [← hae]
      exact (fieldAutEquiv j).symm_apply_apply a'
    have haeq : a = a' := by
      calc a = (fieldAutEquiv j).symm b := hba.symm
        _ = a' := hae'
    rw [haeq]
    exact ha'
  have hcardC0 : Nat.card C0 = 2 ^ l := by
    change Nat.card ↥((hermPlaneFix l hF t).map (MulAut.conj c).toMonoidHom) = 2 ^ l
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      card_hermPlaneFix (hF := hF) ht]
  have hcardC : Nat.card C = 2 ^ l := by
    change Nat.card ↥(C0.map ((fieldAutEquiv j).symm).toMonoidHom) = 2 ^ l
    rw [Subgroup.card_map_of_injective (fieldAutEquiv j).symm.injective, hcardC0]
  have hC_mem : ∀ a : SL(2, F), a ∈ A →
      (a ∈ C ↔ c⁻¹ * fieldAut F j a * c ∈ hermPlaneFix l hF t) := by
    intro a haA
    constructor
    · intro haC
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haC
      have hb_eq : b = fieldAut F j a := by
        rw [← hba]
        exact ((fieldAutEquiv j).apply_symm_apply b).symm
      rw [hb_eq] at hb
      exact CFSG.Timmesfeld.RankOne.mem_map_conj.mp hb
    · intro hs
      have hbC0 : fieldAut F j a ∈ C0 := CFSG.Timmesfeld.RankOne.mem_map_conj.mpr hs
      exact Subgroup.mem_map.mpr ⟨fieldAut F j a, hbC0,
        (fieldAutEquiv j).symm_apply_apply a⟩
  have hAs : ∀ a : SL(2, F), a ∈ A → c⁻¹ * fieldAut F j a * c ∈ upperSylow := by
    intro a haA
    have hsB : fieldAut F j a ∈ B := by
      rw [hB]
      exact Subgroup.mem_map_of_mem _ haA
    have hsS : fieldAut F j a ∈ upperSylow.map (MulAut.conj c).toMonoidHom := by
      rwa [← hEq]
    exact CFSG.Timmesfeld.RankOne.mem_map_conj.mp hsS
  exact ⟨C, hC_le_A, hcardC, hC_mem, hAs⟩

private theorem m3_vector {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    {A B : Subgroup SL(2, F)} {c : SL(2, F)} {t : F} {x : SL(2, F)}
    (hB : B = A.map (fieldAut F j)) (hEq : B = upperSylow.map (MulAut.conj c).toMonoidHom)
    (hxB_eq : fieldAut F j x = c * uMat t * c⁻¹) (ht : t ≠ 0) {w : W}
    (hw : w ∈ fixedSub ρ (Subgroup.zpowers x)) (hwNot : w ∉ fixedSub ρ A) :
    ∃ p : ↥(hermA l F), p ∈ hermPlane l t ∧
      p ∉ fixedSub (hermRep l hF) upperSylow ∧
        hermRep l hF c p = β w ∧ p = hermRep l hF c⁻¹ (β w) := by
  let xB : SL(2, F) := fieldAut F j x
  have hmapzp : (Subgroup.zpowers x).map (fieldAut F j) = Subgroup.zpowers xB :=
    MonoidHom.map_zpowers (fieldAut F j) x
  have hβw_fix : β w ∈ fixedSub (hermRep l hF) (Subgroup.zpowers xB) := by
    have h := (fixedSub_fieldAut_mem (hF := hF) hβ (Subgroup.zpowers x) w).mp hw
    rwa [hmapzp] at h
  have hfixB : fixedSub (hermRep l hF) (Subgroup.zpowers xB) =
      (hermPlane l t).map (hermRep l hF c) := by
    have hconj := fixedSub_zpowers_conj (hermRep l hF) c (uMat t)
    rw [show xB = fieldAut F j x from rfl, hxB_eq, hconj,
      fixedSub_zpowers_uMat_eq_hermPlane (hF := hF) t ht]
  have hbw : β w ∈ (hermPlane l t).map (hermRep l hF c) := by rwa [← hfixB]
  obtain ⟨p, hp, hp_eq⟩ := Submodule.mem_map.mp hbw
  have hp_def : p = hermRep l hF c⁻¹ (β w) := by
    have h := congrArg (hermRep l hF c⁻¹) hp_eq
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
    exact h
  have hβw_not : β w ∉ fixedSub (hermRep l hF) B := by
    intro h
    exact hwNot ((fixedSub_fieldAut_mem (hF := hF) hβ A w).mpr (by rwa [hB] at h))
  have hfixB_S : fixedSub (hermRep l hF) B =
      (fixedSub (hermRep l hF) upperSylow).map (hermRep l hF c) := by
    rw [hEq, fixedSub_map_conj]
  have hp_not : p ∉ fixedSub (hermRep l hF) upperSylow := by
    intro hpS
    apply hβw_not
    rw [hfixB_S]
    exact ⟨p, hpS, hp_eq⟩
  exact ⟨p, hp, hp_not, hp_eq, hp_def⟩

private theorem m3_action_iff {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    {A : Subgroup SL(2, F)} {C : Subgroup SL(2, F)} {c : SL(2, F)} {t : F}
    {p : ↥(hermA l F)} {w : W} (hp : p ∈ hermPlane l t)
    (hp_not : p ∉ fixedSub (hermRep l hF) upperSylow)
    (hp_eq : hermRep l hF c p = β w) (hp_def : p = hermRep l hF c⁻¹ (β w))
    {a : SL(2, F)}
    (hC : a ∈ C ↔ c⁻¹ * fieldAut F j a * c ∈ hermPlaneFix l hF t)
    (hAs : c⁻¹ * fieldAut F j a * c ∈ upperSylow) :
    ρ a w = w ↔ a ∈ C := by
  have hfixator := fixator_hermPlane_eq (hF := hF) hp hp_not
  have hfix_iff : hermRep l hF (c⁻¹ * fieldAut F j a * c) p = p ↔
      c⁻¹ * fieldAut F j a * c ∈ hermPlaneFix l hF t := by
    have h := Set.ext_iff.mp hfixator (c⁻¹ * fieldAut F j a * c)
    constructor
    · intro hp'
      exact h.mp ⟨hAs, hp'⟩
    · intro hfix
      exact (h.mpr hfix).2
  have hiff : ρ a w = w ↔ hermRep l hF (c⁻¹ * fieldAut F j a * c) p = p := by
    have hβa : β (ρ a w) = hermRep l hF (fieldAut F j a) (β w) := by
      simpa [hermRep_apply] using hβ a w
    constructor
    · intro h
      have hβh : hermRep l hF (fieldAut F j a) (β w) = β w := by rw [← hβa, h]
      calc hermRep l hF (c⁻¹ * fieldAut F j a * c) p
          = hermRep l hF c⁻¹ (hermRep l hF (fieldAut F j a)
              (hermRep l hF c p)) := by
              simp only [map_mul, Module.End.mul_apply]
        _ = hermRep l hF c⁻¹ (hermRep l hF (fieldAut F j a) (β w)) := by rw [hp_eq]
        _ = hermRep l hF c⁻¹ (β w) := by rw [hβh]
        _ = p := hp_def.symm
    · intro h
      have h2 : hermRep l hF c (hermRep l hF (c⁻¹ * fieldAut F j a * c) p) =
          hermRep l hF c p := by rw [h]
      have h3 : hermRep l hF (c * (c⁻¹ * fieldAut F j a * c)) p =
          hermRep l hF c p := by
        simpa [map_mul, Module.End.mul_apply] using h2
      have hmul : c * (c⁻¹ * fieldAut F j a * c) = fieldAut F j a * c := by group
      have h4 : hermRep l hF (fieldAut F j a * c) p = hermRep l hF c p := by
        rwa [hmul] at h3
      have h5 : hermRep l hF (fieldAut F j a) (hermRep l hF c p) =
          hermRep l hF c p := by
        simpa [map_mul, Module.End.mul_apply] using h4
      have h6 : hermRep l hF (fieldAut F j a) (β w) = β w := by
        rwa [hp_eq] at h5
      apply β.injective
      rw [hβa]
      exact h6
  rw [hiff, hfix_iff]
  exact hC.symm

theorem IsOrthModule.exists_fixator_fixedSub_zpowers (horth : IsOrthModule hF ρ)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    {x : SL(2, F)} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ C : Subgroup SL(2, F), C ≤ A ∧ Nat.card C = 2 ^ l ∧
      ∀ w ∈ fixedSub ρ (Subgroup.zpowers x), w ∉ fixedSub ρ A →
        ∀ a ∈ A, (ρ a w = w ↔ a ∈ C) := by
  obtain ⟨j, β, B, c, t, hβ, hB, hxB_eq, hEq, ht⟩ :=
    m3_setup (hF := hF) horth A hA2 hA hx hx1
  obtain ⟨C, hC_le_A, hcardC, hC_mem, hAs⟩ :=
    m3_fixator_subgroup (hF := hF) hB hEq ht
  refine ⟨C, hC_le_A, hcardC, ?_⟩
  intro w hw hwNot a ha
  obtain ⟨p, hp, hp_not, hp_eq, hp_def⟩ :=
    m3_vector (hF := hF) hβ hB hEq hxB_eq ht hw hwNot
  exact m3_action_iff (hF := hF) (A := A) (a := a) hβ hp hp_not hp_eq hp_def
    (hC_mem a ha) (hAs a ha)

private theorem tMat_mem_torus (c : F) (hc : c ≠ 0) : tMat c hc ∈ torus F := by
  rw [mem_torus_entries]
  simp [tMat_coe]

private theorem exists_frobFix_ne_zero_one (hF : Fintype.card F = 2 ^ (2 * l)) (hl : 2 ≤ l) :
    ∃ b : ↥(frobFixField l F), b ≠ 0 ∧ b ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset ↥(frobFixField l F)) ⊆ {0, 1} := by
    intro b _
    by_cases hb0 : b = 0
    · exact Finset.mem_insert.mpr (Or.inl hb0)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [Finset.mem_singleton]
      exact h b hb0
  have hle : Nat.card ↥(frobFixField l F) ≤ 2 := by
    have h1 : (Finset.univ : Finset ↥(frobFixField l F)).card ≤ 2 := by
      calc (Finset.univ : Finset ↥(frobFixField l F)).card ≤ ({0, 1} : Finset _).card :=
            Finset.card_le_card hsub
        _ = 2 := by simp
    simpa [Nat.card_eq_fintype_card] using h1
  have hcard : Nat.card ↥(frobFixField l F) = 2 ^ l := card_frobFixField (hF := hF)
  have hge : 4 ≤ 2 ^ l := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  omega

private theorem torus_fixed_apply_01_eq_zero (hl : 2 ≤ l) {X : ↥(hermA l F)}
    (hX : X ∈ fixedSub (hermRep l hF) (torus F)) :
    (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  rw [mem_fixedSub] at hX
  obtain ⟨c, hc⟩ := exists_sig_ne (F := F) hF (lt_of_lt_of_le (by norm_num : 0 < 2) hl)
  have hc0 : c ≠ 0 := by
    intro h
    apply hc
    rw [h]
    simp [sig_apply]
  have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 1)
    (hX (tMat c hc0) (tMat_mem_torus c hc0))
  rw [hermRep_apply, hermAct_tMat_01, sig_apply, inv_pow] at h
  have ht1 : c * (c ^ 2 ^ l)⁻¹ ≠ 1 := by
    intro h1
    apply hc
    have h2 : (c ^ 2 ^ l)⁻¹ = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : c ^ 2 ^ l = c := inv_inj.mp h2
    simpa [sig_apply] using h3
  have h' : (c * (c ^ 2 ^ l)⁻¹ - 1) * (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ht1)

private theorem torus_fixed_apply_00_11_eq_zero (hl : 2 ≤ l) {X : ↥(hermA l F)}
    (hX : X ∈ fixedSub (hermRep l hF) (torus F)) :
    (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  rw [mem_fixedSub] at hX
  obtain ⟨b, hb0, hb1⟩ := exists_frobFix_ne_zero_one (F := F) (l := l) (hF := hF) hl
  obtain ⟨e, he0, he⟩ := exists_mul_sig_eq (hF := hF) b.2
    (fun h0 => hb0 (Subtype.ext h0))
  have he_ne : e * e ^ 2 ^ l ≠ 1 := by
    rw [he]
    exact fun h1 => hb1 (Subtype.ext h1)
  constructor
  · have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hX (tMat e he0) (tMat_mem_torus e he0))
    rw [hermRep_apply, hermAct_tMat_00, sig_apply] at h
    have h' : (e * e ^ 2 ^ l - 1) * (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr he_ne)
  · have h := congrArg (fun Y : ↥(hermA l F) => (Y : Matrix (Fin 2) (Fin 2) F) 1 1)
      (hX (tMat e he0) (tMat_mem_torus e he0))
    rw [hermRep_apply, hermAct_tMat_11, sig_apply, inv_pow] at h
    have heinv : (e * e ^ 2 ^ l)⁻¹ ≠ 1 := by
      intro h1
      exact he_ne (inv_eq_one.mp h1)
    have h' : ((e * e ^ 2 ^ l)⁻¹ - 1) * (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have hcoeff : e⁻¹ * (e ^ 2 ^ l)⁻¹ = (e * e ^ 2 ^ l)⁻¹ := by rw [mul_inv]
      rw [hcoeff] at h
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr heinv)

private theorem fixedSub_torus_eq_bot (hl : 2 ≤ l) :
    fixedSub (hermRep l hF) (torus F) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro X hX
  obtain ⟨h00, h11⟩ := torus_fixed_apply_00_11_eq_zero (hF := hF) hl hX
  have h01 := torus_fixed_apply_01_eq_zero (hF := hF) hl hX
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h01, h11, hermA_10 (a := l) X, sig_apply]

private theorem map_conj_eq_of_subgroupOf_map_conj {G D : Subgroup SL(2, F)} {n : G}
    (hDleG : D ≤ G) (htorusG : torus F ≤ G)
    (hn : D.subgroupOf G = ((torus F).subgroupOf G).map (MulAut.conj n).toMonoidHom) :
    D = (torus F).map (MulAut.conj ((n : G) : SL(2, F))).toMonoidHom := by
  calc D = (D.subgroupOf G).map G.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hDleG).symm
    _ = (((torus F).subgroupOf G).map (MulAut.conj n).toMonoidHom).map G.subtype := by
        rw [hn]
    _ = (torus F).map (MulAut.conj ((n : G) : SL(2, F))).toMonoidHom :=
        CFSG.map_subgroupOf_map_conj_eq htorusG n

private theorem exists_conj_eq_torus_of_le_normalizer
    (hF : Fintype.card F = 2 ^ (2 * l)) (hl : 2 ≤ l)
    {D : Subgroup SL(2, F)}
    (hDle : D ≤ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))))
    (hDcard : Nat.card D = 2 ^ (2 * l) - 1) :
    ∃ g : SL(2, F), D = (torus F).map (MulAut.conj g).toMonoidHom := by
  classical
  let S : Subgroup SL(2, F) := upperSylow (F := F)
  let G : Subgroup SL(2, F) := Subgroup.normalizer (S : Set (SL(2, F)))
  let H : Subgroup G := S.subgroupOf G
  let Kt : Subgroup G := (torus F).subgroupOf G
  let Kd : Subgroup G := D.subgroupOf G
  have hSG : S ≤ G := Subgroup.le_normalizer
  have hDleG : D ≤ G := hDle
  have htorusG : torus F ≤ G := by
    change torus F ≤ Subgroup.normalizer (S : Set (SL(2, F)))
    rw [show S = utri F from upperSylow_eq_utri, normalizer_utri]
    exact torus_le_borel
  have hS_card : Nat.card H = 2 ^ (2 * l) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv]
    change Nat.card ↥(upperSylow (F := F)) = 2 ^ (2 * l)
    rw [upperSylow_eq_utri, card_utri, Nat.card_eq_fintype_card, hF]
  have hKt_card : Nat.card Kt = 2 ^ (2 * l) - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe htorusG).toEquiv, card_torus,
      Nat.card_eq_fintype_card, hF]
  have hKd_card : Nat.card Kd = 2 ^ (2 * l) - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleG).toEquiv, hDcard]
  have hG_card : Nat.card G = 2 ^ (2 * l) * (2 ^ (2 * l) - 1) := by
    change Nat.card ↥(Subgroup.normalizer (S : Set (SL(2, F)))) =
      2 ^ (2 * l) * (2 ^ (2 * l) - 1)
    rw [show Subgroup.normalizer (S : Set (SL(2, F))) = borel F from by
      rw [show S = utri F from upperSylow_eq_utri, normalizer_utri],
      card_borel, Nat.card_eq_fintype_card, hF]
  have hl0 : 2 * l ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hl))
  have hcop2 : Nat.Coprime (2 ^ (2 * l)) (2 ^ (2 * l) - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd (Nat.one_le_two_pow)
        (Nat.even_pow.mpr ⟨even_two, hl0⟩) odd_one))
  have hcompT : H.IsComplement' Kt := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hS_card, hKt_card, hG_card]
    · rw [hS_card, hKt_card]
      exact hcop2
  have hcompD : H.IsComplement' Kd := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hS_card, hKd_card, hG_card]
    · rw [hS_card, hKd_card]
      exact hcop2
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    change ∀ a ∈ upperSylow (F := F), ∀ b ∈ upperSylow (F := F), a * b = b * a
    rw [upperSylow_eq_utri]
    intro a ha b hb
    obtain ⟨s, rfl⟩ := mem_utri_iff.mp ha
    obtain ⟨t, rfl⟩ := mem_utri_iff.mp hb
    rw [← utriElt_add, ← utriElt_add, add_comm]
  have hHcomm : IsMulCommutative H :=
    IsMulCommutative.of_comm fun x y =>
      Subtype.ext (Subtype.ext (hScomm (x : G) x.2 (y : G) y.2))
  have hcopH : Nat.Coprime (Nat.card H) H.index := by
    rw [hcompT.symm.index_eq_card, hS_card, hKt_card]
    exact hcop2
  obtain ⟨n, hn⟩ := Subgroup.exists_conj_eq_of_isComplement' (H := H)
    (K₁ := Kt) (K₂ := Kd) hcopH hcompT hcompD
  exact ⟨((n : G) : SL(2, F)), map_conj_eq_of_subgroupOf_map_conj hDleG htorusG hn⟩

private theorem fixedSub_eq_bot_of_map_conj_inv {D : Subgroup SL(2, F)} {c : SL(2, F)}
    (h : fixedSub (hermRep l hF) (D.map (MulAut.conj c⁻¹).toMonoidHom) = ⊥) :
    fixedSub (hermRep l hF) D = ⊥ := by
  have hD_eq : D = (D.map (MulAut.conj c⁻¹).toMonoidHom).map
      (MulAut.conj c).toMonoidHom := by
    change D = (D.map (MulAut.conj c⁻¹).toMonoidHom).map
      (MulAut.conj c).toMonoidHom
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj c).toMonoidHom.comp
        (MulAut.conj c⁻¹).toMonoidHom = MonoidHom.id (SL(2, F)) := by
      apply MonoidHom.ext
      intro x
      change (MulAut.conj c) ((MulAut.conj c⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  rw [hD_eq, fixedSub_map_conj, h, Submodule.map_bot]

private theorem fixedSub_eq_bot_of_map_fieldAut {j : ℕ} {β : W ≃+ ↥(hermA l F)}
    (hβ : ∀ g w, β (ρ g w) = hermAct l (sig_sig hF) (fieldAut F j g) (β w))
    {T : Subgroup SL(2, F)} (h : fixedSub (hermRep l hF) (T.map (fieldAut F j)) = ⊥) :
    fixedSub ρ T = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hβw : β w ∈ fixedSub (hermRep l hF) (T.map (fieldAut F j)) :=
    (fixedSub_fieldAut_mem (hF := hF) hβ T w).mp hw
  rw [h] at hβw
  simpa using hβw

theorem IsOrthModule.fixedSub_eq_bot_of_torus (horth : IsOrthModule hF ρ)
    (hl : 2 ≤ l) {A T : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = 2 ^ (2 * l))
    (hTA : T ≤ Subgroup.normalizer (A : Set (SL(2, F))))
    (hT : Nat.card T = 2 ^ (2 * l) - 1) : fixedSub ρ T = ⊥ := by
  classical
  obtain ⟨j, β, hβ⟩ := horth
  let B : Subgroup SL(2, F) := A.map (fieldAut F j)
  let D : Subgroup SL(2, F) := T.map (fieldAut F j)
  have hs := fieldAut_image_sylow A hA2 hA j
  have hB2 : ∀ a ∈ B, a * a = 1 := hs.1
  have hB : Nat.card B = 2 ^ (2 * l) := hs.2
  have hDcard : Nat.card D = 2 ^ (2 * l) - 1 := by
    change Nat.card ↥(T.map (fieldAut F j)) = 2 ^ (2 * l) - 1
    rw [Subgroup.card_map_of_injective (fieldAutEquiv j).injective, hT]
  have hBeq : Nat.card B = Nat.card F := by
    rw [hB, Nat.card_eq_fintype_card, hF]
  obtain ⟨c, hc⟩ := eq_conj_rootGroup B hB2 hBeq
  have hEq : B = upperSylow.map (MulAut.conj c).toMonoidHom :=
    eq_map_conj_upperSylow_of_forall_mem_iff hc
  have hDleB : D ≤ Subgroup.normalizer (B : Set (SL(2, F))) := by
    have hmapN : (Subgroup.normalizer (A : Set (SL(2, F)))).map (fieldAut F j) =
        Subgroup.normalizer (B : Set (SL(2, F))) := by
      simpa [B] using
        Subgroup.map_normalizer_eq_of_bijective A
          (f := fieldAut F j) (fieldAut_bijective j)
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hd
    rw [← hmapN]
    exact Subgroup.mem_map_of_mem _ (hTA ht)
  let Dc : Subgroup SL(2, F) := D.map (MulAut.conj c⁻¹).toMonoidHom
  have hDc_card : Nat.card Dc = 2 ^ (2 * l) - 1 := by
    change Nat.card ↥(D.map (MulAut.conj c⁻¹).toMonoidHom) = 2 ^ (2 * l) - 1
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hDcard]
  have hDc_le : Dc ≤ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) := by
    have hNB : Subgroup.normalizer (B : Set (SL(2, F))) =
        (Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F)))).map
          (MulAut.conj c).toMonoidHom := by
      rw [hEq]
      exact (Subgroup.map_normalizer_eq_of_bijective (upperSylow (F := F))
        (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).bijective).symm
    calc Dc = D.map (MulAut.conj c⁻¹).toMonoidHom := rfl
      _ ≤ (Subgroup.normalizer (B : Set (SL(2, F)))).map
            (MulAut.conj c⁻¹).toMonoidHom := Subgroup.map_mono hDleB
      _ = Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) := by
          rw [hNB, Subgroup.map_map]
          have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp
              (MulAut.conj c).toMonoidHom = MonoidHom.id (SL(2, F)) := by
            apply MonoidHom.ext
            intro x
            change (MulAut.conj c⁻¹) ((MulAut.conj c) x) = x
            rw [MulAut.conj_apply, MulAut.conj_apply]
            group
          rw [hcomp, Subgroup.map_id]
  obtain ⟨g, hDc_eq⟩ := exists_conj_eq_torus_of_le_normalizer (hF := hF) hl hDc_le hDc_card
  have hDc_bot : fixedSub (hermRep l hF) Dc = ⊥ := by
    rw [hDc_eq, fixedSub_map_conj, fixedSub_torus_eq_bot hl, Submodule.map_bot]
  have hD_bot : fixedSub (hermRep l hF) D = ⊥ :=
    fixedSub_eq_bot_of_map_conj_inv hDc_bot
  exact fixedSub_eq_bot_of_map_fieldAut hβ hD_bot

private theorem hermAct_wMat_hermDiag (a : F) (ha : a ^ 2 ^ l = a) :
    hermAct l (sig_sig hF) wMat (hermDiag l hF a ha) =
      hermDiag11 l hF a ha := by
  apply Subtype.ext
  rw [hermAct_wMat l hF, hermDiag_coe (hF := hF), hermDiag11_coe (hF := hF)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem isPGroup_upperSylow : IsPGroup 2 ↥(upperSylow (F := F)) := by
  rw [upperSylow_eq_utri]
  exact isPGroup_utri

private theorem hermDiag_eq_zero {a : F} (ha : a ^ 2 ^ l = a) (ha0 : a = 0) :
    hermDiag l hF a ha = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag_coe (hF := hF), ha0]

private theorem hermDiag_one_mem_of_invariant (U : Submodule (ZMod 2) ↥(hermA l F))
    (hU : ∀ g, ∀ u ∈ U, (hermRep l hF) g u ∈ U) (hbot : U ≠ ⊥) :
    hermDiag l hF 1 (by simp) ∈ U := by
  have hUinv : ∀ g : ↥(upperSylow (F := F)), ∀ u ∈ U,
      ((hermRep l hF).comp (upperSylow (F := F)).subtype) g u ∈ U := by
    intro g u hu
    exact hU g.1 u hu
  obtain ⟨w, hwU, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup
    (k := ZMod 2) (p := 2) (G := ↥(upperSylow (F := F))) (V := ↥(hermA l F))
    Nat.prime_two isPGroup_upperSylow
    ((hermRep l hF).comp (upperSylow (F := F)).subtype) U hUinv hbot
  have hwS : w ∈ fixedSub (hermRep l hF) upperSylow := by
    rw [mem_fixedSub]
    intro g hg
    exact hwfix ⟨g, hg⟩
  rw [fixedSub_upperSylow] at hwS
  obtain ⟨h11, h01⟩ := hwS
  have hw_eq : w = hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) w) := eq_hermDiag_of_mem_herm1101 (hF := hF) w ⟨h11, h01⟩
  have ha0 : (w : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    apply hw0
    rw [hw_eq]
    exact hermDiag_eq_zero (hF := hF) (hermA_00 (a := l) w) h0
  have hainv : ((w : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ ^ 2 ^ l =
      ((w : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ := by
    have hfix : ((w : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l =
        (w : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      simpa [sig_apply] using hermA_00 (a := l) w
    rw [inv_pow, hfix]
  obtain ⟨c, hc0, hc⟩ := exists_mul_sig_eq (hF := hF) hainv (inv_ne_zero ha0)
  let D0 : ↥(hermA l F) := hermDiag l hF 1 (by simp)
  have hscale : hermAct l (sig_sig hF) (tMat c hc0) w = D0 := by
    have hstep : hermAct l (sig_sig hF) (tMat c hc0) w =
        hermAct l (sig_sig hF) (tMat c hc0)
          (hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
            (hermA_00 (a := l) w)) :=
      congrArg (fun z => hermAct l (sig_sig hF) (tMat c hc0) z) hw_eq
    rw [hstep, hermAct_tMat_hermDiag (hF := hF) c hc0 _
      (hermA_00 (a := l) w)]
    apply Subtype.ext
    rw [hermDiag_coe (hF := hF), hermDiag_coe (hF := hF)]
    have hprod : c * c ^ 2 ^ l * (w : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      rw [hc, inv_mul_cancel₀ ha0]
    rw [hprod]
  have hD0 : D0 ∈ U := by
    have h := hU (tMat c hc0) w hwU
    change hermAct l (sig_sig hF) (tMat c hc0) w ∈ U at h
    rwa [hscale] at h
  simpa [D0] using hD0

private theorem hermDiag_mem_of_one_mem (U : Submodule (ZMod 2) ↥(hermA l F))
    (hU : ∀ g, ∀ u ∈ U, (hermRep l hF) g u ∈ U)
    (hD0 : hermDiag l hF 1 (by simp) ∈ U) :
    ∀ a : F, ∀ ha : a ^ 2 ^ l = a, hermDiag l hF a ha ∈ U := by
  intro a ha
  by_cases ha0 : a = 0
  · rw [hermDiag_eq_zero (hF := hF) ha ha0]
    exact U.zero_mem
  · obtain ⟨d, hd0, hd⟩ := exists_mul_sig_eq (hF := hF) ha ha0
    have hscale : hermAct l (sig_sig hF) (tMat d hd0)
        (hermDiag l hF 1 (by simp)) = hermDiag l hF a ha := by
      calc hermAct l (sig_sig hF) (tMat d hd0) (hermDiag l hF 1 (by simp))
          = hermDiag l hF (d * d ^ 2 ^ l * 1)
              (mul_sig_mul_fix (hF := hF) d 1 (by simp)) :=
            hermAct_tMat_hermDiag (hF := hF) d hd0 1 (by simp)
        _ = hermDiag l hF a ha := by
            apply Subtype.ext
            rw [hermDiag_coe (hF := hF), hermDiag_coe (hF := hF), hd, mul_one]
    have h := hU (tMat d hd0) _ hD0
    change hermAct l (sig_sig hF) (tMat d hd0) (hermDiag l hF 1 (by simp)) ∈ U at h
    rwa [hscale] at h

private theorem hermE11_mem_of_one_mem (U : Submodule (ZMod 2) ↥(hermA l F))
    (hU : ∀ g, ∀ u ∈ U, (hermRep l hF) g u ∈ U)
    (hD0 : hermDiag l hF 1 (by simp) ∈ U) : hermE11 l hF ∈ U := by
  have h := hU wMat _ hD0
  change hermAct l (sig_sig hF) wMat (hermDiag l hF 1 (by simp)) ∈ U at h
  have hD1eq : hermE11 l hF = hermAct l (sig_sig hF) wMat (hermDiag l hF 1 (by simp)) := by
    rw [hermAct_wMat_hermDiag (hF := hF) 1 (by simp)]
    rfl
  rwa [hD1eq]

private theorem hermRep_invariant_top_of_diag (U : Submodule (ZMod 2) ↥(hermA l F))
    (hU : ∀ g, ∀ u ∈ U, (hermRep l hF) g u ∈ U)
    (hdiag : ∀ a : F, ∀ ha : a ^ 2 ^ l = a, hermDiag l hF a ha ∈ U) : U = ⊤ := by
  have hD1 : hermE11 l hF ∈ U :=
    hermE11_mem_of_one_mem U hU (hdiag 1 (by simp))
  have hdiag11 : ∀ a : F, ∀ ha : a ^ 2 ^ l = a, hermDiag11 l hF a ha ∈ U := by
    intro a ha
    have h := hU wMat (hermDiag l hF a ha) (hdiag a ha)
    change hermAct l (sig_sig hF) wMat (hermDiag l hF a ha) ∈ U at h
    have hEq : hermAct l (sig_sig hF) wMat (hermDiag l hF a ha) =
        hermDiag11 l hF a ha := hermAct_wMat_hermDiag (hF := hF) a ha
    rwa [hEq] at h
  have hoff : ∀ b : F, hermOff l hF b ∈ U := by
    intro b
    have hv : hermV l hF b ∈ U := by
      have h := hU (uMat b) (hermE11 l hF) hD1
      change hermAct l (sig_sig hF) (uMat b) (hermE11 l hF) ∈ U at h
      have hEq : hermV l hF b = hermAct l (sig_sig hF) (uMat b) (hermE11 l hF) -
          hermE11 l hF := rfl
      rw [hEq]
      exact U.sub_mem h hD1
    have hsplit := hermV_eq_diag_add_offdiag (hF := hF) b
    have hsum : hermDiag l hF (b * b ^ 2 ^ l) (mul_pow_fix (hF := hF) b) +
        hermOff l hF b ∈ U := by simpa [hsplit] using hv
    have hd : hermDiag l hF (b * b ^ 2 ^ l) (mul_pow_fix (hF := hF) b) ∈ U :=
      hdiag _ _
    have hO : hermOff l hF b = (hermDiag l hF (b * b ^ 2 ^ l)
        (mul_pow_fix (hF := hF) b) + hermOff l hF b) -
          hermDiag l hF (b * b ^ 2 ^ l) (mul_pow_fix (hF := hF) b) := by abel
    rw [hO]
    exact U.sub_mem hsum hd
  rw [eq_top_iff]
  intro X _
  rw [eq_hermDiag_add_diag_add_offdiag (hF := hF) X]
  exact U.add_mem (U.add_mem (hdiag _ _) (hdiag11 _ _)) (hoff _)

private theorem hermRep_isIrreducible : (hermRep l hF).IsIrreducible := by
  have hl : 1 ≤ l := one_le_of_card hF
  refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (hermRep l hF)).mpr
    ⟨?_, ?_⟩
  · rw [← Finite.one_lt_card_iff_nontrivial]
    rw [card_hermA (s := l) hl hF]
    have h2 : 2 ≤ 2 ^ (4 * l) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro U hU
    by_cases hbot : U = ⊥
    · exact Or.inl hbot
    right
    have hD0 : hermDiag l hF 1 (by simp) ∈ U :=
      hermDiag_one_mem_of_invariant U hU hbot
    exact hermRep_invariant_top_of_diag U hU (hermDiag_mem_of_one_mem U hU hD0)

theorem IsOrthModule.isIrreducible (horth : IsOrthModule hF ρ) : ρ.IsIrreducible := by
  refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mpr ⟨?_, ?_⟩
  · have hl : 1 ≤ l := one_le_of_card hF
    obtain ⟨j, β, -⟩ := horth
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr β.toEquiv,
      card_hermA (s := l) hl hF]
    have h2 : 2 ≤ 2 ^ (4 * l) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro U hU
    obtain ⟨j, β, hβ⟩ := horth
    let f : W →ₗ[ZMod 2] ↥(hermA l F) := β.toAddMonoidHom.toZModLinearMap 2
    have hf_inj : Function.Injective f := fun u v h => β.injective (by simpa [f] using h)
    let U' : Submodule (ZMod 2) ↥(hermA l F) := U.map f
    have hU' : ∀ g, ∀ u ∈ U', (hermRep l hF) g u ∈ U' := by
      intro g u hu
      obtain ⟨v, hv, rfl⟩ := hu
      have hmem : β (ρ ((fieldAutEquiv j).symm g) v) ∈ U' :=
        Submodule.mem_map_of_mem (f := f) (hU _ v hv)
      have hfield : fieldAut F j ((fieldAutEquiv j).symm g) = g := by
        rw [← fieldAutEquiv_apply]
        exact (fieldAutEquiv j).apply_symm_apply g
      rw [hβ, hfield] at hmem
      exact hmem
    have hcases := (hermRep_isIrreducible (hF := hF)).eq_bot_or_eq_top
      (⟨U', hU'⟩ : Subrepresentation (hermRep l hF))
    rcases hcases with h | h
    · left
      have hU'bot : U' = ⊥ := congrArg Subrepresentation.toSubmodule h
      rw [Submodule.eq_bot_iff]
      intro u hu
      have hfu : f u ∈ U' := Submodule.mem_map_of_mem (f := f) hu
      rw [hU'bot] at hfu
      exact hf_inj (by simpa using hfu)
    · right
      have hU'top : U' = ⊤ := congrArg Subrepresentation.toSubmodule h
      rw [eq_top_iff]
      intro w _
      have hfw : f w ∈ U' := by rw [hU'top]; exact Submodule.mem_top
      obtain ⟨u, hu, hfu⟩ := Submodule.mem_map.mp hfw
      have huw : u = w := hf_inj hfu
      rwa [← huw]

theorem IsOrthModule.eq_of_commute_of_iterate (horth : IsOrthModule hF ρ)
    (φ : W →+ W) (hφ : ∀ g w, φ (ρ g w) = ρ g (φ w)) {k : ℕ}
    (hk : ∀ w, φ^[2 ^ k] w = w) : ∀ w, φ w = w := by
  classical
  haveI : Fact ρ.IsIrreducible := ⟨IsOrthModule.isIrreducible horth⟩
  let φₗ : W →ₗ[ZMod 2] W := φ.toZModLinearMap 2
  have hφcomm : ∀ g v, φₗ (ρ g v) = ρ g (φₗ v) := hφ
  obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ φₗ).mpr hφcomm
  have hψfun : (ψ : W → W) = φ := by rw [hψ]; rfl
  have hψpow : ψ ^ (2 ^ k) = 1 := by
    ext w
    rw [Module.End.pow_apply, Module.End.one_apply]
    have hiter : ψ^[2 ^ k] w = φ^[2 ^ k] w := by rw [hψfun]
    rw [hiter, hk w]
  have hψ1 : ψ = 1 := by
    have h2 : (2 : EndRing ρ) = 0 := by
      change ((2 : ℕ) : EndRing ρ) = 0
      ext w
      rw [Module.End.natCast_apply, LinearMap.zero_apply]
      exact CFSG.QuasithinUnique.Setup.X7.p_nsmul_eq_zero_of_charP (ZMod 2) w
    haveI : CharP (EndRing ρ) 2 :=
      CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have hiter : iterateFrobenius (EndRing ρ) 2 k ψ =
        iterateFrobenius (EndRing ρ) 2 k 1 := by
      rw [iterateFrobenius_def, iterateFrobenius_def, one_pow, hψpow]
    exact iterateFrobenius_inj (EndRing ρ) 2 k hiter
  intro w
  have hw : ψ w = w := by rw [hψ1, Module.End.one_apply]
  simpa [hψfun] using hw

private theorem linearMap_map_commSub_eq {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) SL(2, F) N) (a : SL(2, F))
    (f : N →ₗ[ZMod 2] W) (hf : ∀ g n, f (σ g n) = ρ g (f n))
    (hsurj : Function.Surjective f) :
    Submodule.map f (commSub σ (Subgroup.zpowers a)) = commSub ρ (Subgroup.zpowers a) := by
  have hmap_le : Submodule.map f (commSub σ (Subgroup.zpowers a)) ≤
      commSub ρ (Subgroup.zpowers a) := by
    refine Submodule.map_le_iff_le_comap.mpr ?_
    intro x hx
    refine commSub_induction σ (Subgroup.zpowers a)
      (P := fun x => f x ∈ commSub ρ (Subgroup.zpowers a)) ?_ ?_ ?_ hx
    · intro g hg n
      have heq : f ((σ g - 1) n) = (ρ g - 1) (f n) := by
        rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hf]
        rfl
      rw [heq]
      exact range_le_commSub hg ⟨f n, rfl⟩
    · simp
    · intro x y hx hy
      rw [map_add]
      exact (commSub ρ (Subgroup.zpowers a)).add_mem hx hy
  have hmap_ge : commSub ρ (Subgroup.zpowers a) ≤
      Submodule.map f (commSub σ (Subgroup.zpowers a)) := by
    intro y hy
    refine commSub_induction ρ (Subgroup.zpowers a)
      (P := fun y => y ∈ Submodule.map f (commSub σ (Subgroup.zpowers a))) ?_ ?_ ?_ hy
    · intro g hg w
      obtain ⟨n, rfl⟩ := hsurj w
      refine ⟨(σ g - 1) n, range_le_commSub hg ⟨n, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hf]
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  exact le_antisymm hmap_le hmap_ge

theorem IsOrthModule.linearMap_eq_zero (horth : IsOrthModule hF ρ)
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) SL(2, F) N)
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ (2 * l))
    {a : SL(2, F)} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hN : commSub σ (Subgroup.zpowers a) ≤ fixedSub σ A)
    (f : N →ₗ[ZMod 2] W) (hf : ∀ g n, f (σ g n) = ρ g (f n)) : f = 0 := by
  have hl : 1 ≤ l := one_le_of_card hF
  by_contra hf0
  haveI : ρ.IsIrreducible := IsOrthModule.isIrreducible horth
  let fmap : Representation.IntertwiningMap σ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap σ ρ f hf
  have hsurjF : Function.Surjective fmap := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero fmap with h | h0
    · exact h
    · exfalso
      apply hf0
      calc f = (fmap : N →ₗ[ZMod 2] W) := rfl
        _ = 0 := by rw [h0]; rfl
  have hsurj : Function.Surjective f := by
    have hfun : (fmap : N → W) = f := by
      ext n
      rfl
    rwa [hfun] at hsurjF
  have hmap : Submodule.map f (commSub σ (Subgroup.zpowers a)) =
      commSub ρ (Subgroup.zpowers a) :=
    linearMap_map_commSub_eq σ a f hf hsurj
  have hle : commSub ρ (Subgroup.zpowers a) ≤ fixedSub ρ A := by
    rw [← hmap]
    refine (Submodule.map_mono hN).trans ?_
    rintro _ ⟨n, hn, rfl⟩
    simp only [mem_fixedSub] at hn ⊢
    intro g hg
    rw [← hf]
    exact congrArg f (hn g hg)
  have hcomm_card : Nat.card ↥(commSub ρ (Subgroup.zpowers a)) = 2 ^ (2 * l) := by
    have hm2 := IsOrthModule.fixedSub_zpowers_eq_commSub (hF := hF) horth A hA2 hA ha ha1
    have hcard := IsOrthModule.card_fixedSub_zpowers hF horth A hA2 hA ha ha1
    rwa [hm2.1] at hcard
  have hfix_card : Nat.card ↥(fixedSub ρ A) = 2 ^ l :=
    IsOrthModule.card_fixedSub (hF := hF) horth A hA2 hA
  have hcardle : Nat.card ↥(commSub ρ (Subgroup.zpowers a)) ≤
      Nat.card ↥(fixedSub ρ A) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective _)
  rw [hcomm_card, hfix_card] at hcardle
  have hlt : 2 ^ (2 * l) ≤ 2 ^ l := hcardle
  have hle' : 2 * l ≤ l := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

end CFSG.RankThree.GF2n.Tim81.Sec2

end
