module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtRoots

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {H : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem exists_isOrthOn_of_splitSupport (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (horth : IsOrthType p (movedGroup H)) :
    ∃ Q : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ IsOrthOn p Q H := by
  have hlt : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by omega
  obtain ⟨f, hfC, hf0⟩ := hs.exists_mem_centralizerSpace_ne_zero hlt
  obtain ⟨Q, hQ, hQH, -⟩ :=
    exists_isOrthOn_of_isOrthType_movedGroup hp hs horth hfC hf0 (c := 1) one_ne_zero
  exact ⟨Q, hQ, hQH⟩

private theorem exists_root_reflect_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQH : IsOrthOn p Q H) (hh : h ∈ H) (hh' : IsRefl p h) :
    ∃ e : U, e ∈ HardMathSupport.Kantor79.commutatorSpace H ∧ Q e ≠ 0 ∧ e ≠ 0 ∧
      h = CFSG.ClassicalGroups.Orthogonal.reflect Q e ∧ h e = -e := by
  obtain ⟨e, hQe, hee⟩ :=
    CFSG.StandardType.ZS.DimThree.exists_root_of_isRefl_isIsom hp hQ hh' (hQH.isIsom hh)
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcls : CFSG.ClassicalGroups.Orthogonal.reflect Q e ∈ ClassRefl p Q (Q e) :=
    (mem_classRefl_iff hp hQ hQe (CFSG.ClassicalGroups.Orthogonal.reflect Q e)).mpr
      ⟨e, rfl, rfl⟩
  have hself : CFSG.ClassicalGroups.Orthogonal.reflect Q e e = -e :=
    reflect_apply_self hQe
  have hh_eq : h = CFSG.ClassicalGroups.Orthogonal.reflect Q e :=
    CFSG.StandardType.ZS.DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hh'
      (hQH.isIsom hh) hcls.1 hcls.2.1 he0 hee hself
  exact ⟨e, HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hee), hQe, he0, hh_eq,
    by rw [hh_eq]; exact hself⟩

private theorem movedSpace_le_ker_iff (W : Submodule (ZMod p) U) (g : U ≃ₗ[ZMod p] U) :
    HardMathSupport.Kantor79.movedSpace g ≤ W ↔ ∀ v, g v - v ∈ W := by
  constructor
  · intro hg v
    exact hg ⟨v, rfl⟩
  · rintro hg w ⟨v, rfl⟩
    exact hg v

private theorem isOrthOn_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {m : ℕ} {X : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport X m) (hm : 3 ≤ m)
    (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X)
    (hh : h ∈ X) (hh' : IsRefl p h) :
    IsOrthOn p Q (reflStab p X h) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)
  let E := V ⊓ W
  have hVE : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = E :=
    commutatorSpace_reflStab hp hQ hs hm hm3 ho hh hh'
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => ho.isIsom hg
  rcases ho with hfull | ⟨c, hc, hclass⟩
  · left
    rw [hVE, reflStab, reflSubgroupIn]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨hgX, hgr, hgW⟩
      exact Subgroup.subset_closure ⟨hgr, hXiso g hgX,
        le_inf (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgX)
          ((movedSpace_le_ker_iff W g).mpr hgW)⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro t ⟨htr, htiso, htE⟩
      have htX : t ∈ X :=
        hfull.symm.le (Subgroup.subset_closure ⟨htr, htiso, htE.trans inf_le_left⟩)
      exact Subgroup.subset_closure
        ⟨htX, htr, (movedSpace_le_ker_iff W t).mp (htE.trans inf_le_right)⟩
  · right
    refine ⟨c, hc, ?_⟩
    rw [hVE, reflStab, reflSubgroupIn]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨hgX, hgr, hgW⟩
      have hgX' : g ∈ Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤
            HardMathSupport.Kantor79.commutatorSpace X} := hclass.le hgX
      have hgcl : g ∈ Subgroup.closure (ClassRefl p Q c) :=
        Subgroup.closure_mono (fun _ hs => hs.1) hgX'
      exact Subgroup.subset_closure
        ⟨mem_classRefl_of_isRefl_mem_closure hp hQ hc hgcl hgr,
          le_inf (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgX)
            ((movedSpace_le_ker_iff W g).mpr hgW)⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro t ⟨htc, htE⟩
      have htX : t ∈ X :=
        hclass.symm.le (Subgroup.subset_closure ⟨htc, htE.trans inf_le_left⟩)
      exact Subgroup.subset_closure ⟨htX, htc.1,
        (movedSpace_le_ker_iff W t).mp (htE.trans inf_le_right)⟩

private theorem le_centralizerSpace_closure {S : Set (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} (hS : ∀ s ∈ S, ∀ w ∈ W, s w = w) :
    W ≤ centralizerSpace (Subgroup.closure S) := by
  intro w hw g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact hS t ht w hw
  | one => rfl
  | mul a b _ _ iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
  | inv a _ iha =>
      calc a⁻¹ w = a⁻¹ (a w) := by rw [iha]
        _ = w := a.symm_apply_apply w

private theorem orthogonal_le_centralizerSpace_reflStab (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQH : IsOrthOn p Q H) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ≤
      centralizerSpace (reflStab p H h) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)
  let E := V ⊓ W
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hgen : ∀ s ∈ {g : U ≃ₗ[ZMod p] U | g ∈ H ∧ IsRefl p g ∧ ∀ v, g v - v ∈ W},
      ∀ x ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) E, s x = x := by
    rintro s ⟨hsH, hsr, hsW⟩ x hx
    obtain ⟨a, hQa, hsa⟩ :=
      CFSG.StandardType.ZS.DimThree.exists_root_of_isRefl_isIsom hp hQ hsr (hQH.isIsom hsH)
    have ha0 : a ≠ 0 := fun h0 => hQa (by rw [h0]; exact map_zero Q)
    have hcls : CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ ClassRefl p Q (Q a) :=
      (mem_classRefl_iff hp hQ hQa _).mpr ⟨a, rfl, rfl⟩
    have hself : CFSG.ClassicalGroups.Orthogonal.reflect Q a a = -a :=
      reflect_apply_self hQa
    have hseq : s = CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
      CFSG.StandardType.ZS.DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hsr
        (hQH.isIsom hsH) hcls.1 hcls.2.1 ha0 hsa hself
    have haV : a ∈ V := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hsH
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hsa)
    have haW : a ∈ W := by
      obtain ⟨v, hv⟩ := HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hsa
      rw [← hv]
      exact hsW v
    have hpol : QuadraticMap.polar Q a x = 0 := by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) a ⟨haV, haW⟩
      simpa [QuadraticMap.polarBilin_apply_apply] using this
    rw [hseq]
    exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hpol
  have hle : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) E ≤
      centralizerSpace (reflStab p H h) := by
    have := le_centralizerSpace_closure
      (S := {g : U ≃ₗ[ZMod p] U | g ∈ H ∧ IsRefl p g ∧ ∀ v, g v - v ∈ W})
      (W := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) E) hgen
    simpa only [reflStab, reflSubgroupIn] using this
  exact hle

private theorem centralizerSpace_reflStab_le_orthogonal {Q : QuadraticForm (ZMod p) U}
    (hVE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hXiso : ∀ g ∈ reflStab p H h, IsIsom p Q g) :
    centralizerSpace (reflStab p H h) ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (HardMathSupport.Kantor79.commutatorSpace H ⊓
          LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  have hxV : x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [hVE]; exact hx
  have hpol : QuadraticMap.polar Q x v = 0 := by
    rw [QuadraticMap.polar_comm]
    exact polar_eq_zero_of_mem_centralizerSpace (X := reflStab p H h) hXiso hv hxV
  simpa [QuadraticMap.polarBilin_apply_apply] using hpol

private theorem centralizerSpace_reflStab_eq_orthogonal (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQH : IsOrthOn p Q H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hm : 3 ≤ Module.finrank (ZMod p) U - 1)
    (hm3 : p = 3 → 4 ≤ Module.finrank (ZMod p) U - 1)
    (hh : h ∈ H) (hh' : IsRefl p h) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) =
      centralizerSpace (reflStab p H h) := by
  let W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)
  have hVE : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓ W :=
    commutatorSpace_reflStab hp hQ hs hm hm3 hQH hh hh'
  have hXiso : ∀ g ∈ reflStab p H h, IsIsom p Q g := fun g hg =>
    hQH.isIsom (reflSubgroupIn_le H W (by simpa only [reflStab] using hg))
  exact le_antisymm (orthogonal_le_centralizerSpace_reflStab hp hQ hQH)
    (centralizerSpace_reflStab_le_orthogonal hVE hXiso)

private theorem isCompl_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQH : IsOrthOn p Q H) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hm : 3 ≤ Module.finrank (ZMod p) U - 1)
    (hm3 : p = 3 → 4 ≤ Module.finrank (ZMod p) U - 1)
    (hh : h ∈ H) (hh' : IsRefl p h) :
    IsCompl (HardMathSupport.Kantor79.commutatorSpace H ⊓
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
      (centralizerSpace (reflStab p H h)) := by
  obtain ⟨e, heV, hQe, he0, hh_eq, -⟩ := exists_root_reflect_of_isOrthOn hp hQ hQH hh hh'
  have hpol := polarNondegOn_commutatorSpace_reflStab hp hQ hQH hs heV hQe hh_eq
  let E := HardMathSupport.Kantor79.commutatorSpace H ⊓
    LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := fun x y hxy => by
    rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rwa [QuadraticMap.polar_comm]
  have hB : LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) E =
      QuadraticMap.polarBilin (Q.restrict E) := by
    ext x y
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    exact (ClassicalGroups.Orthogonal.polar_restrict (Q := Q) (W := E) x y).symm
  have hrestrict : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) E).Nondegenerate := by
    rw [hB]
    exact ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hpol
  have hcompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hrestrict
  rwa [centralizerSpace_reflStab_eq_orthogonal hp hQ hQH hs hm hm3 hh hh'] at hcompl

theorem isOrthType_movedGroup_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (horth : IsOrthType p (movedGroup H))
    (hh : h ∈ H) (hh' : IsRefl p h) : IsOrthType p (movedGroup (reflStab p H h)) := by
  obtain ⟨Q, hQ, hQH⟩ := exists_isOrthOn_of_splitSupport hp h4 hs horth
  obtain ⟨e, heV, hQe, he0, hh_eq, -⟩ := exists_root_reflect_of_isOrthOn hp hQ hQH hh hh'
  have hm : 3 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hm3 : p = 3 → 4 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hQstab := isOrthOn_reflStab hp hQ hs hm hm3 hQH hh hh'
  have hVE := commutatorSpace_reflStab hp hQ hs hm hm3 hQH hh hh'
  have hpol := polarNondegOn_commutatorSpace_reflStab hp hQ hQH hs heV hQe hh_eq
  have hnd : (QuadraticMap.polarBilin (Q.comp
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)).subtype)).Nondegenerate := by
    rw [hVE]
    exact ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hpol
  exact isOrthType_movedGroup_of_isOrthOn hp hQ hQstab hnd

theorem splitSupport_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (horth : IsOrthType p (movedGroup H))
    (hh : h ∈ H) (hh' : IsRefl p h)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h))) :
    SplitSupport (reflStab p H h) (Module.finrank (ZMod p) U - 2) := by
  obtain ⟨Q, hQ, hQH⟩ := exists_isOrthOn_of_splitSupport hp h4 hs horth
  obtain ⟨e, heV, hQe, he0, hh_eq, hhe⟩ := exists_root_reflect_of_isOrthOn hp hQ hQH hh hh'
  have hm : 3 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hm3 : p = 3 → 4 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hVE := commutatorSpace_reflStab hp hQ hs hm hm3 hQH hh hh'
  have hcompl := isCompl_reflStab hp hQ hQH hs hm hm3 hh hh'
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hne : e ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro hmem
    have heq : h e = e := by simpa [LinearMap.mem_ker, sub_eq_zero] using hmem
    have heneg : e = -e := by rw [← hhe, heq]
    exact he0 (eq_zero_of_eq_neg h2 heneg)
  have hfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) =
      Module.finrank (ZMod p) U - 2 := by
    have hfr := IsRefl.finrank_inf_ker_sub_one_add_one hp hh'
      (A := HardMathSupport.Kantor79.commutatorSpace H) heV hne
    have hV := hs.2.1
    omega
  refine ⟨?_, ?_, hirr₁⟩
  · rw [hVE]; exact hcompl
  · rw [hVE]; exact hfin

end CFSG.StandardType.ZS

end
