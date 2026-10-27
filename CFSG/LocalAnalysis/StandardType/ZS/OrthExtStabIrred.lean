module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtRoots

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

variable {H : Subgroup (U ≃ₗ[ZMod p] U)} {E : Submodule (ZMod p) U} {P : U → Prop}
variable [Module.Finite (ZMod p) U]
variable {W : Submodule (ZMod p) U} {m : ℕ} {c : ZMod p}

private def rootSpace (X : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) :
    Submodule (ZMod p) U :=
  HardMathSupport.Kantor79.commutatorSpace X ⊓
    LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)

private def anisoSet (Q : QuadraticForm (ZMod p) U) (E : Submodule (ZMod p) U) : U → Prop :=
  fun a => a ∈ E ∧ Q a ≠ 0

private def normSet (Q : QuadraticForm (ZMod p) U) (E : Submodule (ZMod p) U)
    (c : ZMod p) : U → Prop :=
  fun a => a ∈ E ∧ Q a = c

private def decompW₁ (P : U → Prop) (W : Submodule (ZMod p) U) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) {a : U | P a ∧ a ∈ W}

private def decompW₂ (P : U → Prop) (W : Submodule (ZMod p) U) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) {a : U | P a ∧ a ∉ W}

private structure DecompCtx (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (Q : QuadraticForm (ZMod p) U)
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (E : Submodule (ZMod p) U) (P : U → Prop) where
  hp : p ≠ 2
  h2 : (2 : ZMod p) ≠ 0
  hQ : (QuadraticMap.polarBilin Q).Nondegenerate
  hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q E
  hHrefl : ReflGen p H
  hVH : HardMathSupport.Kantor79.commutatorSpace H = E
  hPE : ∀ a, P a → a ∈ E
  hQne : ∀ a, P a → Q a ≠ 0
  hroot : ∀ a, P a → ClassicalGroups.Orthogonal.reflect Q a ∈ H
  hgen : ∀ g ∈ H, IsRefl p g → ∃ a, P a ∧ g = ClassicalGroups.Orthogonal.reflect Q a

omit [Module.Finite (ZMod p) U] in
private theorem mem_reflStab_of_mem_aniso (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {a : U} (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (haK : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) (haQ : Q a ≠ 0) :
    ClassicalGroups.Orthogonal.reflect Q a ∈ reflStab p X h := by
  refine mem_reflSubgroupIn_of_movedSpace_le ?_ (isRefl_reflect hp haQ) ?_
  · rw [hfull]
    refine Subgroup.subset_closure ⟨isRefl_reflect hp haQ, isIsom_reflect Q a, ?_⟩
    rw [movedSpace_reflect_eq_span hp haQ]
    exact (Submodule.span_singleton_le_iff_mem a _).mpr haV
  · rw [movedSpace_reflect_eq_span hp haQ]
    exact (Submodule.span_singleton_le_iff_mem a _).mpr haK

omit [Module.Finite (ZMod p) U] in
private theorem mem_reflStab_of_mem_norm (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U} {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    {a : U} (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (haK : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) (haQ : Q a = c) :
    ClassicalGroups.Orthogonal.reflect Q a ∈ reflStab p X h := by
  have hQa : Q a ≠ 0 := by rw [haQ]; exact hc
  refine mem_reflSubgroupIn_of_movedSpace_le ?_ (isRefl_reflect hp hQa) ?_
  · rw [hclass]
    refine Subgroup.subset_closure
      ⟨(mem_classRefl_iff hp hQ hc (ClassicalGroups.Orthogonal.reflect Q a)).mpr
        ⟨a, haQ, rfl⟩, ?_⟩
    rw [movedSpace_reflect_eq_span hp hQa]
    exact (Submodule.span_singleton_le_iff_mem a _).mpr haV
  · rw [movedSpace_reflect_eq_span hp hQa]
    exact (Submodule.span_singleton_le_iff_mem a _).mpr haK

omit [Module.Finite (ZMod p) U] in
private theorem exists_root_mem_reflStab_full (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hXiso : ∀ g ∈ X, IsIsom p Q g)
    (hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h)
    {g : U ≃ₗ[ZMod p] U} (hgH : g ∈ reflStab p X h) (hgr : IsRefl p g) :
    ∃ a, a ∈ rootSpace X h ∧ Q a ≠ 0 ∧ g = ClassicalGroups.Orthogonal.reflect Q a := by
  have hgX : g ∈ X := reflSubgroupIn_le X _ hgH
  obtain ⟨a, haQ, hga⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ hgr (hXiso g hgX)
  have haM : a ∈ HardMathSupport.Kantor79.movedSpace g :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hga
  have haE : a ∈ rootSpace X h := by
    have h := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgH haM
    rwa [hVH] at h
  have ha0 : a ≠ 0 := fun h0 => haQ (by rw [h0]; exact map_zero Q)
  refine ⟨a, haE, haQ, ?_⟩
  exact DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hgr (hXiso g hgX)
    (isRefl_reflect hp haQ) (isIsom_reflect Q a) ha0 hga (reflect_apply_self haQ)

omit [Module.Finite (ZMod p) U] in
private theorem exists_root_mem_reflStab_class (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U} {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h)
    {g : U ≃ₗ[ZMod p] U} (hgH : g ∈ reflStab p X h) (hgr : IsRefl p g) :
    ∃ a, a ∈ rootSpace X h ∧ Q a = c ∧ g = ClassicalGroups.Orthogonal.reflect Q a := by
  have hgX : g ∈ X := reflSubgroupIn_le X _ hgH
  have hgclass : g ∈ ClassRefl p Q c := by
    rw [hclass] at hgX
    exact mem_classRefl_of_isRefl_mem_closure hp hQ hc
      (Subgroup.closure_mono (fun t ht => ht.1) hgX) hgr
  obtain ⟨a, haQ, hga⟩ := (mem_classRefl_iff hp hQ hc g).mp hgclass
  have haQ0 : Q a ≠ 0 := by rw [haQ]; exact hc
  have haM : a ∈ HardMathSupport.Kantor79.movedSpace g := by
    rw [hga]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
      (ZMod.prime_ne_zero p 2 hp) (reflect_apply_self haQ0)
  have haE : a ∈ rootSpace X h := by
    have h := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgH haM
    rwa [hVH] at h
  exact ⟨a, haE, haQ, hga⟩

omit [Module.Finite (ZMod p) U] in
private theorem decompCtx_of_full (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hXiso : ∀ g ∈ X, IsIsom p Q g)
    (hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h)
    (hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q (rootSpace X h))
    (h2 : (2 : ZMod p) ≠ 0) :
    DecompCtx p Q (reflStab p X h) (rootSpace X h) (anisoSet Q (rootSpace X h)) := by
  refine ⟨hp, h2, hQ, hEnd, reflGen_reflSubgroupIn X _, hVH, ?_, ?_, ?_, ?_⟩
  · rintro a ⟨haE, -⟩; exact haE
  · rintro a ⟨-, haQ⟩; exact haQ
  · rintro a ⟨haE, haQ⟩
    exact mem_reflStab_of_mem_aniso hp hQ hfull haE.1 haE.2 haQ
  · intro g hg hgr
    obtain ⟨a, haE, haQ, hga⟩ := exists_root_mem_reflStab_full hp hQ hXiso hVH hg hgr
    exact ⟨a, ⟨haE, haQ⟩, hga⟩

omit [Module.Finite (ZMod p) U] in
private theorem decompCtx_of_class (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U} {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h)
    (hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q (rootSpace X h))
    (h2 : (2 : ZMod p) ≠ 0) :
    DecompCtx p Q (reflStab p X h) (rootSpace X h) (normSet Q (rootSpace X h) c) := by
  refine ⟨hp, h2, hQ, hEnd, reflGen_reflSubgroupIn X _, hVH, ?_, ?_, ?_, ?_⟩
  · rintro a ⟨haE, -⟩; exact haE
  · rintro a ⟨-, haQ⟩; rw [haQ]; exact hc
  · rintro a ⟨haE, haQ⟩
    exact mem_reflStab_of_mem_norm hp hQ hc hclass haE.1 haE.2 haQ
  · intro g hg hgr
    obtain ⟨a, haE, haQ, hga⟩ := exists_root_mem_reflStab_class hp hQ hc hclass hVH hg hgr
    exact ⟨a, ⟨haE, haQ⟩, hga⟩

private theorem mem_or_polar_eq_zero (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W)
    {a : U} (ha : P a) :
    a ∈ W ∨ ∀ w ∈ W, QuadraticMap.polar Q a w = 0 := by
  by_cases haW : a ∈ W
  · exact Or.inl haW
  · right
    have hQa : Q a ≠ 0 := C.hQne a ha
    have hspan : HardMathSupport.Kantor79.movedSpace
        (ClassicalGroups.Orthogonal.reflect Q a) = Submodule.span (ZMod p) {a} :=
      movedSpace_reflect_eq_span C.hp hQa
    have hnotle : ¬ HardMathSupport.Kantor79.movedSpace
        (ClassicalGroups.Orthogonal.reflect Q a) ≤ W := by
      rw [hspan]
      exact fun hle => haW ((Submodule.span_singleton_le_iff_mem a W).mp hle)
    have hfix : ∀ w ∈ W, ClassicalGroups.Orthogonal.reflect Q a w = w :=
      fun w hw => apply_eq_self_of_not_movedSpace_le
        (isRefl_reflect C.hp hQa).2 (fun w hw => hWinv _ (C.hroot a ha) w hw)
        hnotle hw
    intro w hw
    have h := hfix w hw
    rw [ClassicalGroups.Orthogonal.reflect_apply hQa] at h
    have h5 : -((QuadraticMap.polar Q a w / Q a) • a) = 0 := by
      have h' : w - (QuadraticMap.polar Q a w / Q a) • a - w = 0 := by rw [h, sub_self]
      rwa [show w - (QuadraticMap.polar Q a w / Q a) • a - w =
        -((QuadraticMap.polar Q a w / Q a) • a) by abel] at h'
    have h3 : (QuadraticMap.polar Q a w / Q a) • a = 0 := neg_eq_zero.mp h5
    have ha0 : a ≠ 0 := fun h0 => hQa (by rw [h0]; exact map_zero Q)
    have hc : QuadraticMap.polar Q a w / Q a = 0 :=
      (smul_eq_zero.mp h3).resolve_right ha0
    rcases (div_eq_zero_iff.mp hc) with h | h
    · exact h
    · exact absurd h hQa

private theorem le_sup_decomp (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) :
    E ≤ decompW₁ P W ⊔ decompW₂ P W := by
  rw [← C.hVH, commutatorSpace_eq_iSup_of_reflGen C.hHrefl]
  refine iSup_le fun g => iSup_le fun hg => ?_
  obtain ⟨a, haP, rfl⟩ := C.hgen g hg.1 hg.2
  have haQ : Q a ≠ 0 := C.hQne a haP
  rw [movedSpace_reflect_eq_span C.hp haQ]
  rcases mem_or_polar_eq_zero C hWinv haP with haW | haorth
  · exact (Submodule.span_singleton_le_iff_mem a _).mpr
      (Submodule.mem_sup_left (Submodule.subset_span ⟨haP, haW⟩))
  · have haW : a ∉ W := by
      intro haW
      have h := haorth a haW
      rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at h
      exact haQ ((mul_eq_zero.mp h).resolve_left C.h2)
    exact (Submodule.span_singleton_le_iff_mem a _).mpr
      (Submodule.mem_sup_right (Submodule.subset_span ⟨haP, haW⟩))

private theorem decompW₂_orthogonal (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) :
    ∀ b ∈ decompW₂ P W, ∀ w ∈ W, QuadraticMap.polar Q b w = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact (mem_or_polar_eq_zero C hWinv hx.1).resolve_left hx.2
  | zero => intro w hw; rw [QuadraticMap.polar_zero_left]
  | add x y hx hy ihx ihy =>
      intro w hw; rw [QuadraticMap.polar_add_left, ihx w hw, ihy w hw, add_zero]
  | smul c x hx ih =>
      intro w hw
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, ih w hw, mul_zero]

private theorem decomp_orth (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) :
    ∀ a ∈ decompW₁ P W, ∀ b ∈ decompW₂ P W, QuadraticMap.polar Q a b = 0 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
      intro b hb
      rw [QuadraticMap.polar_comm]
      exact decompW₂_orthogonal C hWinv b hb x hx.2
  | zero => intro b hb; rw [QuadraticMap.polar_zero_left]
  | add x y hx hy ihx ihy =>
      intro b hb; rw [QuadraticMap.polar_add_left, ihx b hb, ihy b hb, add_zero]
  | smul c x hx ih =>
      intro b hb
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, ih b hb, mul_zero]

omit [Module.Finite (ZMod p) U] in
private theorem decompW₁_le (W : Submodule (ZMod p) U) :
    decompW₁ P W ≤ W := by
  rw [decompW₁, Submodule.span_le]
  rintro a ⟨-, haW⟩
  exact haW

omit [Module.Finite (ZMod p) U] in
private theorem decompW₁_le_E (C : DecompCtx p Q H E P) (W : Submodule (ZMod p) U) :
    decompW₁ P W ≤ E := by
  rw [decompW₁, Submodule.span_le]
  rintro a ⟨haP, -⟩
  exact C.hPE a haP

omit [Module.Finite (ZMod p) U] in
private theorem decompW₂_le_E (C : DecompCtx p Q H E P) (W : Submodule (ZMod p) U) :
    decompW₂ P W ≤ E := by
  rw [decompW₂, Submodule.span_le]
  rintro a ⟨haP, -⟩
  exact C.hPE a haP

private theorem inf_W_decompW₂_eq_bot (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hE : E = decompW₁ P W ⊔ decompW₂ P W)
    (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) :
    W ⊓ decompW₂ P W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  apply C.hEnd z (decompW₂_le_E C W hz.2)
  intro y hy
  have hy' : y ∈ decompW₁ P W ⊔ decompW₂ P W := hE ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
  rw [QuadraticMap.polar_add_right,
    decompW₂_orthogonal C hWinv z hz.2 a (decompW₁_le W ha),
    (QuadraticMap.polar_comm Q z b).trans
      (decompW₂_orthogonal C hWinv b hb z hz.1), add_zero]

omit [Module.Finite (ZMod p) U] in
private theorem eq_decompW₁ {W : Submodule (ZMod p) U}
    (hE : E = decompW₁ P W ⊔ decompW₂ P W) (hWE : W ≤ E)
    (hinf : W ⊓ decompW₂ P W = ⊥) :
    W = decompW₁ P W := by
  refine le_antisymm ?_ (decompW₁_le W)
  intro w hw
  have hw' : w ∈ decompW₁ P W ⊔ decompW₂ P W := hE ▸ hWE hw
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw'
  have hbW : b ∈ W := by
    have : b = w - a := by rw [← hab]; abel
    rw [this]
    exact W.sub_mem hw (decompW₁_le W ha)
  have hb0 : b = 0 := by
    have hb' : b ∈ W ⊓ decompW₂ P W := ⟨hbW, hb⟩
    rw [hinf] at hb'
    simpa using hb'
  rw [← hab, hb0, add_zero]
  exact ha

omit [Module.Finite (ZMod p) U] in
private theorem inf_decomp_eq_bot (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hE : E = decompW₁ P W ⊔ decompW₂ P W)
    (horth : ∀ a ∈ decompW₁ P W, ∀ b ∈ decompW₂ P W, QuadraticMap.polar Q a b = 0) :
    decompW₁ P W ⊓ decompW₂ P W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  apply C.hEnd z (decompW₁_le_E C W hz.1)
  intro y hy
  have hy' : y ∈ decompW₁ P W ⊔ decompW₂ P W := hE ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
  rw [QuadraticMap.polar_add_right,
    (QuadraticMap.polar_comm Q z a).trans (horth a ha z hz.2),
    horth z hz.1 b hb, add_zero]

omit [Module.Finite (ZMod p) U] in
private theorem polarNondegOn_decompW₁ (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hE : E = decompW₁ P W ⊔ decompW₂ P W)
    (horth : ∀ a ∈ decompW₁ P W, ∀ b ∈ decompW₂ P W, QuadraticMap.polar Q a b = 0) :
    ClassicalGroups.Orthogonal.PolarNondegOn Q (decompW₁ P W) := by
  intro x hx hxorth
  apply C.hEnd x (decompW₁_le_E C W hx)
  intro y hy
  have hy' : y ∈ decompW₁ P W ⊔ decompW₂ P W := hE ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
  rw [QuadraticMap.polar_add_right, hxorth a ha, horth x hx b hb, add_zero]

omit [Module.Finite (ZMod p) U] in
private theorem polarNondegOn_decompW₂ (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hE : E = decompW₁ P W ⊔ decompW₂ P W)
    (horth : ∀ a ∈ decompW₁ P W, ∀ b ∈ decompW₂ P W, QuadraticMap.polar Q a b = 0) :
    ClassicalGroups.Orthogonal.PolarNondegOn Q (decompW₂ P W) := by
  intro x hx hxorth
  apply C.hEnd x (decompW₂_le_E C W hx)
  intro y hy
  have hy' : y ∈ decompW₁ P W ⊔ decompW₂ P W := hE ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
  rw [QuadraticMap.polar_add_right,
    (QuadraticMap.polar_comm Q x a).trans (horth a ha x hx), hxorth b hb, add_zero]

private theorem finrank_decomp_add
    {W : Submodule (ZMod p) U} (hE : E = decompW₁ P W ⊔ decompW₂ P W)
    (hinf : decompW₁ P W ⊓ decompW₂ P W = ⊥) :
    Module.finrank (ZMod p) (decompW₁ P W) +
      Module.finrank (ZMod p) (decompW₂ P W) = Module.finrank (ZMod p) E := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (decompW₁ P W) (decompW₂ P W)
  rw [← hE, hinf, finrank_bot, add_zero] at h
  exact h.symm

omit [Module.Finite (ZMod p) U] in
private theorem exists_mem_ne_zero_of_span_ne_bot {S : Set U}
    (h : Submodule.span (ZMod p) S ≠ ⊥) : ∃ a ∈ S, a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Submodule.span_eq_bot.mpr hcon)

private structure StabDecomp (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (Q : QuadraticForm (ZMod p) U)
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (E W : Submodule (ZMod p) U) (P : U → Prop) where
  x₀ : U
  y₀ : U
  hE : E = decompW₁ P W ⊔ decompW₂ P W
  hinf : decompW₁ P W ⊓ decompW₂ P W = ⊥
  hW : W = decompW₁ P W
  horth : ∀ a ∈ decompW₁ P W, ∀ b ∈ decompW₂ P W, QuadraticMap.polar Q a b = 0
  hWinf : W ⊓ decompW₂ P W = ⊥
  hcases : ∀ a, P a → a ∈ W ∨ ∀ w ∈ W, QuadraticMap.polar Q a w = 0
  hnd₁ : ClassicalGroups.Orthogonal.PolarNondegOn Q (decompW₁ P W)
  hnd₂ : ClassicalGroups.Orthogonal.PolarNondegOn Q (decompW₂ P W)
  hdim : Module.finrank (ZMod p) (decompW₁ P W) +
    Module.finrank (ZMod p) (decompW₂ P W) = Module.finrank (ZMod p) E
  hx₀P : P x₀
  hx₀W : x₀ ∈ decompW₁ P W
  hy₀P : P y₀
  hy₀W₂ : y₀ ∈ decompW₂ P W
  hy₀notW : y₀ ∉ W
  hne₁ : decompW₁ P W ≠ ⊥
  hne₂ : decompW₂ P W ≠ ⊥
  hpol : QuadraticMap.polar Q x₀ y₀ = 0

private noncomputable def exists_stabDecomp (C : DecompCtx p Q H E P)
    {W : Submodule (ZMod p) U} (hWE : W ≤ E)
    (hWinv : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) (hWbot : W ≠ ⊥) (hWtop : W ≠ E) :
    StabDecomp p Q H E W P := by
  have hcases : ∀ a, P a → a ∈ W ∨ ∀ w ∈ W, QuadraticMap.polar Q a w = 0 :=
    fun a ha => mem_or_polar_eq_zero C hWinv ha
  have hE : E = decompW₁ P W ⊔ decompW₂ P W :=
    le_antisymm (le_sup_decomp C hWinv)
      (sup_le (decompW₁_le_E C W) (decompW₂_le_E C W))
  have horth := decomp_orth C hWinv
  have hinf := inf_decomp_eq_bot C hE horth
  have hWinf := inf_W_decompW₂_eq_bot C hE hWinv
  have hW : W = decompW₁ P W := eq_decompW₁ hE hWE hWinf
  have hne₁ : decompW₁ P W ≠ ⊥ := hW ▸ hWbot
  have hne₂ : decompW₂ P W ≠ ⊥ := by
    intro hbot
    apply hWtop
    rw [hW, hE, hbot, sup_bot_eq]
  have hx₀ex := exists_mem_ne_zero_of_span_ne_bot (S := {a : U | P a ∧ a ∈ W}) hne₁
  have hy₀ex := exists_mem_ne_zero_of_span_ne_bot (S := {a : U | P a ∧ a ∉ W}) hne₂
  let x₀ : U := Classical.choose hx₀ex
  let y₀ : U := Classical.choose hy₀ex
  have hx₀S : x₀ ∈ {a : U | P a ∧ a ∈ W} := (Classical.choose_spec hx₀ex).1
  have hy₀S : y₀ ∈ {a : U | P a ∧ a ∉ W} := (Classical.choose_spec hy₀ex).1
  exact ⟨x₀, y₀, hE, hinf, hW, horth, hWinf, hcases,
    polarNondegOn_decompW₁ C hE horth, polarNondegOn_decompW₂ C hE horth,
    finrank_decomp_add hE hinf, hx₀S.1, Submodule.subset_span hx₀S,
    hy₀S.1, Submodule.subset_span hy₀S, hy₀S.2, hne₁, hne₂,
    horth x₀ (Submodule.subset_span hx₀S) y₀ (Submodule.subset_span hy₀S)⟩

omit [Module.Finite (ZMod p) U] in
private theorem false_of_decomp (D : StabDecomp p Q H E W P)
    (h2 : (2 : ZMod p) ≠ 0) {x y : U} (hQx : Q x ≠ 0) (hxW : x ∈ W) (hQy : Q y ≠ 0)
    (hyW₂ : y ∈ decompW₂ P W) (hxy : QuadraticMap.polar Q x y = 0)
    (hzP : P (x + y)) : False := by
  have hy0 : y ≠ 0 := fun h => hQy (by rw [h]; exact map_zero Q)
  rcases D.hcases (x + y) hzP with hzW | hzorth
  · have hyW : y ∈ W := by
      have h : y = (x + y) - x := by abel
      rw [h]
      exact W.sub_mem hzW hxW
    have hybot : y ∈ W ⊓ decompW₂ P W := ⟨hyW, hyW₂⟩
    rw [D.hWinf] at hybot
    exact hy0 (by simpa using hybot)
  · have h0 : QuadraticMap.polar Q (x + y) x = 0 := hzorth x hxW
    have hsplit : QuadraticMap.polar Q (x + y) x =
        QuadraticMap.polar Q x x + QuadraticMap.polar Q y x := by
      rw [QuadraticMap.polar_add_left]
    rw [hsplit, (QuadraticMap.polar_comm Q y x).trans hxy, add_zero,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at h0
    exact hQx ((mul_eq_zero.mp h0).resolve_left h2)

omit [Module.Finite (ZMod p) U] in
private theorem irredOnSection_of_no_invariant
    (hVH : HardMathSupport.Kantor79.commutatorSpace H = E)
    (hno : ∀ W : Submodule (ZMod p) U, W ≤ E →
      (∀ g ∈ H, ∀ w ∈ W, g w ∈ W) → W ≠ ⊥ → W ≠ E → False) :
    IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H) := by
  intro W _ hWE hWinv
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · by_cases hWtop : W = E
    · exact Or.inr (by rw [hVH]; exact hWtop)
    · exact (hno W (hVH ▸ hWE) hWinv hWbot hWtop).elim

private theorem three_five_sq_add_four_five_sq (hp5 : p ≠ 5) :
    (3 / 5 : ZMod p) ^ 2 + (4 / 5 : ZMod p) ^ 2 = 1 := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) (q := 5) (by norm_num) hp5
  field_simp
  ring

omit [Module.Finite (ZMod p) U] in
private theorem mem_of_eq_submodule {V V' : Submodule (ZMod p) U} (h : V = V') {x : U}
    (hx : x ∈ V) : x ∈ V' := h ▸ hx

omit [Module.Finite (ZMod p) U] in
private theorem false_full_char_ne_three (C : DecompCtx p Q H E (anisoSet Q E))
    (D : StabDecomp p Q H E W (anisoSet Q E)) (hp3 : p ≠ 3) : False := by
  have h3 : (3 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) (q := 3) (by norm_num) hp3
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero C.h2 C.h2
  have hxW : D.x₀ ∈ W := mem_of_eq_submodule D.hW.symm D.hx₀W
  by_cases hsum : Q D.x₀ + Q D.y₀ = 0
  · have hQy : Q ((2 : ZMod p) • D.y₀) = 4 * Q D.y₀ := by
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]
      norm_num
    have hQx : Q D.x₀ + 4 * Q D.y₀ = 3 * Q D.y₀ := by
      linear_combination hsum
    have hNz : Q (D.x₀ + (2 : ZMod p) • D.y₀) ≠ 0 := by
      rw [QuadraticMap.map_add Q,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, D.hpol, mul_zero, hQy,
        add_zero, hQx]
      exact mul_ne_zero h3 D.hy₀P.2
    have hQ2 : Q ((2 : ZMod p) • D.y₀) ≠ 0 := by
      rw [hQy]
      exact mul_ne_zero h4 D.hy₀P.2
    refine false_of_decomp D C.h2 D.hx₀P.2 hxW hQ2 ?_ ?_ ?_
    · exact (decompW₂ (anisoSet Q E) W).smul_mem (2 : ZMod p) D.hy₀W₂
    · rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, D.hpol, mul_zero]
    · exact ⟨E.add_mem D.hx₀P.1 (E.smul_mem (2 : ZMod p) D.hy₀P.1), hNz⟩
  · have hNz : Q (D.x₀ + D.y₀) ≠ 0 := by
      rw [QuadraticMap.map_add Q, D.hpol, add_zero]
      exact hsum
    exact false_of_decomp D C.h2 D.hx₀P.2 hxW D.hy₀P.2 D.hy₀W₂
      D.hpol ⟨E.add_mem D.hx₀P.1 D.hy₀P.1, hNz⟩

private theorem false_full_char_three (C : DecompCtx p Q H E (anisoSet Q E))
    (D : StabDecomp p Q H E W (anisoSet Q E))
    (hfin : Module.finrank (ZMod p) E + 1 = m) (hm4 : 4 ≤ m) : False := by
  have hdimD := D.hdim
  have hdimE : 3 ≤ Module.finrank (ZMod p) E := by omega
  have hpos₁ : 0 < Module.finrank (ZMod p) (decompW₁ (anisoSet Q E) W) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact D.hne₁
  have hpos₂ : 0 < Module.finrank (ZMod p) (decompW₂ (anisoSet Q E) W) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact D.hne₂
  by_cases h1 : 2 ≤ Module.finrank (ZMod p) (decompW₁ (anisoSet Q E) W)
  · obtain ⟨x, hxW₁, hxQ⟩ := D.hnd₁.exists_map_eq C.h2 h1 (Q D.y₀)
    have hQx : Q x ≠ 0 := by rw [hxQ]; exact D.hy₀P.2
    have hxy : QuadraticMap.polar Q x D.y₀ = 0 := D.horth x hxW₁ D.y₀ D.hy₀W₂
    have hNz : Q (x + D.y₀) ≠ 0 := by
      rw [QuadraticMap.map_add Q, hxQ, hxy, add_zero, ← two_mul]
      exact mul_ne_zero C.h2 D.hy₀P.2
    refine false_of_decomp D C.h2 hQx (mem_of_eq_submodule D.hW.symm hxW₁) D.hy₀P.2
      D.hy₀W₂ hxy ?_
    exact ⟨E.add_mem (decompW₁_le_E C W hxW₁) D.hy₀P.1, hNz⟩
  · have hle1 : Module.finrank (ZMod p) (decompW₁ (anisoSet Q E) W) ≤ 1 := by omega
    have hdim₂ : 2 ≤ Module.finrank (ZMod p) (decompW₂ (anisoSet Q E) W) := by omega
    obtain ⟨y, hyW₂, hyQ⟩ := D.hnd₂.exists_map_eq C.h2 hdim₂ (Q D.x₀)
    have hQy : Q y ≠ 0 := by rw [hyQ]; exact D.hx₀P.2
    have hxy : QuadraticMap.polar Q D.x₀ y = 0 := D.horth D.x₀ D.hx₀W y hyW₂
    have hNz : Q (D.x₀ + y) ≠ 0 := by
      rw [QuadraticMap.map_add Q, hyQ, hxy, add_zero, ← two_mul]
      exact mul_ne_zero C.h2 D.hx₀P.2
    refine false_of_decomp D C.h2 D.hx₀P.2 (mem_of_eq_submodule D.hW.symm D.hx₀W) hQy
      hyW₂ hxy ?_
    exact ⟨E.add_mem D.hx₀P.1 (decompW₂_le_E C W hyW₂), hNz⟩

omit [Module.Finite (ZMod p) U] in
private theorem false_class_char_ge_seven (C : DecompCtx p Q H E (normSet Q E c))
    (D : StabDecomp p Q H E W (normSet Q E c)) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hc : c ≠ 0) :
    False := by
  set a : ZMod p := 3 / 5
  set b : ZMod p := 4 / 5
  have h5 : (5 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) (q := 5) (by norm_num) hp5
  have h3 : (3 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) (q := 3) (by norm_num) hp3
  have ha : a ≠ 0 := by
    rw [show a = 3 / 5 from rfl]
    exact div_ne_zero h3 h5
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero C.h2 C.h2
  have hb : b ≠ 0 := by
    rw [show b = 4 / 5 from rfl]
    exact div_ne_zero h4 h5
  have hcoef : a ^ 2 + b ^ 2 = 1 := by
    rw [show a = 3 / 5 from rfl, show b = 4 / 5 from rfl]
    exact three_five_sq_add_four_five_sq hp5
  have hxQ : Q (a • D.x₀) = a ^ 2 * c := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, D.hx₀P.2]
  have hyQ : Q (b • D.y₀) = b ^ 2 * c := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, D.hy₀P.2]
  have hxy : QuadraticMap.polar Q (a • D.x₀) (b • D.y₀) = 0 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, D.hpol, mul_zero, mul_zero]
  have hzQ : Q (a • D.x₀ + b • D.y₀) = c := by
    rw [QuadraticMap.map_add Q, hxQ, hyQ, hxy, add_zero, ← add_mul, hcoef, one_mul]
  have hQx : Q (a • D.x₀) ≠ 0 := by
    rw [hxQ]
    exact mul_ne_zero (pow_ne_zero 2 ha) hc
  have hQy : Q (b • D.y₀) ≠ 0 := by
    rw [hyQ]
    exact mul_ne_zero (pow_ne_zero 2 hb) hc
  exact false_of_decomp D C.h2 hQx
    (mem_of_eq_submodule D.hW.symm ((decompW₁ (normSet Q E c) W).smul_mem a D.hx₀W))
    hQy ((decompW₂ (normSet Q E c) W).smul_mem b D.hy₀W₂) hxy
    ⟨E.add_mem (E.smul_mem a D.hx₀P.1) (E.smul_mem b D.hy₀P.1), hzQ⟩

private theorem six_eq_one_four_ne_zero (hp5 : p = 5) (h2 : (2 : ZMod p) ≠ 0) :
    (6 : ZMod p) = 1 ∧ (4 : ZMod p) ≠ 0 := by
  have h5zero : (5 : ZMod p) = 0 := by
    change ((5 : ℕ) : ZMod p) = 0
    rw [ZMod.natCast_eq_zero_iff, hp5]
  have h6 : (6 : ZMod p) = 1 := by
    have h : (6 : ZMod p) = 5 + 1 := by norm_num
    rw [h, h5zero, zero_add]
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  exact ⟨h6, h4⟩

private theorem false_class_five_ge_four (C : DecompCtx p Q H E (normSet Q E c))
    (D : StabDecomp p Q H E W (normSet Q E c)) (hp5 : p = 5) (hc : c ≠ 0)
    (hfin : Module.finrank (ZMod p) E + 1 = m) (hm4 : 4 ≤ m) : False := by
  have hdimD := D.hdim
  have hdimE : 3 ≤ Module.finrank (ZMod p) E := by omega
  obtain ⟨h6, h4⟩ := six_eq_one_four_ne_zero hp5 C.h2
  have hpos₁ : 0 < Module.finrank (ZMod p) (decompW₁ (normSet Q E c) W) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact D.hne₁
  have hyQ : Q ((2 : ZMod p) • D.y₀) = 4 * c := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, D.hy₀P.2]
    norm_num
  have hQy : Q ((2 : ZMod p) • D.y₀) ≠ 0 := by rw [hyQ]; exact mul_ne_zero h4 hc
  by_cases h1 : 2 ≤ Module.finrank (ZMod p) (decompW₁ (normSet Q E c) W)
  · obtain ⟨x, hxW₁, hxQ⟩ := D.hnd₁.exists_map_eq C.h2 h1 (2 * c)
    have hQx : Q x ≠ 0 := by rw [hxQ]; exact mul_ne_zero C.h2 hc
    have hxy : QuadraticMap.polar Q x ((2 : ZMod p) • D.y₀) = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        D.horth x hxW₁ D.y₀ D.hy₀W₂, mul_zero]
    have hzQ : Q (x + (2 : ZMod p) • D.y₀) = c := by
      rw [QuadraticMap.map_add Q, hxQ, hxy, hyQ, add_zero,
        show (2 : ZMod p) * c + 4 * c = 6 * c by ring, h6, one_mul]
    refine false_of_decomp D C.h2 hQx (mem_of_eq_submodule D.hW.symm hxW₁) hQy
      ((decompW₂ (normSet Q E c) W).smul_mem (2 : ZMod p) D.hy₀W₂) hxy ?_
    exact ⟨E.add_mem (decompW₁_le_E C W hxW₁) (E.smul_mem (2 : ZMod p) D.hy₀P.1), hzQ⟩
  · have hle1 : Module.finrank (ZMod p) (decompW₁ (normSet Q E c) W) ≤ 1 := by omega
    have hdim₂ : 2 ≤ Module.finrank (ZMod p) (decompW₂ (normSet Q E c) W) := by omega
    obtain ⟨y, hyW₂, hyQ'⟩ := D.hnd₂.exists_map_eq C.h2 hdim₂ (2 * c)
    have hxQ : Q ((2 : ZMod p) • D.x₀) = 4 * c := by
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, D.hx₀P.2]
      norm_num
    have hQx : Q ((2 : ZMod p) • D.x₀) ≠ 0 := by rw [hxQ]; exact mul_ne_zero h4 hc
    have hQy' : Q y ≠ 0 := by rw [hyQ']; exact mul_ne_zero C.h2 hc
    have hxy : QuadraticMap.polar Q ((2 : ZMod p) • D.x₀) y = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        D.horth D.x₀ D.hx₀W y hyW₂, mul_zero]
    have hzQ : Q ((2 : ZMod p) • D.x₀ + y) = c := by
      rw [QuadraticMap.map_add Q, hxQ, hyQ', hxy, add_zero,
        show (4 : ZMod p) * c + 2 * c = 6 * c by ring, h6, one_mul]
    refine false_of_decomp D C.h2 hQx (mem_of_eq_submodule D.hW.symm
      ((decompW₁ (normSet Q E c) W).smul_mem (2 : ZMod p) D.hx₀W)) hQy' hyW₂ hxy ?_
    exact ⟨E.add_mem (E.smul_mem (2 : ZMod p) D.hx₀P.1) (decompW₂_le_E C W hyW₂), hzQ⟩

private theorem exceptional_class_three_five
    (C : DecompCtx p Q (reflStab p X h) E (normSet Q E c))
    (D : StabDecomp p Q (reflStab p X h) E W (normSet Q E c)) :
    ∃ x ∈ reflStab p X h, ∃ y ∈ reflStab p X h, IsRefl p x ∧ IsRefl p y ∧
      x * y = y * x ∧ x ≠ y := by
  refine ⟨ClassicalGroups.Orthogonal.reflect Q D.x₀,
    C.hroot D.x₀ D.hx₀P, ClassicalGroups.Orthogonal.reflect Q D.y₀,
    C.hroot D.y₀ D.hy₀P, isRefl_reflect C.hp (C.hQne _ D.hx₀P),
    isRefl_reflect C.hp (C.hQne _ D.hy₀P),
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero D.hpol, ?_⟩
  intro hxy
  have h := congrArg (fun g : U ≃ₗ[ZMod p] U => g D.x₀) hxy
  rw [reflect_apply_self (C.hQne _ D.hx₀P),
    ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      ((QuadraticMap.polar_comm Q D.y₀ D.x₀).trans D.hpol)] at h
  have hzero : D.x₀ = 0 := eq_zero_of_eq_neg C.h2 h.symm
  exact C.hQne _ D.hx₀P (by rw [hzero]; exact map_zero Q)

private structure ReflSetup (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (Q : QuadraticForm (ZMod p) U)
    (X : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) (m : ℕ) where
  h2 : (2 : ZMod p) ≠ 0
  hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h
  hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q (rootSpace X h)
  hfin : Module.finrank (ZMod p) (rootSpace X h) + 1 = m

omit [Module.Finite (ZMod p) U] in
private theorem reflStab_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X)
    (hh : h ∈ X) (hh' : IsRefl p h) : ReflSetup p Q X h m := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨e, hQe, hee⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ hh' (ho.isIsom hh)
  have he0 : e ≠ 0 := fun h0 => hQe (by rw [h0]; exact map_zero Q)
  have heV : e ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hee)
  have hheq : h = ClassicalGroups.Orthogonal.reflect Q e :=
    DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hh' (ho.isIsom hh)
      (isRefl_reflect hp hQe) (isIsom_reflect Q e) he0 hee (reflect_apply_self hQe)
  have hker : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
    rw [hheq]
    exact ker_reflect_sub_one_eq_ker_polar hQe
  have hVH : HardMathSupport.Kantor79.commutatorSpace (reflStab p X h) = rootSpace X h :=
    commutatorSpace_reflStab hp hQ hs hm hm3 ho hh hh'
  have hEnd : ClassicalGroups.Orthogonal.PolarNondegOn Q (rootSpace X h) := by
    rw [rootSpace, hker]
    exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2
      (polarNondegOn_commutatorSpace hQ (fun g hg => ho.isIsom hg) hs.1) heV hQe
  have hfin : Module.finrank (ZMod p) (rootSpace X h) + 1 = m := by
    rw [rootSpace, hker]
    have h := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one h2 heV hQe
    rw [hs.2.1] at h
    exact h
  exact ⟨h2, hVH, hEnd, hfin⟩

omit [Module.Finite (ZMod p) U] in
private theorem full_case (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (S : ReflSetup p Q X h m)
    (hm3 : p = 3 → 4 ≤ m) (hXiso : ∀ g ∈ X, IsIsom p Q g)
    (hfull : X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) :
    IrredOnSection (reflStab p X h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p X h)) := by
  let C := decompCtx_of_full hp hQ hfull hXiso S.hVH S.hEnd S.h2
  refine irredOnSection_of_no_invariant S.hVH ?_
  intro W hWE hWinv hWbot hWtop
  obtain D := exists_stabDecomp C hWE hWinv hWbot hWtop
  by_cases hp3 : p = 3
  · exact false_full_char_three C D S.hfin (hm3 hp3)
  · exact false_full_char_ne_three C D hp3

omit [Module.Finite (ZMod p) U] in
private theorem class_case (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (S : ReflSetup p Q X h m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (hXiso : ∀ g ∈ X, IsIsom p Q g)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (h3 : p = 3 → X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) :
    IrredOnSection (reflStab p X h) ⊥
        (HardMathSupport.Kantor79.commutatorSpace (reflStab p X h)) ∨
      m = 3 ∧ p = 5 ∧ (∃ c : ZMod p, c ≠ 0 ∧ X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) ∧
        ∃ x ∈ reflStab p X h, ∃ y ∈ reflStab p X h, IsRefl p x ∧ IsRefl p y ∧
          x * y = y * x ∧ x ≠ y := by
  by_cases hp3 : p = 3
  · exact Or.inl (full_case hp hQ S hm3 hXiso (h3 hp3))
  · let C := decompCtx_of_class hp hQ hc hclass S.hVH S.hEnd S.h2
    by_cases hp5 : p = 5
    · by_cases hm3' : m = 3
      · by_cases hirr : IrredOnSection (reflStab p X h) ⊥
            (HardMathSupport.Kantor79.commutatorSpace (reflStab p X h))
        · exact Or.inl hirr
        · have hnotE : ¬ IrredOnSection (reflStab p X h) ⊥ (rootSpace X h) :=
            fun hirrE => hirr (S.hVH.symm ▸ hirrE)
          rw [IrredOnSection] at hnotE
          push Not at hnotE
          obtain ⟨W, -, hWE, hWinv, hWbot, hWtop⟩ := hnotE
          obtain D := exists_stabDecomp C hWE hWinv hWbot hWtop
          exact Or.inr ⟨hm3', hp5, ⟨c, hc, hclass⟩, exceptional_class_three_five C D⟩
      · have hm4 : 4 ≤ m := by omega
        refine Or.inl (irredOnSection_of_no_invariant S.hVH ?_)
        intro W hWE hWinv hWbot hWtop
        obtain D := exists_stabDecomp C hWE hWinv hWbot hWtop
        exact false_class_five_ge_four C D hp5 hc S.hfin hm4
    · refine Or.inl (irredOnSection_of_no_invariant S.hVH ?_)
      intro W hWE hWinv hWbot hWtop
      obtain D := exists_stabDecomp C hWE hWinv hWbot hWtop
      exact false_class_char_ge_seven C D hp3 hp5 hc

omit [Module.Finite (ZMod p) U] in
private theorem irredOnSection_reflStab_or_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X)
    (h3 : p = 3 → X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hh : h ∈ X) (hh' : IsRefl p h) :
    IrredOnSection (reflStab p X h) ⊥
        (HardMathSupport.Kantor79.commutatorSpace (reflStab p X h)) ∨
      m = 3 ∧ p = 5 ∧ (∃ c : ZMod p, c ≠ 0 ∧ X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) ∧
        ∃ x ∈ reflStab p X h, ∃ y ∈ reflStab p X h, IsRefl p x ∧ IsRefl p y ∧
          x * y = y * x ∧ x ≠ y := by
  let S := reflStab_setup hp hQ hs hm hm3 ho hh hh'
  have hXiso : ∀ g ∈ X, IsIsom p Q g := fun g hg => ho.isIsom hg
  rcases ho with hfull | ⟨c, hc, hclass⟩
  · exact Or.inl (full_case hp hQ S hm3 hXiso hfull)
  · exact class_case hp hQ S hm hm3 hXiso hc hclass h3

omit [Module.Finite (ZMod p) U] in
theorem irredOnSection_reflStab_or (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X)
    (h3 : p = 3 → X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X})
    (hh : h ∈ X) (hh' : IsRefl p h) :
    IrredOnSection (reflStab p X h) ⊥
        (HardMathSupport.Kantor79.commutatorSpace (reflStab p X h)) ∨
      m = 3 ∧ p = 5 ∧ (∃ c : ZMod p, c ≠ 0 ∧ X = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
          HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X}) ∧
        ∃ x ∈ reflStab p X h, ∃ y ∈ reflStab p X h, IsRefl p x ∧ IsRefl p y ∧
          x * y = y * x ∧ x ≠ y := by
  exact irredOnSection_reflStab_or_aux hp hQ hs hm hm3 ho h3 hh hh'

end CFSG.StandardType.ZS

end
