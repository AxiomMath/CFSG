module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryCount
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU10
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FDecomp

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Lines

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K} (h : UnitaryFieldData p f K)
  (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

@[expose] noncomputable def subSU : unitarySU p e k 3 →* unitarySU p f K 3 :=
  ((GeneralLinearGroup.map (k.subtype : k →+* K)).comp (unitarySU p e k 3).subtype).codRestrict
    (unitarySU p f K 3) fun z => Sec19.Item19Res6Proof.map_mem_unitarySU h h₀ hbar z.2

theorem coe_subSU (z : unitarySU p e k 3) :
    ((subSU h h₀ hbar z : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.map (k.subtype : k →+* K) (z : GL (Fin 3) k) :=
  rfl

@[expose] noncomputable def PsiU (H : unitaryIsom3 h) : unitarySU p e k 3 →* unitaryPSU h 3 :=
  (unitaryProj h 3).comp ((suConj h H).toMonoidHom.comp (subSU h h₀ hbar))

@[expose] noncomputable def lineU (H : unitaryIsom3 h) : Subgroup (unitaryPSU h 3) :=
  (PsiU h h₀ hbar H).range

theorem mem_lineU_iff {H : unitaryIsom3 h} {x : unitaryPSU h 3} :
    x ∈ lineU h h₀ hbar H ↔ ∃ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) ∧
        unitaryProj h 3 (suConj h H g) = x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨subSU h h₀ hbar z, fun i j =>
      Sec19.Item19Res6Proof.map_apply_mem (z : GL (Fin 3) k) i j, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨z, hz, hzg⟩ := Sec19.Item19Res6Proof.exists_unitarySU_of_mem h h₀ hbar g.2 hg
    refine ⟨⟨z, hz⟩, ?_⟩
    have : subSU h h₀ hbar ⟨z, hz⟩ = g := Subtype.ext hzg
    show unitaryProj h 3 (suConj h H (subSU h h₀ hbar ⟨z, hz⟩)) = _
    rw [this]

end Lines

section Action

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem psuConj_proj (A : unitaryIsom3 h) (s : unitarySU p f K 3) :
    psuConj h A (unitaryProj h 3 s) = unitaryProj h 3 (suConj h A s) :=
  rfl

theorem fieldLineU_apply_proj (hq : 2 < p ^ f) (H : unitaryIsom3 h) (σ : K ≃+* K)
    (s : unitarySU p f K 3) :
    (psuConj h H * psuField h σ * (psuConj h H)⁻¹) (unitaryProj h 3 s) =
      unitaryProj h 3 ((suConj h H * suField h σ * (suConj h H)⁻¹) s) := by
  have : psuConj h H * psuField h σ * (psuConj h H)⁻¹ =
      Sec19.descPSUHom h hq (suConj h H * suField h σ * (suConj h H)⁻¹) := by
    rw [map_mul, map_mul, map_inv, Sec19.descPSUHom_suConj, Sec19.descPSUHom_suField]
  rw [this]
  rfl

end Action

section Props

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K} (h : UnitaryFieldData p f K)
  (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

theorem fieldLineU_fixes_lineU (hq : 2 < p ^ f) {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {H : unitaryIsom3 h} {x : unitaryPSU h 3} (hx : x ∈ lineU h h₀ hbar H) :
    (psuConj h H * psuField h σ * (psuConj h H)⁻¹) x = x := by
  obtain ⟨g, hg, rfl⟩ := (mem_lineU_iff h h₀ hbar).1 hx
  rw [fieldLineU_apply_proj hq]
  congr 1
  exact Sec19.Item19Res6Proof.conj_suField_fix H σ g fun i j => (hk _).1 (hg i j)

theorem lineU_invariant [Finite K] (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (hk : ∀ x, x ∈ k ↔ σ x = x) {H : unitaryIsom3 h}
    (hφE : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∈ E)
    (hφN : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∉ (psuConj h).range) :
    ∀ x ∈ E, ∀ l ∈ lineU h h₀ hbar H, x l ∈ lineU h h₀ hbar H := by
  intro x hx l hl
  obtain ⟨b, hb, a, rfl⟩ := exists_eq_mul_zpow_of_card hE hc
    (card_inf_psuConj_range_eq_nine h3 hq hE hc) hφE hφN x hx
  have hfix : ((psuConj h H * psuField h σ * (psuConj h H)⁻¹) ^ a) l = l :=
    zpow_apply_eq_of_fixes (fieldLineU_fixes_lineU h h₀ hbar hq hk hl) a
  rw [MulAut.mul_apply, hfix]
  have hcomm : b * (psuConj h H * psuField h σ * (psuConj h H)⁻¹) =
      (psuConj h H * psuField h σ * (psuConj h H)⁻¹) * b := by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨b, hb.1⟩ : E) ⟨_, hφE⟩)
  obtain ⟨B, rfl⟩ := hb.2
  set M : unitaryIsom3 h := H⁻¹ * B * H with hM
  have hMcomm : psuConj h M * psuField h σ = psuField h σ * psuConj h M := by
    rw [hM, map_mul, map_mul, map_inv]
    set a' := psuConj h H
    set b' := psuConj h B
    set f' := psuField h σ
    calc (a'⁻¹ * b' * a') * f' = a'⁻¹ * (b' * (a' * f' * a'⁻¹)) * a' := by group
      _ = a'⁻¹ * ((a' * f' * a'⁻¹) * b') * a' := by rw [hcomm]
      _ = f' * (a'⁻¹ * b' * a') := by group
  obtain ⟨u, g', hMug, hg'k⟩ := exists_rational_rep_psu hq hσ hk hMcomm
  obtain ⟨g, hg, rfl⟩ := (mem_lineU_iff h h₀ hbar).1 hl
  refine (mem_lineU_iff h h₀ hbar).2 ⟨suConj h M g, ?_, ?_⟩
  ·
    have hmat : ((suConj h M g : unitarySU p f K 3) : GL (Fin 3) K) =
        g' * (g : GL (Fin 3) K) * g'⁻¹ := by
      rw [coe_suConj, Subgroup.coe_inv, hMug]
      calc GeneralLinearGroup.scalar (Fin 3) u * g' * (g : GL (Fin 3) K) *
            (GeneralLinearGroup.scalar (Fin 3) u * g')⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) u * (g' * (g : GL (Fin 3) K) * g'⁻¹) *
            (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
        _ = g' * (g : GL (Fin 3) K) * g'⁻¹ := by
          rw [GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
    have hg'm : (g' : Matrix (Fin 3) (Fin 3) K).map σ = g' := by
      ext i j
      exact (hk _).1 (hg'k i j)
    have hgm : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      exact (hk _).1 (hg i j)
    have hinv := inv_map_eq_of_map_eq hg'm
    have hfx : ((g' * (g : GL (Fin 3) K) * g'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        ((g' * (g : GL (Fin 3) K) * g'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hg'm, hgm, hinv]
    intro i j
    rw [hmat, hk]
    exact congrFun (congrFun hfx i) j
  ·
    rw [psuConj_proj]
    congr 1
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [hM]
    group

end Props

end CFSG.RankThree.PartTwo.Sec4.E27
