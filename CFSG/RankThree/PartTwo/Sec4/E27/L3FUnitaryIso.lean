module

public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryLine

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix

section Kernel

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K} (h : UnitaryFieldData p f K)
  (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

theorem suConj_mem_unitaryScalars_iff (A : unitaryIsom3 h) {z : unitarySU p f K 3} :
    suConj h A z ∈ unitaryScalars h 3 ↔ z ∈ unitaryScalars h 3 := by
  refine ⟨fun hz => ?_, suConj_mem_unitaryScalars A⟩
  have := suConj_mem_unitaryScalars A⁻¹ hz
  rwa [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this

include hbar in
theorem subSU_mem_unitaryScalars_iff {z : unitarySU p e k 3} :
    subSU h h₀ hbar z ∈ unitaryScalars h 3 ↔ z ∈ unitaryScalars h₀ 3 := by
  rw [unitaryScalars_eq h (by norm_num), unitaryScalars_eq h₀ (by norm_num),
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hent : ∀ i j, ((((z : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j : k) : K) =
        (Matrix.scalar (Fin 3) (c : K)) i j := fun i j => by
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i j) hc
      simpa [coe_subSU, GeneralLinearGroup.map_apply] using this.symm
    have hck : (c : K) ∈ k := by
      have := hent 0 0
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
      rw [← this]
      exact ((z : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 |>.2
    set c0 : k := ⟨(c : K), hck⟩ with hc0
    have hc0ne : c0 ≠ 0 := fun h0 => (Units.ne_zero c) (congrArg Subtype.val h0)
    refine ⟨Units.mk0 c0 hc0ne, ?_⟩
    apply Units.ext
    ext i j
    rw [hent i j]
    by_cases hij : i = j
    · subst hij
      simp [hc0, GeneralLinearGroup.coe_scalar]
    · simp [hij, GeneralLinearGroup.coe_scalar]
  · rintro ⟨c, hc⟩
    refine ⟨Units.map (k.subtype : k →* K) c, ?_⟩
    rw [coe_subSU, ← hc]
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [GeneralLinearGroup.coe_scalar, GeneralLinearGroup.map_apply]
    · simp [hij, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.map_apply]

include hbar in
theorem ker_PsiU (H : unitaryIsom3 h) : (PsiU h h₀ hbar H).ker = unitaryScalars h₀ 3 := by
  ext z
  rw [MonoidHom.mem_ker]
  change unitaryProj h 3 (suConj h H (subSU h h₀ hbar z)) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_unitaryProj, suConj_mem_unitaryScalars_iff,
    subSU_mem_unitaryScalars_iff h h₀ hbar]

@[expose] noncomputable def lineUEquiv (H : unitaryIsom3 h) :
    unitaryPSU h₀ 3 ≃* lineU h h₀ hbar H :=
  (QuotientGroup.quotientMulEquivOfEq (ker_PsiU h h₀ hbar H).symm).trans
    (QuotientGroup.quotientKerEquivRange (PsiU h h₀ hbar H))

end Kernel

section Iso

theorem isoLThreePi_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    [Fact p.Prime] (h : IsoLThreePi Y p f) : IsoLThreePi X p f := by
  rcases h with ⟨h1, ⟨e'⟩⟩ | ⟨h1, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans e'⟩⟩

theorem isoLThreePi_unitaryPSU {p e : ℕ} [Fact p.Prime] {F : Type} [Field F]
    (h₀ : UnitaryFieldData p e F) (hmod : p ^ e % 3 = 2) :
    IsoLThreePi (unitaryPSU h₀ 3) p e := by
  have := h₀.finite
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField p (2 * e)) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField p (2 * e)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h₀.card,
      GaloisField.card p (2 * e) (by have := h₀.one_le; omega)]
  let φ : F ≃+* GaloisField p (2 * e) := FiniteField.ringEquivOfCardEq hcard
  let e3 : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) F) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ e))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact Or.inr ⟨hmod, ⟨(unitaryPSUEquiv h₀ (by norm_num)).trans
    (e3.trans (Sec4.projSUEquivStatedProj 3 p e).symm)⟩⟩

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K} (h : UnitaryFieldData p f K)
  (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

theorem isoLThreePi_lineU [Fact p.Prime] (hmod : p ^ e % 3 = 2) (H : unitaryIsom3 h) :
    IsoLThreePi (lineU h h₀ hbar H) p e :=
  isoLThreePi_of_equiv (lineUEquiv h h₀ hbar H).symm (isoLThreePi_unitaryPSU h₀ hmod)

end Iso

end CFSG.RankThree.PartTwo.Sec4.E27
