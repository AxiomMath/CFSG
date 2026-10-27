module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdLift
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenL3
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
import CFSG.RankThree.PartTwo.Sec14.Ronan148KN6
import CFSG.Open.StatedAPI

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedClassicalModel)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem scalar_commutant_of_perfect_irred {F : Type} [Field F] [Finite F]
    {D : Subgroup (GL (Fin 3) F)} [Group.IsPerfect D] (hD : SubgroupLists.IsIrreducibleOn D) :
    ∀ M : Matrix (Fin 3) (Fin 3) F, (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
      ∃ c : F, M = Matrix.scalar (Fin 3) c := by
  rcases SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three
      (SubgroupLists.isIrreducibleOn_iff.mp hD) with h | ⟨hcyc, -, -⟩
  · exact h
  · exfalso
    haveI : IsCyclic D := hcyc
    have hD1 : ∀ g : D, g = 1 := by
      intro g
      have hc : commutator D = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _ y _
        exact (IsCyclic.commutative.is_comm.comm x y).symm
      have hg : g ∈ commutator D := by
        rw [Group.IsPerfect.commutator_eq_top]
        exact Subgroup.mem_top g
      rw [hc] at hg
      exact Subgroup.mem_bot.mp hg
    refine SubgroupLists.not_irreducible_of_forall_scalar (by norm_num) (fun h hh => ?_)
      (SubgroupLists.isIrreducibleOn_iff.mp hD)
    have : (⟨h, hh⟩ : D) = 1 := hD1 _
    have h1 : h = 1 := congrArg Subtype.val this
    exact ⟨1, by rw [h1]; simp⟩

theorem even_ident (hIrr : EvenSL3Irred) {X : Type} [Group X] [Finite X]
    {P : Subgroup (MulAut X)} {K₀ : Subgroup X} {π : Bool} {f : ℕ} {F : Type} [Field F]
    (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    (φ : X ≃* projImage (slPi π 3 (2 ^ f) F)) {y₁ y₂ : GL (Fin 3) F} {ζ : Fˣ}
    (hy₁ : y₁ ∈ glPi π 3 (2 ^ f) F) (hy₂ : y₂ ∈ glPi π 3 (2 ^ f) F)
    (hy₁3 : y₁ ^ 3 ∈ StatedScalars (Fin 3) F) (hy₂3 : y₂ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (hact : ∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
      ((φ (σ z) : projImage (slPi π 3 (2 ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        pmk (y₁ ^ i * y₂ ^ j) * (φ z : ProjGenLinGroup (Fin 3) F) * (pmk (y₁ ^ i * y₂ ^ j))⁻¹)
    (hP9 : Nat.card P = 9) (hinv : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀) (hKs : IsSimpleGroup ↥K₀)
    (hnab : ∃ a b : ↥K₀, a * b ≠ b * a) :
    StatedClassicalModel ↥K₀ .PSL 2 3 2 ∨
      ∃ f₁ : ℕ, 1 ≤ f₁ ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
        IsLThreeEpsAt ↥K₀ 2 f₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hF.finite
  haveI hperf : Group.IsPerfect ↥K₀ := isPerfect_of_simple hKs hnab
  have hK1 : K₀ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K₀).mp hKs.toNontrivial
  obtain ⟨D, hDp, hirr, hDH, hDK, hKD⟩ := exists_irred_lift hF φ hy₁ hy₂ hy₁3 hy₂3 hζ1 hζ hact
    hP9 hinv hperf hK1
  haveI := hDp
  have hcomm := scalar_commutant_of_perfect_irred hirr
  have hmem : ∀ d : D, pmk (d : GL (Fin 3) F) ∈ projImage (slPi π 3 (2 ^ f) F) :=
    fun d => ⟨d, hDH d.2, rfl⟩
  let g₁ : D →* X :=
    φ.symm.toMonoidHom.comp ((ProjGenLinGroup.mk.comp D.subtype).codRestrict _ hmem)
  have hg₁ : ∀ d : D, g₁ d ∈ K₀ := by
    intro d
    obtain ⟨k, hk, hkd⟩ := hDK d d.2
    have : g₁ d = k := by
      apply φ.injective
      apply Subtype.ext
      change (φ (φ.symm ⟨pmk d, hmem d⟩) : ProjGenLinGroup (Fin 3) F) = _
      rw [MulEquiv.apply_symm_apply]
      exact hkd
    rw [this]
    exact hk
  let g : D →* K₀ := g₁.codRestrict K₀ hg₁
  have hgs : Function.Surjective g := by
    rintro ⟨k, hk⟩
    obtain ⟨d, hd, hdk⟩ := hKD k hk
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change φ.symm ⟨pmk d, hmem ⟨d, hd⟩⟩ = k
    apply φ.injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply]
    exact hdk
  have hker : Subgroup.center D = g.ker := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      have hsc : ∃ c : F, ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          Matrix.scalar (Fin 3) c := by
        refine hcomm _ fun h hh => ?_
        have := Subgroup.mem_center_iff.mp hd ⟨h, hh⟩
        rw [← Units.val_mul, ← Units.val_mul]
        exact congrArg (fun x : D => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) this
      obtain ⟨c, hc⟩ := hsc
      have hc0 : c ≠ 0 := by
        rintro rfl
        have h1 := congrArg Matrix.det hc
        rw [Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero] at h1
        exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (d : GL (Fin 3) F)) |>.ne_zero h1
      have hd1 : pmk (d : GL (Fin 3) F) = 1 := by
        rw [Sec4.mk_eq_one_iff_mem_statedScalars]
        refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar, hc]
        rfl
      apply Subtype.ext
      change φ.symm ⟨pmk d, hmem d⟩ = 1
      rw [show (⟨pmk d, hmem d⟩ : projImage (slPi π 3 (2 ^ f) F)) = 1 from Subtype.ext hd1,
        map_one]
    · intro hd
      have h1 : pmk (d : GL (Fin 3) F) = 1 := by
        have h2 := congrArg Subtype.val hd
        change φ.symm ⟨pmk d, hmem d⟩ = 1 at h2
        have h3 := congrArg (fun x => ((φ x : projImage (slPi π 3 (2 ^ f) F)) :
          ProjGenLinGroup (Fin 3) F)) h2
        simpa using h3
      obtain ⟨c, hc⟩ := Sec4.mk_eq_one_iff_mem_statedScalars.mp h1
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
      exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (h : GL (Fin 3) F)).eq
  let ψ : D ⧸ Subgroup.center D ≃* K₀ :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  have hDq : IsQuasisimple D := by
    haveI := hKs
    refine ⟨inferInstance, MulEquiv.isSimpleGroup ψ, ?_⟩
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (ψ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hDdet : ∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1 := fun x hx =>
    det_eq_one_of_mem_slPi hF (hDH hx)
  have hDZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1 := by
    intro z hz
    have hz' : z ∈ g.ker := hker ▸ hz
    rw [MonoidHom.mem_ker] at hz'
    have h1 : pmk (z : GL (Fin 3) F) = 1 := by
      have h2 := congrArg Subtype.val hz'
      change φ.symm ⟨pmk z, hmem z⟩ = 1 at h2
      have h3 := congrArg (fun x => ((φ x : projImage (slPi π 3 (2 ^ f) F)) :
        ProjGenLinGroup (Fin 3) F)) h2
      simpa using h3
    obtain ⟨c, hc⟩ := Sec4.mk_eq_one_iff_mem_statedScalars.mp h1
    have hzH : (z : GL (Fin 3) F) ∈ slPi π 3 (2 ^ f) F := hDH z.2
    have hzc : (⟨z, hzH⟩ : slPi π 3 (2 ^ f) F) ∈ Subgroup.center (slPi π 3 (2 ^ f) F) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change (h : GL (Fin 3) F) * z = z * h
      rw [← hc]
      exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (h : GL (Fin 3) F)).eq
    have h3 := pow_three_eq_one_of_mem_center_slPi hF hq hzc
    apply Subtype.ext
    have h4 := congrArg Subtype.val h3
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h4 ⊢
    exact h4
  have hcomm' : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
      ∃ c : F, M = Matrix.scalar (Fin 3) c := hcomm
  have hprim : ¬ SubgroupLists.IsTransitiveMonomial D :=
    SubgroupLists.not_isTransitiveMonomial_of_perfect
  obtain ⟨e, he, hFc, hq3⟩ : ∃ e : ℕ, 1 ≤ e ∧ Nat.card F = 2 ^ e ∧ 2 ^ e % 3 = 1 := by
    have hc := hF.card
    have hf1 := hF.one_le
    cases π
    · refine ⟨2 * f, by omega, ?_, ?_⟩
      · rw [hc]
        change (2 ^ f) ^ 2 = 2 ^ (2 * f)
        ring
      · change (2 ^ f) % 3 = 2 at hq
        rw [pow_mul]
        change (4 ^ f) % 3 = 1
        rw [Nat.pow_mod]
        norm_num
    · exact ⟨f, hf1, hc, hq⟩
  rcases hIrr F e he hFc hq3 D hDdet hDq hDZ3 hirr hcomm' hprim with h | ⟨f', hf', -, h⟩
  · exact Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ψ h)
  · exact Or.inr ⟨f', hf', Ronan148K.isLThreeEpsAt_of_mulEquiv ψ h⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
