module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.LieType.Chevalley Matrix

theorem exists_finite_subfield_projectiveSL_lift
    {n : ℕ} (hn : 0 < n) {K Ω G : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [Group G] [Finite G]
    (ρ : G →* projectiveSL n Ω) (S : Finset Ω) :
    ∃ E : Subfield Ω, Finite E ∧ (S : Set Ω) ⊆ E ∧
      ∃ κ : K →+* E, E.subtype.comp κ = algebraMap K Ω ∧
        (∃ m : ℕ, 0 < m ∧ Nat.card E = Nat.card K ^ m) ∧
        ∃ ρE : G →* projectiveSL n E,
          (linearSubfieldInclusion n E).comp ρE = ρ ∧ ρE.ker = ρ.ker := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let lift : G → SpecialLinearGroup (Fin n) Ω :=
    fun g => Classical.choose (proj_surjective n Ω (ρ g))
  have hlift : ∀ g, proj n Ω (lift g) = ρ g :=
    fun g => Classical.choose_spec (proj_surjective n Ω (ρ g))
  let T : Finset Ω := Finset.univ.biUnion fun g : G =>
    Finset.univ.biUnion fun i : Fin n =>
      Finset.univ.image fun j : Fin n => (lift g : Matrix (Fin n) (Fin n) Ω) i j
  obtain ⟨E, hE, hSTE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (S ∪ T)
  have hSE : (S : Set Ω) ⊆ E := fun c hc => hSTE (Finset.mem_union_left T hc)
  have hcoeff : ∀ g i j, (lift g : Matrix (Fin n) (Fin n) Ω) i j ∈ E := by
    intro g i j
    apply hSTE
    apply Finset.mem_union_right
    simp only [T, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨g, i, j, rfl⟩
  let ι := linearSubfieldInclusion n E
  have hι : Function.Injective ι := linearSubfieldInclusion_injective hn E
  have hrange : ∀ g, ρ g ∈ ι.range := fun g =>
    mem_range_linearSubfieldInclusion.mpr ⟨lift g, hcoeff g, hlift g⟩
  let f : G →* ι.range := ρ.codRestrict ι.range hrange
  let e : projectiveSL n E ≃* ι.range := MonoidHom.ofInjective hι
  let ρE : G →* projectiveSL n E := e.symm.toMonoidHom.comp f
  have hcomp : ι.comp ρE = ρ := by
    ext g
    change ι (e.symm (f g)) = ρ g
    exact (MonoidHom.ofInjective_apply hι (x := e.symm (f g))).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply (f g)))
  let κ : K →+* E := (algebraMap K Ω).codRestrict E fun k => hKE ⟨k, rfl⟩
  have hκ : E.subtype.comp κ = algebraMap K Ω := RingHom.ext fun _ => rfl
  let : Finite E := hE
  let : Algebra K E := κ.toAlgebra
  refine ⟨E, hE, hSE, κ, hκ,
    ⟨Module.finrank K E, Module.finrank_pos, Module.natCard_eq_pow_finrank⟩,
    ρE, hcomp, ?_⟩
  ext g
  change ρE g = 1 ↔ ρ g = 1
  have hg : ι (ρE g) = ρ g := DFunLike.congr_fun hcomp g
  constructor
  · intro h
    rw [← hg, h, map_one]
  · intro h
    apply hι
    rw [hg, h, map_one]

end CFSG.RankThree.PartOne
