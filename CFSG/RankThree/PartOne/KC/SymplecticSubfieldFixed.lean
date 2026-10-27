module

public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneCore
public import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv glFieldEquiv_scalar)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_scalar_of_mem_spScalars [NeZero r] {z : StatedSp r K} (hz : z ∈ spScalars r K) :
    ∃ c : Kˣ, c ^ 2 = 1 ∧
      (z : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  obtain ⟨c, hc⟩ := hz
  have hc' : (z : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := hc.symm
  refine ⟨c, ?_, hc'⟩
  have hz2 : (z : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := z.2
  rw [hc'] at hz2
  exact (CFSG.LieType.Classical.scalar_mem_statedSp_iff NeZero.one_le c).mp hz2

@[expose] def scalarSp [NeZero r] (c : Kˣ) (hc : c ^ 2 = 1) : StatedSp r K :=
  ⟨GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c,
    (CFSG.LieType.Classical.scalar_mem_statedSp_iff NeZero.one_le c).mpr hc⟩

theorem scalarSp_mem [NeZero r] (c : Kˣ) (hc : c ^ 2 = 1) :
    (scalarSp c hc : StatedSp r K) ∈ spScalars r K :=
  ⟨c, rfl⟩

theorem sq_eq_one_of_mem_spScalars [NeZero r] {z : StatedSp r K} (hz : z ∈ spScalars r K) :
    z ^ 2 = 1 := by
  obtain ⟨c, hc2, hc⟩ := exists_scalar_of_mem_spScalars hz
  refine Subtype.ext ?_
  change (z : GL (Fin r ⊕ Fin r) K) ^ 2 = 1
  rw [hc, ← map_pow, hc2, map_one]

theorem units_map_eq_of_sq_eq_one {c : Kˣ} (hc : c ^ 2 = 1) (σ : K ≃+* K) :
    Units.map (σ.toRingHom : K →+* K).toMonoidHom c = c := by
  have h1 : (c : K) * c = 1 := by
    have := congrArg Units.val hc
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · refine Units.ext ?_
    simp [h]
  · refine Units.ext ?_
    simp [h]

theorem fieldSp_eq_of_mem_spScalars [NeZero r] (σ : K ≃+* K) {z : StatedSp r K}
    (hz : z ∈ spScalars r K) : fieldSp r K σ z = z := by
  obtain ⟨c, hc2, hc⟩ := exists_scalar_of_mem_spScalars hz
  refine Subtype.ext ?_
  change glFieldEquiv (Fin r ⊕ Fin r) σ (z : GL (Fin r ⊕ Fin r) K) = (z : GL (Fin r ⊕ Fin r) K)
  rw [hc, glFieldEquiv_scalar, units_map_eq_of_sq_eq_one hc2]

@[expose] def subfieldProj (σ : K ≃+* K) :
    StatedSp r (descentField σ) →* StatedProj (StatedSp r K) :=
  (proj r K).comp (subfieldSpHom r (descentField σ))

theorem subfieldProj_apply (σ : K ≃+* K) (g : StatedSp r (descentField σ)) :
    subfieldProj σ g = proj r K (subfieldSpHom r (descentField σ) g) := rfl

theorem fieldAut_subfieldProj (σ : K ≃+* K) (g : StatedSp r (descentField σ)) :
    fieldAut r K σ (subfieldProj σ g) = subfieldProj σ g := by
  rw [subfieldProj_apply, fieldAut_proj, fieldSp_subfieldSpHom]

theorem fixed_iff_mem_range [NeZero r] {p : ℕ} (hp : Odd p) {σ : K ≃+* K} (hσp : σ ^ p = 1)
    (x : StatedProj (StatedSp r K)) :
    fieldAut r K σ x = x ↔ x ∈ (subfieldProj σ).range := by
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [fieldAut_proj] at hx
    have hw : g⁻¹ * fieldSp r K σ g ∈ spScalars r K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
    set w : StatedSp r K := g⁻¹ * fieldSp r K σ g with hwdef
    have hgw : fieldSp r K σ g = g * w := by rw [hwdef, mul_inv_cancel_left]
    have hfw : fieldSp r K σ w = w := fieldSp_eq_of_mem_spScalars σ hw
    have hw2 : w ^ 2 = 1 := sq_eq_one_of_mem_spScalars hw
    have hiter : ∀ n : ℕ, fieldSp r K (σ ^ n) g = g * w ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, hgw, map_pow, hfw, mul_assoc,
          ← pow_succ']
    have hwp : w ^ p = 1 := by
      have h1 := hiter p
      rw [hσp, map_one, MulAut.one_apply] at h1
      exact (mul_eq_left.mp h1.symm)
    obtain ⟨m, rfl⟩ := hp
    have hw1 : w = 1 := by
      have : w ^ (2 * m + 1) = w := by
        rw [pow_succ, pow_mul, hw2, one_pow, one_mul]
      rw [← this, hwp]
    have hfix : fieldSp r K σ g = g := by rw [hgw, hw1, mul_one]
    obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq hfix
    exact ⟨g₀, by rw [subfieldProj_apply, hg₀]⟩
  · rintro ⟨g₀, rfl⟩
    exact fieldAut_subfieldProj σ g₀

theorem spFixedGroup_fieldAut_eq_range [NeZero r] {p : ℕ} (hp : Odd p) {σ : K ≃+* K}
    (hσp : σ ^ p = 1) : spFixedGroup (fieldAut r K σ) = (subfieldProj σ).range :=
  Subgroup.ext fun x => fixed_iff_mem_range hp hσp x

theorem subfieldProj_eq_one_iff [NeZero r] (σ : K ≃+* K) (g₀ : StatedSp r (descentField σ)) :
    subfieldProj σ g₀ = 1 ↔ g₀ ∈ spScalars r (descentField σ) := by
  constructor
  · intro h
    have hz : subfieldSpHom r (descentField σ) g₀ ∈ spScalars r K := by
      rw [← ker_proj, MonoidHom.mem_ker]
      exact h
    obtain ⟨c, hc2, hc⟩ := exists_scalar_of_mem_spScalars hz
    have h1 : (c : K) * c = 1 := by
      have := congrArg Units.val hc2
      simpa [sq] using this
    have hck : (c : K) ∈ descentField σ := by
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact neg_mem (one_mem _)
    let d : (descentField σ)ˣ := Units.mk0 ⟨(c : K), hck⟩ (fun h0 => c.ne_zero (by
      simpa using congrArg Subtype.val h0))
    have hd2 : d ^ 2 = 1 := by
      refine Units.ext (Subtype.ext ?_)
      change (c : K) ^ 2 = 1
      rw [sq, h1]
    have hjd : subfieldSpHom r (descentField σ) (scalarSp d hd2) =
        subfieldSpHom r (descentField σ) g₀ := by
      refine Subtype.ext ?_
      rw [hc]
      change GeneralLinearGroup.map (descentField σ).subtype
        (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d) = _
      rw [GeneralLinearGroup.map_scalar]
      congr 1
      exact Units.ext rfl
    have := subfieldSpHom_injective (r := r) (descentField σ) hjd
    rw [← this]
    exact scalarSp_mem d hd2
  · intro hg
    obtain ⟨d, hd2, hd⟩ := exists_scalar_of_mem_spScalars hg
    have hdK : (Units.map (descentField σ).subtype.toMonoidHom d) ^ 2 = 1 := by
      rw [← map_pow, hd2, map_one]
    have hz : subfieldSpHom r (descentField σ) g₀ ∈ spScalars r K := by
      refine ⟨Units.map (descentField σ).subtype.toMonoidHom d, ?_⟩
      change GeneralLinearGroup.scalar (Fin r ⊕ Fin r) _ =
        GeneralLinearGroup.map (descentField σ).subtype (g₀ : GL (Fin r ⊕ Fin r) _)
      rw [hd, GeneralLinearGroup.map_scalar]
      rfl
    rw [subfieldProj_apply, ← MonoidHom.mem_ker, ker_proj]
    exact hz

@[expose] noncomputable def subfieldInj [NeZero r] (σ : K ≃+* K) :
    StatedProj (StatedSp r (descentField σ)) →* StatedProj (StatedSp r K) :=
  QuotientGroup.lift (spScalars r (descentField σ)) (subfieldProj σ)
    fun g hg => (subfieldProj_eq_one_iff (r := r) σ g).mpr hg

theorem subfieldInj_proj [NeZero r] (σ : K ≃+* K) (g : StatedSp r (descentField σ)) :
    subfieldInj σ (proj r (descentField σ) g) = subfieldProj σ g := rfl

theorem subfieldInj_injective [NeZero r] (σ : K ≃+* K) :
    Function.Injective (subfieldInj (r := r) σ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [subfieldInj_proj] at hx
  rw [← MonoidHom.mem_ker, ker_proj]
  exact (subfieldProj_eq_one_iff (r := r) σ g).mp hx

theorem range_subfieldInj [NeZero r] (σ : K ≃+* K) :
    (subfieldInj (r := r) σ).range = (subfieldProj (r := r) σ).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective y
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨proj r (descentField σ) g, rfl⟩

end CFSG.RankThree.PartOne.KCSpComm
