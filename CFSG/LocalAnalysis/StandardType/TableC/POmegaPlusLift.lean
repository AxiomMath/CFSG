module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal
open CFSG.StandardType.ClassicalPosition

private lemma o1p_spinMatrix_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)

private lemma o1p_conj_of_lift {F : Type} [Field F] [CharP F 2] {n : ℕ}
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadPlus n F) →* X)
    {d : X} {s₀ : spinGroup (Spin.quadPlus n F)}
    (hsl : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) s₀) d) :
    ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹) := by
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hsl u
  have h : u' = s₀ * u * s₀⁻¹ :=
    o1p_spinMatrix_injective F n (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  exact hu'ψ

private lemma o1p_spin_pow_eq_one {F : Type} [Field F] [CharP F 2] {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadPlus n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n F)))
    {d : X} {p : ℕ} (hdp : d ^ p = 1)
    {s₀ : spinGroup (Spin.quadPlus n F)}
    (hconj : ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹)) :
    s₀ ^ p = 1 := by
  have hinj := o1p_spinMatrix_injective F n
  have hsl : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) s₀) d := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hconj u⟩
  have hslp : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) (s₀ ^ p)) 1 := by
    have h := hsl.pow p
    rw [hdp, ← map_pow] at h
    exact h
  apply conj_eq_unique_POmegaPlus n F hn ψ hψ (s' := 1)
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hslp u
  have h : u' = (s₀ ^ p) * u * (s₀ ^ p)⁻¹ :=
    hinj (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  simpa using hu'ψ.symm

section POmegaPlusLift

theorem ggSixTCLiftPOmegaPlus_holds
    : GGSixTCLiftPOmegaPlus := by
  intro X _ _ k f ψ p G₀ B₁ D J L x hpos
  let F := GaloisField 2 f
  let n := k + 3
  let j : spinGroup (Spin.quadPlus n F) →* GL (Fin n ⊕ Fin n) F :=
    Spin.spinMatrix (Spin.quadPlus n F)
  let ψ' : spinGroup (Spin.quadPlus n F) →* X := ψ
  have hker : ψ'.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n F)) := hpos.ker_le
  have hrange : ψ'.range = G₀ := hpos.range_eq
  have hchoose : ∀ d : ↥D, ∃ s : spinGroup (Spin.quadPlus n F),
      ∀ u : spinGroup (Spin.quadPlus n F),
        (d : X)⁻¹ * ψ' u * (d : X) = ψ' (s * u * s⁻¹) := by
    intro d
    exact exists_conj_eq_POmegaPlus n F (by omega) ψ' hker
      (hpos.innerDiag (d : X) (hpos.D_le d.2))
  let g : ↥D → spinGroup (Spin.quadPlus n F) := fun d => Classical.choose (hchoose d)
  have hg : ∀ d : ↥D, ∀ u : spinGroup (Spin.quadPlus n F),
      (d : X)⁻¹ * ψ' u * (d : X) = ψ' (g d * u * (g d)⁻¹) :=
    fun d => Classical.choose_spec (hchoose d)
  have hiff : ∀ (s : spinGroup (Spin.quadPlus n F)) (b : X),
      IsGLLift j ψ' (j s) b ↔
        ∀ u : spinGroup (Spin.quadPlus n F), b⁻¹ * ψ' u * b = ψ' (s * u * s⁻¹) := by
    intro s b
    constructor
    · intro hs
      exact o1p_conj_of_lift ψ' hs
    · intro h u
      exact ⟨s * u * s⁻¹, by simp only [map_mul, map_inv], h u⟩
  have hg_lift : ∀ d : ↥D, IsGLLift j ψ' (j (g d)) (d : X) :=
    fun d => (hiff (g d) (d : X)).mpr (hg d)
  have hlift_unique : ∀ {b : X} {s s' : spinGroup (Spin.quadPlus n F)},
      IsGLLift j ψ' (j s) b → IsGLLift j ψ' (j s') b → s = s' := by
    intro b s s' hs hs'
    refine conj_eq_unique_POmegaPlus n F (by omega) ψ' hker (fun u => ?_)
    exact ((hiff s b).mp hs u).symm.trans ((hiff s' b).mp hs' u)
  have hone : g 1 = 1 := by
    refine conj_eq_unique_POmegaPlus n F (by omega) ψ' hker (fun u => ?_)
    exact (hg 1 u).symm.trans (by simp)
  have hmul : ∀ d d' : ↥D, g (d * d') = g d * g d' := by
    intro d d'
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hd'B : (d' : X) ∈ B₁ := hpos.D_le d'.2
    have hbb' : Commute (d : X) (d' : X) :=
      congrArg Subtype.val (hpos.elemAbelian.1.is_comm.comm ⟨(d : X), hdB⟩
        ⟨(d' : X), hd'B⟩)
    have hanti : g (d * d') = g d' * g d := by
      have h1 : IsGLLift j ψ' (j (g (d * d'))) ((d : X) * (d' : X)) := by
        simpa using hg_lift (d * d')
      have h2 : IsGLLift j ψ' (j (g d' * g d)) ((d : X) * (d' : X)) := by
        have h := IsGLLift.mul (hg_lift d) (hg_lift d')
        simpa only [map_mul] using h
      exact hlift_unique h1 h2
    have hcomm : g d' * g d = g d * g d' :=
      (conj_eq_commute_POmegaPlus n F (by omega) ψ' hker hbb' (hg d) (hg d')).eq.symm
    rw [hanti, hcomm]
  have hpow : ∀ d : ↥D, g d ^ p = 1 := by
    intro d
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    exact o1p_spin_pow_eq_one (n := n) (F := F) (by omega) ψ' hker
      (hpos.elemAbelian.2 (d : X) hdB) (hg d)
  let ℓ : ↥D →* spinGroup (Spin.quadPlus n F) :=
    { toFun := g, map_one' := hone, map_mul' := hmul }
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro d
    exact hg_lift d
  · intro d
    exact hpow d
  · have hJ : IsComponentOf J (ψ'.range ⊓ Subgroup.centralizer (D : Set X)) := by
      rw [hrange]
      exact hpos.J_comp
    have hlift : ∀ d ∈ D, ∃ s : GL (Fin n ⊕ Fin n) F,
        s ∈ j.range ∧ IsGLLift j ψ' s d := by
      intro d hd
      exact ⟨j (g ⟨d, hd⟩), ⟨g ⟨d, hd⟩, rfl⟩, hg_lift ⟨d, hd⟩⟩
    obtain ⟨J', hJ'comp, hJ'map⟩ :=
      StepA.exists_isComponentOf_comap_lift_of_isGLLift j (o1p_spinMatrix_injective F n) ψ'
        hker (fun s => s ∈ j.range) hJ hlift
    refine ⟨J', ?_, hJ'map⟩
    have hset : Set.range (fun d : ↥D => j (ℓ d)) =
        {s : GL (Fin n ⊕ Fin n) F | s ∈ j.range ∧
          ∃ d ∈ D, IsGLLift j ψ' s d} := by
      ext s
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨⟨g d, rfl⟩, (d : X), d.2, hg_lift d⟩
      · rintro ⟨hsP, d, hd, hsl⟩
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hsP
        have haeq : a = g ⟨d, hd⟩ := hlift_unique hsl (hg_lift ⟨d, hd⟩)
        refine ⟨⟨d, hd⟩, ?_⟩
        show j (g ⟨d, hd⟩) = j a
        rw [haeq]
    rw [hset]
    exact hJ'comp

end POmegaPlusLift

end CFSG.StandardType

end
