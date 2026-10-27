module

public import CFSG.LocalAnalysis.StandardType.TableC.PSpLeafDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition

section PSpLift

theorem ggSixTCLiftPSp_holds
    : GGSixTCLiftPSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos
  let F := GaloisField 2 f
  let ψ' : ↥(StatedSp n F) →* X := ψ
  have hker : ψ'.ker ≤ Subgroup.center ↥(StatedSp n F) := hpos.ker_le
  have hrange : ψ'.range = G₀ := hpos.range_eq
  have hchoose : ∀ d : ↥D, ∃ s : ↥(StatedSp n F),
      ∀ u : ↥(StatedSp n F), (d : X)⁻¹ * ψ' u * (d : X) = ψ' (s * u * s⁻¹) := by
    intro d
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hbN : (d : X) ∈ Subgroup.normalizer (ψ'.range : Set X) := by
      rw [hrange]
      exact hpos.le_N_G0 hdB
    exact exists_conj_eq_PSp n F ψ' hker hbN (hpos.innerDiag (d : X) hdB)
  let f : ↥D → ↥(StatedSp n F) := fun d => Classical.choose (hchoose d)
  have hf : ∀ d : ↥D, ∀ u : ↥(StatedSp n F),
      (d : X)⁻¹ * ψ' u * (d : X) = ψ' (f d * u * (f d)⁻¹) :=
    fun d => Classical.choose_spec (hchoose d)
  have hiff : ∀ (s : ↥(StatedSp n F)) (b : X),
      IsGLLift (StatedSp n F).subtype ψ' (s : GL (Fin n ⊕ Fin n) F) b ↔
        ∀ u : ↥(StatedSp n F), b⁻¹ * ψ' u * b = ψ' (s * u * s⁻¹) := by
    intro s b
    constructor
    · intro hs u
      obtain ⟨u', hu'j, hu'b⟩ := hs u
      have heq : u' = s * u * s⁻¹ := by
        apply Subgroup.subtype_injective
        rw [hu'j]
        simp
      rw [hu'b, heq]
    · intro h u
      exact ⟨s * u * s⁻¹, by simp, h u⟩
  have hlift_unique : ∀ {b : X} {s s' : GL (Fin n ⊕ Fin n) F},
      s ∈ StatedSp n F → s' ∈ StatedSp n F →
      IsGLLift (StatedSp n F).subtype ψ' s b →
      IsGLLift (StatedSp n F).subtype ψ' s' b → s = s' := by
    intro b s s' hsP hs'P hs hs'
    have h1 := (hiff ⟨s, hsP⟩ b).mp hs
    have h2 := (hiff ⟨s', hs'P⟩ b).mp hs'
    have heq : (⟨s, hsP⟩ : ↥(StatedSp n F)) = ⟨s', hs'P⟩ :=
      conj_eq_unique_PSp n F ψ' hker (fun u => by rw [← h1 u, ← h2 u])
    exact congrArg Subtype.val heq
  have hf_lift : ∀ d : ↥D,
      IsGLLift (StatedSp n F).subtype ψ' (f d : GL (Fin n ⊕ Fin n) F) (d : X) :=
    fun d => (hiff (f d) (d : X)).mpr (hf d)
  have hone : f 1 = 1 :=
    Subtype.ext (hlift_unique (f 1).2 (Subgroup.one_mem _) (hf_lift 1) isGLLift_one)
  have hmul : ∀ d d' : ↥D, f (d * d') = f d * f d' := by
    intro d d'
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hd'B : (d' : X) ∈ B₁ := hpos.D_le d'.2
    have hbb' : Commute (d : X) (d' : X) :=
      congrArg Subtype.val (hpos.elemAbelian.1.is_comm.comm ⟨(d : X), hdB⟩
        ⟨(d' : X), hd'B⟩)
    have hanti : f (d * d') = f d' * f d :=
      Subtype.ext (hlift_unique (f (d * d')).2 (Subgroup.mul_mem _ (f d').2 (f d).2)
        (hf_lift (d * d')) (IsGLLift.mul (hf_lift d) (hf_lift d')))
    have hcomm : f d' * f d = f d * f d' :=
      (conj_eq_commute_PSp n F ψ' hker hbb' (hf d) (hf d')).eq.symm
    rw [hanti, hcomm]
  have hpow : ∀ d : ↥D, (f d : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    intro d
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hdpow : (d : X) ^ p = 1 := hpos.elemAbelian.2 (d : X) hdB
    have hslpow : IsGLLift (StatedSp n F).subtype ψ'
        ((f d : GL (Fin n ⊕ Fin n) F) ^ p) 1 := by
      have h := (hf_lift d).pow p
      rwa [hdpow] at h
    exact hlift_unique (Subgroup.pow_mem _ (f d).2 p) (Subgroup.one_mem _)
      hslpow isGLLift_one
  let ℓ : ↥D →* ↥(StatedSp n F) :=
    { toFun := f, map_one' := hone, map_mul' := hmul }
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro d
    change IsGLLift (StatedSp n F).subtype ψ (f d : GL (Fin n ⊕ Fin n) F) (d : X)
    exact hf_lift d
  · intro d
    change (f d : GL (Fin n ⊕ Fin n) F) ^ p = 1
    exact hpow d
  · have hJ : IsComponentOf J (ψ'.range ⊓ Subgroup.centralizer (D : Set X)) := by
      rw [hrange]
      exact hpos.J_comp
    have hlift : ∀ d ∈ D, ∃ s : GL (Fin n ⊕ Fin n) F,
        s ∈ StatedSp n F ∧ IsGLLift (StatedSp n F).subtype ψ' s d := by
      intro d hd
      exact ⟨(f ⟨d, hd⟩ : GL (Fin n ⊕ Fin n) F), (f ⟨d, hd⟩).2,
        (hiff (f ⟨d, hd⟩) d).mpr (hf ⟨d, hd⟩)⟩
    obtain ⟨J', hJ'comp, hJ'map⟩ :=
      StepA.exists_isComponentOf_comap_lift_of_isGLLift (StatedSp n F).subtype
        (Subgroup.subtype_injective (StatedSp n F)) ψ' hker
        (fun s => s ∈ StatedSp n F) hJ hlift
    refine ⟨J', ?_, hJ'map⟩
    have hset : Set.range (fun d : ↥D => (ℓ d : GL (Fin n ⊕ Fin n) F)) =
        {s : GL (Fin n ⊕ Fin n) F | s ∈ StatedSp n F ∧
          ∃ d ∈ D, IsGLLift (StatedSp n F).subtype ψ' s d} := by
      ext s
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨(f d).2, (d : X), d.2, hf_lift d⟩
      · rintro ⟨hsP, d, hd, hsl⟩
        exact ⟨⟨d, hd⟩, hlift_unique (f ⟨d, hd⟩).2 hsP (hf_lift ⟨d, hd⟩) hsl⟩
    rw [hset]
    exact hJ'comp

end PSpLift

end CFSG.StandardType

end
