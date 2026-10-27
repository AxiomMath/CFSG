module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal
open CFSG.StandardType.ClassicalPosition

section POmegaMinusLift

theorem ggSixTCLiftPOmegaMinus_holds
    : GGSixTCLiftPOmegaMinus := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos
  let F := GaloisField 2 f
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let U := ↥(spinGroup Q)
  let j : U →* GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f) := Spin.spinMatrix Q
  let ψ' : U →* X := ψ
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 :=
    minusCoeffs_irr 2 f
  have hn4 : 4 ≤ n := (hpos.model.admissible).2.2
  have hker : ψ'.ker ≤ Subgroup.center U := hpos.ker_le
  have hrange : ψ'.range = G₀ := hpos.range_eq
  have hchar : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
  have hj : Function.Injective j := by
    change Function.Injective (Spin.spinMatrix Q)
    rw [← MonoidHom.ker_eq_bot_iff (Spin.spinMatrix Q)]
    have h := CFSG.LieType.Universal.Spin.ker_spinMatrix_quadMinus_eq_bot
      (n := n) (K := GaloisField 2 f) (b := (minusCoeffs 2 f).1)
      (c := (minusCoeffs 2 f).2) hirr hchar
    simpa only [Q] using h
  have hchoose : ∀ d : ↥D, ∃ s : U,
      ∀ u : U, (d : X)⁻¹ * ψ' u * (d : X) = ψ' (s * u * s⁻¹) := by
    intro d
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    exact exists_conj_eq_POmegaMinus n hirr hn4 ψ' hker (hpos.innerDiag (d : X) hdB)
  let f : ↥D → U := fun d => Classical.choose (hchoose d)
  have hf : ∀ d : ↥D, ∀ u : U,
      (d : X)⁻¹ * ψ' u * (d : X) = ψ' (f d * u * (f d)⁻¹) :=
    fun d => Classical.choose_spec (hchoose d)
  have hiff : ∀ (a : U) (b : X),
      IsGLLift j ψ' (j a) b ↔
        ∀ u : U, b⁻¹ * ψ' u * b = ψ' (a * u * a⁻¹) := by
    intro a b
    constructor
    · intro hs u
      obtain ⟨u', hu'j, hu'b⟩ := hs u
      have heq : u' = a * u * a⁻¹ := by
        apply hj
        simpa only [hu'j, map_mul, map_inv]
      rw [hu'b, heq]
    · intro h u
      exact ⟨a * u * a⁻¹, by simp [map_mul, map_inv], h u⟩
  have hlift_unique : ∀ {b : X} {a a' : U},
      IsGLLift j ψ' (j a) b → IsGLLift j ψ' (j a') b → a = a' := by
    intro b a a' ha ha'
    have h1 := (hiff a b).mp ha
    have h2 := (hiff a' b).mp ha'
    exact conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker (fun u => by rw [← h1 u, ← h2 u])
  have hf_lift : ∀ d : ↥D, IsGLLift j ψ' (j (f d)) (d : X) :=
    fun d => (hiff (f d) (d : X)).mpr (hf d)
  have hone : f 1 = 1 := by
    apply conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker
    intro u
    rw [← (hiff (f 1) (1 : X)).mp (hf_lift 1) u]
    simp
  have hmul : ∀ d d' : ↥D, f (d * d') = f d * f d' := by
    intro d d'
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hd'B : (d' : X) ∈ B₁ := hpos.D_le d'.2
    have hbb' : Commute (d : X) (d' : X) :=
      congrArg Subtype.val (hpos.elemAbelian.1.is_comm.comm ⟨(d : X), hdB⟩
        ⟨(d' : X), hd'B⟩)
    have hanti : f (d * d') = f d' * f d := by
      apply conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker
      intro u
      calc ψ' (f (d * d') * u * (f (d * d'))⁻¹)
          = ((d : X) * (d' : X))⁻¹ * ψ' u * ((d : X) * (d' : X)) :=
            (hf (d * d') u).symm
        _ = ((d' : X))⁻¹ * (((d : X))⁻¹ * ψ' u * (d : X)) * (d' : X) := by group
        _ = ((d' : X))⁻¹ * ψ' (f d * u * (f d)⁻¹) * (d' : X) := by rw [hf d u]
        _ = ψ' (f d' * (f d * u * (f d)⁻¹) * (f d')⁻¹) := hf d' _
        _ = ψ' ((f d' * f d) * u * (f d' * f d)⁻¹) := by congr 1; group
    have hcomm : f d' * f d = f d * f d' :=
      (conj_eq_commute_POmegaMinus n hirr hn4 ψ' hker hbb' (hf d) (hf d')).eq.symm
    rw [hanti, hcomm]
  have hpow : ∀ d : ↥D, f d ^ p = 1 := by
    intro d
    have hdB : (d : X) ∈ B₁ := hpos.D_le d.2
    have hdpow : (d : X) ^ p = 1 := hpos.elemAbelian.2 (d : X) hdB
    have hliftpow : IsGLLift j ψ' (j (f d ^ p)) ((d : X) ^ p) := by
      have h := (hf_lift d).pow p
      rwa [← map_pow] at h
    have hconj := (hiff (f d ^ p) ((d : X) ^ p)).mp hliftpow
    apply conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker
    intro u
    rw [← hconj u, hdpow]
    simp
  let ℓ : ↥D →* U :=
    { toFun := f, map_one' := hone, map_mul' := hmul }
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro d
    change IsGLLift j ψ' (j (f d)) (d : X)
    exact hf_lift d
  · intro d
    change f d ^ p = 1
    exact hpow d
  · have hJ : IsComponentOf J (ψ'.range ⊓ Subgroup.centralizer (D : Set X)) := by
      rw [hrange]
      exact hpos.J_comp
    have hlift : ∀ d ∈ D, ∃ s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
        s ∈ j.range ∧ IsGLLift j ψ' s d := by
      intro d hd
      exact ⟨j (f ⟨d, hd⟩), MonoidHom.mem_range.mpr ⟨f ⟨d, hd⟩, rfl⟩, hf_lift ⟨d, hd⟩⟩
    obtain ⟨J', hJ'comp, hJ'map⟩ :=
      StepA.exists_isComponentOf_comap_lift_of_isGLLift j hj ψ' hker
        (fun s => s ∈ j.range) hJ hlift
    refine ⟨J', ?_, hJ'map⟩
    have hset : Set.range (fun d : ↥D => j (ℓ d)) =
        {s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F |
          s ∈ j.range ∧ ∃ d ∈ D, IsGLLift j ψ' s d} := by
      ext s
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨MonoidHom.mem_range.mpr ⟨f d, rfl⟩, (d : X), d.2, hf_lift d⟩
      · rintro ⟨hsP, d, hd, hsl⟩
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hsP
        have hsl' : IsGLLift j ψ' (j a) d := ha.symm ▸ hsl
        have heq : a = f ⟨d, hd⟩ := hlift_unique hsl' (hf_lift ⟨d, hd⟩)
        refine ⟨⟨d, hd⟩, ?_⟩
        change j (f ⟨d, hd⟩) = s
        simpa only [← heq, ha]
    rw [hset]
    exact hJ'comp

end POmegaMinusLift

end CFSG.StandardType

end
