module

public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.AxisCount.CoverLetters
public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public meta import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public meta import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public meta import CFSG.Monster.Existence.TwoPoint.HNRigid
public meta import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs
public import Certificates.Certificate6091
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public meta import CFSG.Open.MonsterY443Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.AxisCount

theorem validB_of_isVis {g : Native.Gen} (h : g.isVis = true) : g.validB = true := by
  cases g <;> simp_all [Native.Gen.isVis, Native.Gen.validB]

theorem wordLin_eq_of_visConjCheck
    {w₁ w₂ : List Native.Gen} (h : visConjCheck w₁ w₂ = true) :
    wordLin w₁ = wordLin w₂ := by
  unfold visConjCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, hc⟩ := h
  have hv' : ∀ g ∈ w₁ ++ w₂, g.isVis = true := fun g hg => List.all_eq_true.1 hv g hg
  refine wordLin_eq_of_checkP2
    (fun g hg => Native.Gen.ne_tau_of_isVis (hv' g (List.mem_append_left _ hg)))
    (fun g hg => Native.Gen.ne_tau_of_isVis (hv' g (List.mem_append_right _ hg))) ?_ hc
  exact List.all_eq_true.2 fun g hg => validB_of_isVis (hv' g hg)

theorem all_isVis_left_of_visConjCheck {w₁ w₂ : List Native.Gen} (h : visConjCheck w₁ w₂ = true) :
    w₁.all Native.Gen.isVis = true := by
  unfold visConjCheck at h
  rw [Bool.and_eq_true] at h
  have := h.1
  simp only [List.all_append, Bool.and_eq_true] at this
  exact this.1

theorem mem_cent_xGriess_of_word {w : List Native.Gen} (hw : ∀ g ∈ w, ¬ g = .tau)
    {e : MGriess} (he : e.val = wordLin w) : e ∈ cent xGriess := by
  have h := wordLin_mem_Gvis w hw
  rw [← map_cent_xGriess] at h
  obtain ⟨u, hu, hu'⟩ := h
  have e' : u = e := Subtype.ext (hu'.trans he.symm)
  rwa [← e']

theorem trace_order_of_conj {X K M : SpaceB ≃ₗ[ℚ] SpaceB} (hKX : K * X = M * K)
    (hM3 : M * M * M = 1) {T : ℚ}
    (hT : LinearMap.trace ℚ SpaceB (M : SpaceB →ₗ[ℚ] SpaceB) = T) (hT' : T ≠ 196884) :
    LinearMap.trace ℚ SpaceB (X : SpaceB →ₗ[ℚ] SpaceB) = T ∧ X * X * X = 1 ∧ X ≠ 1 := by
  have hX : K * X * K⁻¹ = M := by rw [hKX, mul_inv_cancel_right]
  have hX' : X = K⁻¹ * M * K := by
    rw [← hX]; group
  refine ⟨?_, ?_, ?_⟩
  · rw [← hT, ← hX]
    exact (CFSG.Monster.B.trace_conj K X).symm
  · rw [hX']
    calc K⁻¹ * M * K * (K⁻¹ * M * K) * (K⁻¹ * M * K) = K⁻¹ * (M * M * M) * K := by group
      _ = 1 := by rw [hM3]; group
  · intro h1
    rw [h1] at hX
    have h2 : M = 1 := by rw [← hX]; group
    rw [h2] at hT
    have h3 : LinearMap.trace ℚ SpaceB
        (((1 : SpaceB ≃ₗ[ℚ] SpaceB)) : SpaceB →ₗ[ℚ] SpaceB) = 196884 := by
      show LinearMap.trace ℚ SpaceB LinearMap.id = _
      rw [LinearMap.trace_id, finrank_B]
      rfl
    rw [h3] at hT
    exact hT' hT.symm

theorem orderOf_three_of_cube {x : MGriess} (h3 : x.val * x.val * x.val = 1) (h1 : x.val ≠ 1) :
    orderOf x = 3 := by
  have := Fact.mk Nat.prime_three
  refine orderOf_eq_prime ?_ fun h => h1 (by rw [h]; rfl)
  refine Subtype.ext ?_
  show x.val ^ 3 = 1
  rw [pow_succ, pow_two]
  exact h3

theorem valid_permMonoA : Native.permValid permMonoA = true :=
  Certificates.certificate6091.1

theorem check_conjA :
    wordLin (wordThreeA ++ wordKA) = wordLin (wordKA ++ wordMonoA) :=
  Certificates.certificate6091.2.1

theorem check_cubeA :
    wordLin (wordMonoA ++ wordMonoA ++ wordMonoA) = 1 :=
  Certificates.certificate6091.2.2.1

theorem check_traceA : permTraceCheck permMonoA 783 = true :=
  Certificates.certificate6091.2.2.2.1

theorem trace_wordMonoA :
    LinearMap.trace ℚ SpaceB
      ((wordLin wordMonoA : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 783 := by
  have h := trace_wordLin_perm valid_permMonoA check_traceA
  exact_mod_cast h

theorem conj_relA :
    wordLin wordKA * wordLin wordThreeA = wordLin wordMonoA * wordLin wordKA := by
  have h := check_conjA
  rwa [wordLin_append, wordLin_append] at h

theorem cube_monoA :
    wordLin wordMonoA * wordLin wordMonoA * wordLin wordMonoA = 1 := by
  have h := check_cubeA
  simpa [wordLin_append, mul_assoc] using h

theorem threeDataA :
    LinearMap.trace ℚ SpaceB (wordLin wordThreeA : SpaceB →ₗ[ℚ] SpaceB) = 783 ∧
      wordLin wordThreeA * wordLin wordThreeA * wordLin wordThreeA = 1 ∧
      wordLin wordThreeA ≠ 1 :=
  trace_order_of_conj conj_relA cube_monoA trace_wordMonoA (by norm_num)

theorem trace_threeARep :
    LinearMap.trace ℚ SpaceB ((threeARep.val : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 783 :=
  (threeDataA).1

theorem threeARep_mem_cent_xGriess : threeARep ∈ cent xGriess :=
  mem_cent_xGriess_of_word (fun g hg h => by subst h; simp [wordThreeA] at hg) rfl

theorem orderOf_threeARep :
    orderOf threeARep = 3 :=
  orderOf_three_of_cube (threeDataA).2.1 (threeDataA).2.2

theorem valid_permMonoC : Native.permValid permMonoC = true :=
  Certificates.certificate6091.2.2.2.2.1

theorem check_conjC :
    wordLin (wordThreeC ++ wordKC) = wordLin (wordKC ++ wordMonoC) :=
  Certificates.certificate6091.2.2.2.2.2.1

theorem check_cubeC :
    wordLin (wordMonoC ++ wordMonoC ++ wordMonoC) = 1 :=
  Certificates.certificate6091.2.2.2.2.2.2.1

theorem check_traceC : permTraceCheck permMonoC 0 = true :=
  Certificates.certificate6091.2.2.2.2.2.2.2

theorem trace_wordMonoC :
    LinearMap.trace ℚ SpaceB
      ((wordLin wordMonoC : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 0 := by
  have h := trace_wordLin_perm valid_permMonoC check_traceC
  exact_mod_cast h

theorem conj_relC :
    wordLin wordKC * wordLin wordThreeC = wordLin wordMonoC * wordLin wordKC := by
  have h := check_conjC
  rwa [wordLin_append, wordLin_append] at h

theorem cube_monoC :
    wordLin wordMonoC * wordLin wordMonoC * wordLin wordMonoC = 1 := by
  have h := check_cubeC
  simpa [wordLin_append, mul_assoc] using h

theorem threeDataC :
    LinearMap.trace ℚ SpaceB (wordLin wordThreeC : SpaceB →ₗ[ℚ] SpaceB) = 0 ∧
      wordLin wordThreeC * wordLin wordThreeC * wordLin wordThreeC = 1 ∧
      wordLin wordThreeC ≠ 1 :=
  trace_order_of_conj conj_relC cube_monoC trace_wordMonoC (by norm_num)

theorem trace_threeCRep :
    LinearMap.trace ℚ SpaceB ((threeCRep.val : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 0 :=
  (threeDataC).1

theorem threeCRep_mem_cent_xGriess : threeCRep ∈ cent xGriess :=
  mem_cent_xGriess_of_word (fun g hg h => by subst h; simp [wordThreeC] at hg) rfl

theorem orderOf_threeCRep :
    orderOf threeCRep = 3 :=
  orderOf_three_of_cube (threeDataC).2.1 (threeDataC).2.2


end CFSG.Monster.Existence
