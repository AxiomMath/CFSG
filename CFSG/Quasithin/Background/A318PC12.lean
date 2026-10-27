module

public import CFSG.Quasithin.Background.A318PC10
public import CFSG.Quasithin.Background.A318PC11

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open Matrix

section Linear

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K] {p f : ℕ}
  {e : ↥S ≃* slPi true 3 (p ^ f) K}

theorem eq_of_descendAut_eq [Group.IsPerfect (SpecialLinearGroup (Fin 3) K)]
    {β γ : MulAut (SpecialLinearGroup (Fin 3) K)} (h : descendAut 3 K γ = descendAut 3 K β) :
    β = γ := by
  apply mulAut_eq_of_inv_mul_mem_center
  intro g
  rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    ← descendAut_proj, ← descendAut_proj, h]

variable (e) in
@[expose] noncomputable def phiLin : X →* MulAut (projectiveSL 3 K) :=
  (descendAut 3 K).comp ((MulAut.congr (slPiTrueEquiv (p ^ f) K)).toMonoidHom.comp
    ((slAct e).comp (toNormalizer S)))

theorem phiLin_apply (g : X) :
    phiLin e g = descendAut 3 K (MulAut.congr (slPiTrueEquiv (p ^ f) K)
      (slAct e ⟨g, mem_normalizer_of_normal g⟩)) :=
  rfl

theorem toGL_beta (g : X) (s : slPi true 3 (p ^ f) K) :
    Matrix.SpecialLinearGroup.toGL (MulAut.congr (slPiTrueEquiv (p ^ f) K)
        (slAct e ⟨g, mem_normalizer_of_normal g⟩) (slPiTrueEquiv (p ^ f) K s)) =
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    toGL_slPiTrueEquiv]

theorem phiLin_of_isPGLAt {h : X} {A : GL (Fin 3) K} (hA : IsPGLAt e h A) :
    phiLin e h = conjAut 3 K A := by
  have hβ : MulAut.congr (slPiTrueEquiv (p ^ f) K) (slAct e ⟨h, mem_normalizer_of_normal h⟩) =
      slConjugation 3 K A := by
    refine MulEquiv.ext fun s => ?_
    apply Matrix.SpecialLinearGroup.toGL_injective
    have h1 := toGL_beta (e := e) h ((slPiTrueEquiv (p ^ f) K).symm s)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := toGL_slPiTrueEquiv (q := p ^ f) ((slPiTrueEquiv (p ^ f) K).symm s)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h1, hA.2, toGL_slConjugation, ← h2]
  rw [phiLin_apply, hβ]
  rfl

theorem slAct_eq_frobGL_of_phiLin_eq [Group.IsPerfect ↥S] {g : X} {σ : K ≃+* K}
    (hg : phiLin e g = fieldAut 3 K σ) (s : slPi true 3 (p ^ f) K) :
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
      frobGL σ s := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    Group.IsPerfect.ofSurjective (f := (e.trans (slPiTrueEquiv (p ^ f) K)).toMonoidHom)
      (e.trans (slPiTrueEquiv (p ^ f) K)).surjective
  have h1 : descendAut 3 K (CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ) =
      descendAut 3 K (MulAut.congr (slPiTrueEquiv (p ^ f) K)
        (slAct e ⟨g, mem_normalizer_of_normal g⟩)) := hg.symm
  have h2 := eq_of_descendAut_eq h1
  rw [← toGL_beta (e := e) g s, h2, toGL_slFieldAut, toGL_slPiTrueEquiv]

theorem slAct_eq_self_of_phiLin_eq_one [Group.IsPerfect ↥S] {g : X} (hg : phiLin e g = 1)
    (s : slPi true 3 (p ^ f) K) : slAct e ⟨g, mem_normalizer_of_normal g⟩ s = s := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    Group.IsPerfect.ofSurjective (f := (e.trans (slPiTrueEquiv (p ^ f) K)).toMonoidHom)
      (e.trans (slPiTrueEquiv (p ^ f) K)).surjective
  have h1 : descendAut 3 K (1 : MulAut (SpecialLinearGroup (Fin 3) K)) =
      descendAut 3 K (MulAut.congr (slPiTrueEquiv (p ^ f) K)
        (slAct e ⟨g, mem_normalizer_of_normal g⟩)) := by
    rw [map_one]
    exact hg.symm
  have h2 := eq_of_descendAut_eq h1
  apply Subtype.ext
  rw [← toGL_beta (e := e) g s, h2, MulAut.one_apply, toGL_slPiTrueEquiv]

end Linear

section ThreeElements

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ}

theorem three_elements_mem_sup_linear
    (hQ : CFSG.IsQuasisimple ↥S) (hS2 : 2 ≤ CFSG.Open.pRank 3 S)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (hK : PiField true p f K)
    (hq : ModThree true (p ^ f)) (hq2 : 2 < p ^ f) (e : ↥S ≃* slPi true 3 (p ^ f) K)
    (hZ : Nat.card (Subgroup.center ↥S) = 3) (hP : CFSG.pPrimeCore 3 X = ⊥) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S) :
    ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x := by
  classical
  have := hK.finite
  have : Group.IsPerfect ↥S := hQ.1
  have hCS := centralizer_le_S_native hQ hS2 hX hK hq hq2 e hZ hP hx hxS
  obtain ⟨y, hxy, hy3, -, hnon, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have h3 : 3 ∣ Nat.card K - 1 := by
    have h1 : Nat.card K = p ^ f := hK.card
    have h2 : p ^ f % 3 = 1 := hq
    omega
  have hAle : S ⊔ Subgroup.zpowers x ≤ pglSubgroup e :=
    sup_le (fun s hs => ⟨_, isPGLAt_of_mem e hπ hs⟩) (Subgroup.zpowers_le.2 ⟨y, hxy⟩)
  refine three_elements_mem_of_frame (l3FrameLinear h3) (phiLin e) ?_ ?_ ?_ ?_
  · intro h hh
    obtain ⟨A, hA⟩ := hAle hh
    exact mem_linearAutGroup_iff.2 ⟨A, (phiLin_of_isPGLAt hA).symm⟩
  · intro d hd
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hd
    obtain ⟨a, haA, ha⟩ := exists_lift_mem_sup hK hq hxy hnon (mem_glPi_true _ A)
    exact ⟨a, haA, phiLin_of_isPGLAt ha⟩
  · intro g hg
    have h1 := slAct_eq_self_of_phiLin_eq_one hg
    have hgC : g ∈ S := hCS g fun t ht => by
      have h2 := conj_eq_of_slAct_eq e g (e ⟨t, ht⟩) (h1 _)
      have h3' : ((e.symm (e ⟨t, ht⟩) : ↥S) : X) = t := by rw [MulEquiv.symm_apply_apply]
      rw [h3'] at h2
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h2]
    exact Subgroup.mem_sup_left hgC
  · intro g c hc hΦ hgH
    have hΦ' : phiLin e g = fieldAut 3 K c := hΦ
    exact false_of_pure_field hQ hS2 hX hK hq hq2 e hZ hCS hx hxS hc
      (slAct_eq_frobGL_of_phiLin_eq hΦ') hgH

end ThreeElements

end A318P

end CFSG.Quasithin
