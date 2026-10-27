module

public import CFSG.Quasithin.Background.A318PC10
public import CFSG.Quasithin.Background.A318PC11
public import CFSG.Quasithin.Background.A318PL3Unit

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section Unitary

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K] {p f : ℕ}
  {h : UnitaryFieldData p f K} {hq2 : 2 < p ^ f} {e : ↥S ≃* slPi false 3 (p ^ f) K}

theorem eq_of_centerDescend_eq [Group.IsPerfect (unitarySU p f K 3)]
    {β γ : MulAut (unitarySU p f K 3)}
    (hβγ : MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ) =
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β)) : β = γ := by
  have hγ' : centerDescend _ γ = centerDescend _ β := (MulAut.congr _).injective hβγ
  apply mulAut_eq_of_inv_mul_mem_center
  intro g
  have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
    τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) hγ'
  simp only [centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1

variable (h hq2 e) in
@[expose] noncomputable def phiUni : X →* MulAut (unitaryPSU h 3) :=
  (MulAut.congr (suCenterEquiv h hq2)).toMonoidHom.comp ((centerDescend _).comp
    ((MulAut.congr (slPiFalseEquiv p f K)).toMonoidHom.comp ((slAct e).comp (toNormalizer S))))

theorem phiUni_apply (g : X) :
    phiUni h hq2 e g = MulAut.congr (suCenterEquiv h hq2) (centerDescend _
      (MulAut.congr (slPiFalseEquiv p f K) (slAct e ⟨g, mem_normalizer_of_normal g⟩))) :=
  rfl

theorem coe_beta_uni (g : X) (s : slPi false 3 (p ^ f) K) :
    ((MulAut.congr (slPiFalseEquiv p f K) (slAct e ⟨g, mem_normalizer_of_normal g⟩)
        (slPiFalseEquiv p f K s) : unitarySU p f K 3) : GL (Fin 3) K) =
      ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi false 3 (p ^ f) K) : GL (Fin 3) K) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem phiUni_of_isPGLAt {g : X} (A : unitaryIsom3 h)
    (hA : IsPGLAt e g (A : GL (Fin 3) K)) : phiUni h hq2 e g = psuConj h A := by
  have hβ : MulAut.congr (slPiFalseEquiv p f K) (slAct e ⟨g, mem_normalizer_of_normal g⟩) =
      suConj h A := by
    refine MulEquiv.ext fun s => ?_
    apply Subtype.ext
    have h1 := coe_beta_uni (e := e) g ((slPiFalseEquiv p f K).symm s)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (((slPiFalseEquiv p f K).symm s : slPi false 3 (p ^ f) K) : GL (Fin 3) K) =
        (s : GL (Fin 3) K) := by
      have := coe_slPiFalseEquiv (p := p) (f := f) (K := K) ((slPiFalseEquiv p f K).symm s)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, hA.2, coe_suConj, h2]
    rfl
  rw [phiUni_apply, hβ]
  exact congr_centerDescend_suConj h hq2 A

theorem slAct_eq_frobGL_of_phiUni_eq [Group.IsPerfect ↥S] {g : X} {σ : K ≃+* K}
    (hg : phiUni h hq2 e g = psuField h σ) (s : slPi false 3 (p ^ f) K) :
    ((slAct e ⟨g, mem_normalizer_of_normal g⟩ s : slPi false 3 (p ^ f) K) : GL (Fin 3) K) =
      frobGL σ s := by
  have hperf : Group.IsPerfect (unitarySU p f K 3) :=
    Group.IsPerfect.ofSurjective (f := (e.trans (slPiFalseEquiv p f K)).toMonoidHom)
      (e.trans (slPiFalseEquiv p f K)).surjective
  have h1 : MulAut.congr (suCenterEquiv h hq2) (centerDescend _ (suField h σ)) =
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _
        (MulAut.congr (slPiFalseEquiv p f K) (slAct e ⟨g, mem_normalizer_of_normal g⟩))) := by
    rw [congr_centerDescend_suField h hq2 σ]
    exact hg.symm
  have h2 := eq_of_centerDescend_eq h1
  rw [← coe_beta_uni (e := e) g s, h2, coe_suField, glAut_eq_frobGL]
  rfl

theorem slAct_eq_self_of_phiUni_eq_one [Group.IsPerfect ↥S] {g : X} (hg : phiUni h hq2 e g = 1)
    (s : slPi false 3 (p ^ f) K) : slAct e ⟨g, mem_normalizer_of_normal g⟩ s = s := by
  have hperf : Group.IsPerfect (unitarySU p f K 3) :=
    Group.IsPerfect.ofSurjective (f := (e.trans (slPiFalseEquiv p f K)).toMonoidHom)
      (e.trans (slPiFalseEquiv p f K)).surjective
  have h1 : MulAut.congr (suCenterEquiv h hq2) (centerDescend _
        (1 : MulAut (unitarySU p f K 3))) =
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _
        (MulAut.congr (slPiFalseEquiv p f K) (slAct e ⟨g, mem_normalizer_of_normal g⟩))) := by
    rw [map_one, map_one]
    exact hg.symm
  have h2 := eq_of_centerDescend_eq h1
  apply Subtype.ext
  rw [← coe_beta_uni (e := e) g s, h2, MulAut.one_apply]
  rfl

end Unitary

section ThreeElements

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal] {K : Type} [Field K]
  {p f : ℕ}

theorem three_elements_mem_sup_unitary
    (hQ : CFSG.IsQuasisimple ↥S)
    (hS2 : 2 ≤ CFSG.Open.pRank 3 S) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hK : PiField false p f K) (hq : ModThree false (p ^ f)) (hq2 : 2 < p ^ f)
    (e : ↥S ≃* slPi false 3 (p ^ f) K) (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hP : CFSG.pPrimeCore 3 X = ⊥) {x : X} (hx : orderOf x = 3) (hxS : x ∉ S) :
    ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x := by
  classical
  have := hK.finite
  have : Group.IsPerfect ↥S := hQ.1
  have hU : UnitaryFieldData p f K := hK.unitary
  have hCS := centralizer_le_S_native hQ hS2 hX hK hq hq2 e hZ hP hx hxS
  obtain ⟨y, hxy, hy3, -, hnon, -, -⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
  have hπ : false = false → UnitaryFieldData p f K := fun _ => hU
  have h3 : 3 ∣ p ^ f + 1 := by
    have h2 : p ^ f % 3 = 2 := hq
    omega
  have hAle : S ⊔ Subgroup.zpowers x ≤ pglSubgroup e :=
    sup_le (fun s hs => ⟨_, isPGLAt_of_mem e hπ hs⟩) (Subgroup.zpowers_le.2 ⟨y, hxy⟩)
  refine three_elements_mem_of_frame (l3FramePSU hU hq2 h3) (phiUni hU hq2 e) ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨A, hA⟩ := hAle hg
    have hAU : A ∈ unitaryIsom3 hU := (mem_glPi_false hU).1 hA.1
    exact ⟨⟨A, hAU⟩, (phiUni_of_isPGLAt ⟨A, hAU⟩ hA).symm⟩
  · intro d hd
    obtain ⟨A, rfl⟩ := hd
    obtain ⟨a, haA, ha⟩ := exists_lift_mem_sup hK hq hxy hnon
      ((mem_glPi_false hU).2 ((mem_unitaryIsom3 (h := hU)).1 A.2))
    exact ⟨a, haA, phiUni_of_isPGLAt A ha⟩
  · intro g hg
    have h1 := slAct_eq_self_of_phiUni_eq_one hg
    have hgC : g ∈ S := hCS g fun t ht => by
      have h2 := conj_eq_of_slAct_eq e g (e ⟨t, ht⟩) (h1 _)
      have h3' : ((e.symm (e ⟨t, ht⟩) : ↥S) : X) = t := by rw [MulEquiv.symm_apply_apply]
      rw [h3'] at h2
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h2]
    exact Subgroup.mem_sup_left hgC
  · intro g c hc hΦ hgH
    have hΦ' : phiUni hU hq2 e g = psuField hU c := hΦ
    exact false_of_pure_field hQ hS2 hX hK hq hq2 e hZ hCS hx hxS hc
      (slAct_eq_frobGL_of_phiUni_eq hΦ') hgH

end ThreeElements

end A318P

end CFSG.Quasithin
