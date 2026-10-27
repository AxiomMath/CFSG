module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.Timmesfeld.ARS.CaseEWeight
import CFSG.LocalAnalysis.StandardType.GGRankOneTorus
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerTorus
import CFSG.LieType.Steinberg.BruhatWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.Timmesfeld.ARS

private theorem coroot_torusElt_mem_sup {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (j : Fin D.rank) (s : kˣ) :
    PsiDiag.torusElt x j s ∈ D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1) := by
  have h1 : ∀ c, x (Pi.single j 1) c ∈
      D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1) := fun c =>
    Subgroup.mem_sup_left (((hE.param _ (single_mem_roots j)).1 _).mpr ⟨c, rfl⟩)
  have h2 : ∀ c, x (-Pi.single j 1) c ∈
      D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1) := fun c =>
    Subgroup.mem_sup_right (((hE.param _ (neg_single_mem_roots j)).1 _).mpr ⟨c, rfl⟩)
  have hw : ∀ t : kˣ, weylElement x j t ∈
      D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1) := fun t =>
    mul_mem (mul_mem (h1 _) (h2 _)) (h1 _)
  exact mul_mem (hw s) (inv_mem (hw 1))

theorem ggKGCent_exists_coroot {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hE : ChevalleyExtras D k x C O) (hdiv : D.divisible = ∅)
    (hsymm : ∀ i j, D.cartan i j = D.cartan j i) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ t : kˣ →* K, (∀ s, t s ∈ ggTorus D) ∧
      (∀ s, t s ∈ D.rootGroup β ⊔ D.rootGroup (-β)) ∧
      ∀ s, ∀ γ ∈ D.roots, ∀ z ∈ D.rootGroup γ,
        (s ^ cartanPair D.cartan β γ = 1 → t s * z * (t s)⁻¹ = z) ∧
        (t s * z * (t s)⁻¹ = z → s ^ cartanPair D.cartan β γ = 1 ∨ z = 1) := by
  have hβ' : β ∈ roots D.isFiniteType ∅ := hdiv ▸ hβ
  obtain ⟨w, j, hwj⟩ : ∃ (w : (coxeterMatrix D.isFiniteType).Group) (j : Fin D.rank),
      β = weylAction D.isFiniteType w (Pi.single j 1) := by
    rcases hβ' with h | ⟨w, j, hj, -⟩
    · exact h
    · exact absurd hj (Set.notMem_empty j)
  subst hwj
  obtain ⟨m, hm⟩ : ∃ m : K, ActsAs D m w := ⟨_, actsAs_nrep hct w⟩
  obtain ⟨φ, -, hu, hl⟩ := hE.rankOne j
  obtain ⟨t, ht⟩ : ∃ t : kˣ →* K, ∀ s, t s = m * PsiDiag.torusElt x j s * m⁻¹ :=
    ⟨(MulAut.conj m).toMonoidHom.comp
      (MonoidHom.mk' (PsiDiag.torusElt x j) (ggRootKer_torusElt_mul hE j)), fun s => rfl⟩
  refine ⟨t, fun s => ?_, fun s => ?_, fun s γ hγ z hz => ?_⟩
  · rw [ht]
    refine ggStdPos_conj_mem_ggTorus_of_actsAs ?_ hm
    rw [RankOneXfer.torusElt_eq_map_sl2Diag j φ hu hl s]
    exact RankOneXfer.map_sl2Diag_mem_ggTorus hE j φ hu hl s
  · have hS : (D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1)).map
        (MulAut.conj m).toMonoidHom =
        D.rootGroup (weylAction D.isFiniteType w (Pi.single j 1)) ⊔
          D.rootGroup (-weylAction D.isFiniteType w (Pi.single j 1)) := by
      rw [Subgroup.map_sup, hm _ (single_mem_roots j), hm _ (neg_single_mem_roots j), map_neg]
    rw [ht, ← hS]
    exact Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom (coroot_torusElt_mem_sup hE j s)
  · obtain ⟨γ', hγ'def⟩ : ∃ γ', γ' = weylAction D.isFiniteType w⁻¹ γ := ⟨_, rfl⟩
    have hγw : γ = weylAction D.isFiniteType w γ' := by
      rw [hγ'def, weylAction_apply_inv_apply]
    have hγ' : γ' ∈ D.roots := hγ'def ▸ weylAction_mem_roots D.isFiniteType w⁻¹ hγ
    have hz' : m⁻¹ * z * m ∈ D.rootGroup γ' := by
      rw [hγ'def]
      exact hm.inv_conj_mem hγ hz
    obtain ⟨v, hv⟩ := ((hE.param γ' hγ').1 _).mp hz'
    have hzv : z = m * x γ' v * m⁻¹ := by
      rw [hv]
      group
    have hconj : t s * z * (t s)⁻¹ =
        m * x γ' (((s ^ coroot D.cartan j γ' : kˣ) : k) * v) * m⁻¹ := by
      rw [ht, ← PsiDiag.torusElt_conj hE j s hγ' v, hzv]
      group
    have hpair : cartanPair D.cartan (weylAction D.isFiniteType w (Pi.single j 1)) γ =
        coroot D.cartan j γ' := by
      have h := cartanPair_weylAction D.isFiniteType hsymm w (Pi.single j 1) γ'
      rwa [← hγw, cartanPair_comm hsymm (Pi.single j 1) γ', cartanPair_single] at h
    rw [hpair]
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · rw [hconj, h1, Units.val_one, one_mul, ← hzv]
    · rw [hconj] at h2
      have h4 := (hE.param γ' hγ').2.2 (mul_left_cancel (mul_right_cancel (h2.trans hzv)))
      by_cases hv0 : v = 0
      · right
        have hx0 : x γ' 0 = 1 := by
          have h := (hE.param γ' hγ').2.1 0 0
          rw [add_zero] at h
          exact left_eq_mul.1 h
        rw [hzv, hv0, hx0, mul_one, mul_inv_cancel]
      · left
        have h5 : ((s ^ coroot D.cartan j γ' : kˣ) : k) = 1 :=
          mul_right_cancel₀ hv0 (by rw [one_mul]; exact h4)
        exact Units.ext (by rw [h5, Units.val_one])

end CFSG.StandardType

end
