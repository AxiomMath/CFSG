module

public import CFSG.Quasithin.Background.SmithD321Q

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem isSumMod_comm {C A B Tot : Subgroup W} : IsSumMod C A B Tot ↔ IsSumMod C B A Tot := by
  unfold IsSumMod
  rw [sup_comm A B, inf_comm]

omit [Finite W] in
theorem realizesVia_conjAutSub {D : FFModel} {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (σ : MulAut W) :
    D.RealizesVia (conjAutSub σ H) (U.map σ.toMonoidHom) (Z.map σ.toMonoidHom)
      ((Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
        (MulAut.conj σ).injective).toMonoidHom.comp π) := by
  obtain ⟨hπ, hZU, hks, hU, hZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  set c := Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
    (MulAut.conj σ).injective
  have hconj : ∀ (x : MulAut W) (v : W), (MulAut.conj σ x) (σ v) = σ (x v) := by
    intro x v
    simp [MulAut.conj_apply, MulAut.mul_apply]
  refine ⟨c.surjective.comp hπ, Subgroup.map_mono hZU, hks, ?_, ?_, hsec, hker, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨x u, hU ⟨x, hx⟩ u hu, (hconj x u).symm⟩
  · rintro ⟨_, x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    exact ⟨x z, hZ ⟨x, hx⟩ z hz, (hconj x z).symm⟩
  · set e : ↥U ≃* ↥(U.map σ.toMonoidHom) :=
      Subgroup.equivMapOfInjective U σ.toMonoidHom σ.injective
    have hev : ∀ u : ↥U, ((e u : ↥(U.map σ.toMonoidHom)) : W) = σ u := fun u =>
      Subgroup.coe_equivMapOfInjective_apply U σ.toMonoidHom σ.injective u
    refine ⟨β.comp e.symm.toMonoidHom, hβs.comp e.symm.surjective, fun u => ?_, ?_⟩
    · obtain ⟨u, rfl⟩ := e.surjective u
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply]
      rw [hβk u, hev]
      constructor
      · intro hz
        exact ⟨u, hz, rfl⟩
      · rintro ⟨z, hz, hzu⟩
        rwa [← σ.injective hzu]
    · intro γ u m hu hm hβum
      obtain ⟨u, rfl⟩ := e.surjective u
      have hβum' : β u = QuotientGroup.mk m := by
        change β (e.symm (e u)) = _ at hβum
        rwa [MulEquiv.symm_apply_apply] at hβum
      have hu' : ((π γ : ↥H) : MulAut W) (u : W) ∈ U := hU (π γ) u u.2
      have h1 := hβe γ u m hu' hm hβum'
      have h2 : e.symm ⟨_, hu⟩ = ⟨((π γ : ↥H) : MulAut W) (u : W), hu'⟩ := by
        rw [MulEquiv.symm_apply_eq]
        apply Subtype.ext
        change (MulAut.conj σ ((π γ : ↥H) : MulAut W)) ((e u : ↥(U.map σ.toMonoidHom)) : W) =
          ((e ⟨((π γ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥(U.map σ.toMonoidHom)) : W)
        rw [hev, hev, hconj]
      change β (e.symm ⟨_, hu⟩) = _
      rw [h2]
      exact h1

omit [Finite W] in
theorem directSumOfCopies_conjAutSub {D : FFModel} {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {k : ℕ} (h : DirectSumOfCopies H U Z D k) (σ : MulAut W) :
    DirectSumOfCopies (conjAutSub σ H) (U.map σ.toMonoidHom) (Z.map σ.toMonoidHom) D k := by
  obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := h
  refine ⟨fun i => (I i).map σ.toMonoidHom,
    (Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
      (MulAut.conj σ).injective).toMonoidHom.comp π,
    fun i => Subgroup.map_mono (hZI i), fun i => ?_, ?_,
    fun i => realizesVia_conjAutSub (hreal i) σ⟩
  · have h := congrArg (Subgroup.map σ.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq _ _ σ.toMonoidHom σ.injective, Subgroup.map_sup,
      Subgroup.map_iSup] at h
    simp only [Subgroup.map_iSup] at h
    exact h
  · rw [← hsup, Subgroup.map_sup, Subgroup.map_iSup]

omit [Finite W] in
theorem d321Two_conjAutSub {H : Subgroup (MulAut W)} (h : D321Two H) (σ : MulAut W) :
    D321Two (conjAutSub σ H) := by
  obtain ⟨hpsl, hsum⟩ := h
  refine ⟨isPSL_congr (Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
    (MulAut.conj σ).injective) hpsl, ?_⟩
  have h2 := directSumOfCopies_conjAutSub hsum σ
  rwa [map_commV_conjAutSub, Subgroup.map_bot] at h2

omit [Finite W] in
theorem d321Three_conjAutSub {Mp H : Subgroup (MulAut W)} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (Mp : Set (MulAut W))) (h : D321Three Mp H) :
    D321Three Mp (conjAutSub σ H) := by
  obtain ⟨n, hpsl, K, hK, hKf, hcard, hsum⟩ := h
  refine ⟨n, isPSL_congr (Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
    (MulAut.conj σ).injective) hpsl, K, hK, hKf, hcard, ?_⟩
  have h2 := directSumOfCopies_conjAutSub hsum σ
  rwa [Subgroup.map_inf_eq _ _ σ.toMonoidHom σ.injective, map_commV_conjAutSub,
    map_fixV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hσ] at h2

theorem d3Std_swap {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V)
    {t : MulAut W} (htT : t ∈ T) : D3Std M Mp T (conjAutSub t L) V :=
  ⟨hD.hyp.conj htT, hD.qhat, hD.irrT⟩

theorem D321Base.swap {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) : D321Base M Mp T (conjAutSub t L) V t⁻¹ where
  hD := d3Std_swap hB.hD hB.htT
  htT := T.inv_mem hB.htT
  htn := not_mem_normalizer_conjAutSub hB.htn
  hMp := by
    rw [conjAutSub_inv_conjAutSub, sup_comm]
    exact hB.hMp
  hA38 := a38Types_conjAutSub t hB.hA38
  hsimp := hB.Lt_simp
  hcomm := by
    rw [conjAutSub_inv_conjAutSub, Subgroup.commutator_comm]
    exact hB.hcomm
  hinf := by
    rw [conjAutSub_inv_conjAutSub, inf_comm]
    exact hB.hinf
  hTperm := by
    intro s hs
    rw [conjAutSub_inv_conjAutSub, ← conjAutSub_mul]
    exact (hB.hTperm (s * t) (T.mul_mem hs hB.htT)).symm

theorem D321Sit.swap {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r) :
    D321Sit M Mp T (conjAutSub t L) V t⁻¹ A r :=
  ⟨hS.toD321Base.swap, hS.hr, hS.hr2, hS.htop, hS.hAQ, hS.hAT, hS.hAr⟩

theorem D321Base.concl_of_swap {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t)
    (h : IsSumMod (fixV Mp) (commV (conjAutSub t L))
        ((commV (conjAutSub t L)).map t⁻¹.toMonoidHom) ⊤ ∧
      commV (conjAutSub t L) ≤ fixV (conjAutSub t⁻¹ (conjAutSub t L)) ∧
      (D321Two (conjAutSub t L) ∨ D321Three Mp (conjAutSub t L))) :
    IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
      commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hU : (commV (conjAutSub t L)).map t⁻¹.toMonoidHom = commV L := by
    rw [map_commV_conjAutSub, conjAutSub_inv_conjAutSub]
  have htM : t⁻¹ ∈ M := M.inv_mem hB.t_mem
  have htL : t⁻¹ ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun h => hB.htn (inv_mem_iff.1 h)
  refine ⟨?_, ?_, ?_⟩
  · rw [hU, ← map_commV_conjAutSub] at h1
    exact isSumMod_comm.1 h1
  · rw [conjAutSub_inv_conjAutSub] at h2
    have h4 := Subgroup.map_mono (f := t⁻¹.toMonoidHom) h2
    rwa [hU, map_fixV_conjAutSub, (hB.conj_swap htM htL).1] at h4
  · rcases h3 with h3 | h3
    · have h5 := d321Two_conjAutSub h3 t⁻¹
      rw [conjAutSub_inv_conjAutSub] at h5
      exact Or.inl h5
    · have h5 := d321Three_conjAutSub (hB.hD.hyp.Mp_normal htM) h3
      rw [conjAutSub_inv_conjAutSub] at h5
      exact Or.inr h5

end CFSG.Quasithin.SmithD321
