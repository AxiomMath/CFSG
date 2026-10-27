module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.NS
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

variable {Γ : Type*} [Group Γ]

theorem kUp_eq_sSup_lcalA {G A : Subgroup Γ} (hsol : sol G = ⊥) :
    kUp G A = sSup (lcalA G A) := by
  have h : mcalA G A = lcalA G A := by
    unfold mcalA lcalA
    rw [mcal_eq_lcal_of_sol_eq_bot hsol]
  unfold kUp
  rw [h, sSup_eq_iSup]

theorem orbitClosure_map_conj_le {A J : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (A : Set Γ)) :
    orbitClosure (J.map (MulAut.conj g).toMonoidHom) A ≤
      (orbitClosure J A).map (MulAut.conj g).toMonoidHom := by
  refine orbitClosure_le fun a ha => ?_
  have ha' : g⁻¹ * a * g ∈ A := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) a).mp ha
  rw [L514.map_conj_map_conj, show a * g = g * (g⁻¹ * a * g) by group,
    ← L514.map_conj_map_conj J (g⁻¹ * a * g) g]
  exact Subgroup.map_mono (map_conj_le_orbitClosure J ha')

theorem smear_map_conj_le {A J : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (A : Set Γ)) :
    smear (J.map (MulAut.conj g).toMonoidHom) A ≤
      (smear J A).map (MulAut.conj g).toMonoidHom := by
  intro x hx
  obtain ⟨hxO, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, rfl⟩ := orbitClosure_map_conj_le hg hxO
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, rfl⟩
  have ha' : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have h1 : g * a * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * a * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hxC (g * a * g⁻¹) ha'
  have e1 : a * y = g⁻¹ * (g * a * g⁻¹ * (g * y * g⁻¹)) * g := by group
  have e2 : y * a = g⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹)) * g := by group
  rw [e1, e2, h1]

theorem isSolvable_smear_map_conj {A J : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (A : Set Γ)) (h : Group.IsSolvable ↥(smear J A)) :
    Group.IsSolvable ↥(smear (J.map (MulAut.conj g).toMonoidHom) A) :=
  isSolvable_of_le (smear_map_conj_le hg) (isSolvable_map_mulEquiv (MulAut.conj g) h)

theorem map_conj_mem_lcalA {G A J : Subgroup Γ} {g : Γ}
    (hgG : g ∈ Subgroup.normalizer (G : Set Γ)) (hgA : g ∈ Subgroup.normalizer (A : Set Γ))
    (hJ : J ∈ lcalA G A) : J.map (MulAut.conj g).toMonoidHom ∈ lcalA G A := by
  refine ⟨map_conj_mem_lcal hJ.1 hgG, fun hs => hJ.2 ?_⟩
  have := isSolvable_smear_map_conj (inv_mem hgA) hs
  rwa [L514.map_conj_map_conj_inv] at this

theorem mem_normalizer_kUp {G A : Subgroup Γ} (hsol : sol G = ⊥) {g : Γ}
    (hgG : g ∈ Subgroup.normalizer (G : Set Γ)) (hgA : g ∈ Subgroup.normalizer (A : Set Γ)) :
    g ∈ Subgroup.normalizer (kUp G A : Set Γ) := by
  rw [kUp_eq_sSup_lcalA hsol]
  exact L514.mem_normalizer_sSup (fun J hJ => map_conj_mem_lcalA hgG hgA hJ)
    (fun J hJ => map_conj_mem_lcalA (inv_mem hgG) (inv_mem hgA) hJ)

theorem mul_comm_of_mem_kDown {G A : Subgroup Γ} (hsol : sol G = ⊥) {g k : Γ}
    (hg : g ∈ kDown G A) (hk : k ∈ kUp G A) : g * k = k * g := by
  have h := (mem_kDown_iff.mp hg).2 k hk
  rw [hsol, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

variable [Finite Γ]

theorem mem_normalizer_kDown {G A : Subgroup Γ} {g : Γ}
    (hgG : g ∈ Subgroup.normalizer (G : Set Γ))
    (hgK : g ∈ Subgroup.normalizer (kUp G A : Set Γ)) :
    g ∈ Subgroup.normalizer (kDown G A : Set Γ) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  obtain ⟨htG, ht⟩ := mem_kDown_iff.mp ht
  refine mem_kDown_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgG t).mp htG, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ kUp G A := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
  have h1 := (Subgroup.mem_normalizer_iff.mp (SolQuot.normalizer_le_nrm_sol G hgG) _).mp
    (ht _ hk')
  have e : ⁅g * t * g⁻¹, k⁆ = g * ⁅t, g⁻¹ * k * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem isDAInvariant_kDown {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G) (hsol : sol G = ⊥) :
    IsDAInvariant A G (kDown G A) := by
  refine ⟨kDown_le G A, fun d hd => ?_, fun a ha => ?_⟩
  · have hdG : d ∈ Subgroup.normalizer (G : Set Γ) := Subgroup.le_normalizer hd.1
    exact mem_normalizer_kDown hdG (mem_normalizer_kUp hsol hdG
      (Subgroup.centralizer_le_normalizer (A : Set Γ) hd.2))
  · exact mem_normalizer_kDown (h.normalizes ha) (mem_normalizer_kUp hsol (h.normalizes ha)
      (Subgroup.le_normalizer ha))

theorem kDown_inf_kUp_eq_bot {G A : Subgroup Γ} (hsol : sol G = ⊥) :
    kDown G A ⊓ kUp G A = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hzT, hzK⟩ := Subgroup.mem_inf.mp hz
  have hK := isDirectProduct_lcal_kOf hsol
  have hsub : lcalA G A ⊆ lcal G := lcalA_subset G A
  have hcomm : ∀ u ∈ sSup (lcalA G A), ∀ v ∈ sSup (lcal G \ lcalA G A), Commute u v :=
    L514.commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ u hu v hv =>
      hK.commute J₁ (hsub hJ₁) J₂ hJ₂.1 (fun h => hJ₂.2 (h ▸ hJ₁)) u hu v hv
  have hsup : kOf G = sSup (lcalA G A) ⊔ sSup (lcal G \ lcalA G A) := by
    rw [← hK.sSup_eq, ← sSup_union, Set.union_sdiff_cancel hsub]
  have hzK' : z ∈ sSup (lcalA G A) := (kUp_eq_sSup_lcalA hsol).symm ▸ hzK
  have hle : kOf G ≤ Subgroup.centralizer ({z} : Set Γ) := by
    rw [hsup]
    refine sup_le (fun k hk => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_comm_of_mem_kDown hsol hzT ((kUp_eq_sSup_lcalA hsol).symm ▸ hk)).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm z hzK' v hv).eq.symm
  have hzc : z ∈ Subgroup.centralizer (kOf G : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have := centralizer_kOf_eq_bot hsol
  rw [eq_bot_iff] at this
  exact this (Subgroup.mem_inf.mpr ⟨kDown_le G A hzT, hzc⟩)

theorem isDirectPair_kDown_kUp {G A : Subgroup Γ} (hsol : sol G = ⊥) :
    IsDirectPair (kDown G A) (kUp G A) (kDown G A ⊔ kUp G A) :=
  ⟨fun _ hx _ hy => (mul_comm_of_mem_kDown hsol hx hy), kDown_inf_kUp_eq_bot hsol, rfl⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
