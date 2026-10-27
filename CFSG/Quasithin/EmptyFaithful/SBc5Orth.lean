module

public import CFSG.Quasithin.EmptyFaithful.A38c5Omega
public import CFSG.Quasithin.EmptyFaithful.SBc5OrthDefs

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth
open scoped commutatorElement

namespace CFSG.Quasithin

@[expose] def S8ModelFact : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 8)), IsSylowTwoOf T ⊤ → ∀ w : p4insporth_V8, w ≠ 0 →
    (∀ t ∈ T, p4insporth_perm8Hom t w = w) →
      ∀ K : Subgroup (Equiv.Perm (Fin 8)),
        (∀ σ : Equiv.Perm (Fin 8), σ ∈ K ↔ σ ∈ alternatingGroup (Fin 8) ∧ p4insporth_perm8Hom σ w = w) →
          IsMaxParabolic2 (alternatingGroup (Fin 8)) K

namespace SBc5

open CFSG.Quasithin.B3

theorem orthoFixedParabolic_of_model (hM : S8ModelFact) : OrthoFixedParabolic := by
  intro W _ _ hW q hq hnd E hE hEq hcard S₀ L₀ hS hLΩ hLn hLp hL1 a ha1 hfix
  obtain ⟨ε, hε⟩ := A38c5.exists_model_mulEquiv hW q hq hnd E hE hEq hcard
  have hactinj : Function.Injective (Mod.act 8 Mod.ut0) := B3.act_injective (by norm_num) _
  set ψ₀ : B3.Gp 8 →* MulAut W := (H.congrHom ε.symm).comp (Mod.act 8 Mod.ut0) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ := (H.congrHom_injective ε.symm).comp hactinj
  have hψ₀range : ψ₀.range = orthogonalGroupOf q := by
    rw [hψ₀, MonoidHom.range_comp, ← hε, Subgroup.map_map]
    have : (H.congrHom ε.symm).comp (H.congrHom ε) = MonoidHom.id (MulAut W) := by
      ext x v
      simp
    rw [this, Subgroup.map_id]
  have hS₀le : S₀ ≤ ψ₀.range := hψ₀range ▸ hS.1
  have hT₀ : IsSylowTwoOf (S₀.comap ψ₀) ⊤ := by
    have h1 : IsSylowTwoOf ((S₀.comap ψ₀).map ψ₀) ((⊤ : Subgroup (B3.Gp 8)).map ψ₀) := by
      rw [Subgroup.map_comap_eq_self hS₀le, ← MonoidHom.range_eq_map, hψ₀range]
      exact hS
    exact (A38c5.isSylowTwoOf_map_iff ψ₀ hψ₀inj _ _).1 h1
  have hLrange : L₀ ≤ ψ₀.range := hψ₀range ▸ hLΩ
  have hLe : (L₀.comap ψ₀).map ψ₀ = L₀ := Subgroup.map_comap_eq_self hLrange
  have hn : (L₀.comap ψ₀).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    have hxΩ : ψ₀ x ∈ orthogonalGroupOf q := hψ₀range ▸ ⟨x, rfl⟩
    have hgΩ : ψ₀ g ∈ orthogonalGroupOf q := hψ₀range ▸ ⟨g, rfl⟩
    exact hLn.conj_mem ⟨ψ₀ x, hxΩ⟩ hx ⟨ψ₀ g, hgΩ⟩
  have hperf : ⁅L₀.comap ψ₀, L₀.comap ψ₀⁆ = L₀.comap ψ₀ := by
    apply Subgroup.map_injective hψ₀inj
    rw [Subgroup.map_commutator, hLe, hLp]
  have hbot : L₀.comap ψ₀ ≠ ⊥ := by
    intro h
    apply hL1
    rw [← hLe, h, Subgroup.map_bot]
  have hL₈ : L₀.comap ψ₀ = alternatingGroup (Fin 8) :=
    A38c5.eq_alternatingGroup_of_perfect_normal hn hperf hbot
  set w : p4insporth_V8 := Multiplicative.toAdd (A38c5.betaEquiv (ε a)) with hwdef
  have hfixiff : ∀ σ : Equiv.Perm (Fin 8), ψ₀ σ a = a ↔ p4insporth_perm8Hom σ w = w := by
    intro σ
    have h1 : ψ₀ σ a = ε.symm (Mod.act 8 Mod.ut0 σ (ε a)) := by
      rw [hψ₀, MonoidHom.comp_apply, H.congrHom_apply, MulEquiv.symm_symm]
    rw [h1]
    constructor
    · intro h
      have h2 : Mod.act 8 Mod.ut0 σ (ε a) = ε a := by
        have := congrArg ε h
        simpa using this
      have h3 := congrArg A38c5.betaEquiv h2
      rw [A38c5.betaEquiv_act, A38c5.cvt_apply] at h3
      have h4 := congrArg Multiplicative.toAdd h3
      simpa [hwdef] using h4
    · intro h
      have h3 : A38c5.betaEquiv (Mod.act 8 Mod.ut0 σ (ε a)) = A38c5.betaEquiv (ε a) := by
        rw [A38c5.betaEquiv_act, A38c5.cvt_apply]
        have : p4insporth_perm8Hom σ (Multiplicative.toAdd (A38c5.betaEquiv (ε a))) =
            Multiplicative.toAdd (A38c5.betaEquiv (ε a)) := h
        rw [this]
        simp
      have h2 : Mod.act 8 Mod.ut0 σ (ε a) = ε a := A38c5.betaEquiv.injective h3
      rw [h2]
      simp
  have hw0 : w ≠ 0 := by
    intro h
    apply ha1
    have h1 : A38c5.betaEquiv (ε a) = 1 := by
      have : Multiplicative.toAdd (A38c5.betaEquiv (ε a)) = 0 := h
      simpa using this
    have h2 : ε a = 1 := A38c5.betaEquiv.injective (by rw [h1, map_one])
    exact ε.injective (by rw [h2, map_one])
  have hwfix : ∀ t ∈ S₀.comap ψ₀, p4insporth_perm8Hom t w = w := fun t ht =>
    (hfixiff t).1 (hfix _ ht)
  have hK := hM (S₀.comap ψ₀) hT₀ w hw0 hwfix ((L₀ ⊓ MulAction.stabilizer (MulAut W) a).comap ψ₀)
    (by
      intro σ
      have hσL : ψ₀ σ ∈ L₀ ↔ σ ∈ alternatingGroup (Fin 8) := by
        rw [← hL₈, Subgroup.mem_comap]
      rw [Subgroup.mem_comap, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def,
        hfixiff, hσL])
  have hKrange : L₀ ⊓ MulAction.stabilizer (MulAut W) a ≤ ψ₀.range :=
    inf_le_left.trans hLrange
  have := (A38c5.isMaxParabolic2_map_iff ψ₀ hψ₀inj (alternatingGroup (Fin 8))
    ((L₀ ⊓ MulAction.stabilizer (MulAut W) a).comap ψ₀)).2 hK
  rwa [← hL₈, Subgroup.map_comap_eq_self hLrange, Subgroup.map_comap_eq_self hKrange] at this

end SBc5

end CFSG.Quasithin
