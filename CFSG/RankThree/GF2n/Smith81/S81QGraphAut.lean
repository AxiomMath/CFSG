module

public import CFSG.RankThree.GF2n.Smith81.S81QGraphRoot
public import CFSG.RankThree.GF2n.Smith81.S81QGen
public import CFSG.RankThree.GF2n.Smith81.S81G2D6

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.Blueprint CFSG.SeitzReduction CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint.Chevalley
open CFSG.LieType.RootSystem (roots)


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def spinEquivEAut0 : spinGroup (quadPlus 6 K) ≃* ↥(EAut0 K) :=
  (E7Pilot.spinEquivPerpLevi K).trans ((perpLeviEquivLam K).trans
    ((lamEquivLamW K).trans (lamWEquivEAut0 K)))

variable {K}

theorem d6Embed_mem_Perp {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) :
    E7Pilot.d6Embed γ ∈ Perp := by
  rw [← perpRoots_eq]
  exact E7Pilot.d6Embed_mem_perpRoots hγ

theorem coe_perpLeviEquivLam (y : ↥(EPilot.perpLevi .E7 K)) :
    ((perpLeviEquivLam K y : ↥(Lam K)) : (Module.End K (V K))ˣ) =
      ((e7Psi K (y : ↥(adjointGroup .E7 K)) : ↥(e7Data_valid.minGroup K)) :
        (Module.End K (V K))ˣ) := rfl

theorem coe_lamEquivLamW (l : ↥(Lam K)) :
    ((lamEquivLamW K l : ↥(LamW K)) : (Module.End K (W K))ˣ) = resV0 K l := rfl

theorem coe_lamWEquivEAut0 (g : ↥(LamW K)) :
    ((lamWEquivEAut0 K g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = vAut0 K (g : (Module.End K (W K))ˣ) :=
  rfl

theorem spinEquivEAut0_x {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    ((spinEquivEAut0 K (SpinPlus.x 6 K E7Pilot.three_le_rank_D6 γ c) : ↥(EAut0 K)) :
        W K ≃ₗ[K] W K) = vAut0 K (xuWUnit (d6Embed_mem_Perp hγ) c) := by
  have hβ := d6Embed_mem_Perp hγ
  have hβR : IsRoot .E7 (E7Pilot.d6Embed γ) := (perp_iff.1 hβ).1
  unfold spinEquivEAut0
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    E7Pilot.spinEquivPerpLevi_x hγ c, coe_lamWEquivEAut0, coe_lamEquivLamW]
  congr 1
  refine Induces.unique (resV0_induces _) ?_
  have h1 : ((perpLeviEquivLam K ⟨E7Pilot.d6LeviPar K γ c, E7Pilot.d6LeviPar_mem_perpLevi hγ c⟩ :
      ↥(Lam K)) : (Module.End K (V K))ˣ) = e7Data_valid.xu K (E7Pilot.d6Embed γ) c := by
    rw [coe_perpLeviEquivLam]
    change ((e7Psi K (EPilot.pinnedElt .E7 (E7Pilot.d6Embed γ) c) : ↥(e7Data_valid.minGroup K)) :
      (Module.End K (V K))ˣ) = _
    rw [e7Psi_pinnedElt' hβR c]
    rfl
  change Induces (xuWUnit hβ c) ((perpLeviEquivLam K ⟨E7Pilot.d6LeviPar K γ c,
      E7Pilot.d6LeviPar_mem_perpLevi hγ c⟩ : ↥(Lam K)) : (Module.End K (V K))ˣ)
  rw [h1]
  exact xuWUnit_induces hβ c


section Graph

variable (K)

@[expose] def graphAut0 : ↥(EAut0 K) ≃* ↥(EAut0 K) :=
  (spinEquivEAut0 K).symm.trans ((graphSpin 6 K 5).trans (spinEquivEAut0 K))

variable {K}

@[expose] def swap12 (β : Fin (Tag.rank .E7) → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  β ∘ Equiv.swap (⟨1, by decide⟩ : Fin (Tag.rank .E7)) ⟨2, by decide⟩

theorem swap12_swap12 (β : Fin (Tag.rank .E7) → ℤ) : swap12 (swap12 β) = β := by
  funext a
  simp [swap12, Function.comp_apply, Equiv.swap_apply_self]

theorem d6Embed_swap45 (γ : Fin 6 → ℤ) : E7Pilot.d6Embed (swap45 γ) = swap12 (E7Pilot.d6Embed γ) := by
  funext j
  obtain ⟨j, hj⟩ := j
  change j < 7 at hj
  interval_cases j <;>
    simp [E7Pilot.d6Embed, swap12, swap45, Equiv.swap_apply_of_ne_of_ne, Fin.ext_iff]

theorem swap12_mem_Perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) : swap12 β ∈ Perp := by
  rw [← perpRoots_eq] at hβ ⊢
  obtain ⟨γ, hγ, rfl⟩ := E7Pilot.exists_d6Embed_eq_of_mem_perpRoots hβ
  rw [← d6Embed_swap45]
  exact E7Pilot.d6Embed_mem_perpRoots (swap45_mem_roots hγ)

theorem graphAut0_xu {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) :
    graphAut0 K ⟨vAut0 K (xuWUnit hβ c), vAut0_xuWUnit_mem_EAut0 hβ c⟩ =
      ⟨vAut0 K (xuWUnit (swap12_mem_Perp hβ) c), vAut0_xuWUnit_mem_EAut0 (swap12_mem_Perp hβ) c⟩ := by
  have hβ' := hβ
  rw [← perpRoots_eq] at hβ'
  obtain ⟨γ, hγ, rfl⟩ := E7Pilot.exists_d6Embed_eq_of_mem_perpRoots hβ'
  have h1 : (⟨vAut0 K (xuWUnit hβ c), vAut0_xuWUnit_mem_EAut0 hβ c⟩ : ↥(EAut0 K)) =
      spinEquivEAut0 K (SpinPlus.x 6 K E7Pilot.three_le_rank_D6 γ c) := by
    apply Subtype.ext
    rw [spinEquivEAut0_x hγ c]
  rw [h1]
  unfold graphAut0
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    graphSpin_x hγ c]
  apply Subtype.ext
  rw [spinEquivEAut0_x (swap45_mem_roots hγ) c]
  exact congrArg (vAut0 K) (xuWUnit_congr (d6Embed_swap45 γ) _ _ c)

theorem exists_graphAut_EAut0 :
    ∃ γ : ↥(EAut0 K) ≃* ↥(EAut0 K),
      ((rootRadν K).subgroupOf (EAut0 K)).map γ.toMonoidHom = (rootRad0 K).subgroupOf (EAut0 K) := by
  refine ⟨graphAut0 K, ?_⟩
  unfold rootRadν rootRad0
  rw [subgroupOf_closure_eq _ _ rootSetν_subset_EAut0, subgroupOf_closure_eq _ _ rootSet0_subset_EAut0,
    MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, h1, c, hxc⟩ := mem_rootSetν_iff.1 hx
    have hx' : x = ⟨vAut0 K (xuWUnit hγ c), vAut0_xuWUnit_mem_EAut0 hγ c⟩ := Subtype.ext hxc
    show ((graphAut0 K x : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootSet0 K
    rw [hx', graphAut0_xu hγ c]
    exact mem_rootSet0_iff.2 ⟨swap12 γ, swap12_mem_Perp hγ, by simpa [swap12] using h1, c, rfl⟩
  · intro hy
    obtain ⟨γ, hγ, h1, c, hyc⟩ := mem_rootSet0_iff.1 hy
    have hy' : y = ⟨vAut0 K (xuWUnit hγ c), vAut0_xuWUnit_mem_EAut0 hγ c⟩ := Subtype.ext hyc
    have hσ := swap12_mem_Perp hγ
    refine ⟨⟨vAut0 K (xuWUnit hσ c), vAut0_xuWUnit_mem_EAut0 hσ c⟩, ?_, ?_⟩
    · exact mem_rootSetν_iff.2 ⟨swap12 γ, hσ, by simpa [swap12] using h1, c, rfl⟩
    · rw [hy']
      show graphAut0 K ⟨vAut0 K (xuWUnit hσ c), _⟩ = _
      rw [graphAut0_xu hσ c]
      apply Subtype.ext
      exact congrArg (vAut0 K) (xuWUnit_congr (swap12_swap12 γ) _ _ c)

end Graph

end CFSG.RankThree.GF2n.Smith81.D6Spin
