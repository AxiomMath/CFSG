module

public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Quasithin.Background.B5FinS8Schur
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.Background.B5Inputs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace B5FinS8

theorem extend_equivariant {G X M : Type*} [Group G] [Group X] [Group M]
    (a : G →* MulAut X) (β : X →* M) (hβ : Function.Surjective β)
    (ρ : Equiv.Perm (Fin 8) →* MulAut M) (θ : G ≃* Equiv.Perm (Fin 8))
    (hker : ∀ g x, β x = 1 → β (a g x) = 1)
    (hcomm : ∀ g ∈ commutator G, ∀ x, β (a g x) = ρ (θ g) (β x))
    (hK8 : ∀ μ : M →* M, Function.Injective μ →
      (∀ σ ∈ alternatingGroup (Fin 8), ∀ q, μ (ρ σ q) = ρ σ (μ q)) → ∀ q, μ q = q) :
    ∀ g x, β (a g x) = ρ (θ g) (β x) := by
  intro h x
  have hθ : ∀ σ' ∈ alternatingGroup (Fin 8), ∃ g' ∈ commutator G, θ g' = σ' := by
    intro σ' hσ'
    have hA : commutator (Equiv.Perm (Fin 8)) = alternatingGroup (Fin 8) :=
      alternatingGroup.commutator_perm_eq (by simp)
    have hmap : (commutator G).map θ.toMonoidHom = commutator (Equiv.Perm (Fin 8)) := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 θ.surjective, ← commutator_def]
    rw [← hA, ← hmap] at hσ'
    obtain ⟨g', hg', rfl⟩ := hσ'
    exact ⟨g', hg', rfl⟩
  let f : X →* M := β.comp (a h).toMonoidHom
  have hfk : β.ker ≤ f.ker := fun x hx => hker h x hx
  let lam : M →* M :=
    (MonoidHom.liftOfRightInverse β (Function.surjInv hβ) (Function.rightInverse_surjInv hβ))
      ⟨f, hfk⟩
  have hlam : ∀ x, lam (β x) = β (a h x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply β (Function.surjInv hβ)
      (Function.rightInverse_surjInv hβ) ⟨f, hfk⟩ x
  set σ := θ h with hσ
  let μ : M →* M := (ρ σ⁻¹).toMonoidHom.comp lam
  have hμx : ∀ x, μ (β x) = ρ σ⁻¹ (β (a h x)) := fun x => by
    change ρ σ⁻¹ (lam (β x)) = _
    rw [hlam]
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨y, rfl⟩ := hβ q
    rw [hμx] at hq
    have h1 : β (a h y) = 1 := ((ρ σ⁻¹).map_eq_one_iff).1 hq
    have h2 := hker h⁻¹ _ h1
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
  have hμcomm : ∀ σ' ∈ alternatingGroup (Fin 8), ∀ q, μ (ρ σ' q) = ρ σ' (μ q) := by
    intro σ' hσ' q
    obtain ⟨g', hg', hg'σ⟩ := hθ σ' hσ'
    obtain ⟨y, rfl⟩ := hβ q
    have e1 : ρ σ' (β y) = β (a g' y) := by rw [← hg'σ]; exact (hcomm g' hg' y).symm
    rw [e1, hμx, hμx]
    have hgc : h * g' * h⁻¹ ∈ commutator G :=
      (inferInstance : (commutator G).Normal).conj_mem g' hg' h
    have e2 : (a h) ((a g') y) = (a (h * g' * h⁻¹)) ((a h) y) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
    have e3 := hcomm (h * g' * h⁻¹) hgc ((a h) y)
    have e4 : θ (h * g' * h⁻¹) = σ * σ' * σ⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg'σ]
    rw [e2, e3, e4, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  have h5 := hK8 μ hμinj hμcomm (β x)
  rw [hμx] at h5
  have h6 : ρ σ (ρ σ⁻¹ (β (a h x))) = ρ σ (β x) := congrArg (ρ σ) h5
  rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h6

section Assembly

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}

private theorem commutator_le_self' (H : Subgroup (MulAut V)) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] noncomputable def actU (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) : ↥H →* MulAut ↥U where
  toFun h :=
    { toFun := fun u => ⟨(h : MulAut V) u, hU h h.2 u u.2⟩
      invFun := fun u => ⟨((h⁻¹ : ↥H) : MulAut V) u, hU _ (h⁻¹ : ↥H).2 u u.2⟩
      left_inv := fun u => Subtype.ext (by
        change ((h⁻¹ : ↥H) : MulAut V) ((h : MulAut V) u) = u
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
      right_inv := fun u => Subtype.ext (by
        change (h : MulAut V) (((h⁻¹ : ↥H) : MulAut V) u) = u
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply])
      map_mul' := fun u v => Subtype.ext (map_mul _ _ _) }
  map_one' := by
    ext u
    rfl
  map_mul' g h := by
    ext u
    rfl

private theorem theta_commutator (θ : ↥H ≃* Equiv.Perm (Fin 8)) :
    (commutator ↥H).map θ.toMonoidHom = alternatingGroup (Fin 8) := by
  have hA : commutator (Equiv.Perm (Fin 8)) = alternatingGroup (Fin 8) :=
    alternatingGroup.commutator_perm_eq (by simp)
  rw [← hA, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top.2 θ.surjective, ← commutator_def]

theorem symmetricNatural_eight_of_exteriorTwo (θ : ↥H ≃* Equiv.Perm (Fin 8))
    (h : SLExteriorTwo ⁅H, H⁆ U Z 4) (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) : SymmetricNatural H U Z 8 := by
  obtain ⟨π, hπs, hZU, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let hD := FFModel.symDn_isActionModel 8
  let hE := FFModel.extSq_isActionModel (ZMod 2) 4
  let ρ : Equiv.Perm (Fin 8) →* MulAut (FFModel.symDn 8).Mod := hD.modAct
  let alphaG : alternatingGroup (Fin 8) →* (FFModel.extSq (ZMod 2) 4).Gam := alpha
  have hβmod : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (u : ↥U)
      (hu : ((π γ : ↥⁅H, H⁆) : MulAut V) (u : V) ∈ U),
      β ⟨((π γ : ↥⁅H, H⁆) : MulAut V) (u : V), hu⟩ = hE.modAct γ (β u) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    rw [← hm]
    exact hβe γ u m hu (hsec γ m m.2) hm.symm
  have hle : ⁅H, H⁆ ≤ H := commutator_le_self' H
  let jH : ↥⁅H, H⁆ →* ↥H := Subgroup.inclusion hle
  have hmapC : (commutator ↥H).map H.subtype = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  have hC1 : ∀ x : ↥⁅H, H⁆, jH x ∈ commutator ↥H := by
    intro x
    have hx : (x : MulAut V) ∈ (commutator ↥H).map H.subtype := by rw [hmapC]; exact x.2
    obtain ⟨c, hc, hcx⟩ := hx
    have : jH x = c := Subtype.ext hcx.symm
    rw [this]
    exact hc
  have hC2 : ∀ c ∈ commutator ↥H, ∃ x : ↥⁅H, H⁆, jH x = c := by
    intro c hc
    have hx : (c : MulAut V) ∈ ⁅H, H⁆ := by rw [← hmapC]; exact ⟨c, hc, rfl⟩
    exact ⟨⟨c, hx⟩, rfl⟩
  have hθA : ∀ c ∈ commutator ↥H, θ c ∈ alternatingGroup (Fin 8) := by
    intro c hc
    rw [← theta_commutator θ]
    exact ⟨c, hc, rfl⟩
  have hθA' : ∀ a ∈ alternatingGroup (Fin 8), ∃ c ∈ commutator ↥H, θ c = a := by
    intro a ha
    rw [← theta_commutator θ] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact ⟨c, hc, rfl⟩
  let ψ : alternatingGroup (Fin 8) →* ↥⁅H, H⁆ := π.comp alphaG
  have hψs : Function.Surjective ψ := hπs.comp alpha_surjective
  let ε : alternatingGroup (Fin 8) →* alternatingGroup (Fin 8) :=
    (θ.toMonoidHom.comp (jH.comp ψ)).codRestrict (alternatingGroup (Fin 8))
      (fun σ => hθA _ (hC1 (ψ σ)))
  have hεs : Function.Surjective ε := by
    intro a
    obtain ⟨c, hc, hca⟩ := hθA' a a.2
    obtain ⟨x, hx⟩ := hC2 c hc
    obtain ⟨σ, hσ⟩ := hψs x
    refine ⟨σ, Subtype.ext ?_⟩
    change θ (jH (ψ σ)) = a
    rw [hσ, hx, hca]
  have hεi : Function.Injective ε := Finite.injective_iff_surjective.2 hεs
  obtain ⟨τ, hτ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)).2 (MulEquiv.ofBijective ε ⟨hεi, hεs⟩)
  have hτσ : ∀ σ : alternatingGroup (Fin 8),
      θ (jH (ψ σ)) = τ * (σ : Equiv.Perm (Fin 8)) * τ⁻¹ := by
    intro σ
    have h1 := congrArg (fun e : MulAut ↥(alternatingGroup (Fin 8)) => ((e σ : _) : Equiv.Perm (Fin 8))) hτ
    simp only [MulAut.conjNormal_apply] at h1
    exact h1.symm
  let β₂ : ↥U →* (FFModel.symDn 8).Mod :=
    (ρ τ).toMonoidHom.comp (G8.symm.toMonoidHom.comp β)
  have hβ₂s : Function.Surjective β₂ :=
    (ρ τ).surjective.comp (G8.symm.surjective.comp hβs)
  have hβ₂k : ∀ u : ↥U, β₂ u = 1 ↔ (u : V) ∈ Z := fun u =>
    ((ρ τ).map_eq_one_iff).trans ((G8.symm.map_eq_one_iff).trans (hβk u))
  have hcomm : ∀ g ∈ commutator ↥H, ∀ u : ↥U, β₂ (actU hU g u) = ρ (θ g) (β₂ u) := by
    intro g hg u
    obtain ⟨x, hx⟩ := hC2 g hg
    obtain ⟨σ, hσ⟩ := hψs x
    have hgσ : g = jH (ψ σ) := by rw [hσ, hx]
    have e1 : actU hU g u =
        ⟨((π (alphaG σ) : ↥⁅H, H⁆) : MulAut V) (u : V), by
          have := (actU hU g u).2
          rw [hgσ] at this
          exact this⟩ := by
      subst hgσ
      rfl
    have e3 : β (actU hU g u) = hE.modAct (alphaG σ) (β u) := by
      rw [e1]
      exact hβmod (alphaG σ) u _
    have e4 : β₂ (actU hU g u) = ρ τ (G8.symm (hE.modAct (alphaG σ) (β u))) := by
      change ρ τ (G8.symm (β (actU hU g u))) = _
      rw [e3]
    have e2 : G8.symm (hE.modAct (alphaG σ) (β u)) =
        ρ (σ : Equiv.Perm (Fin 8)) (G8.symm (β u)) := by
      have h1 := G8_modAct σ (G8.symm (β u))
      rw [MulEquiv.apply_symm_apply] at h1
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    rw [e4, e2, hgσ, hτσ σ]
    change ρ τ (ρ σ (G8.symm (β u))) = ρ (τ * σ * τ⁻¹) (ρ τ (G8.symm (β u)))
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  have hker' : ∀ (g : ↥H) (u : ↥U), β₂ u = 1 → β₂ (actU hU g u) = 1 := by
    intro g u hu
    rw [hβ₂k] at hu ⊢
    exact hZ g g.2 u hu
  have hK8 : ∀ μ : (FFModel.symDn 8).Mod →* (FFModel.symDn 8).Mod, Function.Injective μ →
      (∀ σ ∈ alternatingGroup (Fin 8), ∀ q, μ (ρ σ q) = ρ σ (μ q)) → ∀ q, μ q = q :=
    fun μ hinj hc => k8 μ hinj (fun σ hσ q => hc σ hσ q)
  have key := extend_equivariant (actU hU) β₂ hβ₂s ρ θ hker' hcomm hK8
  refine ⟨θ.symm.toMonoidHom, θ.symm.surjective, hZU, hD.ker_le, fun g u hu => hU g g.2 u hu,
    fun g z hz => hZ g g.2 z hz, hD.sec_inv, hD.ker_inv, β₂, hβ₂s, hβ₂k, ?_⟩
  intro γ u m hu hm hum
  have h1 := key (θ.symm γ) u
  have h2 : θ (θ.symm γ) = γ := θ.apply_symm_apply γ
  rw [h2] at h1
  change β₂ (actU hU (θ.symm γ) u) = _
  rw [h1, hum]
  rfl

end Assembly

end B5FinS8

theorem asS8D8Inv :
    ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V),
      Nonempty (↥H ≃* Equiv.Perm (Fin 8)) → SLExteriorTwo ⁅H, H⁆ U Z 4 →
      (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → (∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) → SymmetricNatural H U Z 8 := by
  intro V _ H U Z ⟨θ⟩ h hU hZ
  exact B5FinS8.symmetricNatural_eight_of_exteriorTwo θ h hU hZ

theorem symmetricNatural_eight_top {V : Type} [CommGroup V] (H : Subgroup (MulAut V))
    (hH : Nonempty (↥H ≃* Equiv.Perm (Fin 8))) (h : SLExteriorTwo ⁅H, H⁆ ⊤ ⊥ 4) :
    SymmetricNatural H ⊤ ⊥ 8 := by
  obtain ⟨θ⟩ := hH
  refine B5FinS8.symmetricNatural_eight_of_exteriorTwo θ h (fun _ _ _ _ => trivial) ?_
  intro g _ z hz
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz]
  exact map_one g

theorem asS8D8 : AsS8D8 := asS8D8Inv

end CFSG.Quasithin
