module

public import CFSG.Milestones.ASVolI.H13
public import CFSG.Quasithin.Background.RonanH15Model
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.RonanH15
  CFSG.Monster.Code CFSG.ASVolI.ChH

section Generic

variable {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]
  {V : Type*} [CommGroup V]

theorem exists_equiv_of_realizesBy (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    {H : Subgroup (MulAut V)} {π : (FFModel.golaySec Γ numer denom).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (hb : RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β) :
    ∃ e : V ≃* W, (∀ (γ : ↥Γ) (v : V), e (((π γ : ↥H) : MulAut V) v) = c.rho Γ hΓ γ (e v)) ∧
      ∀ (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔ e v = c.κ m := by
  obtain ⟨-, -, -, -, -, -, -, hβs, hβ1, hβa⟩ := hb
  exact c.exists_equiv_compat hΓ (fun γ => ((π γ : ↥H) : MulAut V)) β hβs
    (fun v hv => Subgroup.mem_bot.1 ((hβ1 _).1 hv))
    (fun γ v m hm => hβa γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hm)

end Generic

theorem map_congrHom_range_eq {G : Type*} [Group G] {V W : Type*} [CommGroup V] [CommGroup W]
    (e : V ≃* W) (ρ : G →* MulAut V) (ρ' : G →* MulAut W)
    (h : ∀ (γ : G) (v : V), e (ρ γ v) = ρ' γ (e v)) :
    ρ.range.map (congrHom e) = ρ'.range := by
  have key : ∀ γ : G, congrHom e (ρ γ) = ρ' γ := by
    intro γ
    ext w
    rw [congrHom_apply, h γ, MulEquiv.apply_symm_apply]
  ext x
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨γ, (key γ).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨ρ γ, ⟨γ, rfl⟩, key γ⟩

section Cocode24

variable {V : Type*} [CommGroup V]

theorem exists_equiv_cocodeStd {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) golayC) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    ∃ e : V ≃* W11, (∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v)) ∧
      ρ.range.map (congrHom e) = (rho11 Γ hΓ).range ∧
      ∀ (v : V) (m : ↥(G6.coreMod 24)), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
        e v = cocodeCoords.κ m := by
  obtain ⟨e, hpt, hcompat⟩ := exists_equiv_of_realizesBy cocodeCoords
    (fun _ hσ => preserves_cocode (hΓ hσ)) h
  have hpt' : ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v) := fun γ v => hpt γ v
  exact ⟨e, hpt', map_congrHom_range_eq e ρ _ hpt', hcompat⟩

theorem o2_twist24_pred {e : V ≃* W11} (P : V → Prop)
    (hO2 : ∀ (v : V) (i j : Fin 24), i ≠ j → e v = cocodeCoords.κ (pairVec i j) → P v)
    (g : ↥AutPerm) :
    ∀ o ∈ o2Masks24, (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).vm o ∈ {v | P v} := by
  intro o ho
  obtain ⟨i, j, hij, hjo⟩ := toW_o2_24 ho
  set σ : Equiv.Perm (Fin 24) := ((g⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) with hσ
  refine hO2 _ (σ i) (σ j) (σ.injective.ne hij) ?_
  rw [MaskCoords.ofEquiv_vm]
  change e (e.symm ((rhoM24 g).symm (toW 11 o))) = _
  rw [MulEquiv.apply_symm_apply, hjo, rho11_inv_pairVec24]

end Cocode24

end CFSG.ASVolI.AppH
