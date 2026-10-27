module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitAct
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitBridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitPi
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {F : Type} [Field F]

theorem beta_one_of_mem (S : AbelSub G) (W Z : Subgroup G) {N : Type} [AddCommGroup N]
    (β : ↥S.carrier →* Multiplicative N) (hβker : β.ker = Z.subgroupOf S.carrier)
    (hWZ : W ≤ Z) (x : S.carrier) (hx : (x : G) ∈ W) : β x = 1 := by
  have hxZ : x ∈ Z.subgroupOf S.carrier := Subgroup.mem_subgroupOf.mpr (hWZ hx)
  rw [← hβker] at hxZ
  exact MonoidHom.mem_ker.mp hxZ

theorem mem_Z_of_beta_one (S : AbelSub G) (Z : Subgroup G) {N : Type} [AddCommGroup N]
    (β : ↥S.carrier →* Multiplicative N) (hβker : β.ker = Z.subgroupOf S.carrier)
    (x : S.carrier) (hx : β x = 1) : (x : G) ∈ Z := by
  have hk : x ∈ β.ker := MonoidHom.mem_ker.mpr hx
  rw [hβker] at hk
  exact Subgroup.mem_subgroupOf.mp hk

@[expose] noncomputable def splitSetupOf (S : AbelSub G) (W Z A : Subgroup G) {k : ℕ}
    {α : ↥A →* ↥(StatedSL 3 F)} (ρ0 : Matrix.SpecialLinearGroup (Fin 3) F →*
      AddMonoid.End (Fin 3 → F))
    (hA : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWZ : W ≤ Z)
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hker : ∀ a : ↥A, α a = 1 → ∀ v : S.carrier, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W)
    (β : ↥S.carrier →* Multiplicative (Fin k → Fin 3 → F))
    (hβker : β.ker = Z.subgroupOf S.carrier)
    (hβeq : ∀ (a : ↥A) (u v : S.carrier), (v : G) = (a : G) * (u : G) * (a : G)⁻¹ →
      ∀ i : Fin k, Multiplicative.toAdd (β v) i =
        ρ0 ((statedSLEquiv 3).symm (α a)) (Multiplicative.toAdd (β u) i))
    [Module (ZMod 2) (S.quot W)] [Module (ZMod 2) (Fin k → Fin 3 → F)] :
    SplitSetup ↥A (Matrix.SpecialLinearGroup (Fin 3) F) (S.quot W) (Fin k → Fin 3 → F) where
  ψ := (statedSLEquiv 3).symm.toMonoidHom.comp α
  ρE := rhoE S W A hA hAW
  ρN := piAct ρ0
  π := piL S W β (fun x hx => beta_one_of_mem S W Z β hβker hWZ x hx)
  hequiv := fun a e => by
    obtain ⟨v, rfl⟩ := exists_mk S W e
    rw [rhoE_mk, piL_mk, piL_mk]
    exact funext fun i => hβeq a v (conjSub S (hA a.2) v) rfl i
  htriv := fun a z hz => by
    obtain ⟨x, rfl⟩ := exists_mk S W z
    have hpi : Multiplicative.toAdd (β x) = 0 := by
      have h := hz
      rw [piL_mk] at h
      exact h
    have hxZ : (x : G) ∈ Z := mem_Z_of_beta_one S Z β hβker x (toAdd_eq_zero.mp hpi)
    exact rhoE_mk_of_comm S W A hA hAW a x (hZW a a.2 x hxZ)
  hker := fun a ha e => by
    have ha0 : (statedSLEquiv 3).symm (α a) = 1 := ha
    have ha' : α a = 1 := (statedSLEquiv 3).symm.injective (ha0.trans (map_one _).symm)
    obtain ⟨v, rfl⟩ := exists_mk S W e
    exact rhoE_mk_of_comm S W A hA hAW a v (hker a ha' v)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
