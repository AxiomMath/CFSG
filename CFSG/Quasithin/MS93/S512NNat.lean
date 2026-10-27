module

public import CFSG.Quasithin.MS93.S512NTwo

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace NatHyp

variable {h : PUHyp M T L} {V E Z Y : Subgroup (puAmalgam h.le).Universal}

theorem isSumOfNaturalModulesVia (h14 : MS14AS)
    (hSQ : SQTKQuot) (hT : S32.TypeFacts) (h51 : S51) (hpu : PUMin M T L)
    (hd : S5.IsSp4Data M T L k F a) (hn : NatHyp h k V E Z Y) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (a' : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F')),
      Fintype.card F' = 2 ^ k ∧ Function.Surjective a' ∧
      IsSumOfNaturalModulesVia (stab _ (baseA (puAmalgam h.le))) V
        (V ⊓ S5.bSub h.le L (baseA _)) a' false 1 := by
  obtain ⟨S, _, p, ρ, hs⟩ := hn.toSecHyp.exists_secMod
  obtain ⟨S₀, hS₀, hne, hmin, F', iF, fF, a', θ, hcard, ha', hθ, hker⟩ :=
    hn.exists_natSub hs h14 hSQ hT hd
  have htop : S₀ = ⊤ := by
    rcases Nat.lt_or_ge k 2 with hk | hk2
    · exact hn.eq_top_of_one hs h51 hpu hd (by have := hd.1; omega) hS₀ hne hmin hcard ha' hθ
        hker
    · exact hn.eq_top_of_two_le hs hd hk2 hS₀ hne hmin hcard ha' hθ hker
  have hmemS₀ : ∀ s : S, s ∈ S₀ := fun s => by
    rw [htop]
    exact Subgroup.mem_top s
  let ι : S →* ↥S₀ := (MonoidHom.id S).codRestrict S₀ hmemS₀
  let e₁ : Multiplicative (MSP.V4 F') ≃* Multiplicative (Fin 1 → MSP.V4 F') :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (MSP.V4 F')).symm
  let β : ↥V →* Multiplicative (Fin 1 → MSP.V4 F') :=
    e₁.toMonoidHom.comp (θ.toMonoidHom.comp (ι.comp p))
  have hβ : ∀ (v : ↥V) (i : Fin 1),
      Multiplicative.toAdd (β v) i = Multiplicative.toAdd (θ ⟨p v, hmemS₀ _⟩) := fun _ _ => rfl
  refine ⟨F', iF, fF, a', hcard, ha', hn.vn, inf_le_left, β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hs.surj ((θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd y 0)) : ↥S₀) :
      S)
    refine ⟨v, Multiplicative.toAdd.injective (funext fun i => ?_)⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hβ]
    have e : (⟨p v, hmemS₀ _⟩ : ↥S₀) = θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd y 0)) :=
      Subtype.ext hv
    rw [e, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hs.ker v]
    constructor
    · intro h1
      have h2 : θ ⟨p v, hmemS₀ _⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        have := congrArg (fun x : Multiplicative (Fin 1 → MSP.V4 F') =>
          Multiplicative.toAdd x 0) h1
        simpa [hβ] using this
      have h3 : (⟨p v, hmemS₀ _⟩ : ↥S₀) = 1 := by
        rw [← map_one θ] at h2
        exact θ.injective h2
      exact congrArg Subtype.val h3
    · intro h1
      apply Multiplicative.toAdd.injective
      funext i
      rw [hβ]
      have h3 : (⟨p v, hmemS₀ _⟩ : ↥S₀) = 1 := Subtype.ext h1
      rw [h3, map_one]
      rfl
  · intro g u v huv i
    rw [hβ, hβ]
    have hv : v = ⟨(g : (puAmalgam h.le).Universal) * u * (g : (puAmalgam h.le).Universal)⁻¹,
        huv ▸ v.2⟩ := Subtype.ext huv
    have h1 : (⟨p v, hmemS₀ _⟩ : ↥S₀) = restrict ρ hS₀ g ⟨p u, hmemS₀ _⟩ := by
      apply Subtype.ext
      rw [coe_restrict_apply, hs.conj g u (huv ▸ v.2)]
      exact congrArg p hv
    rw [h1, hθ]
    simp [moduleAct]

end NatHyp

end S512N

end CFSG.Quasithin.MS93
