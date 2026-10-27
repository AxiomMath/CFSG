module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_addEquiv_imgSub {ι : Type} {G : Type} [Group G] {Kg K' : Type} [Field Kg]
    [Field K'] {Q Z V : Subgroup G} {γ : G → Kg} (M₀ : Tim79.QuadModel Q Z Kg γ)
    (hVQ : V ≤ Q) (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K')) :
    ∃ Ψ : ↥(imgSub M₀ V hS) ≃+ (ι → K'), ∀ (v : ↥V) (h : M₀.π v ∈ imgSub M₀ V hS),
      Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
  classical
  let A : Submodule Kg M₀.E := imgSub M₀ V hS
  have hπV : ∀ v : ↥V, M₀.π v ∈ A := fun v => M₀.pi_mem_img v.2 (hVQ v.2)
  let κ : ↥V →* Multiplicative ↥A :=
    { toFun := fun v => Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext M₀.pi_one
      map_mul' := fun x y => by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2)) }
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, -, hx⟩ := a.toAdd.2
    exact ⟨⟨x, hxV⟩, by
      show Multiplicative.ofAdd (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥A) = a
      apply congrArg Multiplicative.ofAdd
      exact Subtype.ext hx⟩
  have hker : κ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2)]
    constructor
    · intro h
      exact congrArg Subtype.val (Multiplicative.ofAdd.injective h)
    · intro h
      exact congrArg Multiplicative.ofAdd (Subtype.ext h)
  let e₁ : ↥V ⧸ κ.ker ≃* Multiplicative ↥A := QuotientGroup.quotientKerEquivOfSurjective κ hκsurj
  let e₂ : ↥V ⧸ Z.subgroupOf V ≃* ↥V ⧸ κ.ker := QuotientGroup.quotientMulEquivOfEq hker.symm
  let Ψm : Multiplicative ↥A ≃* Multiplicative (ι → K') :=
    e₁.symm.trans (e₂.symm.trans ψ)
  let Ψ : ↥A ≃+ (ι → K') := AddEquiv.toMultiplicative.symm Ψm
  have hΨ : ∀ v : ↥V, Ψ ⟨M₀.π v, hπV v⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro v
    show Multiplicative.toAdd (Ψm (Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩)) = _
    have h1 : e₁.symm (κ v) = QuotientGroup.mk v := by
      apply e₁.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 : e₂.symm (QuotientGroup.mk v) = QuotientGroup.mk v := rfl
    show Multiplicative.toAdd (ψ (e₂.symm (e₁.symm (κ v)))) = _
    rw [h1, h2]
  exact ⟨Ψ, fun v h => hΨ v⟩

end CFSG.RankThree.GF2n.Stroth80
