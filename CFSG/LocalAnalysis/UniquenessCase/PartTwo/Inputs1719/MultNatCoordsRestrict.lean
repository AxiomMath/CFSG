module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem exists_realizesVia_restrict {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U : Subgroup W} {π : D.Gam →* ↥H}
    (hU : D.RealizesVia H U ⊥ π) :
    ∃ (H' : Subgroup (MulAut ↥U)) (π' : D.Gam →* ↥H'),
      H' = (actOnSub (fun (a : MulAut W) (ha : a ∈ H) (u : W) (hu : u ∈ U) =>
        hU.2.2.2.1 ⟨a, ha⟩ u hu)).range ∧
      (∀ γ : D.Gam,
        ((π' γ : ↥H') : MulAut ↥U) =
          actOnSub (fun (a : MulAut W) (ha : a ∈ H) (u : W) (hu : u ∈ U) =>
            hU.2.2.2.1 ⟨a, ha⟩ u hu) (π γ)) ∧
      D.RealizesVia H' ⊤ ⊥ π' := by
  obtain ⟨hπ, -, hker, hHU, -, hsec, hDker, β, hβs, hβk, hβe⟩ := hU
  let hKA : ∀ a ∈ H, ∀ u ∈ U, a u ∈ U :=
    fun a ha u hu => hHU ⟨a, ha⟩ u hu
  let f : ↥H →* MulAut ↥U := actOnSub hKA
  let H' : Subgroup (MulAut ↥U) := f.range
  let π' : D.Gam →* ↥H' := f.rangeRestrict.comp π
  have hπ' : ∀ γ : D.Gam, ((π' γ : ↥H') : MulAut ↥U) = f (π γ) := fun γ => rfl
  let τ : ↥(⊤ : Subgroup ↥U) ≃* ↥U := Subgroup.topEquiv
  let β' : ↥(⊤ : Subgroup ↥U) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp τ.toMonoidHom
  have hβ'u : ∀ u : ↥(⊤ : Subgroup ↥U), β' u = β (τ u) := fun u => rfl
  have hβ's : Function.Surjective β' := by
    intro x
    obtain ⟨u, hu⟩ := hβs x
    refine ⟨τ.symm u, ?_⟩
    rw [hβ'u, MulEquiv.apply_symm_apply]
    exact hu
  have hβ'k : ∀ u : ↥(⊤ : Subgroup ↥U), β' u = 1 ↔
      (u : ↥U) ∈ (⊥ : Subgroup ↥U) := by
    intro u
    rw [hβ'u, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      simpa using congrArg (fun x : ↥U => (x : W)) h
  have hβ'e : ∀ (γ : D.Gam) (u : ↥(⊤ : Subgroup ↥U)) (m : ↥D.sec)
      (hu : ((π' γ : ↥H') : MulAut ↥U) (u : ↥U) ∈ ⊤)
      (hm : D.act γ (m : D.Amb) ∈ D.sec),
      β' u = QuotientGroup.mk m →
        β' ⟨((π' γ : ↥H') : MulAut ↥U) (u : ↥U), hu⟩ =
          QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := by
    intro γ u m hu hm hβu
    set u' : ↥U := τ u with hu'
    have hβu' : β u' = QuotientGroup.mk m := hβu
    have hwU : ((π γ : ↥H) : MulAut W) (u' : W) ∈ U := hHU (π γ) u' u'.2
    have hstep : β ⟨((π γ : ↥H) : MulAut W) (u' : W), hwU⟩ =
        QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := hβe γ u' m hwU hm hβu'
    have hfcoe : ((f (π γ) u' : ↥U) : W) =
        ((π γ : ↥H) : MulAut W) (u' : W) := actOnSub_apply hKA (π γ) u'
    have hfEq : f (π γ) u' = ⟨((π γ : ↥H) : MulAut W) (u' : W), hwU⟩ := Subtype.ext hfcoe
    have hact : τ ⟨((π' γ : ↥H') : MulAut ↥U) (u : ↥U), hu⟩ = f (π γ) u' := by
      apply Subtype.ext
      change (((π' γ : ↥H') : MulAut ↥U) (u : ↥U) : W) = ((f (π γ) u' : ↥U) : W)
      rw [hπ' γ]
      rfl
    rw [hβ'u, hact, hfEq, hstep]
  have hπ's : Function.Surjective π' := by
    intro x
    obtain ⟨h, hh⟩ := x.2
    obtain ⟨γ, hγ⟩ := hπ h
    refine ⟨γ, Subtype.ext ?_⟩
    change f (π γ) = (x : MulAut ↥U)
    rw [hγ]
    exact hh
  exact ⟨H', π', rfl, hπ', hπ's, bot_le, hker,
    fun h u _ => Subgroup.mem_top _,
    fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one],
    hsec, hDker, β', hβ's, hβ'k, hβ'e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
