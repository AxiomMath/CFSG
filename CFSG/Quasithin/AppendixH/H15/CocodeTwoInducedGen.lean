module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiPair
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiRange

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem induced_2b (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    ∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
      ((∀ u ∈ fixV (rImg ρ (octFix O)), ρ g u = u) ↔ (g : S24) ∈ octFix O) := by
  intro g _
  constructor
  · intro hfix
    obtain ⟨P⟩ := exists_phiData hM
    exact P.mem_octFix_of_fix_pairs hM fun p q _ _ =>
      hfix _ (P.range_le_fixV hM (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
  · intro hgfix u hu
    exact (mem_fixV.mp hu) (ρ g)
      (Subgroup.mem_map.mpr ⟨g, Subgroup.mem_subgroupOf.mpr hgfix, rfl⟩)

theorem inducesOn_phi (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (P : PhiData O β)
    (hker : P.φ.ker = ⊥) (Ω : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))))
    (h1 : ∀ m : ↥Γ, (m : S24) ∈ MY Γ (Yd d a b O) →
      ∃ σ ∈ alternatingGroup (Fin 8), (∀ p, (m : S24) (P.o p) = P.o (σ p)) ∧ evActHom σ ∈ Ω)
    (h2 : ∀ γ ∈ Ω, ∃ m : ↥Γ, (m : S24) ∈ MY Γ (Yd d a b O) ∧
      ∃ σ ∈ alternatingGroup (Fin 8), (∀ p, (m : S24) (P.o p) = P.o (σ p)) ∧ evActHom σ = γ) :
    InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (octFix O))) ⊥
      (Multiplicative (Fin 6 → ZMod 2)) Ω := by
  have hinj : Function.Injective P.φ := (MonoidHom.ker_eq_bot_iff P.φ).mp hker
  have hU : P.φ.range = fixV (rImg ρ (octFix O)) := P.range_eq_fixV hM
  let β : ↥(fixV (rImg ρ (octFix O))) →* Multiplicative (Fin 6 → ZMod 2) :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (Subgroup.inclusion hU.ge)
  have hψ : ∀ u : ↥(fixV (rImg ρ (octFix O))), P.φ (β u) = (u : V) := by
    intro u
    change P.φ ((MonoidHom.ofInjective hinj).symm (Subgroup.inclusion hU.ge u)) = (u : V)
    rw [← MonoidHom.ofInjective_apply hinj, MulEquiv.apply_symm_apply]
    rfl
  have hβsurj : Function.Surjective β := by
    intro a
    refine ⟨⟨P.φ a, hU.le (MonoidHom.mem_range.mpr ⟨a, rfl⟩)⟩, ?_⟩
    apply hinj
    rw [hψ]
  have hβker : ∀ u : ↥(fixV (rImg ρ (octFix O))), β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := by
    intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      rw [← hψ u, h, map_one]
    · intro h
      apply hinj
      rw [hψ u, h, map_one]
  unfold InducesOn
  refine ⟨bot_le, ?_, ?_, β, hβsurj, hβker, ?_, ?_⟩
  · intro g hg u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
    have hmMY : (m : S24) ∈ MY Γ (Yd d a b O) := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨σ, _, hσ, _⟩ := h1 m hmMY
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hU.ge hu)
    rw [P.equivariant hM hσ x]
    exact hU.le (MonoidHom.mem_range.mpr ⟨evActHom σ x, rfl⟩)
  · intro g _ z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one g
  · intro g hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
    have hmMY : (m : S24) ∈ MY Γ (Yd d a b O) := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨σ, _, hσ, hσΩ⟩ := h1 m hmMY
    refine ⟨evActHom σ, hσΩ, ?_⟩
    intro u u' huu
    apply hinj
    calc P.φ (β u') = (u' : V) := hψ u'
      _ = ρ m u := huu
      _ = ρ m (P.φ (β u)) := by rw [hψ u]
      _ = P.φ (evActHom σ (β u)) := P.equivariant hM hσ (β u)
  · intro γ hγ
    obtain ⟨m, hmMY, σ, _, hσ, hσeq⟩ := h2 γ hγ
    refine ⟨ρ m, Subgroup.mem_map.mpr
      ⟨m, Subgroup.mem_subgroupOf.mpr hmMY, rfl⟩, ?_⟩
    intro u u' huu
    apply hinj
    calc P.φ (β u') = (u' : V) := hψ u'
      _ = ρ m u := huu
      _ = ρ m (P.φ (β u)) := by rw [hψ u]
      _ = P.φ (evActHom σ (β u)) := P.equivariant hM hσ (β u)
      _ = P.φ (γ (β u)) := congrArg (fun f => P.φ (f (β u))) hσeq

end CFSG.ASVolI.AppH

