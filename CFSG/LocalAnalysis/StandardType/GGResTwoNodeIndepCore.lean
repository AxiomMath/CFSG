module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepData
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepExclude

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIndep_absIrred_mono {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A B : Subgroup (U ≃ₗ[ZMod p] U)} (hAB : A ≤ B) (h : ZS.AbsIrred p A) : ZS.AbsIrred p B :=
  ⟨fun W hW => h.1 W (fun a ha w hw => hW a (hAB ha) w hw),
    fun T hT => h.2 T (fun a ha => hT a (hAB ha))⟩

theorem ggIndep_absIrred_of_restrict_top {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (U : Submodule (ZMod p) V) (hU : U = ⊤) (R : Subgroup (V ≃ₗ[ZMod p] V))
    (res : ↥R →* (↥U ≃ₗ[ZMod p] ↥U))
    (he : ∀ (g : ↥R) (u : ↥U), ((res g u : ↥U) : V) = (g : V ≃ₗ[ZMod p] V) u)
    (hirr : ZS.AbsIrred p res.range) : ZS.AbsIrred p R := by
  have hmem : ∀ v : V, v ∈ U := fun v => by rw [hU]; trivial
  constructor
  · intro X hX
    have hX' : ∀ a ∈ res.range, ∀ w ∈ X.comap U.subtype, a w ∈ X.comap U.subtype := by
      rintro a ⟨g, rfl⟩ w hw
      show ((res g w : ↥U) : V) ∈ X
      rw [he]
      exact hX g g.2 w hw
    rcases hirr.1 (X.comap U.subtype) hX' with h0 | h1
    · left
      rw [eq_bot_iff]
      intro v hv
      have hv' : (⟨v, hmem v⟩ : ↥U) ∈ X.comap U.subtype := hv
      rw [h0] at hv'
      have hv0 : (⟨v, hmem v⟩ : ↥U) = 0 := hv'
      have := congrArg Subtype.val hv0
      simpa using this
    · right
      rw [eq_top_iff]
      intro v _
      have hv' : (⟨v, hmem v⟩ : ↥U) ∈ X.comap U.subtype := by rw [h1]; trivial
      exact hv'
  · intro T hT
    let T' : Module.End (ZMod p) ↥U :=
      { toFun := fun u => ⟨T u.1, hmem _⟩
        map_add' := fun a b => Subtype.ext (map_add T a.1 b.1)
        map_smul' := fun c a => Subtype.ext (map_smul T c a.1) }
    obtain ⟨c, hc⟩ := hirr.2 T' (by
      rintro a ⟨g, rfl⟩
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      have h1 := congrArg (fun f : Module.End (ZMod p) V => f u.1) (hT g g.2)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1 ⊢
      show T ((res g u : ↥U) : V) = ((res g (T' u) : ↥U) : V)
      rw [he g u, he g (T' u)]
      exact h1)
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro v
    have h2 := congrArg (fun f : Module.End (ZMod p) ↥U => ((f ⟨v, hmem v⟩ : ↥U) : V)) hc
    simpa [T'] using h2

theorem ggIndepFrame_finrank_le {p N : ℕ} [Fact p.Prime] (hN : 1 ≤ N) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGIndepAFrame p N h α x) :
    Module.finrank (ZMod p) V ≤ N := by
  let Φ : V →ₗ[ZMod p] (Fin (N - 1) → ZMod p) := LinearMap.pi α
  have hker : LinearMap.ker Φ ≤ Submodule.span (ZMod p) {x} := by
    intro v hv
    apply F.fix v
    intro i
    have := congrFun (LinearMap.mem_ker.mp hv) i
    simpa [Φ] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : Module.finrank (ZMod p) ↥(LinearMap.range Φ) ≤ N - 1 := by
    calc Module.finrank (ZMod p) ↥(LinearMap.range Φ)
        ≤ Module.finrank (ZMod p) (Fin (N - 1) → ZMod p) := Submodule.finrank_le _
      _ = N - 1 := by simp
  have h3 : Module.finrank (ZMod p) ↥(LinearMap.ker Φ) ≤ 1 := by
    calc Module.finrank (ZMod p) ↥(LinearMap.ker Φ)
        ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {x}) := Submodule.finrank_mono hker
      _ = 1 := finrank_span_singleton F.x_ne
  omega

theorem ggIndepFrame_finrank_ge {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGIndepAFrame p N h α x) :
    N - 1 ≤ Module.finrank (ZMod p) V := by
  have := F.indep.fintype_card_le_finrank
  simpa using this

theorem ggIndepA_false_of_mem (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hN : 10 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGIndepAFrame p N h α x) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod p] V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ (N - 1) * (6 * (p - 1) * Nat.factorial N))
    (hmem : ha ∈ Submodule.span (ZMod p) (Set.range h)) : False := by
  obtain ⟨U, res, -, -, -, hdim, hirr, hgen, hres, ψ, hψ⟩ :=
    ggIndep_data (by omega) (by omega) F r hr ra ha αa hra hαa hw hnt
  rcases hdim with ⟨-, hU⟩ | ⟨hnm, -⟩
  · exact ggIndep_exclude hKG hp hN F.dvd hU res.range hirr hgen (hres.trans hcard) ψ hψ
  · exact hnm hmem

theorem ggIndepA_top {p N : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGIndepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hnmem : ha ∉ Submodule.span (ZMod p) (Set.range h))
    (hVN : Module.finrank (ZMod p) V ≤ N) :
    Module.finrank (ZMod p) V = N ∧ ZS.AbsIrred p (Subgroup.closure (Set.range r ∪ {ra})) := by
  obtain ⟨U, res, he, -, -, hdim, hirr, -, -, -, -⟩ :=
    ggIndep_data hp hN F r hr ra ha αa hra hαa hw hnt
  rcases hdim with ⟨hmem, -⟩ | ⟨-, hU⟩
  · exact absurd hmem hnmem
  · have hle : Module.finrank (ZMod p) ↥U ≤ Module.finrank (ZMod p) V := Submodule.finrank_le U
    have hVeq : Module.finrank (ZMod p) V = N := by omega
    have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    exact ⟨hVeq, ggIndep_absIrred_of_restrict_top U hUtop _ res he hirr⟩

end CFSG.StandardType

end
