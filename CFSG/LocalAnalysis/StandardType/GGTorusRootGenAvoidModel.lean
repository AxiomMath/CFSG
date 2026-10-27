module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTorusModelAt (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* G) (ι : Type) (w : ι → G)
    (s : ι → MulAut (Fin k → Multiplicative (ZMod p))) (S : ι → Subgroup G),
    Nonempty ι ∧ Function.Injective τ ∧ τ.range = E ∧
    (∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) ∧ (∀ i, s i * s i = 1) ∧
    (∀ i, Nat.card {f // s i f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p))) ∧
    Function.Injective s ∧ (∀ i, w i ∈ S i) ∧
    (∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f}))) ∧
    (∀ i, p ∣ Nat.card (S i)) ∧ ∀ j, (⨆ (i : ι) (_ : i ≠ j), S i) = ⊤

theorem GGTorusModelAt.map {p : ℕ} {G G' : Type} [Group G] [Group G'] {E : Subgroup G}
    (h : GGTorusModelAt p E) (α : G ≃* G') : GGTorusModelAt p (E.map α.toMonoidHom) := by
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτE, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ := h
  refine ⟨k, α.toMonoidHom.comp τ, ι, fun i => α (w i), s, fun i => (S i).map α.toMonoidHom, hι,
    α.injective.comp hτ, by rw [MonoidHom.range_comp, hτE], fun i f => ?_, hs, hfix, hsinj,
    fun i => Subgroup.mem_map_of_mem _ (hwS i), fun i => ?_, fun i => ?_, fun j => ?_⟩
  · change α (w i) * α (τ f) * (α (w i))⁻¹ = α (τ (s i f))
    rw [← hws i f, map_mul, map_mul, map_inv]
  · have hC : (Subgroup.centralizer (τ '' {f | s i f = f})).map α.toMonoidHom =
        Subgroup.centralizer ((α.toMonoidHom.comp τ) '' {f | s i f = f}) := by
      ext x
      simp only [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Set.forall_mem_image,
        MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      refine forall₂_congr fun f _ => ?_
      rw [← α.injective.eq_iff, map_mul, map_mul, MulEquiv.apply_symm_apply]
    rw [← hC]
    exact isComponentOf_map_mulEquiv α (hcomp i)
  · rw [Subgroup.card_map_of_injective α.injective]
    exact hdvd i
  · rw [← Subgroup.map_top_of_surjective α.toMonoidHom α.surjective, ← hgen j]
    simp only [Subgroup.map_iSup]

private theorem exists_mulCoords_of_ggTorusModelAt {p : ℕ} {G : Type} [Group G]
    {E : Subgroup G} (h : GGTorusModelAt p E) :
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* G) (ι : Type) (w : ι → G)
      (s : ι → MulAut (Multiplicative (Fin k → ZMod p))) (S : ι → Subgroup G),
      Nonempty ι ∧ Function.Injective τ ∧ τ.range = E ∧
      (∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) ∧ (∀ i, s i * s i = 1) ∧
      (∀ i, Nat.card {f // s i f = f} * p = p ^ k) ∧ Function.Injective s ∧
      (∀ i, w i ∈ S i) ∧
      (∀ i, IsComponentOf (S i) (Subgroup.centralizer {x | x ∈ τ.range ∧ w i * x = x * w i})) ∧
      (∀ i, p ∣ Nat.card (S i)) ∧ ∀ j, (⨆ (i : ι) (_ : i ≠ j), S i) = ⊤ := by
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτE, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ := h
  let ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)) :=
    MulEquiv.piMultiplicative _
  let τ' : Multiplicative (Fin k → ZMod p) →* G := τ.comp ε.toMonoidHom
  have hrange : τ'.range = τ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.surjective, ← MonoidHom.range_eq_map]
  let s' : ι → MulAut (Multiplicative (Fin k → ZMod p)) := fun i => MulAut.congr ε.symm (s i)
  have hs'app : ∀ i f, s' i f = ε.symm (s i (ε f)) := fun i f => rfl
  have hfix' : ∀ i, Nat.card {f // s' i f = f} * p = p ^ k := by
    intro i
    have h1 : Nat.card {f // s' i f = f} = Nat.card {g // s i g = g} := by
      refine Nat.card_congr (Equiv.subtypeEquiv ε.toEquiv fun f => ?_)
      rw [hs'app]
      constructor
      · intro h
        have h2 := congrArg ε h
        rwa [MulEquiv.apply_symm_apply] at h2
      · intro h
        change s i (ε f) = ε f at h
        change ε.symm (s i (ε f)) = f
        rw [h, MulEquiv.symm_apply_apply]
    have h2 : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [← Nat.card_congr ε.toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin k → ZMod p) ≃ _), Nat.card_fun,
        Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    rw [h1, hfix i, h2]
  have hset : ∀ i, {x : G | x ∈ τ'.range ∧ w i * x = x * w i} = τ '' {f | s i f = f} := by
    intro i
    ext x
    constructor
    · rintro ⟨hx, hw⟩
      rw [hrange] at hx
      obtain ⟨f, rfl⟩ := hx
      refine ⟨f, ?_, rfl⟩
      apply hτ
      rw [← hws i f, hw, mul_inv_cancel_right]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨hrange ▸ ⟨f, rfl⟩, ?_⟩
      have h := hws i f
      rw [show s i f = f from hf] at h
      calc w i * τ f = w i * τ f * (w i)⁻¹ * w i := by group
        _ = τ f * w i := by rw [h]
  refine ⟨k, τ', ι, w, s', S, hι, hτ.comp ε.injective, hrange.trans hτE, fun i f => ?_,
    fun i => ?_, hfix', fun i j h => hsinj ((MulAut.congr ε.symm).injective h), hwS,
    fun i => by rw [hset i]; exact hcomp i, hdvd, hgen⟩
  · change w i * τ (ε f) * (w i)⁻¹ = τ (ε (s' i f))
    rw [hs'app, MulEquiv.apply_symm_apply]
    exact hws i (ε f)
  · ext f
    rw [MulAut.mul_apply, hs'app, hs'app, MulEquiv.apply_symm_apply, ← MulAut.mul_apply, hs i,
      MulAut.one_apply, MulEquiv.symm_apply_apply, MulAut.one_apply]

theorem ggTorusRootGenAvoidKG_of_scTorusModel {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] {I : Set (MulAut G)}
    (hinj : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* G), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Function.Injective ψ)
    (hZ : Subgroup.center G = ⊥) (hI : I ⊆ Set.range (MulAut.conj : G →* MulAut G))
    (hmodel : ∀ E : Subgroup G, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
      (∀ g : G, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGTorusModelAt p E) :
    GGTorusRootGenAvoidKG p r G I := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hψinj : Function.Injective ψ := hinj L' ψ hψ hker hperf
  let Ψ : L' ≃* G := MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  have hψsymm : ∀ x : G, ψ (Ψ.symm x) = x := fun x => MulEquiv.apply_symm_apply Ψ x
  let Λ : G →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp Ψ.symm.toMonoidHom
  have hΛinj : Function.Injective Λ := by
    intro e₁ e₂ h
    have h1 : MulAut.conj (Ψ.symm e₁) = MulAut.conj (Ψ.symm e₂) := h
    have h2 := ReflInner.map_eq_of_conj_eq hψ hZ h1
    simpa only [hψsymm] using h2
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [show (Λ e) l = MulAut.conj (Ψ.symm e) l from rfl, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hψsymm e, ← hφ l, MulAut.conj_apply]
  set E : Subgroup G := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from by rw [he]; exact a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have h1 : MulAut.conj (Ψ.symm g) ∈ A := by
      refine hsc (Ψ.symm g) (fun a ha => ?_) (by rw [← map_pow, hgp, map_one])
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have he : e ∈ E := by
        rw [hE]
        exact ha
      have h2 : e * g * e⁻¹ = g := by rw [← hg e he, mul_inv_cancel_right]
      show Ψ.symm e * Ψ.symm g * (Ψ.symm e)⁻¹ = Ψ.symm g
      rw [← map_inv Ψ.symm e, ← map_mul Ψ.symm, ← map_mul Ψ.symm, h2]
    rw [hE]
    exact h1
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτE, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ :=
    exists_mulCoords_of_ggTorusModelAt
      (hmodel E hEab (by rw [hcardE]; exact hr) (by rw [hcardE]; exact h3) hscE)
  have hcardT : Nat.card τ.range = p ^ k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin k → ZMod p) ≃ _), Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  have hcardA : Nat.card A = p ^ k := by
    rw [← hcardE, ← hτE, hcardT]
  let Φ : G ≃* L' := Ψ.symm
  have hψΦ : ∀ x : G, ψ (Φ x) = x := hψsymm
  let σ : Multiplicative (Fin k → ZMod p) →* L' := Φ.toMonoidHom.comp τ
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => hψΦ (τ f)
  have hconj_inj : Function.Injective (MulAut.conj : L' →* MulAut L') :=
    fun x y h => hψinj (ReflInner.map_eq_of_conj_eq hψ hZ h)
  have hσmem : ∀ f, (MulAut.conj (σ f) : MulAut L') ∈ A := by
    intro f
    have hmemE : τ f ∈ E := by
      rw [← hτE]
      exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
    rw [hE] at hmemE
    exact hmemE
  let Θ₀ : Multiplicative (Fin k → ZMod p) →* ↥A :=
    ((MulAut.conj : L' →* MulAut L').comp σ).codRestrict A hσmem
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g' hfg => ?_, fun a => ?_⟩
    · have h1 : MulAut.conj (σ f) = MulAut.conj (σ g') := congrArg Subtype.val hfg
      exact hτ (Φ.injective (hconj_inj h1))
    · obtain ⟨e, he⟩ := hAΛ a a.2
      have heE : e ∈ E := by
        rw [hE]
        change Λ e ∈ A
        rw [he]
        exact a.2
      rw [← hτE] at heE
      obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp heE
      refine ⟨f, Subtype.ext ?_⟩
      show MulAut.conj (σ f) = a
      rw [← he, ← hf]
      rfl
  let Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f => rfl
  intro ρ
  let nOf (i : ι) : L' := Φ (w i)
  have hreflect_congr : ∀ i, GGIsReflection p (MulAut.congr Θ (s i)) := by
    intro i
    have hsq : MulAut.congr Θ (s i) * MulAut.congr Θ (s i) = 1 := by
      rw [← map_mul, hs i, map_one]
    refine ⟨hsq, ?_⟩
    have hfix' : Nat.card {b : ↥A // MulAut.congr Θ (s i) b = b} =
        Nat.card {f : Multiplicative (Fin k → ZMod p) // s i f = f} := by
      refine Nat.card_congr (Equiv.subtypeEquiv Θ.symm.toEquiv fun b => ?_)
      rw [MulAut.congr_apply]
      show Θ (s i (Θ.symm b)) = b ↔ s i (Θ.symm b) = Θ.symm b
      constructor
      · intro hb
        have h1 := congrArg Θ.symm hb
        rwa [MulEquiv.symm_apply_apply] at h1
      · intro hb
        rw [hb, MulEquiv.apply_symm_apply]
    rw [hfix', hfix i, hcardA]
  have hkey : ∀ i, ∃ (hn : MulAut.conj (nOf i) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt p A (nOf i) ∧ GGIsReflection p (ggConjAut A hn) ∧
        ggConjAut A hn = MulAut.congr Θ (s i) := by
    intro i
    have hs' : ∀ f, ψ (nOf i) * ψ (σ f) * (ψ (nOf i))⁻¹ = ψ (σ (s i f)) := by
      intro f
      rw [hψΦ (w i), hψσ f, hψσ (s i f)]
      exact hws i f
    obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘval
      (n := nOf i) (s := s i) hs'
    have hweyl : GGTorusWeylElt p A (nOf i) :=
      ggTorusWeylElt_of_model (p := p) (k := k) hker Θ hΘval (n := nOf i)
        (fun f => ⟨s i f, hs' f⟩)
    have hreflect : GGIsReflection p (ggConjAut A hn) := by
      rw [heq]
      exact hreflect_congr i
    exact ⟨hn, hweyl, hreflect, heq⟩
  have huniq : ∀ i j : ι, ggConjAut A ((hkey i).choose) = ggConjAut A ((hkey j).choose) →
      i = j := by
    intro i j h
    have hi := (hkey i).choose_spec.2.2
    have hj := (hkey j).choose_spec.2.2
    have h1 : MulAut.congr Θ (s i) = MulAut.congr Θ (s j) := by
      rw [← hi, ← hj]
      exact h
    exact hsinj ((MulAut.congr Θ).injective h1)
  set ρ₀ : ι := if h : ∃ i : ι, ggConjAut A ((hkey i).choose) = ρ then Classical.choose h
    else Classical.arbitrary ι with hρ₀def
  have hρ₀ : ∀ i : ι, ggConjAut A ((hkey i).choose) = ρ → i = ρ₀ := by
    intro i hi
    have hex : ∃ j : ι, ggConjAut A ((hkey j).choose) = ρ := ⟨i, hi⟩
    have hspec := Classical.choose_spec hex
    rw [hρ₀def, dif_pos hex]
    exact huniq i (Classical.choose hex) (hi.trans hspec.symm)
  have hhyp : ∀ i, ggHypCent A (nOf i) = (Subgroup.centralizer
      {x : G | x ∈ τ.range ∧ w i * x = x * w i}).map Φ.toMonoidHom := by
    intro i
    have hwcomm : ∀ f, (MulAut.conj (nOf i) * Θ f = Θ f * MulAut.conj (nOf i)) ↔
        (w i * τ f = τ f * w i) := by
      intro f
      rw [hΘval f]
      constructor
      · intro h
        have h' : MulAut.conj (nOf i * σ f) = MulAut.conj (σ f * nOf i) := by
          simpa only [map_mul] using h
        have h2 : nOf i * σ f = σ f * nOf i := hconj_inj h'
        exact Φ.injective (by rw [map_mul, map_mul]; exact h2)
      · intro h
        have h1 : nOf i * σ f = σ f * nOf i := by
          change Φ (w i) * Φ (τ f) = Φ (τ f) * Φ (w i)
          rw [← map_mul, ← map_mul]
          exact congrArg Φ h
        rw [← map_mul, ← map_mul]
        exact congrArg MulAut.conj h1
    have hmem : ∀ l : L', l ∈ ggHypCent A (nOf i) ↔
        ∀ f, w i * τ f = τ f * w i → σ f * l = l * σ f := by
      intro l
      rw [ggHypCent]
      simp only [Subgroup.mem_iInf, mem_ggFix]
      constructor
      · intro hl f hf
        have h1 : ((Θ f : ↥A) : MulAut L') l = l :=
          hl ((Θ f : ↥A) : MulAut L') ⟨(Θ f).2, (hwcomm f).mpr hf⟩
        rw [hΘval f, MulAut.conj_apply] at h1
        calc σ f * l = (σ f * l * (σ f)⁻¹) * σ f := by group
          _ = l * σ f := by rw [h1]
      · intro hl a ha
        obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha.1⟩
        have hae : ((Θ f : ↥A) : MulAut L') = a := congrArg Subtype.val hf
        have hcomm : MulAut.conj (nOf i) * ((Θ f : ↥A) : MulAut L') =
            ((Θ f : ↥A) : MulAut L') * MulAut.conj (nOf i) := by
          rw [hae]
          exact ha.2
        rw [← hae, hΘval f, MulAut.conj_apply]
        have hf' : w i * τ f = τ f * w i := (hwcomm f).mp hcomm
        rw [hl f hf']
        group
    have hmem2 : ∀ l : L', l ∈ (Subgroup.centralizer
        {x : G | x ∈ τ.range ∧ w i * x = x * w i}).map Φ.toMonoidHom ↔
        ∀ f, w i * τ f = τ f * w i → σ f * l = l * σ f := by
      intro l
      constructor
      · intro hl f hf
        rw [Subgroup.mem_map] at hl
        obtain ⟨y, hy, hyl⟩ := hl
        have hx : τ f ∈ {x : G | x ∈ τ.range ∧ w i * x = x * w i} :=
          ⟨MonoidHom.mem_range.mpr ⟨f, rfl⟩, hf⟩
        have hcomm := (Subgroup.mem_centralizer_iff.mp hy) (τ f) hx
        have hyl' : Φ y = l := hyl
        have h1 : Φ (τ f) * l = l * Φ (τ f) := by
          rw [← hyl', ← map_mul, ← map_mul, hcomm]
        exact h1
      · intro hl
        rw [Subgroup.mem_map]
        refine ⟨Φ.symm l, ?_, Φ.apply_symm_apply l⟩
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hx.1
        rw [← hf] at hx ⊢
        apply Φ.injective
        rw [map_mul, map_mul, Φ.apply_symm_apply]
        exact hl f hx.2
    refine Subgroup.ext fun l => ?_
    rw [hmem l, hmem2 l]
  refine le_antisymm le_top ?_
  rw [← Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective, ← hgen ρ₀, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hi => ?_
  have hweyl : GGTorusWeylElt p A (nOf i) := (hkey i).choose_spec.1
  have hreflect : GGIsReflection p (ggConjAut A ((hkey i).choose)) := (hkey i).choose_spec.2.1
  have hne : ggConjAut A ((hkey i).choose) ≠ ρ := fun hcon => hi (hρ₀ i hcon)
  have hnmemJ : nOf i ∈ (S i).map Φ.toMonoidHom := Subgroup.mem_map_of_mem Φ.toMonoidHom (hwS i)
  have hdvd' : p ∣ Nat.card ((S i).map Φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective Φ.injective]
    exact hdvd i
  have hComp : IsComponentOf ((S i).map Φ.toMonoidHom) (ggHypCent A (nOf i)) := by
    have h1 := isComponentOf_map_mulEquiv Φ (hcomp i)
    rwa [← hhyp i] at h1
  refine le_iSup_of_le (nOf i) ?_
  refine le_iSup_of_le ((hkey i).choose) ?_
  refine le_iSup_of_le ((S i).map Φ.toMonoidHom) ?_
  exact le_iSup_of_le ⟨hweyl, hreflect, hne, hnmemJ, hComp, hdvd'⟩ le_rfl

theorem ggTorusRootGenAvoidKG_of_torusModel {p k r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] {I : Set (MulAut G)}
    (hinj : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* G), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Function.Injective ψ)
    (hZ : Subgroup.center G = ⊥) (hI : I ⊆ Set.range (MulAut.conj : G →* MulAut G))
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (hτ : Function.Injective τ)
    (hconj : ∀ E : Subgroup G, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
      ∃ α : G ≃* G, E = τ.range.map α.toMonoidHom)
    {ι : Type} [Nonempty ι] (w : ι → G) (s : ι → MulAut (Fin k → Multiplicative (ZMod p)))
    (S : ι → Subgroup G)
    (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f))
    (hs : ∀ i, s i * s i = 1)
    (hfix : ∀ i, Nat.card {f // s i f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)))
    (hsinj : Function.Injective s)
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hgen : ∀ j, (⨆ (i : ι) (_ : i ≠ j), S i) = ⊤) :
    GGTorusRootGenAvoidKG p r G I := by
  refine ggTorusRootGenAvoidKG_of_scTorusModel hp hinj hZ hI fun E hE hr h3 _ => ?_
  obtain ⟨α, rfl⟩ := hconj E hE hr h3
  exact GGTorusModelAt.map
    ⟨k, τ, ι, w, s, S, inferInstance, hτ, rfl, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ α

end CFSG.StandardType

end
