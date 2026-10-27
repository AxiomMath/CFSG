module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l6tr_refl_ne_one {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (h : GGIsReflection p φ) : φ ≠ 1 := by
  intro h1
  obtain ⟨-, hfix⟩ := h
  have hfix1 : Nat.card {b : ↥Bs // φ b = b} = Nat.card ↥Bs :=
    Nat.card_congr
      { toFun := fun x => x.1
        invFun := fun b => ⟨b, by rw [h1]; simp⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun b => rfl }
  rw [hfix1] at hfix
  have hne : Nat.card ↥Bs ≠ 0 := by
    have hle1 : 1 ≤ Nat.card ↥Bs := by
      have hcard := Nat.card_le_card_of_injective (fun _ : Fin 1 => (1 : ↥Bs))
        (fun a b _ => Subsingleton.elim a b)
      simpa using hcard
    omega
  have hp1 : p = 1 := mul_left_cancel₀ hne (by rw [hfix, mul_one])
  exact (Fact.out : p.Prime).ne_one hp1

lemma l6tr_span_eq {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hA : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    Submodule.span (ZMod p) (Set.range h) =
      Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    have hex : ∃ w : V, α i w • h i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hgg : ggLin (p := p) ι (φ i) = 1 := by
        ext w
        rw [hφ i w, hcon w, sub_zero]
        simp
      have hphi1 : φ i = 1 :=
        ggLin_injective (p := p) ι (by rw [hgg, map_one (ggLin (p := p) ι)])
      exact l6tr_refl_ne_one (hrefl i) hphi1
    obtain ⟨w, hw⟩ := hex
    have hc : α i w ≠ 0 := fun hc0 => hw (by rw [hc0, zero_smul])
    have hmem : φ i ∈ ggAutomizer X Bs := by
      rw [hA]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hgen : ggLin (p := p) ι (φ i) w - w ∈
        Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
          ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) :=
      Submodule.subset_span ⟨(⟨φ i, hmem⟩, w), rfl⟩
    have heq : ggLin (p := p) ι (φ i) w - w = (-(α i w)) • h i := by
      rw [hφ i w, neg_smul]
      abel
    rw [heq] at hgen
    have hsm := Submodule.smul_mem _ ((-(α i w))⁻¹) hgen
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hc), one_smul] at hsm
  · rw [Submodule.span_le]
    rintro v ⟨q, rfl⟩
    exact ggAutomizer_sub_mem_span (p := p) hφ hA q.1.2 q.2

theorem l6tr_normalizer_span {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hA : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    {t : MulAut ↥Bs} (ht : t ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs))) :
    ∀ v ∈ Submodule.span (ZMod p) (Set.range h),
      ggLin (p := p) ι t v ∈ Submodule.span (ZMod p) (Set.range h) := by
  let gen : ↥(ggAutomizer X Bs) × V → V :=
    fun q => ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2
  have hspan : Submodule.span (ZMod p) (Set.range h) =
      Submodule.span (ZMod p) (Set.range gen) := l6tr_span_eq (p := p) hφ hrefl hA
  rw [hspan]
  intro v hv
  refine Submodule.span_induction (p := fun v _ => ggLin (p := p) ι t v ∈
      Submodule.span (ZMod p) (Set.range gen)) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨q, rfl⟩
    have htq : t * (q.1 : MulAut ↥Bs) * t⁻¹ ∈ ggAutomizer X Bs :=
      (Subgroup.mem_normalizer_iff.mp ht (q.1 : MulAut ↥Bs)).mp q.1.2
    have hmem : ggLin (p := p) ι (t * (q.1 : MulAut ↥Bs) * t⁻¹)
        (ggLin (p := p) ι t q.2) - ggLin (p := p) ι t q.2 ∈
        Submodule.span (ZMod p) (Set.range gen) :=
      Submodule.subset_span
        ⟨(⟨t * (q.1 : MulAut ↥Bs) * t⁻¹, htq⟩, ggLin (p := p) ι t q.2), rfl⟩
    have hid : ggLin (p := p) ι t (ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2) =
        ggLin (p := p) ι (t * (q.1 : MulAut ↥Bs) * t⁻¹)
          (ggLin (p := p) ι t q.2) := by
      rw [map_mul, map_mul, map_inv]
      simp
    rw [map_sub, hid]
    exact hmem
  · simp
  · intro a b ha hb iha ihb
    rw [map_add]
    exact Submodule.add_mem _ iha ihb
  · intro c a ha iha
    rw [map_smul]
    exact Submodule.smul_mem _ c iha

@[expose] noncomputable def l6tr_iso {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') : V ≃ₗ[ZMod p] V' :=
  LinearEquiv.ofBijective ((ι.symm.trans ι').toAddMonoidHom.toZModLinearMap p)
    (ι.symm.trans ι').bijective

lemma l6tr_iso_apply {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') (v : V) :
    l6tr_iso (p := p) ι ι' v = ι' (ι.symm v) := rfl

lemma l6tr_lin_conj_apply {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V V' : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (ι : Additive ↥Bs ≃+ V) (ι' : Additive ↥Bs ≃+ V') (a : MulAut ↥Bs) (v : V) :
    ggLin (p := p) ι' a (l6tr_iso (p := p) ι ι' v) =
      l6tr_iso (p := p) ι ι' (ggLin (p := p) ι a v) := by
  rw [l6tr_iso_apply, ggLin_apply, ggLin_apply, l6tr_iso_apply]
  simp

theorem ggDatum_indep_transfer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {Λ Λ' : Type} [Fintype Λ] [Fintype Λ'] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V'] {ι : Additive ↥Bs ≃+ V} {ι' : Additive ↥Bs ≃+ V'}
    {φ : Λ → MulAut ↥Bs} {φ' : Λ' → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {h' : Λ' → V'} {α' : Λ' → Module.Dual (ZMod p) V'}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) (hrefl : ∀ i, GGIsReflection p (φ i))
    (hφ' : ∀ i w, ggLin (p := p) ι' (φ' i) w = w - α' i w • h' i)
    (hrefl' : ∀ i, GGIsReflection p (φ' i))
    (hA : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hA' : ggAutomizer X Bs = Subgroup.closure (Set.range φ'))
    (hcard : Fintype.card Λ = Fintype.card Λ') (hind : LinearIndependent (ZMod p) h) :
    LinearIndependent (ZMod p) h' := by
  let gen : ↥(ggAutomizer X Bs) × V → V :=
    fun q => ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2
  let gen' : ↥(ggAutomizer X Bs) × V' → V' :=
    fun q => ggLin (p := p) ι' (q.1 : MulAut ↥Bs) q.2 - q.2
  have hD : Submodule.span (ZMod p) (Set.range h) = Submodule.span (ZMod p) (Set.range gen) :=
    l6tr_span_eq (p := p) hφ hrefl hA
  have hD' : Submodule.span (ZMod p) (Set.range h') = Submodule.span (ZMod p) (Set.range gen') :=
    l6tr_span_eq (p := p) hφ' hrefl' hA'
  let τ : V ≃ₗ[ZMod p] V' := l6tr_iso (p := p) ι ι'
  have hgen_map : ∀ q : ↥(ggAutomizer X Bs) × V, τ (gen q) = gen' (q.1, τ q.2) := by
    intro q
    have h1 := l6tr_lin_conj_apply (p := p) ι ι' q.1.1 q.2
    change τ (ggLin (p := p) ι q.1.1 q.2 - q.2) =
      ggLin (p := p) ι' q.1.1 (τ q.2) - τ q.2
    rw [map_sub, h1]
  have hrange : Set.range (fun q : ↥(ggAutomizer X Bs) × V => τ (gen q)) = Set.range gen' := by
    ext v
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q.1, τ q.2), (hgen_map q).symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨(q.1, τ.symm q.2), ?_⟩
      change τ (gen (q.1, τ.symm q.2)) = gen' q
      rw [hgen_map]
      simp
  have hmap : Submodule.span (ZMod p) (Set.range gen') =
      (Submodule.span (ZMod p) (Set.range gen)).map (τ : V →ₗ[ZMod p] V') := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    exact hrange.symm
  have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range gen')) =
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range gen)) := by
    rw [hmap]
    exact ((Submodule.span (ZMod p) (Set.range gen)).equivMapOfInjective
      (τ : V →ₗ[ZMod p] V') τ.injective).finrank_eq.symm
  have hfinΛ : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = Fintype.card Λ :=
    finrank_span_eq_card hind
  have hfin' : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h')) = Fintype.card Λ' := by
    rw [hD', hfin, ← hD, hfinΛ, hcard]
  exact linearIndependent_iff_card_eq_finrank_span.mpr hfin'.symm

end CFSG.StandardType

end
