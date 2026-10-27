module

public import CFSG.Quasithin.Background.FLc3Sum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_one_of_natAct_fixed {n : ℕ} (γ : ↥(StatedSL n (ZMod 2)))
    (h : ∀ x : Multiplicative (Fin n → ZMod 2), natAct (StatedSL n (ZMod 2)) γ x = x) : γ = 1 := by
  have hmat : ((γ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    ext i j
    have h1 := congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd (Pi.single j 1)))
    have h2 := congrFun h1 i
    simp only [natAct, toAdd_ofAdd] at h2
    rw [Matrix.mulVec_single_one] at h2
    simpa [Matrix.one_apply, Pi.single_apply] using h2
  apply Subtype.ext
  apply Units.ext
  simpa using hmat

theorem injective_of_rhoOf_injective {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H} (h : Function.Injective (rhoOf π)) : Function.Injective π := by
  intro x y hxy
  have h1 : rhoOf π ((specialLinearGroupEquivStatedSL n (ZMod 2)).symm x) =
      rhoOf π ((specialLinearGroupEquivStatedSL n (ZMod 2)).symm y) := by
    rw [rhoOf_apply, rhoOf_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hxy]
  exact (specialLinearGroupEquivStatedSL n (ZMod 2)).symm.injective (h h1)

theorem isNaturalSection_of_realizes {G : Type} [Group G] {V : Type} [CommGroup V] (ι : V →* G)
    (hι : Function.Injective ι) {L : Subgroup G} (θ : ↥L →* MulAut V)
    (hθ : ∀ (l : ↥L) (v : V), ι (θ l v) = (l : G) * ι v * (l : G)⁻¹) {n : ℕ} {H : Subgroup (MulAut V)}
    (hθH : ∀ l, θ l ∈ H) (hHθ : ∀ k ∈ H, ∃ l, θ l = k) {ULV : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H} (hπinj : Function.Injective π)
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H ULV ⊥ π) :
    IsNaturalSection L (ULV.map ι) ⊥
      ((L ⊓ Subgroup.centralizer ((ULV.map ι : Subgroup G) : Set G)).subgroupOf L)
      (StatedSL n (ZMod 2)) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, hπs⟩ := vmodel_of_realizes (natAct (StatedSL n (ZMod 2))) h
  let e : ↥(StatedSL n (ZMod 2)) ≃* ↥H := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  let α₀ : ↥L →* ↥H := θ.codRestrict H hθH
  let α : ↥L →* ↥(StatedSL n (ZMod 2)) := e.symm.toMonoidHom.comp α₀
  have hα : ∀ l : ↥L, π (α l) = α₀ l := fun l => e.apply_symm_apply (α₀ l)
  have hαθ : ∀ l : ↥L, ((π (α l) : ↥H) : MulAut V) = θ l := fun l => congrArg Subtype.val (hα l)
  have hαs : Function.Surjective α := by
    intro γ
    obtain ⟨l, hl⟩ := hHθ (π γ : MulAut V) (π γ).2
    refine ⟨l, hπinj (Subtype.ext ((hαθ l).trans hl))⟩
  have hnorm1 : ∀ l : ↥L, ∀ x ∈ ULV.map ι, (l : G) * x * (l : G)⁻¹ ∈ ULV.map ι := by
    rintro l x ⟨u, hu, rfl⟩
    exact ⟨θ l u, hUinv ⟨θ l, hθH l⟩ u hu, by rw [hθ]⟩
  have hLN : L ≤ Subgroup.normalizer ((ULV.map ι : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm1 ⟨l, hl⟩ x hx, fun hx => ?_⟩
    have h2 : (l⁻¹ : G) * (l * x * l⁻¹) * (l⁻¹)⁻¹ ∈ ULV.map ι := hnorm1 ⟨l⁻¹, L.inv_mem hl⟩ _ hx
    rwa [show (l⁻¹ : G) * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group] at h2
  have hker : α.ker =
      (L ⊓ Subgroup.centralizer ((ULV.map ι : Subgroup G) : Set G)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hl1
      have hθ1 : θ l = 1 := by rw [← hαθ l, hl1, map_one]; rfl
      refine ⟨l.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      have h1 : ι u = (l : G) * ι u * (l : G)⁻¹ := by
        have := hθ l u
        rw [hθ1] at this
        exact this
      calc ι u * (l : G) = ((l : G) * ι u * (l : G)⁻¹) * l := by rw [← h1]
        _ = (l : G) * ι u := by group
    · rintro ⟨-, hc⟩
      have hfix : ∀ u ∈ ULV, θ l u = u := by
        intro u hu
        apply hι
        rw [hθ]
        have := Subgroup.mem_centralizer_iff.1 hc (ι u) ⟨u, hu, rfl⟩
        calc (l : G) * ι u * (l : G)⁻¹ = (ι u * (l : G)) * (l : G)⁻¹ := by rw [this]
          _ = ι u := by group
      apply eq_one_of_natAct_fixed
      intro x
      obtain ⟨u, rfl⟩ := hβs x
      have hu := hUinv (π (α l)) u u.2
      have h1 := hβe (α l) u hu
      have e1 : (⟨((π (α l) : ↥H) : MulAut V) (u : V), hu⟩ : ↥ULV) = u :=
        Subtype.ext (by
          show ((π (α l) : ↥H) : MulAut V) (u : V) = u
          rw [hαθ]
          exact hfix u u.2)
      rw [e1] at h1
      exact h1.symm
  let eι : ↥ULV ≃* ↥(ULV.map ι) := Subgroup.equivMapOfInjective ULV ι hι
  have heι : ∀ v : ↥(ULV.map ι), ((v : ↥(ULV.map ι)) : G) = ι ((eι.symm v : ↥ULV) : V) := by
    intro v
    have := Subgroup.coe_equivMapOfInjective_apply ULV ι hι (eι.symm v)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  refine ⟨hLN, α, hαs, hker, β.comp eι.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu⟩ := hβs x
    exact ⟨eι u, by simpa using hu⟩
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : ((eι.symm v : ↥ULV) : V) ∈ (⊥ : Subgroup V) := (hβk (eι.symm v)).1 hv
      rw [heι v, Subgroup.mem_bot.1 h1, map_one]
      exact (⊥ : Subgroup G).one_mem
    · intro hv
      have h0 : (v : G) = 1 := Subgroup.mem_bot.1 hv
      have h1 : ι ((eι.symm v : ↥ULV) : V) = ι 1 := by rw [← heι v, h0, map_one]
      have h2 : ((eι.symm v : ↥ULV) : V) = 1 := hι h1
      exact (hβk (eι.symm v)).2 (by rw [h2]; exact (⊥ : Subgroup V).one_mem)
  · intro a u v huv
    have hu_ι := heι u
    have hv_ι := heι v
    have huv' : (v : G) = (a : G) * (u : G) * (a : G)⁻¹ := huv
    have hθuv : ((π (α a) : ↥H) : MulAut V) ((eι.symm u : ↥ULV) : V) = ((eι.symm v : ↥ULV) : V) := by
      apply hι
      rw [hαθ, hθ, ← hu_ι, ← huv', hv_ι]
    have hmem := hUinv (π (α a)) (eι.symm u : ↥ULV) (eι.symm u).2
    have h1 := hβe (α a) (eι.symm u) hmem
    have e1 : (⟨((π (α a) : ↥H) : MulAut V) ((eι.symm u : ↥ULV) : V), hmem⟩ : ↥ULV) = eι.symm v :=
      Subtype.ext hθuv
    rw [e1] at h1
    show Multiplicative.toAdd (β (eι.symm v)) = _
    rw [h1]
    rfl

theorem card_le_two_of_ut_fixed {V : Type} [CommGroup V] {n : ℕ} (hn : 1 ≤ n) {ρ : SLt n →* MulAut V}
    {U' : Subgroup V}
    (D : VModel n ρ U' ⊥ (Multiplicative (Vt n)) (fun g a => actM g a)) {W : Subgroup V} (hWU : W ≤ U')
    (hW : ∀ w ∈ W, ∀ s ∈ Ut n, ρ s w = w) : Nat.card W ≤ 2 := by
  have hinj := D.β_injective
  let f : ↥W → Multiplicative (Vt n) := fun w => D.β ⟨w, hWU w.2⟩
  have hf : Function.Injective f := fun w w' hww => Subtype.ext (Subtype.mk.inj (hinj hww))
  have hmem : ∀ w, f w ∈ ({1, fstBasis n hn} : Finset (Multiplicative (Vt n))) := by
    intro w
    by_cases h1 : f w = 1
    · simp [h1]
    · have hfix : ∀ g ∈ Ut n, actM g (f w) = f w := by
        intro g hg
        have h2 := D.equiv g ⟨w, hWU w.2⟩ (D.inv g w (hWU w.2))
        have e : (⟨(ρ g) w, D.inv g w (hWU w.2)⟩ : ↥U') = ⟨w, hWU w.2⟩ :=
          Subtype.ext (hW w w.2 g hg)
        rw [e] at h2
        exact h2.symm
      simp [eq_e0_of_fixed hn h1 hfix]
  let g : ↥W → ↥({1, fstBasis n hn} : Finset (Multiplicative (Vt n))) := fun w => ⟨f w, hmem w⟩
  have hg : Function.Injective g := fun w w' hww => hf (Subtype.mk.inj hww)
  calc Nat.card W ≤ Nat.card ↥({1, fstBasis n hn} : Finset (Multiplicative (Vt n))) :=
        Nat.card_le_card_of_injective g hg
    _ = ({1, fstBasis n hn} : Finset (Multiplicative (Vt n))).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 := Finset.card_le_two

theorem fixed_of_two {V : Type} [CommGroup V] {U₁ U₂ : Subgroup V} (hdisj : U₁ ⊓ U₂ = ⊥)
    (σ : MulAut V) (h₁ : ∀ u ∈ U₁, σ u ∈ U₁) (h₂ : ∀ u ∈ U₂, σ u ∈ U₂) {v₁ v₂ : V} (hv₁ : v₁ ∈ U₁)
    (hv₂ : v₂ ∈ U₂) (hf : σ (v₁ * v₂) = v₁ * v₂) : σ v₁ = v₁ ∧ σ v₂ = v₂ := by
  rw [map_mul] at hf
  have e : σ v₁ / v₁ = v₂ / σ v₂ := div_eq_div_iff_mul_eq_mul.2 (hf.trans (mul_comm _ _))
  have m₁ : σ v₁ / v₁ ∈ U₁ := U₁.div_mem (h₁ v₁ hv₁) hv₁
  have m₂ : σ v₁ / v₁ ∈ U₂ := by rw [e]; exact U₂.div_mem hv₂ (h₂ v₂ hv₂)
  have h0 : σ v₁ / v₁ ∈ (⊥ : Subgroup V) := hdisj ▸ ⟨m₁, m₂⟩
  have h1 : σ v₁ / v₁ = 1 := Subgroup.mem_bot.1 h0
  have h2 : v₂ / σ v₂ = 1 := by rw [← e]; exact h1
  exact ⟨div_eq_one.1 h1, (div_eq_one.1 h2).symm⟩

end CFSG.Quasithin.FLc
