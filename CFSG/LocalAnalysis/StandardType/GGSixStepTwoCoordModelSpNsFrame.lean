module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsBlock
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameBlock
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spForm_isAlt spForm_nondegenerate spLin_injective
  range_spLin spLin_mem)

namespace CFSG.StandardType

namespace CoordSpNs

section Coord

variable {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ}

@[expose] noncomputable def spIso (n : ℕ) (F : Type) [Field F] :
    StatedSp n F ≃* ↥(sesqUnitaryGroup (spForm n F)) :=
  (MonoidHom.ofInjective spLin_injective).trans (MulEquiv.subgroupCongr range_spLin)

theorem coe_spIso (X : StatedSp n F) :
    ((spIso n F X : ↥(sesqUnitaryGroup (spForm n F))) :
      LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) = spLin n F X := rfl

variable {D : Type} [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type} [NeZero p]

@[expose] noncomputable def nsCoord (ψ : StatedSp n F →* G) {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
    {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
    (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
    (hcω : ∀ x y, ω (c x) (c y) = ω x y) : Multiplicative (Fin s → ZMod p) →* G :=
  ψ.comp ((spIso n F).symm.toMonoidHom.comp (torHomD hc hdec hcω))

theorem nsCoord_apply (ψ : StatedSp n F →* G) {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
    {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
    (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
    (hcω : ∀ x y, ω (c x) (c y) = ω x y) (a : Multiplicative (Fin s → ZMod p)) :
    nsCoord ψ hc hdec hcω a = ψ ((spIso n F).symm (torHomD hc hdec hcω a)) := rfl

end Coord

@[expose] def NsBlockType {F : Type} [Field F] (g : F[X]) [Fact (Irreducible g)] (p : ℕ)
    (D : Type) [AddCommGroup D] [Module F D] (c : D ≃ₗ[F] D) : Prop :=
  (aeval (AdjoinRoot.root g ^ (p - 1)) g = 0 ∧
      ∃ e : D ≃ₗ[F] AdjoinRoot g, ∀ x, e (c x) = AdjoinRoot.root g * e x) ∨
    (aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0 ∧
      ∃ e : D ≃ₗ[F] AdjoinRoot g × AdjoinRoot g,
        ∀ x, e (c x) = (AdjoinRoot.root g * (e x).1, AdjoinRoot.root g ^ (p - 1) * (e x).2))

section Bstar

variable {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ}

theorem pow_apply_eq {D : Type} [AddCommGroup D] [Module F D] {c : D →ₗ[F] D} {cE : D ≃ₗ[F] D}
    (hcE : ∀ x, cE x = c x) (m : ℕ) (x : D) : (cE ^ m) x = (c ^ m) x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, ih, hcE, pow_succ', Module.End.mul_apply]

theorem exists_coord_of_block [NeZero p] (hp : p.Prime) {D : Type} [AddCommGroup D] [Module F D]
    [FiniteDimensional F D] [Nontrivial D] {c : D →ₗ[F] D} {cE : D ≃ₗ[F] D}
    (hcE : ∀ x, cE x = c x) (hcp : cE ^ p = 1) (hD : SpNS.SpBlockExists F p D c)
    (hc1 : ∀ u : D, ∃ u₀, c u₀ - u₀ = u) (hfix : ∀ x, c x = x → x = 0)
    (htr : FormTransitive F D cE) {O : Subgroup (ZMod p)ˣ}
    (hO : ∀ ω : LinearMap.BilinForm F D, ω.IsAlt → ω.Nondegenerate →
      (∀ x y, ω (cE x) (cE y) = ω x y) → O ≤ twistGroup ω cE hcp)
    (ψ : StatedSp n F →* G) (hψ : Function.Injective ψ) {Bs : Subgroup G} (hmem : Bs ≤ ψ.range)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ ψ.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hne : ∃ b ∈ Bs, b ≠ 1) :
    ∃ (s : ℕ) (κ : Type) (_ : Fintype κ)
      (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (ω : LinearMap.BilinForm F D)
      (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
        ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
      (hcω : ∀ x y, ω (cE x) (cE y) = ω x y),
      Function.Injective (nsCoord ψ hcp hdec hcω) ∧ (nsCoord ψ hcp hdec hcω).range = Bs ∧
      ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
        ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ t : Fin s → ZMod p,
          w⁻¹ * nsCoord ψ hcp hdec hcω (ofAdd t) * w =
            nsCoord ψ hcp hdec hcω (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  classical
  set S : Set (Module.End F (Fin n ⊕ Fin n → F)) :=
    {x | ∃ X : StatedSp n F, ψ X ∈ Bs ∧
      x = ((spLin n F X : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
        Module.End F (Fin n ⊕ Fin n → F))} with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    have h1 : X * Y = Y * X := hψ (by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs hX hY)
    have h2 := congrArg (fun Z : StatedSp n F =>
      ((spLin n F Z : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
        Module.End F (Fin n ⊕ Fin n → F))) h1
    simp only [map_mul, Units.val_mul] at h2
    exact h2
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨X, hX, rfl⟩
    have h1 : X ^ p = 1 := hψ (by rw [map_pow, map_one]; exact hBs.2 _ hX)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  have hSB : ∀ x ∈ S, ∀ u w, spForm n F (x u) (x w) = spForm n F u w := by
    rintro _ ⟨X, -, rfl⟩ u w
    exact (mem_sesqUnitaryGroup.mp (spLin_mem X)) u w
  have hS1 : ∃ x ∈ S, x ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    obtain ⟨X, rfl⟩ := hmem hb
    refine ⟨_, ⟨X, hb, rfl⟩, fun h => hb1 ?_⟩
    have hX : X = 1 := spLin_injective (Units.ext (by rw [h, map_one]; rfl))
    rw [hX, map_one]
  obtain ⟨s, κ, _, Φ, ω, hωa, hωnd, hωc, hΦS, hdec⟩ := exists_normFrame hcE hD hp.one_lt.le hc1
    htr spForm_isAlt spForm_nondegenerate S hSc hSp hSB hS1
  have hfixE : ∀ x, cE x = x → x = 0 := fun x h => hfix x (by rw [← hcE]; exact h)
  have hcpc : c ^ p = 1 := LinearMap.ext fun x => by
    rw [← pow_apply_eq hcE, hcp]
    rfl
  set ι := nsCoord ψ hcp hdec hωc with hι
  have hBsι : Bs ≤ ι.range := by
    intro b hb
    obtain ⟨X, rfl⟩ := hmem hb
    obtain ⟨k, hk⟩ := hΦS _ ⟨X, hb, rfl⟩
    refine ⟨ofAdd fun i => (k i : ZMod p), ?_⟩
    rw [hι, nsCoord_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [coe_torHomD, coe_spIso, SpNS.frameUnit_apply, torD_apply, hk]
    congr 2
    funext i
    rw [pow_apply_eq hcE, ZMod.val_natCast, ← pow_eq_pow_mod _ hcpc]
  have hrange : ι.range = Bs := by
    refine le_antisymm ?_ hBsι
    rintro _ ⟨a, rfl⟩
    refine hSC _ (Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩) ?_
    · obtain ⟨a', rfl⟩ := hBsι hb
      rw [← map_mul, ← map_mul, mul_comm]
    · have ha : a ^ p = 1 := by
        apply toAdd.injective
        funext i
        simp [toAdd_pow]
      rw [← map_pow, ha, map_one]
  have hτinj := torHomD_injective (κ := κ) hp hcp hfixE hdec hωc
  have hinj : Function.Injective ι := fun a b hab => by
    rw [hι, nsCoord_apply, nsCoord_apply] at hab
    exact hτinj ((spIso n F).symm.injective (hψ hab))
  refine ⟨s, κ, inferInstance, Φ, ω, hdec, hωc, hinj, hrange, fun π η hη => ?_⟩
  have hT : ∀ i, ∃ T : D ≃ₗ[F] D, IsTwist ω cE (η (π.symm i)) T := fun i =>
    mem_twistGroup.mp (hO ω hωa hωnd hωc (hη (π.symm i)))
  choose T hT using hT
  obtain ⟨w₀, hw₀⟩ := torHomD_move (κ := κ) hcp hdec hωc π η T hT
  have hw : ∀ t : Fin s → ZMod p, (ψ ((spIso n F).symm w₀))⁻¹ * ι (ofAdd t) *
      ψ ((spIso n F).symm w₀) = ι (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
    intro t
    rw [hι, nsCoord_apply, nsCoord_apply, ← hw₀ t]
    simp only [map_mul, map_inv]
  refine ⟨ψ ((spIso n F).symm w₀), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, ?_⟩, hw⟩
  rw [← hrange]
  exact CoordSL.mem_normalizer_range_of_conj π η hw

end Bstar

end CoordSpNs

open CoordSpNs

@[expose] def GGSpNsFrameCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (D : Type) [AddCommGroup D] [Module F D] (c : D ≃ₗ[F] D), NsBlockType g p D c →
    ∀ (hc : c ^ p = 1) (s : ℕ) (κ : Type) [Fintype κ]
      (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (ω : LinearMap.BilinForm F D)
      (hdec : ∀ d d' w w', CFSG.RankThree.Classical.spForm n F (Φ (d, w)) (Φ (d', w')) =
        ∑ i, ω (d i) (d' i) + CFSG.RankThree.Classical.spForm n F (Φ (0, w)) (Φ (0, w')))
      (hcω : ∀ x y, ω (c x) (c y) = ω x y), 4 ≤ s →
    ∀ (b : G) (L₁ : Subgroup G), b ∈ (nsCoord ψ hc hdec hcω).range → b ≠ 1 →
      IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
      Nat.card ((nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (L₁ : Set G) :
        Subgroup G) ≤ p ^ 2 →
      ∀ β : Fin s → ZMod p, nsCoord ψ hc hdec hcω (ofAdd β) = b →
        (∃ j j' : Fin s, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
          ∀ t : Fin s → ZMod p, t j = 0 → t j' = 0 → nsCoord ψ hc hdec hcω (ofAdd t) ∈ L₁) ∨
        (∃ (k : Fin s) (c₀ : ZMod p) (ε : Fin s → (ZMod p)ˣ), c₀ ≠ 0 ∧
          (∀ i, ε i ∈ galSigns p (Nat.card F)) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c₀) ∧
          ∀ t : Fin s → ZMod p, t k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * t i = 0 →
            nsCoord ψ hc hdec hcω (ofAdd t) ∈ L₁)

@[expose] def GGSpNsFrameShapeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (D : Type) [AddCommGroup D] [Module F D] (c : D ≃ₗ[F] D), NsBlockType g p D c →
    ∀ (hc : c ^ p = 1) (s : ℕ) (κ : Type) [Fintype κ]
      (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (ω : LinearMap.BilinForm F D)
      (hdec : ∀ d d' w w', CFSG.RankThree.Classical.spForm n F (Φ (d, w)) (Φ (d', w')) =
        ∑ i, ω (d i) (d' i) + CFSG.RankThree.Classical.spForm n F (Φ (0, w)) (Φ (0, w')))
      (hcω : ∀ x y, ω (c x) (c y) = ω x y), 4 ≤ s →
    ∀ E J : Subgroup G, E ≤ (nsCoord ψ hc hdec hcω).range →
      IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)) →
      Nat.card ((nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) :
        Subgroup G) ≤ p ^ 3 →
      StepTwoToral.GGStepTwoCoordShape p s (galSigns p (Nat.card F)) (nsCoord ψ hc hdec hcω) E

section Assembly

namespace CoordSpNs

theorem four_le_of_range {G : Type} [Group G] {p s : ℕ} [Fact p.Prime]
    {ι : Multiplicative (Fin s → ZMod p) →* G} {Bs : Subgroup G} (hι : ι.range = Bs)
    (h4 : p ^ 4 ≤ Nat.card Bs) : 4 ≤ s := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card ι.range ≤ p ^ s := by
    calc Nat.card ι.range ≤ Nat.card (Multiplicative (Fin s → ZMod p)) :=
          Nat.card_le_card_of_surjective _ ι.rangeRestrict_surjective
      _ = p ^ s := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
            Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin]
  rw [hι] at hcard
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp (h4.trans hcard)

theorem coordInput_of_block (hcomp : GGSpNsFrameCompInput) (hshape : GGSpNsFrameShapeInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hns : ¬ p ∣ Nat.card F - 1) {ψ : StatedSp n F →* G}
    (hψ : Function.Injective ψ) {g : F[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p F)
    {D : Type} [AddCommGroup D] [Module F D] {c : D ≃ₗ[F] D} (hbt : NsBlockType g p D c)
    (hc : c ^ p = 1) {s : ℕ} {κ : Type} [Fintype κ]
    {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
    (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
    (hcω : ∀ x y, ω (c x) (c y) = ω x y) {Bs : Subgroup G} (h4 : p ^ 4 ≤ Nat.card Bs)
    (hinj : Function.Injective (nsCoord ψ hc hdec hcω))
    (hrange : (nsCoord ψ hc hdec hcω).range = Bs)
    (hmove : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ),
      (∀ i, η i ∈ galSigns p (Nat.card F)) →
        ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ t : Fin s → ZMod p,
          w⁻¹ * nsCoord ψ hc hdec hcω (ofAdd t) * w =
            nsCoord ψ hc hdec hcω (ofAdd fun i => (η i : ZMod p) * t (π i))) :
    ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G),
      Function.Injective ι ∧ ι.range = Bs ∧
      (∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
        (∀ i, η i ∈ galSigns p (Nat.card F)) → ∏ i, η i = 1 →
        ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
          w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i))) ∧
      (∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
        Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
        ∀ β : Fin r → ZMod p, ι (ofAdd β) = b →
          (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
            ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → ι (ofAdd s) ∈ L₁) ∨
          (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
            (∀ i, ε i ∈ galSigns p (Nat.card F)) ∧
            (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
            ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
              ι (ofAdd s) ∈ L₁)) ∧
      ∀ E J : Subgroup G, E ≤ Bs →
        IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)) →
        Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 →
        StepTwoToral.GGStepTwoCoordShape p r (galSigns p (Nat.card F)) ι E := by
  refine ⟨s, nsCoord ψ hc hdec hcω, hinj, hrange, fun π η hη _ => hmove π η hη,
    fun b L₁ hb hb1 hL₁ hcard β hβ => ?_, fun E J hE hJ hcard => ?_⟩
  · rw [← hrange] at hb hcard
    exact hcomp G F n p hp2 hns ψ hψ g hgd D c hbt hc s κ Φ ω hdec hcω
      (four_le_of_range hrange h4) b L₁ hb hb1 hL₁ hcard β hβ
  · rw [← hrange] at hE hcard
    exact hshape G F n p hp2 hns ψ hψ g hgd D c hbt hc s κ Φ ω hdec hcω
      (four_le_of_range hrange h4) E J hE hJ hcard

end CoordSpNs

theorem ggSpNsCoordInput_of_frame (hcomp : GGSpNsFrameCompInput)
    (hshape : GGSpNsFrameShapeInput) : GGSpNsCoordInput := by
  intro G _ _ F _ _ _ n p _ hp2 hns ψ hψ Bs hmem hBs h4 hSC
  classical
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have hne : ∃ b ∈ Bs, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Bs = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at h4
    have h1 : 1 < p ^ 4 := Nat.one_lt_pow (by norm_num) hpp.one_lt
    omega
  have hne' : ¬ IsUnit (cyclotomic p F) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hpp]
    have := hpp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne' (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hpp hpF hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζ.pow_eq_one
  have hζ0 : AdjoinRoot.root g ≠ 0 := hζ.ne_zero hpp.ne_zero
  have : Module.Finite F (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζ.ne_one hpp.one_lt
  have hζ1' : AdjoinRoot.root g ^ (p - 1) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by have := hpp.two_le; omega) (by have := hpp.pos; omega)
  have hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ0
  have hfix : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ d : AdjoinRoot g, μ * d = d → d = 0 :=
    fun μ hμ d hd => by
      have h0 : (μ - 1) * d = 0 := by rw [sub_mul, hd, one_mul, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  have hsurj : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ u : AdjoinRoot g, ∃ u₀, μ * u₀ - u₀ = u :=
    fun μ hμ u => ⟨(μ - 1)⁻¹ * u, by
      rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hμ), one_mul]⟩
  have : Nontrivial (AdjoinRoot g) := inferInstance
  by_cases hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0
  ·
    obtain ⟨s, κ, _, Φ, ω, hdec, hcω, hinj, hrange, hmove⟩ :=
      exists_coord_of_block (c := LinearMap.mulLeft F (AdjoinRoot.root g)) (cE := sdC hζ0)
        hpp (fun x => rfl) (sdC_pow_eq_one hζ0 hζp)
        (SpNS.spBlockExists_selfDual hpp hp2 hpF hgd hσ) (hsurj _ hζ1)
        (fun d hd => hfix _ hζ1 d hd) (formTransitive_sd hζp hζ0)
        (fun ω hωa hωnd hωc => galSigns_le_twistGroup_sd hζp hζ hσ hζ0 hωa hωnd hωc)
        ψ hψ hmem hBs hSC hne
    exact coordInput_of_block hcomp hshape hp2 hns hψ hgd
      (Or.inl ⟨hσ, LinearEquiv.refl F _, fun x => rfl⟩) (sdC_pow_eq_one hζ0 hζp) hdec hcω h4
      hinj hrange hmove
  ·
    obtain ⟨s, κ, _, Φ, ω, hdec, hcω, hinj, hrange, hmove⟩ :=
      exists_coord_of_block
        (c := (LinearMap.mulLeft F (AdjoinRoot.root g)).prodMap
          (LinearMap.mulLeft F (AdjoinRoot.root g ^ (p - 1)))) (cE := prC hζ0 hζ0')
        hpp (fun x => rfl) (prC_pow_eq_one hζ0 hζ0' hζp)
        (SpNS.spBlockExists_paired hpp hpF hgd hσ)
        (fun u => by
          obtain ⟨u₁, hu₁⟩ := hsurj _ hζ1 u.1
          obtain ⟨u₂, hu₂⟩ := hsurj _ hζ1' u.2
          exact ⟨(u₁, u₂), Prod.ext hu₁ hu₂⟩)
        (fun d hd => by
          obtain ⟨μ, ν⟩ := d
          rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
          exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
        (formTransitive_pr hζ0 hζ0' hζp hζ hσ)
        (fun ω hωa hωnd hωc => galSigns_le_twistGroup_pr hζ0 hζ0' hζp hζ hσ hωa hωnd hωc)
        ψ hψ hmem hBs hSC hne
    exact coordInput_of_block hcomp hshape hp2 hns hψ hgd
      (Or.inr ⟨hσ, LinearEquiv.refl F _, fun x => rfl⟩) (prC_pow_eq_one hζ0 hζ0' hζp) hdec hcω h4
      hinj hrange hmove

section Certified

theorem ggSpCoordModelNonsplitInput_of_frame (hcomp : GGSpNsFrameCompInput)
    (hshape : GGSpNsFrameShapeInput) : GGSpCoordModelNonsplitInput :=
  ggSpCoordModelNonsplitInput_of_coord (ggSpNsCoordInput_of_frame hcomp hshape)

end Certified

end Assembly

end CFSG.StandardType
