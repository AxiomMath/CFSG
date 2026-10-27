module

public import CFSG.Quasithin.Recognition.CertD4BridgeTheta
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Open (quasithinRootElt quasithinD4Root)

section Natural

variable (k : Type) [Field k]

@[expose] def d4bTwGens : Set (Matrix (Fin 8) (Fin 8) k) :=
  {M | ∃ (a : k) (s : Bool), M = quasithinRootElt (quasithinD4Root 0 s) a *
      quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)} ∪
  {M | ∃ s : Bool, M = quasithinRootElt (quasithinD4Root 1 s) 1}

@[expose] def d4bG8 : Subgroup (GL (Fin 8) k) :=
  Subgroup.closure {A | (A : Matrix (Fin 8) (Fin 8) k) ∈ d4bTwGens k}

@[expose] def d4bQ (i : Fin Tag.D4.rank) : Fin 4 := (![0, 2, 1, 3] : Fin 4 → Fin 4) i

end Natural

theorem d4bEs_pos : ∀ (i : Fin Tag.D4.rank) (s : Bool),
    d4bEs i s = Matrix.of fun r c => if (r, c) ∈ quasithinD4Root (d4bQ i) s then 1 else 0 := by
  decide +kernel

theorem quasithinRootElt_eq {k : Type} [Field k] (pos : List (Fin 8 × Fin 8)) (t : k) :
    quasithinRootElt pos t = 1 + t • Matrix.of fun r c => if (r, c) ∈ pos then (1 : k) else 0 := by
  ext r c
  by_cases h : (r, c) ∈ pos <;> by_cases hrc : r = c <;>
    simp [quasithinRootElt, h, hrc]

theorem d4bUm_eq (k : Type) [Field k] [CharP k 2] (i : Fin Tag.D4.rank) (s : Bool) (c : k) :
    d4bUm k i s c = quasithinRootElt (quasithinD4Root (d4bQ i) s) c := by
  rw [quasithinRootElt_eq, d4bUm, d4bEk, d4bEs_pos]
  congr 2
  ext r c'
  simp [apply_ite (d4bφ k)]


section Gen

variable {k : Type} [Field k] [CharP k 2]

theorem d4bUm_outer (i₀ i₁ i₃ : Fin Tag.D4.rank) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1)
    (h₃ : i₃.val = 3) (s : Bool) (a b e : k) :
    d4bUm k i₀ s a * d4bUm k i₁ s b * d4bUm k i₃ s e =
      quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) b *
        quasithinRootElt (quasithinD4Root 3 s) e := by
  have e₀ : i₀ = ⟨0, by decide⟩ := Fin.ext h₀
  have e₁ : i₁ = ⟨1, by decide⟩ := Fin.ext h₁
  have e₃ : i₃ = ⟨3, by decide⟩ := Fin.ext h₃
  subst e₀ e₁ e₃
  rw [d4bUm_eq, d4bUm_eq, d4bUm_eq]
  rfl

theorem d4bUm_mid (i : Fin Tag.D4.rank) (hi : i.val = 2) (s : Bool) (c : k) :
    d4bUm k i s c = quasithinRootElt (quasithinD4Root 1 s) c := by
  have e : i = ⟨2, by decide⟩ := Fin.ext hi
  subst e
  rw [d4bUm_eq]
  rfl

theorem d4bNat_zero
    (i : Fin Tag.D4.rank) (s : Bool) : d4bNat k i s 0 = 1 :=
  Units.ext (by simp [d4bNat, d4bUm])

theorem d4b_mem_outer
    (i₀ i₁ i₃ : Fin Tag.D4.rank) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1)
    (h₃ : i₃.val = 3) (s : Bool) (a : k) :
    d4bNat k i₀ s a * d4bNat k i₁ s (a ^ 2) * d4bNat k i₃ s (a ^ 4) ∈ d4bG8 k := by
  refine Subgroup.subset_closure (Or.inl ⟨a, s, ?_⟩)
  rw [Units.val_mul, Units.val_mul]
  exact d4bUm_outer i₀ i₁ i₃ h₀ h₁ h₃ s a _ _

theorem d4b_mem_mid
    (i : Fin Tag.D4.rank) (hi : i.val = 2) (s : Bool) :
    d4bNat k i s 1 ∈ d4bG8 k := by
  refine Subgroup.subset_closure (Or.inr ⟨s, ?_⟩)
  exact d4bUm_mid i hi s 1

end Gen

section GenΨ

variable {k : Type} [Field k] [CharP k 2] [Finite k] (hk : Nat.card k = 8)

@[expose] noncomputable def d4bΨ'
    : ↥(adjointGroup d4 k) →* GL (Fin 8) k := d4bΨ k hk

theorem d4bΨ_xPar_pos
    (i : Fin d4.rank) (c : k) :
    d4bΨ' hk (xPar (rootOperatorFamily d4) (Pi.single i 1) c) = d4bNat k i true c := by
  rw [xPar_simple, eltElement_simpleRoot]
  exact d4bΨ_of_xOp k hk _ i c rfl

theorem d4bΨ_xPar_neg
    (i : Fin d4.rank) (c : k) :
    d4bΨ' hk (xPar (rootOperatorFamily d4) (-Pi.single i 1) c) = d4bNat k i false c := by
  have e : xPar (rootOperatorFamily d4) (-Pi.single i 1) c = yElement i c :=
    (xPar_neg_simple i c).trans (Subtype.ext ((rootOperatorFamily d4).eltUnit_neg_simple i c))
  rw [e]
  exact d4bΨ_of_yOp k hk _ i c rfl


variable (σ : k →+* k) (hσ : ∀ c, σ c = c ^ 2)

omit [CharP k 2] in
include hk hσ in
theorem d4b_sigma3 (c : k) : σ (σ (σ c)) = c :=
  sigma_three_of_card (q := 2) hk hσ c

include hσ in
theorem d4b_base_long
    {s : ℤ} (hs : s = 1 ∨ s = -1) {g : adjointGroup d4 k}
    (hg : g ∈ twistedRootSubgroupD4 σ (s • Pi.single (ng 0) 1)) :
    d4bΨ' hk g ∈ d4bG8 k := by
  have hα₀ : IsRoot d4 (s • Pi.single (nd 2) 1) := isRoot_smul_single hs (nd 2)
  have hp : proj (s • Pi.single (nd 2) 1) = s • Pi.single (ng 0) 1 := by
    rw [proj_smul_single hs]
    rfl
  have hfix : rho (s • Pi.single (nd 2) 1) = s • Pi.single (nd 2) 1 := by
    rw [rho_smul_single, rhoPerm_two]
  obtain ⟨c, hc, rfl⟩ :=
    (mem_twistedRootSubgroupD4_iff_of_fixed (σ := σ) (d4b_sigma3 hk σ hσ) hα₀ hp hfix g).1 hg
  have h2 : c ^ 2 = c := (hσ c).symm.trans hc
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hs with rfl | rfl
  · rw [one_smul, d4bΨ_xPar_pos hk]
    rcases hc01 with rfl | rfl
    · rw [show d4bNat k (nd 2) true 0 = 1 from d4bNat_zero _ _]; exact Subgroup.one_mem _
    · exact d4b_mem_mid (nd 2) rfl true
  · rw [neg_one_smul, d4bΨ_xPar_neg hk]
    rcases hc01 with rfl | rfl
    · rw [show d4bNat k (nd 2) false 0 = 1 from d4bNat_zero _ _]; exact Subgroup.one_mem _
    · exact d4b_mem_mid (nd 2) rfl false

include hσ in
theorem d4b_base_short
    {s : ℤ} (hs : s = 1 ∨ s = -1) {g : adjointGroup d4 k}
    (hg : g ∈ twistedRootSubgroupD4 σ (s • Pi.single (ng 1) 1)) :
    d4bΨ' hk g ∈ d4bG8 k := by
  have hα₀ : IsRoot d4 (s • Pi.single (nd 0) 1) := isRoot_smul_single hs (nd 0)
  have hp : proj (s • Pi.single (nd 0) 1) = s • Pi.single (ng 1) 1 := by
    rw [proj_smul_single hs]
    rfl
  have hne : rho (s • Pi.single (nd 0) 1) ≠ s • Pi.single (nd 0) 1 :=
    rho_smul_single_ne hs (by decide)
  obtain ⟨c, rfl⟩ :=
    (mem_twistedRootSubgroupD4_iff_of_orbit (σ := σ) (d4b_sigma3 hk σ hσ) hα₀ hp hne g).1 hg
  have e1 : σ c = c ^ 2 := hσ c
  have e2 : σ (σ c) = c ^ 4 := by rw [e1, hσ, ← pow_mul]
  rw [xOrbit_smul_single σ hs, e2, e1]
  rcases hs with rfl | rfl
  · simp only [xOuter, one_smul, map_mul, d4bΨ_xPar_pos hk]
    exact d4b_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl true c
  · simp only [xOuter, neg_one_smul, map_mul, d4bΨ_xPar_neg hk]
    exact d4b_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl false c


include hσ in
theorem d4b_twistedGroup_le
    :
    twistedGroup σ ≤ (d4bG8 k).comap (d4bΨ' hk) := by
  set R : Subgroup (adjointGroup d4 k) := (d4bG8 k).comap (d4bΨ' hk) with hR
  have base : ∀ (j : Fin (Tag.rank .G2)) {s : ℤ}, (s = 1 ∨ s = -1) →
      twistedRootSubgroupD4 σ (s • Pi.single j 1) ≤ R := by
    intro j s hs g hg
    rw [hR, Subgroup.mem_comap]
    match j with
    | ⟨0, _⟩ => exact d4b_base_long hk σ hσ hs hg
    | ⟨1, _⟩ => exact d4b_base_short hk σ hσ hs hg
  have base₁ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (Pi.single j 1) ≤ R := by
    intro j
    have := base j (Or.inl rfl)
    rwa [one_smul] at this
  have base₂ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (-Pi.single j 1) ≤ R := by
    intro j
    have := base j (Or.inr rfl)
    rwa [neg_one_smul] at this
  have hn : ∀ i : Fin (Tag.rank .G2), ((nHat σ i : twistedGroup σ) : adjointGroup d4 k) ∈ R := by
    intro i
    have hle : CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i ≤
        R.subgroupOf (twistedGroup σ) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact base₁ i ((mem_twistedRootGroup σ).1 hx)
      · exact base₂ i ((mem_twistedRootGroup σ).1 hx)
    exact hle (nHat_mem_rankOne σ i)
  have key : ∀ β, IsRoot .G2 β → twistedRootSubgroupD4 σ β ≤ R := by
    intro β hβ
    induction hβ with
    | basis j => exact base₁ j
    | reflect i hβ' ih =>
      intro g hg
      have hgΓ : g ∈ twistedGroup σ := twistedRootSubgroupD4_le_twistedGroup σ (hβ'.reflect i) hg
      have hx : (⟨g, hgΓ⟩ : twistedGroup σ) ∈ twistedRootGroup σ (reflect .G2 i _) :=
        (mem_twistedRootGroup σ).2 hg
      have h1 := nHat_conj_mem σ i (hβ'.reflect i) hx
      rw [reflect_reflect] at h1
      have h2 := ih ((mem_twistedRootGroup σ).1 h1)
      have h3 : (g : adjointGroup d4 k) =
          ((nHat σ i : twistedGroup σ) : adjointGroup d4 k)⁻¹ *
            (((nHat σ i : twistedGroup σ) : adjointGroup d4 k) * g *
              ((nHat σ i : twistedGroup σ) : adjointGroup d4 k)⁻¹) *
            ((nHat σ i : twistedGroup σ) : adjointGroup d4 k) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hn i)) h2) (hn i)
  exact iSup₂_le fun β hβ => key β hβ


include hσ in
theorem d4b_G8_le_map
    : d4bG8 k ≤ (twistedGroup σ).map (d4bΨ' hk) := by
  have hσ3 := d4b_sigma3 hk σ hσ
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  rw [d4bG8, Subgroup.closure_le]
  rintro A (⟨a, s, hA⟩ | ⟨s, hA⟩)
  · have e1 : σ a = a ^ 2 := hσ a
    have e2 : σ (σ a) = a ^ 4 := by rw [e1, hσ, ← pow_mul]
    cases s
    · refine ⟨xOuter (-1) a (σ a) (σ (σ a)), twistedRootSubgroupD4_le_twistedGroup σ
        (isRoot_smul_single_G2 hn (ng 1)) (xOuter_mem σ hn (hσ3 a)), ?_⟩
      apply Units.ext
      simp only [xOuter, neg_one_smul, map_mul, d4bΨ_xPar_neg hk, Units.val_mul]
      rw [hA, e2, e1]
      exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl false a _ _
    · refine ⟨xOuter 1 a (σ a) (σ (σ a)), twistedRootSubgroupD4_le_twistedGroup σ
        (isRoot_smul_single_G2 hp (ng 1)) (xOuter_mem σ hp (hσ3 a)), ?_⟩
      apply Units.ext
      simp only [xOuter, one_smul, map_mul, d4bΨ_xPar_pos hk, Units.val_mul]
      rw [hA, e2, e1]
      exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl true a _ _
  · cases s
    · refine ⟨xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single (nd 2) 1) 1,
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hn (ng 0))
          (xPar_two_mem σ hn (map_one σ)), ?_⟩
      apply Units.ext
      rw [neg_one_smul, d4bΨ_xPar_neg hk, hA]
      exact d4bUm_mid (nd 2) rfl false 1
    · refine ⟨xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1,
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hp (ng 0))
          (xPar_two_mem σ hp (map_one σ)), ?_⟩
      apply Units.ext
      rw [one_smul, d4bΨ_xPar_pos hk, hA]
      exact d4bUm_mid (nd 2) rfl true 1

include hσ in
theorem d4b_map_twistedGroup
    : (twistedGroup σ).map (d4bΨ' hk) = d4bG8 k :=
  le_antisymm (Subgroup.map_le_iff_le_comap.2 (d4b_twistedGroup_le hk σ hσ))
    (d4b_G8_le_map hk σ hσ)

end GenΨ

end CFSG.Quasithin
