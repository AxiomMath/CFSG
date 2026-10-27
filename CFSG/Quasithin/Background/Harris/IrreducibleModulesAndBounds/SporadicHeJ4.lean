module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem false_of_He
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .He)) : False := by
  obtain ⟨e⟩ := hM
  exact false_of_cover_rank_dim h e
    (fun E _ _ _ π hπ hC hodd => he_cover E π hπ hC hodd) (r := 6) heTwoRankProp
    (ρ := 21) (fun W _ _ hW σ hσ => he_dim W hW σ hσ) (by norm_num)

theorem center_eq_bot_of_simple_not_prime {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  rcases (inferInstance : (Subgroup.center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

theorem dim_of_extraspecial11 {S : Type} [Group S] {x y : S} (hx : x ^ 11 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (W : Type) [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (σ : S →* MulAut W) (hσ : Function.Injective σ) :
    2 ^ 110 ≤ Nat.card W := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hx' : (σ x) ^ 11 = 1 := by rw [← map_pow, hx, map_one]
  have hz' : ⁅σ x, σ y⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun h => hz (hσ (h.trans (map_one σ).symm))
  have hzx' : Commute ⁅σ x, σ y⁆ (σ x) := by
    rw [← map_commutatorElement]
    exact hzx.map σ
  have hzy' : Commute ⁅σ x, σ y⁆ (σ y) := by
    rw [← map_commutatorElement]
    exact hzy.map σ
  have h := two_pow_mul_le_card_of_extraspecial hW (p := 11) (by norm_num) hx' hz' hzx' hzy'
  rwa [orderOf_two_zmod_11] at h

theorem autRank_of_outer_odd {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    (hOut : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (B : Subgroup (MulAut S)) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hs : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ r := by
  let c : S →* MulAut S := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have hmem : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) hs1
      have h2 : s * g * s⁻¹ = g := this
      calc g * s = (s * g * s⁻¹) * s := by rw [h2]
        _ = s * g := by group
    rwa [hcen, Subgroup.mem_bot] at hmem
  have hrange : ∀ x ∈ B, x ∈ c.range := by
    intro x hx
    have hxx : x * x = 1 := hs x hx
    have hφ : ∀ y, x (x y) = y := fun y => by
      have := congrArg (fun φ : MulAut S => φ y) hxx
      exact this
    obtain ⟨s, hsx⟩ := autInner_of_outer_odd hOut x hφ
    exact ⟨s, MulEquiv.ext fun y => (hsx y).symm⟩
  have hmap : (B.comap c).map c = B := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hcard : Nat.card B = Nat.card (B.comap c) := by
    rw [← Subgroup.card_map_of_injective (f := c) (K := B.comap c) hcinj, hmap]
  rw [hcard]
  refine hr (B.comap c) ?_ ?_
  · intro x hx y hy
    apply hcinj
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  · intro x hx
    apply hcinj
    rw [map_mul, map_one]
    exact hs _ hx

theorem j4_autRank
    (B : Subgroup (MulAut (NativeSporadic.Carrier .J4)))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 17 := by
  have hsimple : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hcen : Subgroup.center (NativeSporadic.Carrier .J4) = ⊥ := by
    refine center_eq_bot_of_simple_not_prime ?_
    show ¬ (Nat.card NativeSporadic.J4).Prime
    rw [CFSG.Sporadic.J4.card_J4]
    norm_num
  exact autRank_of_outer_odd hcen j4OuterOdd j4TwoRank B hc hs

theorem false_of_J4
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .J4)) : False := by
  obtain ⟨e⟩ := hM
  refine false_of_cover_rank_dim h e
    (fun E _ _ _ π hπ hC hodd => j4_cover E π hπ hC hodd) (r := 17) j4_autRank
    (ρ := 110) ?_ (by norm_num)
  intro W _ _ hW σ hσ
  have hF := CFSG.Sporadic.J4.j4Facts
  have es : NativeSporadic.Carrier .J4 ≃* CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv hF.mat
  obtain ⟨h1, -, h3, h4, h5, -, -, -⟩ := CFSG.Sporadic.J4.QT.witness11 hF
  have hcomm : ⁅es.symm CFSG.Sporadic.J4.QT.xE, es.symm CFSG.Sporadic.J4.QT.yE⁆ =
      es.symm CFSG.Sporadic.J4.QT.zE := by
    rw [← map_commutatorElement, commutatorElement_def]
    rfl
  refine dim_of_extraspecial11 (x := es.symm CFSG.Sporadic.J4.QT.xE)
    (y := es.symm CFSG.Sporadic.J4.QT.yE) ?_ ?_ ?_ ?_ W hW σ hσ
  · rw [← map_pow, h1, map_one]
  · rw [hcomm]
    exact fun h => h3 (es.symm.injective (h.trans (map_one es.symm).symm))
  · rw [hcomm]
    exact (Commute.map (show Commute CFSG.Sporadic.J4.QT.zE CFSG.Sporadic.J4.QT.xE from h4.symm)
      es.symm)
  · rw [hcomm]
    exact (Commute.map (show Commute CFSG.Sporadic.J4.QT.zE CFSG.Sporadic.J4.QT.yE from h5.symm)
      es.symm)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
