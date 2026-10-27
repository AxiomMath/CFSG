module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Chart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

section Inputs


@[expose] def GGQTwoDSelModuleInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∃ β : Additive ↥Bs ≃+ DVec m, ∀ (t : Fin m) (s : ↥Bs),
          β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
              MulAut ↥Bs)) s)) =
            dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
              (β (Additive.ofMul s))

@[expose] def GGQTwoDSelModuleInput : Prop :=
  GGQTwoDSelModuleInputOn fun m => 7 ≤ m

@[expose] def GGQTwoDOrthJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ Φ : OrthTorus.OrthFrameCore p Bs L, Nat.card Φ.F = 2 → 5 ≤ Φ.r →
        Subgroup.center ↥L = ⊥ →
          ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
            GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
              (labJ.tag = .twD → labJ.rank ≠ 2)

end Inputs

section Setup

variable {G : Type} [Group G] [Finite G]

theorem card_dvec (m : ℕ) : Nat.card (DVec m) = 3 ^ m := by
  rw [Nat.card_pi]
  simp [Nat.card_zmod]

theorem card_bs_of_module {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m) :
    Nat.card ↥Bs = 3 ^ m := by
  rw [← card_dvec m]
  exact Nat.card_congr (Additive.ofMul.trans β.toEquiv)

theorem qtwoDNbr_card_cent_le {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {X : Subgroup G} (hnbr : GGNbr 3 B x D J y X) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2 :=
  card_bstar_inf_centralizer_le hcfg hnbr

theorem card_bs_eq_cent_mul_gamma {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card ↥Bs =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * Nat.card (ggGamma X hN).range := by
  have h := Subgroup.card_ker_mul_card_range (ggGamma X hN)
  have hker : (ggGamma X hN).ker = (Bs ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker] at h
  rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs)).toEquiv]

theorem three_pow_le_card_range_gamma {Bs X : Subgroup G} {m : ℕ} (hcard : Nat.card ↥Bs = 3 ^ m)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ (m - 2) ≤ Nat.card (ggGamma X hN).range := by
  have h := card_bs_eq_cent_mul_gamma hN
  rw [hcard] at h
  by_cases hm : 2 ≤ m
  · have h9 : 3 ^ (m - 2) * 3 ^ 2 ≤ Nat.card (ggGamma X hN).range * 3 ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hm, h, mul_comm]
      exact Nat.mul_le_mul_left _ hcent
    exact Nat.le_of_mul_le_mul_right h9 (by positivity)
  · have : m - 2 = 0 := by omega
    rw [this, pow_zero]
    exact Nat.card_pos

end Setup

end CFSG.StandardType.QTwo

end
