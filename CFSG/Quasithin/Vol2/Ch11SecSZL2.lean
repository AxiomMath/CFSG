module

public import CFSG.Quasithin.Vol2.Ch11SecSSym4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped commutatorElement IsMulCommutative

@[expose] def FactNatFixedSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π → (∀ z ∈ Z, ∀ h ∈ H, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ R : Subgroup (MulAut W), IsPGroup 2 ↥R → P ≤ R →
        R ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          ∃ w : W, (∀ r ∈ R, r w = w) ∧ ∃ g ∈ gammaW H U₂, g w ≠ w

@[expose] def FactNatFixedSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → (∀ z ∈ Z, ∀ h ∈ H, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ R : Subgroup (MulAut W), IsPGroup 2 ↥R → P ≤ R →
        R ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          ∃ w : W, (∀ r ∈ R, r w = w) ∧ ∃ g ∈ gammaW H U₂, g w ≠ w

@[expose] def FactNatFixedG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      (∀ z ∈ Z, ∀ h ∈ H, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ R : Subgroup (MulAut W), IsPGroup 2 ↥R → P ≤ R →
        R ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          ∃ w : W, (∀ r ∈ R, r w = w) ∧ ∃ g ∈ gammaW H U₂, g w ≠ w

structure NatFixedFacts : Prop where
  sl3 : FactNatFixedSL3
  sp4 : FactNatFixedSp4
  g2 : FactNatFixedG2

variable {G : Type} [Group G] [Finite G]

theorem obl11_1_2StarZL2_of (hNF : NatFixedFacts) (h1102 : Stmt11_0_2) : Obl11_1_2StarZL2 := by
  intro G _ _ T L I V₁ V₂ X K h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h.hyp).2 w w.2)
  have hP := isSylowTwoOf_P h.hyp
  have hU₂ := isFlagW_of_isVi h.hyp h.v₂
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I
  have hR2 : IsPGroup 2 ↥(autOn T (fsuV T I)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))) :=
      h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm
    exact h2.map _
  have hPR : autOn (T ⊓ L) (fsuV T I) ≤ autOn T (fsuV T I) := autOn_mono inf_le_left
  have hRN := autOn_le_normalizer (V := fsuV T I) h.hyp.normal
  have hZ : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I),
      ∀ g ∈ autOn L (fsuV T I), g z = z := by
    rintro z hz _ ⟨⟨x, hx⟩, hxL, rfl⟩
    apply Subtype.ext
    change ((conjV (fsuV T I) x hx z : ↥(fsuV T I)) : G) = z
    rw [conjV_apply_coe]
    have hxz : x * (z : G) = (z : G) * x := Subgroup.mem_centralizer_iff.mp hz x hxL
    rw [hxz, mul_assoc, mul_inv_cancel, mul_one]
  have key : ∀ w : ↥(fsuV T I), (∀ r ∈ autOn T (fsuV T I), r w = w) →
      (∃ g ∈ gammaW (autOn L (fsuV T I)) (V₂.subgroupOf (fsuV T I)), g w ≠ w) →
        ⁅quasithinOmegaOneCenter T, LOf L V₂⁆ ≠ ⊥ := by
    rintro w hwR ⟨g, hg, hgw⟩ hb
    rw [← autOn_lOf (L_le_normalizer_fsuV h.hyp) (IsVi.le_fsuV h.v₂)] at hg
    obtain ⟨⟨x, hx⟩, hxL, rfl⟩ := hg
    have hwZ : (w : G) ∈ quasithinOmegaOneCenter T := by
      refine Subgroup.subset_closure ⟨⟨fsuV_le_T h.hyp w.2, ?_⟩, ?_⟩
      · show (w : G) ∈ Subgroup.centralizer (T : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have h1 := congrArg Subtype.val (hwR _ (conjV_mem_autOn ht (hTV ht)))
        rw [conjV_apply_coe] at h1
        calc t * w = t * w * t⁻¹ * t := by group
          _ = w * t := by rw [h1]
      · simpa using congrArg Subtype.val (hsq w)
    have hxL' : x ∈ LOf L V₂ := hxL
    have hc : ⁅(w : G), x⁆ ∈ ⁅quasithinOmegaOneCenter T, LOf L V₂⁆ :=
      Subgroup.commutator_mem_commutator hwZ hxL'
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    apply hgw
    apply Subtype.ext
    change ((conjV (fsuV T I) x hx w : ↥(fsuV T I)) : G) = w
    rw [conjV_apply_coe, ← hc, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I 2 h.hyp
  rcases hk with ⟨K', _, _, hK, -, π, hπ, -⟩ | ⟨K', _, _, hK, -, π, hπ, -⟩ | ⟨K', _, _, hK, -, hnat⟩
  · obtain ⟨w, hw, hg⟩ := hNF.sl3 K' 2 le_rfl hK _ hsq _ _ π hπ hZ _ hP _ hU₂ _ hR2 hPR hRN
    exact key w hw hg
  · obtain ⟨w, hw, hg⟩ := hNF.sp4 K' 2 le_rfl hK _ hsq _ _ π hπ hZ _ hP _ hU₂ _ hR2 hPR hRN
    exact key w hw hg
  · obtain ⟨K'', _, _, hK'', π, hπ⟩ := hnat
    obtain ⟨w, hw, hg⟩ := hNF.g2 K'' 2 le_rfl hK'' _ hsq _ _ π hπ hZ _ hP _ hU₂ _ hR2 hPR hRN
    exact key w hw hg

end CFSG.Quasithin.Vol2.Ch11.SecS
