module

public import CFSG.Quasithin.EmptyFaithful.S153D54
public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def A7NotA38Type : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    (∃ α : ↥L →* alternatingGroup (Fin 7), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) →
      ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def HatA6ProperThreePart : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ X : Subgroup G),
    IsHatA6Block L → IsSylowTwoOf S₀ L → S₀ ≤ X → X ≤ L → X ≠ L → ¬ 27 ∣ Nat.card ↥X

@[expose] def ExcA7NoS3Section : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S Y : Subgroup G),
    IsExcA7Block L → IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → Y ≤ L →
      ¬ ∃ φ : ↥(Y ⊔ S) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = (oTwoPhi (Y ⊔ S)).subgroupOf (Y ⊔ S)

@[expose] def OrdA7ConfigNoNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V Y : Subgroup G),
    IsAltBlockType K 7 → R ≤ Subgroup.normalizer (K : Set G) →
      V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) → C27Concl H R M K V →
      Y ≤ M ⊓ K → Y ≤ Subgroup.normalizer (R : Set G) → 9 ∣ Nat.card ↥Y → False

@[expose] def HatA6Endgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsHatA6Block L → Yp ≤ L →
      IsElemAbelianOfRank 3 2 (OTwoQuot Yp) →
      (∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)) → False

namespace S153F

open CFSG.Quasithin.S153D

section Helpers

variable {G : Type} [Group G] [Finite G] {T M V₁ Yp I : Subgroup G}

theorem nine_dvd_card_Yp (hF : Facts15311 T M V₁ Yp I) : 9 ∣ Nat.card ↥Yp := by
  have hq : 9 ∣ Nat.card (OTwoQuot Yp) := by
    rcases hF.struct_Yp with he | ⟨-, hcard, -⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card]
    · rw [hcard]
      norm_num
  exact hq.trans (Subgroup.card_quotient_dvd_card _)

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input15321Rest_of_named_inputs (hcover : AsA36NoOddCover) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kR : Input21Rank) (h36 : Input15336One) (kN : A7NotA38Type)
    (kT : HatA6ProperThreePart) (kE : ExcA7NoS3Section) (kO : OrdA7ConfigNoNine)
    (kH : HatA6Endgame) : Input15321Rest := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 _ _ n20a _
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYM : Yp ≤ M ⊓ I := hF.norm_eq ▸ le_inf hYI Subgroup.le_normalizer
  have hS3 := h36 G T Mc M V₁ V₂ Yp t hh c.ctx.rank I hI
  have hExc : ¬ IsExcA7Block L := by
    intro hE
    have hYL := Yp_le_of_concl15317 hcover c c17
      (kR G L (Or.inr (Or.inr (Or.inr (Or.inr hE))))) n20a
    have hSIL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
      have hq := hh.hyp.qtfe
      rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hI.1.2 hLI with hn | ⟨-, h2⟩
      · exact hF.sylow.1.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn)
      · exact absurd h2 (kN G L hE.2.1)
    exact kE G L (Sgp153 T V₁) Yp hE hF.sylow.2.1 hSIL hYL hS3
  have hOrd : ¬ IsAltBlockType L 7 := by
    intro hA
    have hYL := Yp_le_of_concl15317 hcover c c17
      (kR G L (Or.inr (Or.inr (Or.inr (Or.inl hA))))) n20a
    have hYR : Yp ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
      le_sup_left.trans (le_normalizer_pCoreOf 2 _)
    exact kO G I (R153 T V₁ Yp) (M ⊓ I) L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp))) Yp
      hA c.c16.R_norm rfl c.c16.desc (le_inf hYM hYL) hYR (nine_dvd_card_Yp hF)
  have hHat : ¬ IsHatA6Block L := by
    intro hA
    have hYL := Yp_le_of_concl15317 hcover c c17
      (kR G L (Or.inr (Or.inr (Or.inl hA)))) n20a
    have hXL : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ L := sup_le hYL inf_le_right
    have hXM : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ M :=
      sup_le (hh.Yp_le_Y153.trans (Y153_le Mc M)) (inf_le_left.trans (inf_le_left.trans hh.hyp.T_le))
    have hXne : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≠ L := fun h => hLn (le_inf (h ▸ hXM) hLle)
    have h27 := kT G L (Sgp153 T V₁ ⊓ L) (Yp ⊔ (Sgp153 T V₁ ⊓ L)) hA hSL le_sup_right hXL hXne
    have hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
      rcases hF.struct_Yp with h | ⟨-, hcard, -⟩
      · exact h
      · exfalso
        apply h27
        have h1 : 27 ∣ Nat.card ↥Yp := by
          have := Subgroup.card_quotient_dvd_card (CFSG.Open.pCore 2 ↥Yp)
          rw [show Nat.card (OTwoQuot Yp) = 27 by rw [hcard]; norm_num] at this
          exact this
        exact h1.trans (Subgroup.card_dvd_of_le (le_sup_left : Yp ≤ Yp ⊔ (Sgp153 T V₁ ⊓ L)))
    exact kH G T Mc M V₁ V₂ Yp I L t c hA hYL hE9 hS3
  exact ⟨hHat, hOrd, hExc⟩

end Main

end S153F

end CFSG.Quasithin
