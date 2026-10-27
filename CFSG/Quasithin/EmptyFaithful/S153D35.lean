module

public import CFSG.Quasithin.EmptyFaithful.S153D33
public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15336One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        ∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)

structure CtxComp2 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends CtxComp T Mc M V₁ V₂ Yp I t where
  rank : CFSG.Open.pRank 3 Yp = 2
  facts11 : Facts15311 T M V₁ Yp I
  s3s3 : ∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
    Function.Surjective φ ∧
      φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)
  c33 : Concl15333 T M V₁ Yp I L
  c34 : Concl15334 L

@[expose] def Concl15337 {G : Type} [Group G] (T V₁ Yp L : Subgroup G) : Prop :=
  Yp ≤ conjClosure L (Sgp153 T V₁) ∨
  (L = conjClosure L (Sgp153 T V₁) ∧
    ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ n : ℕ, Even n ∧ IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
      IsPSL 3 2 1 (↥L ⧸ Subgroup.center ↥L)) ∧
    Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) ∧
    padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1 ∧
    padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1 ∧
    IsElemAbelianOfRank 3 2 (OTwoQuot Yp)) ∨
  (L = conjClosure L (Sgp153 T V₁) ∧
    ((∃ n : ℕ, Even n ∧ IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)) ∧
    oTwoUpper (Yp ⊓ L) ≠ ⊥ ∧
    ∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
      Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp)

@[expose] def Input15337 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → Concl15337 T V₁ Yp L

@[expose] def Input15338 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → Concl15337 T V₁ Yp L → CFSG.Open.pRank 3 L = 2 → Yp ≤ L

@[expose] def Input15339 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → Concl15337 T V₁ Yp L → (CFSG.Open.pRank 3 L = 2 → Yp ≤ L) →
      L = conjClosure L (Sgp153 T V₁)

@[expose] def Input15340 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → Concl15337 T V₁ Yp L → (CFSG.Open.pRank 3 L = 2 → Yp ≤ L) →
      L = conjClosure L (Sgp153 T V₁) → Yp ≤ L

@[expose] def Input15335Close : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
      I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L → False

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem isHPlus_of_le (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts153 T M V₁ Yp I)
    {K : Subgroup G} (hKI : K ≤ I) (hYSK : Yp ⊔ Sgp153 T V₁ ≤ K) (hKM : ¬ K ≤ M) :
    IsHPlus Yp (Sgp153 T V₁) M K := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : pCoreOf 2 I ≤ K := (pCoreOf_le_Sgp153' hF).trans (le_sup_right.trans hYSK)
  have h1 : pCoreOf 2 I ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 hOK (fun g hg => le_normalizer_pCoreOf 2 I (hKI hg))
      (pCoreOf_isPGroup 2 I)
  refine ⟨⟨hYSK, ?_⟩, hKM⟩
  intro hbot
  exact hI.1.2 (eq_bot_iff.mpr (hbot ▸ h1))

theorem lemma_comp_I_eq_LS (c : CtxComp T Mc M V₁ V₂ Yp I t) {L : Subgroup G}
    (hL : L ∈ cComp I) (hLM : ¬ L ≤ M)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) (hYL : Yp ≤ L) :
    I ≤ Subgroup.normalizer (L : Set G) ∧ I = L ⊔ Sgp153 T V₁ := by
  have hLI : L ≤ I := le_of_mem_cComp hL
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs =>
    A4.mem_normalizer_of_conj_mem fun l hl => by
      rw [hL0]
      exact mem_conjClosure hs hl
  have hYSN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hYL.trans Subgroup.le_normalizer) hSN
  constructor
  · have hNK : IsHPlus Yp (Sgp153 T V₁) M (I ⊓ Subgroup.normalizer (L : Set G)) :=
      isHPlus_of_le c.inH c.facts inf_le_left (le_inf c.inH.1.1 hYSN)
        (fun hle => hLM fun x hx => hle ⟨hLI hx, Subgroup.le_normalizer hx⟩)
    have hN : I ⊓ Subgroup.normalizer (L : Set G) = I := hmin _ hNK inf_le_left
    intro g hg
    rw [← hN] at hg
    exact hg.2
  · have hK : IsHPlus Yp (Sgp153 T V₁) M (L ⊔ Sgp153 T V₁) :=
      isHPlus_of_le c.inH c.facts (sup_le hLI hSI) (sup_le (hYL.trans le_sup_left) le_sup_right)
        (fun hle => hLM (le_sup_left.trans hle))
    exact (hmin _ hK (sup_le hLI hSI)).symm

end S153D

@[expose] def StageComponentTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

theorem stageComponentTwo_of_inputs (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h25 : Stage15325) (h8 : Input15311Eight) (h33 : Input15333) (h34 : Input15334)
    (h36 : Input15336One) (h37 : Input15337) (h38 : Input15338) (h39 : Input15339)
    (h40 : Input15340) (hcl : Input15335Close) : StageComponentTwo := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI hmin hnc
  have c0 : CtxComp T Mc M V₁ V₂ Yp I t := ctxComp_of_inputs h8 h11 h113 h hI hnc
  obtain ⟨L, hL⟩ := h33 h25 G T Mc M V₁ V₂ Yp I t c0
  have c1 : CtxComp2 T Mc M V₁ V₂ Yp I L t :=
    { c0 with
      rank := hr
      facts11 := S153D.facts15311_of_stages h11 h113 h hr hI
      s3s3 := h36 G T Mc M V₁ V₂ Yp t h hr I hI
      c33 := hL
      c34 := h34 G T Mc M V₁ V₂ Yp I L t c0 hL }
  have c37 := h37 G T Mc M V₁ V₂ Yp I L t c1
  have c38 := h38 G T Mc M V₁ V₂ Yp I L t c1 c37
  have c39 := h39 G T Mc M V₁ V₂ Yp I L t c1 c37 c38
  have c40 := h40 G T Mc M V₁ V₂ Yp I L t c1 c37 c38 c39
  obtain ⟨hN, hIeq⟩ := S153D.lemma_comp_I_eq_LS c0 hL.mem hL.not_le hmin c39 c40
  exact hcl G T Mc M V₁ V₂ Yp I L t c1 hmin hN hIeq c40

end CFSG.Quasithin
