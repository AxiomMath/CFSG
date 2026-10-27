module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs
public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResHyp {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ GGNbr p B x D J y K ∧ GGReflGenerated p (ggAutomizer K Bs) ∧
    GGScalarsOrWeyl' p B Bs x D J

abbrev GGResCase : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), Prop

@[expose] def GGResLeaf (P : GGResCase) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    ¬ GGCoxeterForkDatum p Bs L K → ¬ GGCoxeterStdDatum p Bs L K → ¬ GGE6DepPerpCfg p Bs L K →
    P G p B Bs x L D J y K → GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

theorem ggCoxeterLabelResidualOffE6DepInput_of_leaf
    (h : GGResLeaf fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True) :
    GGCoxeterLabelResidualOffE6DepInput := by
  intro G _ _ p B Bs x L D J hC hO hI hT y K hK hRG hSW _ hF hS hl
  exact h G p B Bs x L D J y K ⟨hC, hO, hI, hT, hK, hRG, hSW⟩ hF hS hl trivial

@[expose] def GGIsTypeE6 {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e

@[expose] def GGIsTypeA {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ M = (CoxeterMatrix.A n).reindex e

@[expose] def GGDeletedConnected {Λ : Type} (ML : CoxeterMatrix Λ) (b : Λ) : Prop :=
  ∀ i j : {i : Λ // i ≠ b},
    Relation.ReflTransGen (fun u v : {i : Λ // i ≠ b} => u ≠ v ∧ ML.M u v ≠ 2) i j

@[expose] def GGResLeviDatum {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G)
    (sel : Prop → Prop → Prop)
    (typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b : Λ) (ML : CoxeterMatrix Λ)
    (CL : Matrix Λ Λ ℤ) (MK : CoxeterMatrix (Option {i : Λ // i ≠ b}))
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Option Λ → MulAut ↥Bs) (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      typ ML MK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : Option {i : Λ // i ≠ b},
        α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)) ∧
      sel (LinearIndependent (ZMod p) fun i : Λ => h (some i)) (LinearIndependent (ZMod p) h) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (some i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}) ∧
      GGDeletedConnected ML b ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j))

@[expose] def ggSelAny : Prop → Prop → Prop := fun _ _ => True
@[expose] def ggSelI : Prop → Prop → Prop := fun _ all => all
@[expose] def ggSelII : Prop → Prop → Prop := fun l all => l ∧ ¬ all
@[expose] def ggSelDep : Prop → Prop → Prop := fun l _ => ¬ l

@[expose] def ggTypAny {Λ Λ' : Type} (_ : CoxeterMatrix Λ) (_ : CoxeterMatrix Λ') : Prop := True
@[expose] def ggTypRankGe (k : ℕ) {Λ Λ' : Type} (_ : CoxeterMatrix Λ) (_ : CoxeterMatrix Λ') :
    Prop := k ≤ Nat.card Λ
@[expose] def ggTypRankLt (k : ℕ) {Λ Λ' : Type} (_ : CoxeterMatrix Λ) (_ : CoxeterMatrix Λ') :
    Prop := Nat.card Λ < k
@[expose] def ggTypLE6 {Λ Λ' : Type} (ML : CoxeterMatrix Λ) (_ : CoxeterMatrix Λ') : Prop :=
  GGIsTypeE6 ML
@[expose] def ggTypLKE6 {Λ Λ' : Type} (ML : CoxeterMatrix Λ) (MK : CoxeterMatrix Λ') : Prop :=
  GGIsTypeE6 ML ∧ GGIsTypeE6 MK
@[expose] def ggTypLA {Λ Λ' : Type} (ML : CoxeterMatrix Λ) (_ : CoxeterMatrix Λ') : Prop :=
  GGIsTypeA ML

theorem GGResLeviDatum.mono {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {sel sel' : Prop → Prop → Prop}
    {typ typ' : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatum p Bs L J K sel typ) (hsel : ∀ l a : Prop, sel l a → sel' l a)
    (htyp : ∀ {Λ Λ' : Type} (M : CoxeterMatrix Λ) (M' : CoxeterMatrix Λ'), typ M M' → typ' M M') :
    GGResLeviDatum p Bs L J K sel' typ' := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16⟩ := hD
  exact ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, htyp _ _ h5, h6, h7,
    h8, h9, hsel _ _ h10, h11, h12, h13, h14, h15, h16⟩

theorem GGResLeviDatum.cases {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatum p Bs L J K ggSelAny typ) :
    GGResLeviDatum p Bs L J K ggSelI typ ∨ GGResLeviDatum p Bs L J K ggSelII typ ∨
      GGResLeviDatum p Bs L J K ggSelDep typ := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    -, h11, h12, h13, h14, h15, h16⟩ := hD
  by_cases hl : LinearIndependent (ZMod p) fun i : Λ => h (some i)
  · by_cases ha : LinearIndependent (ZMod p) h
    · exact Or.inl ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6,
        h7, h8, h9, ha, h11, h12, h13, h14, h15, h16⟩
    · exact Or.inr (Or.inl ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4,
        h5, h6, h7, h8, h9, ⟨hl, ha⟩, h11, h12, h13, h14, h15, h16⟩)
  · exact Or.inr (Or.inr ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4,
      h5, h6, h7, h8, h9, hl, h11, h12, h13, h14, h15, h16⟩)

theorem GGResLeviDatum.split {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatum p Bs L J K sel typ)
    (Q : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop) :
    GGResLeviDatum p Bs L J K sel (fun M M' => typ M M' ∧ Q M M') ∨
      GGResLeviDatum p Bs L J K sel (fun M M' => typ M M' ∧ ¬ Q M M') := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16⟩ := hD
  by_cases hQ : Q ML MK
  · exact Or.inl ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, ⟨h5, hQ⟩,
      h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  · exact Or.inr ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, h1, h2, h3, h4, ⟨h5, hQ⟩,
      h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem GGResLeviDatum.dependent {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatum p Bs L J K sel typ) (hsel : ∀ l a : Prop, (a → l) → sel l a → ¬ a)
    (hp2 : p ≠ 2) :
    GGDependentReflectionDatum p Bs L K := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, -, h2, -, h4, -, h6, -, h8, h9,
    h10, -, -, h13, h14, -, -⟩ := hD
  have hdiag : ∀ o, α o (h o) = 2 := by
    rintro (_ | i)
    · have := h9 none none
      rw [h4.1 none] at this
      simpa using this
    · rw [h8 i i, h2.1 i]
      norm_num
  refine ⟨Λ, i1, i2, V, i3, i4, ι, φ, h, α, b, hdiag, fun o h0 => ?_, h6,
    hsel _ _ (fun ha => ha.comp _ (Option.some_injective _)) h10, h13, h14⟩
  have := hdiag o
  rw [h0, map_zero] at this
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast this.symm
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')


theorem GGResHyp.Bs_le_normalizer_J {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Bs ≤ Subgroup.normalizer (J : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hBsB : GGBstar p B Bs := hcfg.2.1
  have hDJ : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hH.2.2.1.1
  exact GGDichotomy.le_normalizer_stdSub
    (fun a ha b hb => congrArg Subtype.val (hBsB.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    hBsB.1 hDJ hN

theorem GGResHyp.gamma_J_selfCent {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    GGTorusSelfCent p (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
  ggTorusSelfCent_ggGamma (GGResHyp.Bs_le_normalizer_J hH) hH.1.2.1.2.2.2

theorem GGConfig.card_range_gamma_B_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hBN : B ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hBN).range = p ^ (LargeEvenTwoLocalRank p G - 2) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hm : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hker : (ggGamma J hBN).ker = (Subgroup.centralizer (J : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf B) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard := TableB.card_range_mul_card_ker (ggGamma J hBN)
  rw [hker, hkerCard, ← hD, hDcard, hBcard] at hcard
  have hdecomp : p ^ LargeEvenTwoLocalRank p G =
      p ^ (LargeEvenTwoLocalRank p G - 2) * p ^ 2 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hdecomp] at hcard
  exact Nat.mul_right_cancel (pow_pos hp.pos 2) hcard

theorem GGConfig.pow_le_card_gamma_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    p ^ (LargeEvenTwoLocalRank p G - 2) ≤ Nat.card (ggGamma J hN).range := by
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hB := hcfg.card_range_gamma_B_J (hBBs.trans hN)
  rw [← hB]
  refine Subgroup.card_le_of_le ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b, hBBs b.2⟩, rfl⟩

theorem GGResHyp.pow_le_card_gamma_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    p ^ (LargeEvenTwoLocalRank p G - 2) ≤
      Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
  hH.1.pow_le_card_gamma_J hH.Bs_le_normalizer_J

theorem GGResHyp.sq_le_card_gamma_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    p ^ 2 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hm : 4 ≤ LargeEvenTwoLocalRank p G := hH.1.1.2.2.2.2.2.1.2.2.2
  exact (Nat.pow_le_pow_right hp.pos (by omega)).trans (GGResHyp.pow_le_card_gamma_J hH)

theorem GGResHyp.card_range_gamma_J_of_exactThree_centralizer
    {G : Type} [Group G] [Finite G] {p r : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hBs : Nat.card Bs = p ^ r)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3) :
    5 ≤ r ∧ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ (r - 3) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have hker : (ggGamma J hH.Bs_le_normalizer_J).ker =
      (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := TableB.card_range_mul_card_ker (ggGamma J hH.Bs_le_normalizer_J)
  rw [hker, hkerCard, hC, hBs] at hcount
  have hbound : p ^ 5 ≤ p ^ r := by
    calc p ^ 5 = p ^ 2 * p ^ 3 := by rw [← pow_add]
      _ ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range * p ^ 3 :=
        Nat.mul_le_mul_right _ hH.sq_le_card_gamma_J
      _ = p ^ r := hcount
  have hr : 5 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).mp hbound
  refine ⟨hr, Nat.mul_right_cancel (pow_pos hp.pos 3) ?_⟩
  rw [hcount, ← pow_add]
  congr 1
  omega

theorem GGConfig.torusLift_add_two_le_twoLocalRank {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    {R : Type} [Group R] (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) {r : ℕ}
    (hT : GGTorusLift p r R) :
    r + 2 ≤ LargeEvenTwoLocalRank p G := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hJperf : commutator ↥J = ⊤ := hpre.2.2.2.2.2.1.2.2.1
  have hDC : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hpre.2.2.2.2.2.2]
    exact inf_le_right
  have h1 := CFSG.LocalAnalysis.GLTheoremA.S265.SF.pow_mul_card_le_of_torusLift
    (Ω := G) (K := J) (D := D) hp hJperf θ hT hpre.2.1 hDC
  rw [hpre.2.2.1, ← Nat.pow_add] at h1
  have hrank : CFSG.Open.GLATwoLocalRank p G = LargeEvenTwoLocalRank p G := rfl
  rw [hrank] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem GGConfig.pow_le_card_range_gamma_J_of_torusLift {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {R : Type} [Group R] (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) {r : ℕ}
    (hT : GGTorusLift p r R) : p ^ r ≤ Nat.card (ggGamma J hN).range := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hcore := hcfg.torusLift_add_two_le_twoLocalRank θ hT
  have hr : r ≤ LargeEvenTwoLocalRank p G - 2 := by omega
  exact (Nat.pow_le_pow_right hp.pos hr).trans (hcfg.pow_le_card_gamma_J hN)

theorem GGResHyp.pow_le_card_range_gamma_J_of_torusLift {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {R : Type} [Group R] (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) {r : ℕ}
    (hT : GGTorusLift p r R) :
    p ^ r ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
  hH.1.pow_le_card_range_gamma_J_of_torusLift hH.Bs_le_normalizer_J θ hT

end CFSG.StandardType
