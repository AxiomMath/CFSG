module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Milestones.ASVolI.I7
public import CFSG.Milestones.ASVolI.I8
public import CFSG.Milestones.ASVolI.J1
public import CFSG.Milestones.ASVolI.J2
public import CFSG.Milestones.ASVolI.J3
public import CFSG.Milestones.ASVolI.J4
public import CFSG.Quasithin.Recognition.RuRank3J5
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.Quasithin.Recognition.RuTypeJ47l
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmFinal2
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuCert
public import CFSG.Quasithin.Vol2.TwoF4F48Cert
public import CFSG.Quasithin.Recognition.RuRank3Main
public import CFSG.Quasithin.Recognition.RuTypeJ11c
public import CFSG.Quasithin.Recognition.RuTypeJ29f
public import CFSG.Quasithin.Recognition.RuTypeJ27l
public import CFSG.Quasithin.Recognition.RuTypeJ47b
public import CFSG.Quasithin.Recognition.RuTypeJ44c
public import CFSG.RankThree.PartOne.K159F.L2Leaf
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut
public import CFSG.Walter.JRFacts
public import CFSG.Quasithin.Recognition.RuRank3J55Data
public import CFSG.Quasithin.EmptyFaithful.S152N2Frob
public import Certificates.Certificate4160
public import Certificates.Certificate7340
public import Certificates.Certificate7341
public import Certificates.Certificate7342
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuStab
public import Certificates.Data.RuF45Geom
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152FinBasic
public import CFSG.Quasithin.EmptyFaithful.S152N2L14C
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

scoped instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

section J5

@[expose] def IsParabolicTwoSub {X : Type} [Group X] (P : Subgroup X) : Prop :=
  ∃ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P

@[expose] def IsL225Plus (Y : Type) [Group Y] : Prop :=
  ∃ N : Subgroup Y, N.Normal ∧ N.index = 2 ∧ StatedClassicalModel ↥N .PSL 2 5 2 ∧
    ∃ (P : Sylow 2 Y) (n : ℕ), 4 ≤ n ∧ Nonempty (↥(P : Subgroup Y) ≃* SemidihedralGroup n)

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

@[expose] def IsRudvalisRank3 (G : Type) [Group G] (Ω : Type) [MulAction G Ω] : Prop :=
  Nonempty Ω ∧ (∀ g : G, (∀ ω : Ω, g • ω = ω) → g = 1) ∧ MulAction.IsPretransitive G Ω ∧
    ∀ ω : Ω, Nat.card (MulAction.orbitRel.Quotient ↥(MulAction.stabilizer G ω) Ω) = 3 ∧
      IsTwoF4TwoGroup ↥(MulAction.stabilizer G ω) ∧
      (∃ δ : Ω, IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
          (MulAction.stabilizer G ω)) ∧
        Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) = 2 ^ 12 * 5) ∧
      ∃ γ : Ω, IsL225Plus ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ)

@[expose] def DeltaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ ρ : Ω) : Set Ω :=
  {σ | ∃ g : G, g • ω = ρ ∧ g⁻¹ • σ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) δ}

@[expose] def SigmaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω γ ρ : Ω) : Set Ω :=
  {σ | ∃ g : G, g • ω = ρ ∧ g⁻¹ • σ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) γ}

@[expose] def pairStab (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (α β : Ω) : Set G :=
  {g | ({g • α, g • β} : Set Ω) = {α, β}}

structure RudvalisSetting (G : Type) [Group G] (Ω : Type) [MulAction G Ω] (ω δ γ : Ω) : Prop where
  rank3 : IsRudvalisRank3 G Ω
  rub : IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
      (MulAction.stabilizer G ω)) ∧
    Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) = 2 ^ 12 * 5
  ruc : IsL225Plus ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ)

end J5

section Geometry

variable {Y : Type} [Group Y]

@[expose] def incGraph (M1 M2 : Subgroup Y) : SimpleGraph (Y ⧸ M1 ⊕ Y ⧸ M2) where
  Adj u v := (∃ y : Y, u = Sum.inl (y : Y ⧸ M1) ∧ v = Sum.inr (y : Y ⧸ M2)) ∨
    (∃ y : Y, v = Sum.inl (y : Y ⧸ M1) ∧ u = Sum.inr (y : Y ⧸ M2))
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨y, h1, h2⟩ | ⟨y, h1, h2⟩
    · rw [h1] at h2; exact Sum.inl_ne_inr h2
    · rw [h1] at h2; exact Sum.inl_ne_inr h2⟩

end Geometry

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J5b

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

@[expose] def FdOf (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ : Ω) :
    Subgroup ↥(MulAction.stabilizer G ω) :=
  (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf (MulAction.stabilizer G ω)

structure RuBuilding (G : Type) [Group G] (Ω : Type) [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ) : Prop where
  setting : RudvalisSetting G Ω ω δ γ
  amalgam : ∃ T' : Subgroup ↥(MulAction.stabilizer G ω),
    CFSG.Quasithin.IsYAmalgamPair T' (FdOf G ω δ) M2
  bij : Set.BijOn φ (DeltaAt G ω δ ω) Set.univ
  equivariant : ∀ f : ↥(MulAction.stabilizer G ω), ∀ ρ ∈ DeltaAt G ω δ ω, φ (f • ρ) = f • φ ρ
  base : φ δ = ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ)
  nbhd : ∀ ρ ∈ DeltaAt G ω δ ω, (ρ ∈ DeltaAt G ω δ δ ↔
    (0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) < 8))

@[expose] def thetaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ u : Ω) : Set Ω :=
  {w | w ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ u ∧
    (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G u) w).ncard = 10}

@[expose] def LambdaAt (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ γ u : Ω) : Set Ω :=
  DeltaAt G ω δ ω ∩ DeltaAt G ω δ u ∩ SigmaAt G ω γ δ

@[expose] def GeoFrom {W : Type} (Γ : SimpleGraph W) (x : W) (S : Set W) :
    Set (Σ b : W, Γ.Walk x b) :=
  {p | p.1 ∈ S ∧ p.2.length = Γ.dist x p.1}

@[expose] def WalkIncreases {W : Type} (Γ : SimpleGraph W) (δv : W) {a b : W} (p : Γ.Walk a b)
    (i i' : ℕ) : Prop :=
  i ≤ i' ∧ i' ≤ p.length ∧
    ∀ j, j ≤ i' - i → Γ.dist δv (p.getVert (i + j)) = Γ.dist δv (p.getVert i) + j

@[expose] noncomputable def dseq {W : Type} (Γ : SimpleGraph W) (δv : W) {a b : W} (p : Γ.Walk a b) (i : ℕ) : ℕ :=
  Γ.dist δv (p.getVert i)

@[expose] def NgeoSet {W : Type} (Γ : SimpleGraph W) (δv y : W) (e : ℕ) : Set (Σ b : W, Γ.Walk y b) :=
  {q | q.2.length = 8 - e ∧ ∀ j, j ≤ 8 - e → Γ.dist δv (q.2.getVert j) = e + j}

@[expose] def omegaGraph (G : Type) [Group G] {Ω : Type} [MulAction G Ω] (ω δ : Ω) : SimpleGraph Ω :=
  SimpleGraph.fromRel (fun ρ τ => τ ∈ DeltaAt G ω δ ρ)

@[expose] noncomputable def OmegaPrime (F : Type) [Group F] (M1 M2 E : Subgroup F) :
    SimpleGraph (Option (F ⧸ M1 ⊕ F ⧸ E)) :=
  SimpleGraph.fromRel (fun a b =>
    (∃ u : F ⧸ M1, a = none ∧ b = some (Sum.inl u)) ∨
    (∃ u v : F ⧸ M1, a = some (Sum.inl u) ∧ b = some (Sum.inl v) ∧
      (incGraph M1 M2).Reachable (Sum.inl u) (Sum.inl v) ∧
      (incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ≤ 6) ∨
    (∃ (u : F ⧸ M1) (v : F ⧸ E), a = some (Sum.inl u) ∧ b = some (Sum.inr v) ∧
      (MulAction.orbit ↥(MulAction.stabilizer F v) u).ncard = 780) ∨
    (∃ v w : F ⧸ E, a = some (Sum.inr v) ∧ b = some (Sum.inr w) ∧
      (MulAction.orbit ↥(MulAction.stabilizer F v) w).ncard = 975))

end J5b

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        Nat.card (G ⧸ FRu L V V2 T a B5 X) = 2 ^ 2 * 5 * 7 * 29 ∧ 2 ^ 2 * 5 * 7 * 29 = 4060

section BurnsideJ10b

private theorem burnsideJ10b_card_quotient_conjugate {G : Type} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (G ⧸ CFSG.conjugate A g) = Nat.card (G ⧸ A) := by
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
  unfold CFSG.conjugate
  exact Subgroup.index_map_equiv A (MulAut.conj g⁻¹)

private theorem burnsideJ10b_stabilizer_coset {G : Type} [Group G] (F : Subgroup G) (h : G) :
    MulAction.stabilizer G (h : G ⧸ F) = CFSG.conjugate F h⁻¹ := by
  ext x
  rw [MulAction.mem_stabilizer_iff, RuChoice.mem_conjugate]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  have e : (x * h)⁻¹ * h = (h⁻¹ * x * h)⁻¹ := by group
  rw [e, inv_mem_iff]
  simp

private theorem burnsideJ10b_smul_one_eq_iff {G : Type} [Group G] (F : Subgroup G) (x : G) :
    x • ((1 : G) : G ⧸ F) = ((1 : G) : G ⧸ F) ↔ x ∈ F := by
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

open scoped Pointwise in
private theorem burnsideJ10b_J53_abstract {G : Type} [Group G] [Finite G] (F F1 Q : Subgroup G)
    (hF1F : F1 ≤ F) (hN : ∀ q ∈ Q, ∀ f ∈ F1, q * f * q⁻¹ ∈ F1)
    (hQi : ((F1 ⊓ Q).subgroupOf Q).index = 2)
    (hcard : Nat.card F = 1755 * Nat.card F1)
    (hmax : ∀ h ∈ Q, h ∉ F1 → F ⊓ CFSG.conjugate F h⁻¹ = F1) :
    ∃ δ : G ⧸ F, Nat.card ↥(MulAction.orbit ↥F δ) = 1755 ∧
      F ⊓ MulAction.stabilizer G δ = F1 ∧
      ChIJK.pairStab G ((1 : G) : G ⧸ F) δ = ((F1 ⊔ Q : Subgroup G) : Set G) := by
  obtain ⟨h, hhQ, hhF1⟩ : ∃ h ∈ Q, h ∉ F1 := by
    by_contra hcon
    push Not at hcon
    have hle : Q ≤ F1 := hcon
    have : (F1 ⊓ Q).subgroupOf Q = ⊤ := by
      rw [Subgroup.subgroupOf_eq_top]
      exact fun x hx => ⟨hle hx, hx⟩
    rw [this, Subgroup.index_top] at hQi
    omega
  have hsq : ∀ q ∈ Q, q ∉ F1 → ∀ q' ∈ Q, q' ∈ F1 ∨ q⁻¹ * q' ∈ F1 := by
    intro q hq hqF q' hq'
    by_cases h1 : q' ∈ F1
    · exact Or.inl h1
    · right
      have key := (Subgroup.mul_mem_iff_of_index_two hQi
        (a := (⟨q, hq⟩ : Q)⁻¹) (b := (⟨q', hq'⟩ : Q))).mpr (iff_of_false ?_ ?_)
      · exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp key)).1
      · intro hh
        have := inv_mem hh
        rw [inv_inv] at this
        exact hqF (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1
      · exact fun hh => h1 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hh)).1
  have hh2 : h * h ∈ F1 := by
    have := hsq h hhQ hhF1 h⁻¹ (inv_mem hhQ)
    rcases this with h1 | h1
    · exact absurd (by simpa using inv_mem h1) hhF1
    · have := inv_mem h1
      simpa [mul_inv_rev] using this
  have hstab : MulAction.stabilizer G (h : G ⧸ F) = CFSG.conjugate F h⁻¹ :=
    burnsideJ10b_stabilizer_coset F h
  have hFδ : F ⊓ MulAction.stabilizer G (h : G ⧸ F) = F1 := by
    rw [hstab]
    exact hmax h hhQ hhF1
  refine ⟨(h : G ⧸ F), ?_, hFδ, ?_⟩
  ·
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥F (h : G ⧸ F))
    rw [CFSG.Quasithin.RuType.J11.card_stabilizer_subgroup, hFδ, MulAction.index_stabilizer] at h1
    rw [hcard] at h1
    have h2 : Nat.card F1 * (MulAction.orbit ↥F (h : G ⧸ F)).ncard = Nat.card F1 * 1755 := by
      rw [h1]
      ring
    have hF1pos : 0 < Nat.card F1 := Nat.card_pos
    have h3 := Nat.eq_of_mul_eq_mul_left hF1pos h2
    rw [Nat.card_coe_set_eq]
    exact h3
  ·
    have hhQ' : h⁻¹ ∈ Q := inv_mem hhQ
    have hh2F : h * h ∈ F := hF1F hh2
    have hQN : Q ≤ Subgroup.normalizer (F1 : Set G) := fun q hq => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => hN q hq x hx
      · intro hx
        have := hN q⁻¹ (inv_mem hq) _ hx
        simpa [mul_assoc] using this
    have hset : ((F1 ⊔ Q : Subgroup G) : Set G) = ((Q : Subgroup G) : Set G) * (F1 : Set G) := by
      rw [sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQN
    have c1 : ∀ x : G, x • ((1 : G) : G ⧸ F) = ((1 : G) : G ⧸ F) ↔ x ∈ F :=
      burnsideJ10b_smul_one_eq_iff F
    have c2 : ∀ x : G, x • ((1 : G) : G ⧸ F) = (h : G ⧸ F) ↔ x⁻¹ * h ∈ F := by
      intro x
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_one]
    have c3 : ∀ x : G, x • (h : G ⧸ F) = ((1 : G) : G ⧸ F) ↔ x * h ∈ F := by
      intro x
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_one, inv_mem_iff]
    have c4 : ∀ x : G, x • (h : G ⧸ F) = (h : G ⧸ F) ↔ x ∈ MulAction.stabilizer G (h : G ⧸ F) :=
      fun x => (MulAction.mem_stabilizer_iff).symm
    ext g
    show ({g • ((1 : G) : G ⧸ F), g • (h : G ⧸ F)} : Set (G ⧸ F)) = {((1 : G) : G ⧸ F), (h : G ⧸ F)}
      ↔ g ∈ ((F1 ⊔ Q : Subgroup G) : Set G)
    rw [Set.pair_eq_pair_iff, c1, c2, c3, c4]
    constructor
    · rintro (⟨hgF, hgs⟩ | ⟨hgh, hgh'⟩)
      · have : g ∈ F ⊓ MulAction.stabilizer G (h : G ⧸ F) := ⟨hgF, hgs⟩
        rw [hFδ] at this
        exact Subgroup.mem_sup_left this
      ·
        have hf : h⁻¹ * g ∈ F := by
          have := inv_mem hgh
          simpa using this
        have hfs : h⁻¹ * g ∈ MulAction.stabilizer G (h : G ⧸ F) := by
          rw [hstab, RuChoice.mem_conjugate]
          have e : h⁻¹ * (h⁻¹ * g) * h⁻¹⁻¹ = (h * h)⁻¹ * (g * h) := by group
          rw [e]
          exact mul_mem (inv_mem hh2F) hgh'
        have hf1 : h⁻¹ * g ∈ F1 := by
          have : h⁻¹ * g ∈ F ⊓ MulAction.stabilizer G (h : G ⧸ F) := ⟨hf, hfs⟩
          rwa [hFδ] at this
        have e : g = h * (h⁻¹ * g) := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_right hhQ) (Subgroup.mem_sup_left hf1)
    · intro hg
      have hg' : g ∈ ((Q : Subgroup G) : Set G) * (F1 : Set G) := by
        rw [← hset]
        exact hg
      obtain ⟨q, hq, f, hf, rfl⟩ := Set.mem_mul.mp hg'
      rcases hsq h hhQ hhF1 q hq with hqF | hqF
      · left
        have hqf : q * f ∈ F1 := mul_mem hqF hf
        refine ⟨hF1F hqf, ?_⟩
        have : q * f ∈ F ⊓ MulAction.stabilizer G (h : G ⧸ F) := by
          rw [hFδ]
          exact hqf
        exact this.2
      · right
        have hg1 : h⁻¹ * (q * f) ∈ F1 := by
          have e : h⁻¹ * (q * f) = (h⁻¹ * q) * f := by group
          rw [e]
          exact mul_mem hqF hf
        have hgF1 : (h⁻¹ * (q * f))  ∈ F ⊓ MulAction.stabilizer G (h : G ⧸ F) := by
          rw [hFδ]
          exact hg1
        refine ⟨?_, ?_⟩
        ·
          have e : (q * f)⁻¹ * h = (h⁻¹ * (q * f))⁻¹ := by group
          rw [e]
          exact inv_mem (hF1F hg1)
        ·
          have hs0 := hgF1.2
          rw [hstab] at hs0
          have hs := (RuChoice.mem_conjugate (A := F) (t := h⁻¹) (x := h⁻¹ * (q * f))).mp hs0
          have e : q * f * h = (h * h) * (h⁻¹⁻¹ ⁻¹ * (h⁻¹ * (q * f)) * h⁻¹⁻¹) := by group
          rw [e]
          exact mul_mem hh2F (by simpa using hs)

section

open CFSG.Quasithin.RuType in
private theorem burnsideJ10b_J53_of_M {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (φ : ↥(M.F1 ⊔ M.F2) ≃* CFSG.Sporadic.Schreier.Tits.titsA) {y : G}
    (hy : y ∈ (M.T : Subgroup G)) {F F1 : Subgroup G}
    (hF : F = CFSG.conjugate (M.F1 ⊔ M.F2) y) (hF1 : F1 = CFSG.conjugate M.F1 y) :
    ∃ δ : G ⧸ F, Nat.card ↥(MulAction.orbit ↥F δ) = 1755 ∧
      F ⊓ MulAction.stabilizer G δ = F1 ∧
      ChIJK.pairStab G ((1 : G) : G ⧸ F) δ =
        ((F1 ⊔ ChIJK.QRu (M.T : Subgroup G) : Subgroup G) : Set G) := by
  have hyH : y ∈ ruH M.T := M.toRuData.T_le_H hy
  have hQ : ∀ q ∈ ruQ M.T, y * q * y⁻¹ ∈ ruQ M.T := fun q hq => M.conj_mem_Q hyH hq
  have hQ' : ∀ q ∈ ruQ M.T, y⁻¹ * q * y ∈ ruQ M.T := fun q hq => by
    simpa using M.conj_mem_Q (inv_mem hyH) hq
  have hQfix : CFSG.conjugate (ruQ M.T) y = ruQ M.T :=
    RuChoice.conjugate_eq_self hQ hQ'
  rw [RuChoice.QRu_eq M]
  have hC := M.centralizer_Fd_F_eq_bot φ
  refine burnsideJ10b_J53_abstract F F1 (ruQ M.T) ?_ ?_ ?_ ?_ ?_
  ·
    rw [hF, hF1]
    exact RuChoice.fx_conjugate_mono y le_sup_left
  ·
    intro q hq f hf
    rw [hF1, RuChoice.mem_conjugate] at hf ⊢
    have h1 := M.Q_conj_mem_F1 (hQ q hq) hf
    have e : y * (q * f * q⁻¹) * y⁻¹ = (y * q * y⁻¹) * (y * f * y⁻¹) * (y * q * y⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  ·
    have hcard : Nat.card ↥(F1 ⊓ ruQ M.T) = 2 ^ 10 := by
      have : F1 ⊓ ruQ M.T = CFSG.conjugate (M.F1 ⊓ ruQ M.T) y := by
        rw [hF1, RuChoice.conjugate_inf, hQfix]
      rw [this, RuChoice.fx_card_conjugate, M.F1_inf_Q, M.card_Y]
    have h := Subgroup.card_mul_index ((F1 ⊓ ruQ M.T).subgroupOf (ruQ M.T))
    rw [card_subgroupOf_of_le inf_le_right, hcard, M.toRuData.card_Q] at h
    omega
  ·
    rw [hF, hF1, RuChoice.fx_card_conjugate, RuChoice.fx_card_conjugate, RuDataM.card_F_of φ,
      M.card_F1]
    norm_num
  ·
    intro h hh hhF1
    have hh' : y * h * y⁻¹ ∈ ruQ M.T := hQ h hh
    have hhF1' : y * h * y⁻¹ ∉ M.F1 := by
      intro hmem
      apply hhF1
      rw [hF1, RuChoice.mem_conjugate]
      exact hmem
    have hinf := M.inf_conj_eq_F1 φ hC hh' hhF1'
    have hmapeq : (M.F1 ⊔ M.F2).map (MulAut.conj (y * h * y⁻¹)).toMonoidHom =
        CFSG.conjugate (M.F1 ⊔ M.F2) (y * h * y⁻¹)⁻¹ := by
      unfold CFSG.conjugate
      rw [inv_inv]
    rw [hmapeq] at hinf
    have h2 := congrArg (fun A : Subgroup G => CFSG.conjugate A y) hinf
    simp only [RuChoice.conjugate_inf, RuChoice.fx_conjugate_conjugate] at h2
    have e : (y * h * y⁻¹)⁻¹ * y = y * h⁻¹ := by group
    rw [e] at h2
    rw [hF, hF1, RuChoice.fx_conjugate_conjugate]
    exact h2

end

noncomputable def burnsideJ10b_quotEquiv {G : Type} [Group G] (A : Subgroup G) (y : G) :
    G ⧸ CFSG.conjugate A y ≃ G ⧸ A where
  toFun := Quotient.map' (fun g => g * y⁻¹) (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have := (RuChoice.mem_conjugate (A := A) (t := y) (x := a⁻¹ * b)).mp h
    convert this using 1
    group)
  invFun := Quotient.map' (fun g => g * y) (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [RuChoice.mem_conjugate]
    convert h using 1
    group)
  left_inv := fun q => by
    induction q using Quotient.inductionOn' with
    | h g => simp
  right_inv := fun q => by
    induction q using Quotient.inductionOn' with
    | h g => simp

private theorem burnsideJ10b_quotEquiv_smul {G : Type} [Group G] (A : Subgroup G) (y : G) (g : G)
    (q : G ⧸ CFSG.conjugate A y) :
    burnsideJ10b_quotEquiv A y (g • q) = g • burnsideJ10b_quotEquiv A y q := by
  induction q using Quotient.inductionOn' with
  | h x =>
    show ((g * x * y⁻¹ : G) : G ⧸ A) = g • ((x * y⁻¹ : G) : G ⧸ A)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]

open MulAction CFSG.Quasithin.RuRank3 in
private theorem burnsideJ10b_rr3_of_equiv {G Ω Ω' : Type} [Group G] [MulAction G Ω] [MulAction G Ω']
    (e : Ω ≃ Ω') (he : ∀ (g : G) (x : Ω), e (g • x) = g • e x)
    (h : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω') :
    CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω := by
  have hst : ∀ x : Ω, stabilizer G (e x) = stabilizer G x := by
    intro x
    ext g
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← he, e.apply_eq_iff_eq]
  have hes : ∀ (g : G) (y : Ω'), e.symm (g • y) = g • e.symm y := fun g y => by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hsub : ∀ x : Ω, ∀ δ' : Ω', (stabilizer (stabilizer G (e x)) δ').map
      (MulEquiv.subgroupCongr (hst x)).toMonoidHom = stabilizer (stabilizer G x) (e.symm δ') := by
    intro x δ'
    ext s
    rw [Subgroup.mem_map_equiv, mem_stabilizer_iff, mem_stabilizer_iff]
    show ((s : G)) • δ' = δ' ↔ ((s : G)) • e.symm δ' = e.symm δ'
    rw [← e.symm.apply_eq_iff_eq, hes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun {a b} hab => ?_⟩
    refine h.faithful.eq_of_smul_eq_smul (fun p => ?_)
    obtain ⟨q, rfl⟩ := e.surjective p
    rw [← he, ← he, hab q]
  · exact h.nonempty.map e.symm
  · refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := h.transitive.exists_smul_eq (e x) (e y)
    exact ⟨g, e.injective (by rw [he, hg])⟩
  · intro x
    have h3 := h.rank_three (e x)
    rw [hst x] at h3
    rw [← h3]
    refine Nat.card_congr (Quotient.congr e (fun a b => ?_))
    show orbitRel (stabilizer G x) Ω a b ↔ orbitRel (stabilizer G x) Ω' (e a) (e b)
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [show (m : stabilizer G x) • e b = (m : G) • e b from rfl, ← he]; congr 1⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, e.injective (by
        rw [show (m : stabilizer G x) • b = (m : G) • b from rfl, he]
        exact hm)⟩
  · intro x
    obtain ⟨φ⟩ := h.twoF4 (e x)
    exact ⟨(MulEquiv.subgroupCongr (hst x).symm).trans φ⟩
  · intro x
    obtain ⟨δ', hc, hp⟩ := h.parabolic (e x)
    refine ⟨e.symm δ', ?_, ?_⟩
    · rw [← hsub x δ', Subgroup.card_map_of_injective (MulEquiv.subgroupCongr (hst x)).injective]
      exact hc
    · rw [← hsub x δ']
      exact hp.map_mulEquiv _
  · intro x
    obtain ⟨γ', hγ⟩ := h.l225 (e x)
    refine ⟨e.symm γ', ?_⟩
    rw [← hsub x γ']
    exact hγ.of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulEquiv.subgroupCongr (hst x)).injective)

private theorem burnsideJ10b_subgroupOf_eq {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf (MulAction.stabilizer G ω) =
      MulAction.stabilizer (MulAction.stabilizer G ω) δ := by
  ext f
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

noncomputable def burnsideJ10b_stabEquiv {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    MulAction.stabilizer (MulAction.stabilizer G ω) δ ≃*
      ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) :=
  (MulEquiv.subgroupCongr (burnsideJ10b_subgroupOf_eq ω δ)).symm.trans
    (Subgroup.subgroupOfEquivOfLe inf_le_left)

private theorem burnsideJ10b_exists_reeTitsModel :
    ∃ (Y0 : Type) (_ : Group Y0), CFSG.Blueprint.ReeTitsModel Y0 .Tits 2 1 := by
  refine ⟨CFSG.Blueprint.DerivedCentralQuotient
    (CFSG.Blueprint.reeFixedGroup CFSG.Blueprint.Chevalley.Tag.F4 (ZMod 2)
      CFSG.Blueprint.reeF4Perm
      fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)),
    inferInstance, ?_⟩
  refine ⟨⟨Nat.prime_two, le_refl _, rfl, rfl, rfl⟩, 0, rfl, ?_⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

section

private theorem burnsideJ10b_isTwoF4TwoGroup_of_titsA {Y : Type} [Group Y]
    (e : Nonempty (Y ≃* ↥CFSG.Sporadic.Schreier.Tits.titsA)) :
    ChIJK.IsTwoF4TwoGroup Y := by
  obtain ⟨Y0, _, hY0⟩ := burnsideJ10b_exists_reeTitsModel
  obtain ⟨e1⟩ := e
  obtain ⟨e2⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y0 2 1 hY0
  exact ⟨Y0, inferInstance, hY0,
    ⟨e1.trans (CFSG.Sporadic.Schreier.Tits.titsConjEquiv.trans (MulAut.congr e2.symm))⟩⟩

end

private theorem burnsideJ10b_isL225Plus_of_RT {Y : Type} [Group Y]
    (h : CFSG.Quasithin.RuRank3.IsL225Plus Y) : ChIJK.IsL225Plus Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨K, hK, hidx, ⟨e⟩, -, hS⟩ := h
  refine ⟨K, hK, hidx, ?_, ?_⟩
  · exact CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ 5 2
      (by norm_num) e
  · obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
    obtain ⟨e4⟩ := hS P
    exact ⟨P, 4, le_rfl, ⟨e4.symm⟩⟩

section

private theorem burnsideJ10b_ofRT {G Ω : Type} [Group G] [MulAction G Ω]
    (h : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω) : ChIJK.IsRudvalisRank3 G Ω := by
  refine ⟨h.nonempty, fun g hg => ?_, h.transitive, fun ω => ⟨h.rank_three ω, ?_, ?_, ?_⟩⟩
  · exact h.faithful.eq_of_smul_eq_smul (m₂ := 1) (fun a => by rw [hg a, one_smul])
  · exact burnsideJ10b_isTwoF4TwoGroup_of_titsA (h.twoF4 ω)
  · obtain ⟨δ, hc, hp⟩ := h.parabolic ω
    refine ⟨δ, ?_, ?_⟩
    · rw [burnsideJ10b_subgroupOf_eq]
      exact hp
    · rw [← Nat.card_congr (burnsideJ10b_stabEquiv ω δ).toEquiv]
      exact hc
  · obtain ⟨γ, hγ⟩ := h.l225 ω
    refine ⟨γ, burnsideJ10b_isL225Plus_of_RT ?_⟩
    exact CFSG.Quasithin.RuRank3.IsL225Plus.of_mulEquiv (burnsideJ10b_stabEquiv ω γ) hγ

end

open scoped MatrixGroups in
private theorem burnsideJ10b_card_mulAut_psl25 [Fact (Nat.Prime 5)] :
    Nat.card (MulAut PSL(2, GaloisField 5 2)) = 31200 := by
  have hKcard : Nat.card (GaloisField 5 2) = 5 ^ 2 := GaloisField.card 5 2 (by norm_num)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 5 2)) :=
    ⟨5, 2, Fact.out, by decide, by norm_num, hKcard⟩
  have h4 : 3 < Nat.card (GaloisField 5 2) := by rw [hKcard]; norm_num
  have hsurj :=
    CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective (GaloisField 5 2) hKcard hodd h4
  let eAut := CFSG.GorensteinWalter.pGammaL2EquivMulAutPSL2 (GaloisField 5 2) hodd h4 hsurj
  have h := CFSG.RankThree.PartOne.K159F.card_pGammaL2_two (p := 5)
  rw [Nat.card_congr eAut.toEquiv] at h
  rw [h]
  norm_num

open scoped MatrixGroups in
private theorem burnsideJ10b_card_psl25 [Fact (Nat.Prime 5)] : Nat.card PSL(2, GaloisField 5 2)
    = 7800 := by
  have := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := 5) (m := 2) (by norm_num)
    (by norm_num)
  rw [this]
  norm_num

open scoped MatrixGroups in
private theorem burnsideJ10b_psl25_perfect [Fact (Nat.Prime 5)] :
    Group.IsPerfect PSL(2, GaloisField 5 2) := by
  have hK : 4 ≤ Nat.card (GaloisField 5 2) := by
    rw [GaloisField.card 5 2 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup PSL(2, GaloisField 5 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  obtain ⟨a, b, hab⟩ := CFSG.Walter.psl2_exists_mul_ne_mul (GaloisField 5 2) hK
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator PSL(2, GaloisField 5 2)) with h | h
  · exfalso
    have hc : IsMulCommutative PSL(2, GaloisField 5 2) := (commutator_eq_bot_iff _).mp h
    exact hab (hc.is_comm.comm a b)
  · exact h

open scoped MatrixGroups in
private theorem burnsideJ10b_commutator_eq [Fact (Nat.Prime 5)] {G : Type*} [Group G] (F :
    Subgroup G)
    (K : Subgroup F) [K.Normal] (hidx : K.index = 2) (e : K ≃* PSL(2, GaloisField 5 2)) :
    ⁅F, F⁆ = K.map F.subtype := by
  haveI : Group.IsPerfect PSL(2, GaloisField 5 2) := burnsideJ10b_psl25_perfect
  haveI : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : commutator F = K := by
    apply le_antisymm
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : IsCyclic (F ⧸ K) := isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index, hidx])
      haveI : IsMulCommutative (F ⧸ K) := inferInstance
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp this
    · calc K = ⁅K, K⁆ := (Subgroup.commutator_eq_self).symm
        _ ≤ ⁅(⊤ : Subgroup F), ⊤⁆ := Subgroup.commutator_mono le_top le_top
  rw [← Subgroup.map_subtype_commutator, h1]

open scoped MatrixGroups in
private theorem burnsideJ10b_aut_core [Fact (Nat.Prime 5)] {G : Type*} [Group G] [Finite G]
    (S F K : Subgroup G) (hFS : F ≤ S) (hSn : ∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F)
    (hsq : ∀ s ∈ S, s ^ 2 ∈ F) (hcomm : K = ⁅F, F⁆) (e : K ≃* PSL(2, GaloisField 5 2))
    (hCK : ∀ f ∈ F, (∀ k ∈ K, f * k = k * f) → f = 1) (hS : 31200 ≤ Nat.card S)
    (hC : ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∀ P : Subgroup G, Nat.card P = 25 →
      ¬ P ≤ Subgroup.centralizer ({t} : Set G)) :
    Nonempty (↥S ≃* MulAut PSL(2, GaloisField 5 2)) := by
  have hKF : K ≤ F := hcomm ▸ Subgroup.commutator_le_self F
  have hKS : K ≤ S := hKF.trans hFS
  have hKn : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
    intro s hs k hk
    have h2 : F.map (MulAut.conj s).toMonoidHom ≤ F := by
      rintro _ ⟨f, hf, rfl⟩
      simpa [MulAut.conj_apply] using hSn s hs f hf
    have hmap : ⁅F, F⁆.map (MulAut.conj s).toMonoidHom ≤ ⁅F, F⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono h2 h2
    rw [hcomm] at hk ⊢
    have := hmap ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using this
  let Y : Subgroup ↥S := K.subgroupOf S
  haveI hYn : Y.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKn g g.2 n hn⟩
  have hKcard : Nat.card K = 7800 := by
    rw [Nat.card_congr e.toEquiv]
    exact burnsideJ10b_card_psl25
  obtain ⟨P0, hP0⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 5 (n := 2) (by
    rw [hKcard]
    norm_num)
  have hP : Nat.card (P0.map K.subtype) = 25 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hP0]
    norm_num
  have hPK : P0.map K.subtype ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hYC : Subgroup.centralizer (Y : Set ↥S) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_centralizer_iff] at hs
    have hcs : ∀ k ∈ K, (k : G) * s = s * k := fun k hk => by
      have := hs ⟨k, hKS hk⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hk)
      exact congrArg Subtype.val this
    have hs2 : (s : G) ^ 2 = 1 := by
      refine hCK _ (hsq s s.2) fun k hk => ?_
      rw [pow_two, mul_assoc, ← hcs k hk, ← mul_assoc, ← hcs k hk, mul_assoc]
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hC (s : G) hs2 (fun h => hne (Subtype.ext h)) _ hP fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcs x (hPK hx)).symm ▸ rfl
  let eY : ↥Y ≃* PSL(2, GaloisField 5 2) := (Subgroup.subgroupOfEquivOfLe hKS).trans e
  have hAut : Nat.card (MulAut ↥Y) = 31200 := by
    rw [Nat.card_congr (MulAut.congr eY).toEquiv]
    exact burnsideJ10b_card_mulAut_psl25
  haveI : Finite (MulAut ↥Y) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  exact ⟨(CFSG.Sporadic.Recognition.LyonsSims.conjNormalEquiv Y hYC (by rw [hAut]; exact hS)).trans
    (MulAut.congr eY)⟩

section

open CFSG.Quasithin.RuType in
private theorem burnsideJ10b_no_involution_centralizes {G : Type} [Group G] [Finite G] (M :
    RuDataM G)
    (t : G) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (P : Subgroup G) (hP : Nat.card P = 25) :
    ¬ P ≤ Subgroup.centralizer ({t} : Set G) := by
  intro hPle
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  rcases (M.lemma_J27_4 hs hs1).2 t ht2 ht1 with hz | hs'
  · have h := M.card_le_five_of_isPGroup hz hPle hP5
    omega
  · obtain ⟨c, hc⟩ := isConj_iff.mp hs'
    obtain ⟨⟨-, hinf, hsup, hcomm⟩, -, -⟩ := M.lemma_J29 hs hs1
    have hmap : P.map (MulAut.conj c⁻¹).toMonoidHom ≤ Cen s := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_Cen]
      have hxt := Subgroup.mem_centralizer_singleton_iff.mp (hPle hx)
      rw [← hc] at hxt
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc c⁻¹ * x * c * s = c⁻¹ * (x * (c * s * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * s * c⁻¹) * x) * c := by rw [hxt]
        _ = s * (c⁻¹ * x * c) := by group
    have hdvd : 25 ∣ Nat.card (Cen s) := by
      have := Subgroup.card_dvd_of_le hmap
      rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hP] at this
    have hcen : Nat.card (Cen s) = 4 * 29120 := by
      have hN : M.S0 ≤ Subgroup.normalizer ((Ls s : Subgroup G) : Set G) := fun x hx =>
        Subgroup.centralizer_le_normalizer (Ls s : Set G)
          (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
      have h := card_sup_mul_inf_of_normalizes hN
      rw [hsup, hinf, Subgroup.card_bot, mul_one, M.card_S0, M.card_Ls hs hs1] at h
      exact h
    rw [hcen] at hdvd
    norm_num at hdvd

end

private theorem burnsideJ10b_exists_pairStab_subgroup {G Ω : Type} [Group G] [MulAction G Ω] (α
    β : Ω) :
    ∃ S : Subgroup G, (S : Set G) = ChIJK.pairStab G α β ∧
      ∀ s : G, s ∈ S ↔ (s • α = α ∧ s • β = β) ∨ (s • α = β ∧ s • β = α) := by
  have key : ∀ s : G, s ∈ ChIJK.pairStab G α β ↔
      (s • α = α ∧ s • β = β) ∨ (s • α = β ∧ s • β = α) := fun s => by
    show ({s • α, s • β} : Set Ω) = {α, β} ↔ _
    exact Set.pair_eq_pair_iff
  refine ⟨{ carrier := ChIJK.pairStab G α β, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ },
    rfl, key⟩
  · intro s t hs ht
    rw [key] at hs ht ⊢
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ht with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp [mul_smul, h1, h2, h3, h4]
  · rw [key]
    simp
  · intro s hs
    rw [key] at hs ⊢
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨inv_smul_eq_iff.mpr h1.symm, inv_smul_eq_iff.mpr h2.symm⟩
    · right
      exact ⟨inv_smul_eq_iff.mpr h2.symm, inv_smul_eq_iff.mpr h1.symm⟩

open scoped MatrixGroups in
private theorem burnsideJ10b_card_isL225Plus [Fact (Nat.Prime 5)] {Y : Type*} [Group Y]
    (h : CFSG.Quasithin.RuRank3.IsL225Plus Y) : Nat.card Y = 15600 := by
  obtain ⟨K, -, hidx, ⟨e⟩, -, -⟩ := h
  have hK : Nat.card K = 7800 := by
    rw [Nat.card_congr e.toEquiv]
    exact burnsideJ10b_card_psl25
  have := Subgroup.card_mul_index K
  rw [hK, hidx] at this
  omega

private theorem burnsideJ10b_eq_of_card_three {α : Type*} [Finite α] (hc : Nat.card α = 3) {a b
    c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) : x = a ∨ x = b ∨ x = c := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hxa, hxb, hxc⟩ := hcon
  haveI := Fintype.ofFinite α
  have h4 : ({a, b, c, x} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hxc.symm
    · simp [hbc, hxb.symm]
    · simp [hab, hac, hxa.symm]
  have h5 := Finset.card_le_univ ({a, b, c, x} : Finset α)
  rw [h4, ← Nat.card_eq_fintype_card, hc] at h5
  omega

open scoped MatrixGroups in
open CFSG.Quasithin.RuRank3 MulAction in
private theorem burnsideJ10b_J54_abstract [Fact (Nat.Prime 5)] {G Ω : Type} [Group G] [Finite G]
    [MulAction G Ω] (hrt : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω) (ω δ : Ω) {F : Subgroup G}
    (hF : stabilizer G ω = F)
    (hFcard : Nat.card F = 35942400) (hδ : Nat.card ↥(orbit ↥F δ) = 1755)
    (hC : ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∀ P : Subgroup G, Nat.card P = 25 →
      ¬ P ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ γ : Ω, ((Set.univ : Set Ω) = {ω} ∪ orbit ↥F δ ∪ orbit ↥F γ ∧
        Nat.card ↥(orbit ↥F γ) = 2304 ∧ ChIJK.IsL225Plus ↥(F ⊓ stabilizer G γ)) ∧
      ∃ S : Subgroup G, (S : Set G) = ChIJK.pairStab G ω γ ∧
        Nonempty (↥S ≃* MulAut PSL(2, GaloisField 5 2)) := by
  subst hF
  obtain ⟨γ, hγ⟩ := hrt.l225 ω
  have hγcard : Nat.card ↥(stabilizer ↥(stabilizer G ω) γ) = 15600 :=
    burnsideJ10b_card_isL225Plus hγ
  have horb : ∀ z : Ω, Nat.card ↥(orbit ↥(stabilizer G ω) z) *
      Nat.card ↥(stabilizer ↥(stabilizer G ω) z) = 35942400 := by
    intro z
    rw [Nat.card_coe_set_eq, ← index_stabilizer, mul_comm, Subgroup.card_mul_index, hFcard]
  have hγorb : Nat.card ↥(orbit ↥(stabilizer G ω) γ) = 2304 := by
    have := horb γ
    rw [hγcard] at this
    omega
  have horbω : orbit ↥(stabilizer G ω) ω = {ω} := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      exact mem_stabilizer_iff.mp f.2
    · rintro rfl
      exact mem_orbit_self _
  have hcardω : Nat.card ↥(orbit ↥(stabilizer G ω) ω) = 1 := by
    rw [horbω]
    simp
  have hne : ∀ x y : Ω, Nat.card ↥(orbit ↥(stabilizer G ω) x) ≠
      Nat.card ↥(orbit ↥(stabilizer G ω) y) →
      Quotient.mk (orbitRel ↥(stabilizer G ω) Ω) x ≠
        Quotient.mk (orbitRel ↥(stabilizer G ω) Ω) y := by
    intro x y hxy hq
    apply hxy
    have h : orbitRel ↥(stabilizer G ω) Ω x y := Quotient.exact hq
    rw [orbitRel_apply] at h
    rw [orbit_eq_iff.mpr h]
  have hq3 := hrt.rank_three ω
  haveI : Finite (orbitRel.Quotient ↥(stabilizer G ω) Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hq3]; norm_num)
  have hcover : ∀ x : Ω, x ∈ orbit ↥(stabilizer G ω) ω ∨ x ∈ orbit ↥(stabilizer G ω) δ ∨
      x ∈ orbit ↥(stabilizer G ω) γ := by
    intro x
    have h := burnsideJ10b_eq_of_card_three hq3
      (hne ω δ (by rw [hcardω, hδ]; norm_num)) (hne ω γ (by rw [hcardω, hγorb]; norm_num))
      (hne δ γ (by rw [hδ, hγorb]; norm_num)) (Quotient.mk (orbitRel ↥(stabilizer G ω) Ω) x)
    rcases h with h | h | h
    · left
      have h' : orbitRel ↥(stabilizer G ω) Ω x ω := Quotient.exact h
      rwa [orbitRel_apply] at h'
    · right; left
      have h' : orbitRel ↥(stabilizer G ω) Ω x δ := Quotient.exact h
      rwa [orbitRel_apply] at h'
    · right; right
      have h' : orbitRel ↥(stabilizer G ω) Ω x γ := Quotient.exact h
      rwa [orbitRel_apply] at h'
  have hswap : ∃ c : G, c • ω = γ ∧ c • γ = ω := by
    haveI := hrt.transitive
    refine CFSG.Quasithin.RuRank3.exists_smul_swap (fun z hz => ?_)
    rcases hcover z with h | h | h
    · exfalso
      have h1 := horb z
      rw [orbit_eq_iff.mpr h, hcardω, hz, hγcard] at h1
      omega
    · exfalso
      have h1 := horb z
      rw [orbit_eq_iff.mpr h, hδ, hz, hγcard] at h1
      omega
    · exact h
  have hL : CFSG.Quasithin.RuRank3.IsL225Plus ↥(stabilizer G ω ⊓ stabilizer G γ) :=
    CFSG.Quasithin.RuRank3.IsL225Plus.of_mulEquiv (burnsideJ10b_stabEquiv ω γ) hγ
  obtain ⟨S, hSset, hSmem⟩ := burnsideJ10b_exists_pairStab_subgroup (G := G) ω γ
  refine ⟨γ, ⟨?_, hγorb, burnsideJ10b_isL225Plus_of_RT hL⟩, S, hSset, ?_⟩
  · symm
    refine Set.eq_univ_of_forall fun x => ?_
    rcases hcover x with h | h | h
    · rw [horbω] at h
      exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · have hωγ : ω ≠ γ := fun h =>
      hne ω γ (by rw [hcardω, hγorb]; norm_num) (by rw [h])
    have hFγcard : Nat.card ↥(stabilizer G ω ⊓ stabilizer G γ) = 15600 :=
      burnsideJ10b_card_isL225Plus hL
    set Fγ : Subgroup G := stabilizer G ω ⊓ stabilizer G γ with hFγ
    obtain ⟨K, hKn, hidx, ⟨e⟩, hCK, -⟩ := hL
    haveI := hKn
    obtain ⟨c, hcω, hcγ⟩ := hswap
    have hfixmem : ∀ f, f ∈ Fγ ↔ f • ω = ω ∧ f • γ = γ := fun f => by
      rw [hFγ, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff]
    have hFS : Fγ ≤ S := fun f hf => (hSmem f).mpr (Or.inl ((hfixmem f).mp hf))
    have hcS : c ∈ S := (hSmem c).mpr (Or.inr ⟨hcω, hcγ⟩)
    have hSpair : ∀ s ∈ S, ∀ z, (z = ω ∨ z = γ) → (s • z = ω ∨ s • z = γ) := by
      intro s hs z hz
      rcases (hSmem s).mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with hz | hz <;> rw [hz] <;>
        simp [h1, h2]
    have hSn : ∀ s ∈ S, ∀ f ∈ Fγ, s * f * s⁻¹ ∈ Fγ := by
      intro s hs f hf
      have hs' : s⁻¹ ∈ S := S.inv_mem hs
      rw [hfixmem] at hf ⊢
      obtain ⟨hfω, hfγ⟩ := hf
      have hf' : ∀ z, (z = ω ∨ z = γ) → f • z = z := by
        intro z hz
        rcases hz with hz | hz <;> rw [hz] <;> assumption
      constructor
      · have hu : f • (s⁻¹ • ω) = s⁻¹ • ω := hf' _ (hSpair s⁻¹ hs' ω (Or.inl rfl))
        rw [mul_smul, mul_smul, hu, smul_inv_smul]
      · have hu : f • (s⁻¹ • γ) = s⁻¹ • γ := hf' _ (hSpair s⁻¹ hs' γ (Or.inr rfl))
        rw [mul_smul, mul_smul, hu, smul_inv_smul]
    have hsq : ∀ s ∈ S, s ^ 2 ∈ Fγ := by
      intro s hs
      rw [hfixmem, pow_two, mul_smul, mul_smul]
      rcases (hSmem s).mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    have hS : 31200 ≤ Nat.card S := by
      have h1 := Subgroup.card_mul_index (Fγ.subgroupOf S)
      have h2 : Nat.card (Fγ.subgroupOf S) = Nat.card Fγ :=
        CFSG.Quasithin.RuType.card_subgroupOf_of_le hFS
      have h3 : (Fγ.subgroupOf S).index ≠ 1 := by
        intro h
        rw [Subgroup.index_eq_one] at h
        have hmem : (⟨c, hcS⟩ : ↥S) ∈ Fγ.subgroupOf S := by
          rw [h]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf, hfixmem] at hmem
        exact hωγ (hcω.symm.trans hmem.1).symm
      have h4 : (Fγ.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rw [h2, hFγcard] at h1
      omega
    have hKcomm : K.map Fγ.subtype = ⁅Fγ, Fγ⁆ := (burnsideJ10b_commutator_eq Fγ K hidx e).symm
    have hCK' : ∀ f ∈ Fγ, (∀ k ∈ K.map Fγ.subtype, f * k = k * f) → f = 1 := by
      intro f hf hcomm
      have hmem : (⟨f, hf⟩ : ↥Fγ) ∈ Subgroup.centralizer (K : Set ↥Fγ) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact Subtype.ext (hcomm (k : G) ⟨k, hk, rfl⟩).symm
      rw [hCK, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    exact burnsideJ10b_aut_core S Fγ (K.map Fγ.subtype) hFS hSn hsq hKcomm
      ((Subgroup.equivMapOfInjective K Fγ.subtype Fγ.subtype_injective).symm.trans e) hCK' hS hC

section

open CFSG.Quasithin.RuType in
open scoped MatrixGroups in
private theorem burnsideJ10b_J54_of_M [Fact (Nat.Prime 5)] {G : Type} [Group G] [Finite G] (M :
    RuDataM G)
    (φ : ↥(M.F1 ⊔ M.F2) ≃* CFSG.Sporadic.Schreier.Tits.titsA) {F : Subgroup G} {y : G}
    (hF : F = CFSG.conjugate (M.F1 ⊔ M.F2) y) (δ : G ⧸ F)
    (hδ : Nat.card ↥(MulAction.orbit ↥F δ) = 1755) :
    (∃ γ : G ⧸ F, ((Set.univ : Set (G ⧸ F)) =
          {((1 : G) : G ⧸ F)} ∪ MulAction.orbit ↥F δ ∪ MulAction.orbit ↥F γ ∧
        Nat.card ↥(MulAction.orbit ↥F γ) = 2304 ∧
        ChIJK.IsL225Plus ↥(F ⊓ MulAction.stabilizer G γ)) ∧
      ∃ S : Subgroup G, (S : Set G) = ChIJK.pairStab G ((1 : G) : G ⧸ F) γ ∧
        Nonempty (↥S ≃* MulAut PSL(2, GaloisField 5 2))) ∧
    ChIJK.IsRudvalisRank3 G (G ⧸ F) := by
  subst hF
  have hrt0 := M.isRudvalisRank3 φ
  have hrt : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G (G ⧸ CFSG.conjugate (M.F1 ⊔ M.F2) y) :=
    burnsideJ10b_rr3_of_equiv (burnsideJ10b_quotEquiv (M.F1 ⊔ M.F2) y)
      (burnsideJ10b_quotEquiv_smul (M.F1 ⊔ M.F2) y) hrt0
  have hFcard : Nat.card ↥(CFSG.conjugate (M.F1 ⊔ M.F2) y) = 35942400 := by
    rw [RuChoice.fx_card_conjugate, RuDataM.card_F_of φ]
  have hω : MulAction.stabilizer G ((1 : G) : G ⧸ CFSG.conjugate (M.F1 ⊔ M.F2) y) =
      CFSG.conjugate (M.F1 ⊔ M.F2) y := MulAction.stabilizer_quotient _
  exact ⟨burnsideJ10b_J54_abstract hrt _ δ hω hFcard hδ
    (fun t ht2 ht1 P hP => burnsideJ10b_no_involution_centralizes M t ht2 ht1 P hP),
    burnsideJ10b_ofRT hrt⟩

end

end BurnsideJ10b

section

theorem as_J_5_2 : J_5_2 := by
  intro G _ _ L V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv X hX a ha hA hQ
  obtain ⟨M, y, -, -, -, -, -, -, -, -, -, -, -, hF⟩ :=
    RuChoice.reduce h hV2 hg hgH hv hvQ hB5 hinv hX ha hA hQ
  obtain ⟨φ⟩ := M.theorem_J47 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
    CFSG.Quasithin.H13.F45Ru.f45TwoF4 CFSG.Quasithin.H13.TwoF4F48.f48TwoF4
  refine ⟨?_, by norm_num⟩
  rw [hF, burnsideJ10b_card_quotient_conjugate, M.card_quotient_F φ]
  norm_num

end

@[expose] def J_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        ∃ δ : G ⧸ FRu L V V2 T a B5 X,
          Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) δ) = 1755 ∧
          FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G δ = F1Ru L V V2 T a B5 ∧
          pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) δ =
            ((F1Ru L V V2 T a B5 ⊔ QRu T : Subgroup G) : Set G)

section

open CFSG.Quasithin.RuType in
theorem as_J_5_3 : J_5_3 := by
  intro G _ _ L V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv X hX a ha hA hQ
  obtain ⟨M, y, hML, hMT, hy, -, -, -, -, -, -, hF1, -, hF⟩ :=
    RuChoice.reduce h hV2 hg hgH hv hvQ hB5 hinv hX ha hA hQ
  obtain ⟨φ⟩ := M.theorem_J47 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
    CFSG.Quasithin.H13.F45Ru.f45TwoF4 CFSG.Quasithin.H13.TwoF4F48.f48TwoF4
  subst hML
  subst hMT
  have hV : V = ruV M.L := h.V_eq_ruV
  subst hV
  exact burnsideJ10b_J53_of_M M φ hy hF hF1

end

@[expose] def J_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
      ∀ δ : G ⧸ FRu L V V2 T a B5 X,
        Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) δ) = 1755 →
        FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G δ = F1Ru L V V2 T a B5 →
        pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) δ =
          ((F1Ru L V V2 T a B5 ⊔ QRu T : Subgroup G) : Set G) →
        (∃ γ : G ⧸ FRu L V V2 T a B5 X,
          ((Set.univ : Set (G ⧸ FRu L V V2 T a B5 X)) =
              {((1 : G) : G ⧸ FRu L V V2 T a B5 X)} ∪ MulAction.orbit ↥(FRu L V V2 T a B5 X) δ ∪
                MulAction.orbit ↥(FRu L V V2 T a B5 X) γ ∧
            Nat.card ↥(MulAction.orbit ↥(FRu L V V2 T a B5 X) γ) = 2304 ∧
            IsL225Plus ↥(FRu L V V2 T a B5 X ⊓ MulAction.stabilizer G γ)) ∧
          ∃ S : Subgroup G,
            (S : Set G) = pairStab G ((1 : G) : G ⧸ FRu L V V2 T a B5 X) γ ∧
              Nonempty (↥S ≃* MulAut PSL(2, GaloisField 5 2))) ∧
        IsRudvalisRank3 G (G ⧸ FRu L V V2 T a B5 X)

section

theorem as_J_5_4 : J_5_4 := by
  intro G _ _ L V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv X hX a ha hA hQ δ hδc _ _
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨M, y, -, -, -, -, -, -, -, -, -, -, -, hF⟩ :=
    RuChoice.reduce h hV2 hg hgH hv hvQ hB5 hinv hX ha hA hQ
  obtain ⟨φ⟩ := M.theorem_J47 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
    CFSG.Quasithin.H13.F45Ru.f45TwoF4 CFSG.Quasithin.H13.TwoF4F48.f48TwoF4
  exact burnsideJ10b_J54_of_M M φ hF δ hδc

end

@[expose] def J_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω),
    RudvalisSetting G Ω ω δ γ →
      ((DeltaAt G ω δ ω).ncard = 1755 ∧ (SigmaAt G ω γ ω).ncard = 2304 ∧
        (∀ ρ ∈ DeltaAt G ω δ ω, (DeltaAt G ω δ ω ∩ DeltaAt G ω δ ρ).ncard = 730) ∧
        (∀ ρ ∈ SigmaAt G ω γ ω, (DeltaAt G ω δ ω ∩ DeltaAt G ω δ ρ).ncard = 780)) ∧
      (∃ (T' M2 : Subgroup ↥(MulAction.stabilizer G ω)),
        CFSG.Quasithin.IsYAmalgamPair T'
          ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
            (MulAction.stabilizer G ω)) M2 ∧
        ∃ φ : Ω → ↥(MulAction.stabilizer G ω) ⧸
            (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω),
          Set.BijOn φ (DeltaAt G ω δ ω) Set.univ ∧
          (∀ f : ↥(MulAction.stabilizer G ω), ∀ ρ ∈ DeltaAt G ω δ ω, φ (f • ρ) = f • φ ρ) ∧
          φ δ = ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸
            (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω)) ∧
          ∀ ρ ∈ DeltaAt G ω δ ω, (ρ ∈ DeltaAt G ω δ δ ↔
            (0 < (incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
                (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) ∧
              (incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
                (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) < 8))) ∧
      (∃ a ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ, ∃ b ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        ∃ c ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ =
          MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a ∪
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b ∪
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a).ncard = 10 ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b).ncard = 80 ∧
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c).ncard = 640 ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b) ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c) ∧
        Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b)
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c)) ∧
      ((DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ).ncard = 780 ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ, ∀ τ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        (DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ).ncard = 975 ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ, ∀ τ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        (∀ σ ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ γ,
          Nonempty (↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
            MulAction.stabilizer G σ) ≃* Sz 0)) ∧
        (∀ τ ∈ DeltaAt G ω δ ω ∩ SigmaAt G ω γ γ,
          IsSylowTwoIn (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
            MulAction.stabilizer G τ) (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ))) ∧
      ((DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω).ncard = 975 ∧
        (∀ σ ∈ DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω, ∀ τ ∈ DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
        ∀ ρ ∈ SigmaAt G ω γ ω,
          (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ).ncard = 975 →
            MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ =
              DeltaAt G ω δ γ ∩ SigmaAt G ω γ ω)

section BurnsideJ55

private theorem burnsideJ55_perm_inv_apply {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

private theorem burnsideJ55_perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

section ModelE

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP genSubgroup)

@[expose] def burnsideJ55_E0 : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruR0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 4060)) ruG0F

private theorem burnsideJ55_mem_E0 {p : Equiv.Perm (Fin 4060)} :
    p ∈ burnsideJ55_E0 ↔ p ∈ ruR0 ∧ p ruG0F = ruG0F := by
  unfold burnsideJ55_E0
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

section

private theorem burnsideJ55_ruEGen_mem_stab {i : ℕ} (hi : i < 2) :
    ruEGen i ∈ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (0 : Fin 4060) := by
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact ruEGen_zero hi

end

section

private theorem burnsideJ55_genE_le :
    genSubgroup 4060 ruEGArrs.size ruEGen ≤ burnsideJ55_E0 := by
  rw [genSubgroup, ruEGArrs_size, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact burnsideJ55_mem_E0.2
    ⟨Subgroup.mem_inf.2 ⟨ruEGen_mem hi, burnsideJ55_ruEGen_mem_stab hi⟩, ruEGen_g0 hi⟩

private theorem burnsideJ55_E0_trans
    {y z : Fin 4060} (h : ruELab[(y : ℕ)]! = ruELab[(z : ℕ)]!) :
    ∃ p ∈ burnsideJ55_E0, p y = z := by
  have hor := orbit_eq_labels ruEGArrs_rep ruStabs_check.2.2.2.2.1 y
  have hz : z ∈ MulAction.orbit (genSubgroup 4060 ruEGArrs.size ruEGen) y := by
    rw [hor]
    exact h.symm
  obtain ⟨⟨g, hg⟩, rfl⟩ := hz
  exact ⟨g, burnsideJ55_genE_le hg, rfl⟩

end

section

private theorem burnsideJ55_ELab2_iff (x : Fin 4060) :
    ruELab[(x : ℕ)]! = 2 ↔ (x ∈ Set.range ruB ∧ ruAdj ruG0F x) := by
  have h := allLt_spec ruE0Cls_check.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h, ruInD, beq_iff_eq, ← mem_range_ruB_iff, ruRowA_g0]

private theorem burnsideJ55_ELab1_iff (x : Fin 4060) :
    ruELab[(x : ℕ)]! = 1 ↔ (x ∈ Set.range ruB ∧ ¬ ruAdj ruG0F x) := by
  have h := allLt_spec ruE0Cls_check.2.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h, ruInD, beq_iff_eq, ← mem_range_ruB_iff, ← ruRowA_g0]
  simp

private theorem burnsideJ55_ELab3_iff (x : Fin 4060) :
    ruELab[(x : ℕ)]! = 3 ↔ (x ∈ ruS ∧ ruAdj ruG0F x) := by
  have h := allLt_spec ruE0Cls_check.2.2.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h, ruInS_iff, ruRowA_g0]

end

private theorem burnsideJ55_adj_conj {p : Equiv.Perm (Fin 4060)} (hp : p ∈ ruR0) (x y : Fin 4060) :
    ruAdj (p x) (p y) ↔ ruAdj x y :=
  ruAdj_apply (ruR0_le_ruP hp) x y

section

private theorem burnsideJ55_trans_780 {s : Fin 4060} (hs : s ∈ ruS)
    {y z : Fin 4060} (hy0 : ruAdj 0 y) (hys : ruAdj s y) (hz0 : ruAdj 0 z) (hzs : ruAdj s z) :
    ∃ p ∈ ruR0, p s = s ∧ p y = z := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := exists_ruR0_g0 hs
  have hinv : p₀⁻¹ ∈ ruR0 := inv_mem hp₀
  have hps : p₀⁻¹ s = ruG0F := by rw [← hp₀g, burnsideJ55_perm_inv_apply]
  have key : ∀ w, ruAdj 0 w → ruAdj s w → ruELab[((p₀⁻¹ w : Fin 4060) : ℕ)]! = 2 := by
    intro w hw0 hws
    refine (burnsideJ55_ELab2_iff _).2 ⟨?_, ?_⟩
    · rw [ruR0_mem_range_ruB_iff hinv]
      exact (ruAdj_zero_iff w).1 hw0
    · rw [← hps]
      exact (burnsideJ55_adj_conj hinv s w).2 hws
  obtain ⟨e, he, hey⟩ := burnsideJ55_E0_trans ((key y hy0 hys).trans (key z hz0 hzs).symm)
  obtain ⟨heR, heg⟩ := burnsideJ55_mem_E0.1 he
  refine ⟨p₀ * e * p₀⁻¹, mul_mem (mul_mem hp₀ heR) hinv, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hps, heg, hp₀g]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hey, burnsideJ55_perm_apply_inv]

private theorem burnsideJ55_trans_D975 {s : Fin 4060} (hs : s ∈ ruS)
    {y z : Fin 4060} (hy0 : ruAdj 0 y) (hys : ¬ ruAdj s y) (hz0 : ruAdj 0 z) (hzs : ¬ ruAdj s z) :
    ∃ p ∈ ruR0, p s = s ∧ p y = z := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := exists_ruR0_g0 hs
  have hinv : p₀⁻¹ ∈ ruR0 := inv_mem hp₀
  have hps : p₀⁻¹ s = ruG0F := by rw [← hp₀g, burnsideJ55_perm_inv_apply]
  have key : ∀ w, ruAdj 0 w → ¬ ruAdj s w → ruELab[((p₀⁻¹ w : Fin 4060) : ℕ)]! = 1 := by
    intro w hw0 hws
    refine (burnsideJ55_ELab1_iff _).2 ⟨?_, ?_⟩
    · rw [ruR0_mem_range_ruB_iff hinv]
      exact (ruAdj_zero_iff w).1 hw0
    · rw [← hps]
      exact fun h => hws ((burnsideJ55_adj_conj hinv s w).1 h)
  obtain ⟨e, he, hey⟩ := burnsideJ55_E0_trans ((key y hy0 hys).trans (key z hz0 hzs).symm)
  obtain ⟨heR, heg⟩ := burnsideJ55_mem_E0.1 he
  refine ⟨p₀ * e * p₀⁻¹, mul_mem (mul_mem hp₀ heR) hinv, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hps, heg, hp₀g]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hey, burnsideJ55_perm_apply_inv]

private theorem burnsideJ55_trans_S975 {s : Fin 4060} (hs : s ∈ ruS)
    {y z : Fin 4060} (hy0 : y ∈ ruS) (hys : ruAdj s y) (hz0 : z ∈ ruS) (hzs : ruAdj s z) :
    ∃ p ∈ ruR0, p s = s ∧ p y = z := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := exists_ruR0_g0 hs
  have hinv : p₀⁻¹ ∈ ruR0 := inv_mem hp₀
  have hps : p₀⁻¹ s = ruG0F := by rw [← hp₀g, burnsideJ55_perm_inv_apply]
  have key : ∀ w, w ∈ ruS → ruAdj s w → ruELab[((p₀⁻¹ w : Fin 4060) : ℕ)]! = 3 := by
    intro w hw0 hws
    refine (burnsideJ55_ELab3_iff _).2 ⟨?_, ?_⟩
    · exact (ruR0_mem_ruS_iff hinv w).2 hw0
    · rw [← hps]
      exact (burnsideJ55_adj_conj hinv s w).2 hws
  obtain ⟨e, he, hey⟩ := burnsideJ55_E0_trans ((key y hy0 hys).trans (key z hz0 hzs).symm)
  obtain ⟨heR, heg⟩ := burnsideJ55_mem_E0.1 he
  refine ⟨p₀ * e * p₀⁻¹, mul_mem (mul_mem hp₀ heR) hinv, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hps, heg, hp₀g]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hey, burnsideJ55_perm_apply_inv]

end

section

private theorem burnsideJ55_ruEGen_mem_E0 {k : ℕ} (hk : k < 2) : ruEGen k ∈ burnsideJ55_E0 :=
  burnsideJ55_mem_E0.2 ⟨Subgroup.mem_inf.2 ⟨ruEGen_mem hk, burnsideJ55_ruEGen_mem_stab hk⟩,
    ruEGen_g0 hk⟩

end

section

private theorem burnsideJ55_E0_invariant_975 {T : Set (Fin 4060)}
    (hinv : ∀ q ∈ burnsideJ55_E0, ∀ x, q x ∈ T ↔ x ∈ T) (hS : ∀ x ∈ T, x ∈ ruS)
    (hcard : T.ncard = 975) : ∀ x, x ∈ T ↔ (x ∈ ruS ∧ ruAdj ruG0F x) := by
  have hTinv : ∀ k < ruEGArrs.size, ∀ x, ruEGen k x ∈ T ↔ x ∈ T := by
    intro k hk x
    rw [ruEGArrs_size] at hk
    exact hinv _ (burnsideJ55_ruEGen_mem_E0 hk) x
  have hm : ∀ x : Fin 4060, ruELab[(x : ℕ)]! < 9 := fun x => by
    have := allLt_spec ruStabs_check.2.2.2.2.2 x.2
    simpa using this
  obtain ⟨b, hb⟩ := exists_bool_of_invariant (lab := ruELab) (orbLab_eq _ _) ruEGArrs_rep
    ruStabs_check.2.2.2.2.1 hm hTinv
  have hsel : selCount 4060 ruELab b = 975 := by rw [← ncard_eq_selCount hb, hcard]
  have hTS : ∀ x : Fin 4060, bAt b ruELab[(x : ℕ)]! = true → ruInS (x : ℕ) = true := by
    intro x hx
    rw [ruInS_iff]
    exact hS x ((hb x).2 hx)
  have hcond : (allLt 4060 fun x => !(bAt b ruELab[x]!) || ruInS x) = true := by
    rw [allLt_iff]
    intro x hx
    have := hTS ⟨x, hx⟩
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hbx : bAt b ruELab[x]! = true
    · exact Or.inr (this hbx)
    · exact Or.inl (by simpa using hbx)
  have hres := ruE0Cls_check.2.2.2.2 b hsel hcond
  intro x
  rw [hb x, ← burnsideJ55_ELab3_iff]
  have := allLt_spec hres x.2
  rw [beq_iff_eq] at this
  rw [this, beq_iff_eq]

end

@[expose] def burnsideJ55_orbSet (s y : Fin 4060) : Set (Fin 4060) :=
  {z | ∃ p ∈ ruR0, p s = s ∧ p y = z}

private theorem burnsideJ55_orbSet_invariant {s y : Fin 4060} {q : Equiv.Perm (Fin 4060)} (hq :
    q ∈ ruR0)
    (hqs : q s = s) (z : Fin 4060) : q z ∈ burnsideJ55_orbSet s y ↔ z ∈ burnsideJ55_orbSet s y := by
  constructor
  · rintro ⟨p, hp, hps', hpy⟩
    refine ⟨q⁻¹ * p, mul_mem (inv_mem hq) hp, ?_, ?_⟩
    · have hqi : q⁻¹ s = s := by
        have := burnsideJ55_perm_inv_apply q s
        rwa [hqs] at this
      rw [Equiv.Perm.mul_apply, hps', hqi]
    · rw [Equiv.Perm.mul_apply, hpy, burnsideJ55_perm_inv_apply]
  · rintro ⟨p, hp, hps', hpy⟩
    exact ⟨q * p, mul_mem hq hp, by rw [Equiv.Perm.mul_apply, hps', hqs],
      by rw [Equiv.Perm.mul_apply, hpy]⟩

section

private theorem burnsideJ55_orbSet_subset_S {s y : Fin 4060} (hy : y ∈ ruS) {z : Fin 4060}
    (hz : z ∈ burnsideJ55_orbSet s y) : z ∈ ruS := by
  obtain ⟨p, hp, -, rfl⟩ := hz
  exact (ruR0_mem_ruS_iff hp y).2 hy

end

section

private theorem burnsideJ55_unique_975 {s : Fin 4060} (hs : s ∈ ruS)
    {y : Fin 4060} (hy : y ∈ ruS) (hcard : (burnsideJ55_orbSet s y).ncard = 975) :
    burnsideJ55_orbSet s y = {z | z ∈ ruS ∧ ruAdj s z} := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := exists_ruR0_g0 hs
  have hinv : p₀⁻¹ ∈ ruR0 := inv_mem hp₀
  have hps : p₀⁻¹ s = ruG0F := by rw [← hp₀g, burnsideJ55_perm_inv_apply]
  have key := burnsideJ55_E0_invariant_975 (T := p₀ ⁻¹' burnsideJ55_orbSet s y)
    (fun q hq x => by
      obtain ⟨hqR, hqg⟩ := burnsideJ55_mem_E0.1 hq
      have hq' : p₀ * q * p₀⁻¹ ∈ ruR0 := mul_mem (mul_mem hp₀ hqR) hinv
      have hqs : (p₀ * q * p₀⁻¹) s = s := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hps, hqg, hp₀g]
      have := burnsideJ55_orbSet_invariant (y := y) hq' hqs (p₀ x)
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, burnsideJ55_perm_inv_apply] at this
      exact this)
    (fun x hx => (ruR0_mem_ruS_iff hp₀ x).1 (burnsideJ55_orbSet_subset_S hy hx))
    (by
      rw [Set.ncard_preimage_of_injective_subset_range p₀.injective
        (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), hcard])
  ext z
  have h1 : z ∈ burnsideJ55_orbSet s y ↔ p₀⁻¹ z ∈ p₀ ⁻¹' burnsideJ55_orbSet s y := by
    show z ∈ burnsideJ55_orbSet s y ↔ p₀ (p₀⁻¹ z) ∈ burnsideJ55_orbSet s y
    rw [burnsideJ55_perm_apply_inv]
  rw [h1, key, ruR0_mem_ruS_iff hinv, ← hps, burnsideJ55_adj_conj hinv]
  rfl

end

private theorem burnsideJ55_mem_ruR0 {p : Equiv.Perm (Fin 4060)} : p ∈ ruR0 ↔ p ∈ ruP ∧ p 0 = 0
    := by
  unfold ruR0
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

private theorem burnsideJ55_val_two : ((2 : Fin 4060) : ℕ) = 2 := rfl

section

private theorem burnsideJ55_frob_facts {i : ℕ} (hi : i < 2) :
    isInvA 4060 (ruFrobArr i) (invCand 4060 (ruFrobArr i)) = true ∧
      CFSG.Sporadic.RuSchreier.ruSift 4060 (CFSG.Sporadic.RuSchreier.ruField4060 3)
        CFSG.Sporadic.RuSchreier.ruJoinBase (ruFrobArr i) = true ∧
      (ruFrobArr i)[0]! = 0 ∧ (ruFrobArr i)[ruG0]! = ruG0 ∧ (ruFrobArr i)[2]! = 2 := by
  have h := allLt_spec ruFrob_check.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

end

@[expose] noncomputable def burnsideJ55_frobP (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruFrobArr i)

section

private theorem burnsideJ55_rep_frobP {i : ℕ} (hi : i < 2) :
    Rep 4060 (ruFrobArr i) (burnsideJ55_frobP i) :=
  (rep_permOfArr (burnsideJ55_frob_facts hi).1).1

private theorem burnsideJ55_rep_frobP_inv {i : ℕ} (hi : i < 2) :
    Rep 4060 (invCand 4060 (ruFrobArr i)) (burnsideJ55_frobP i)⁻¹ :=
  (rep_permOfArr (burnsideJ55_frob_facts hi).1).2

end

section

private theorem burnsideJ55_frobP_mem {i : ℕ} (hi : i < 2) :
    burnsideJ55_frobP i ∈ ruP :=
  mem_ruP_of_sift (burnsideJ55_rep_frobP hi) (burnsideJ55_frob_facts hi).2.1

end

section

private theorem burnsideJ55_frobP_zero {i : ℕ} (hi : i < 2) :
    burnsideJ55_frobP i 0 = 0 :=
  Fin.ext ((burnsideJ55_rep_frobP hi 0).symm.trans (by
    rw [Fin.val_zero]
    exact (burnsideJ55_frob_facts hi).2.2.1))

private theorem burnsideJ55_frobP_g0 {i : ℕ} (hi : i < 2) :
    burnsideJ55_frobP i ruG0F = ruG0F :=
  Fin.ext ((burnsideJ55_rep_frobP hi ruG0F).symm.trans (by
    rw [ruG0F_val]
    exact (burnsideJ55_frob_facts hi).2.2.2.1))

private theorem burnsideJ55_frobP_two {i : ℕ} (hi : i < 2) :
    burnsideJ55_frobP i 2 = 2 :=
  Fin.ext ((burnsideJ55_rep_frobP hi 2).symm.trans (by
    rw [burnsideJ55_val_two]
    exact (burnsideJ55_frob_facts hi).2.2.2.2))

private theorem burnsideJ55_frobA_pow5 :
    burnsideJ55_frobP 0 ^ 5 = 1 :=
  eq_of_eqA (CFSG.Sporadic.RuSchreier.rep_powA (burnsideJ55_rep_frobP (by norm_num)) 5)
    rep_idA ruFrob_check.2.1

private theorem burnsideJ55_frobA_ne_one :
    burnsideJ55_frobP 0 ≠ 1 := fun h => by
  have := (eqA_iff (burnsideJ55_rep_frobP (by norm_num : 0 < 2)) rep_idA).2 h
  rw [ruFrob_check.2.2.1] at this
  exact Bool.false_ne_true this

private theorem burnsideJ55_frobB_pow4 :
    burnsideJ55_frobP 1 ^ 4 = 1 :=
  eq_of_eqA (CFSG.Sporadic.RuSchreier.rep_powA (burnsideJ55_rep_frobP (by norm_num)) 4)
    rep_idA ruFrob_check.2.2.2.1

private theorem burnsideJ55_frobB_sq_ne_one :
    burnsideJ55_frobP 1 ^ 2 ≠ 1 := fun h => by
  have := (eqA_iff (CFSG.Sporadic.RuSchreier.rep_powA (burnsideJ55_rep_frobP (by norm_num : 1 < 2)) 2)
    rep_idA).2 h
  rw [ruFrob_check.2.2.2.2.1] at this
  exact Bool.false_ne_true this

private theorem burnsideJ55_frob_conj :
    burnsideJ55_frobP 1 * burnsideJ55_frobP 0 * (burnsideJ55_frobP 1)⁻¹ =
      burnsideJ55_frobP 0 ^ 2 :=
  eq_of_eqA (rep_compA (rep_compA (burnsideJ55_rep_frobP (by norm_num))
    (burnsideJ55_rep_frobP (by norm_num))) (burnsideJ55_rep_frobP_inv (by norm_num)))
    (CFSG.Sporadic.RuSchreier.rep_powA (burnsideJ55_rep_frobP (by norm_num)) 2)
    ruFrob_check.2.2.2.2.2

end

section

private theorem burnsideJ55_frob_elements {s : Fin 4060} (hs : s ∈ ruS)
    {y : Fin 4060} (hy0 : ruAdj 0 y) (hys : ruAdj s y) :
    ∃ a b : Equiv.Perm (Fin 4060), a ∈ ruR0 ∧ b ∈ ruR0 ∧ a s = s ∧ a y = y ∧ b s = s ∧ b y = y ∧
      a ^ 5 = 1 ∧ a ≠ 1 ∧ b ^ 4 = 1 ∧ b ^ 2 ≠ 1 ∧ b * a * b⁻¹ = a ^ 2 := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := exists_ruR0_g0 hs
  have hinv : p₀⁻¹ ∈ ruR0 := inv_mem hp₀
  have hps : p₀⁻¹ s = ruG0F := by rw [← hp₀g, burnsideJ55_perm_inv_apply]
  have hy2 : ruELab[((p₀⁻¹ y : Fin 4060) : ℕ)]! = 2 := by
    refine (burnsideJ55_ELab2_iff _).2 ⟨?_, ?_⟩
    · rw [ruR0_mem_range_ruB_iff hinv]
      exact (ruAdj_zero_iff y).1 hy0
    · rw [← hps]
      exact (burnsideJ55_adj_conj hinv s y).2 hys
  have h2 : ruELab[((2 : Fin 4060) : ℕ)]! = 2 := by
    rw [burnsideJ55_val_two]
    exact ruE0Cls_check.2.2.2.1
  obtain ⟨e, he, hey⟩ := burnsideJ55_E0_trans (hy2.trans h2.symm)
  obtain ⟨heR, heg⟩ := burnsideJ55_mem_E0.1 he
  have hegi : e⁻¹ ruG0F = ruG0F := by
    have := burnsideJ55_perm_inv_apply e ruG0F
    rwa [heg] at this
  set c : Equiv.Perm (Fin 4060) := p₀ * e⁻¹ with hc
  have hcR : c ∈ ruR0 := mul_mem hp₀ (inv_mem heR)
  have hcg : c ruG0F = s := by rw [hc, Equiv.Perm.mul_apply, hegi, hp₀g]
  have hc2 : c 2 = y := by
    rw [hc, Equiv.Perm.mul_apply]
    have : e⁻¹ 2 = p₀⁻¹ y := by
      rw [← hey, burnsideJ55_perm_inv_apply]
    rw [this, burnsideJ55_perm_apply_inv]
  have hA : burnsideJ55_frobP 0 ∈ ruR0 :=
    burnsideJ55_mem_ruR0.2 ⟨burnsideJ55_frobP_mem (by norm_num), burnsideJ55_frobP_zero (by norm_num)⟩
  have hB : burnsideJ55_frobP 1 ∈ ruR0 :=
    burnsideJ55_mem_ruR0.2 ⟨burnsideJ55_frobP_mem (by norm_num), burnsideJ55_frobP_zero (by norm_num)⟩
  refine ⟨c * burnsideJ55_frobP 0 * c⁻¹, c * burnsideJ55_frobP 1 * c⁻¹,
    mul_mem (mul_mem hcR hA) (inv_mem hcR), mul_mem (mul_mem hcR hB) (inv_mem hcR), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hcg, burnsideJ55_perm_inv_apply,
      burnsideJ55_frobP_g0 (by norm_num : 0 < 2)]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hc2, burnsideJ55_perm_inv_apply,
      burnsideJ55_frobP_two (by norm_num : 0 < 2)]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hcg, burnsideJ55_perm_inv_apply,
      burnsideJ55_frobP_g0 (by norm_num : 1 < 2)]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hc2, burnsideJ55_perm_inv_apply,
      burnsideJ55_frobP_two (by norm_num : 1 < 2)]
  · rw [show c * burnsideJ55_frobP 0 * c⁻¹ = MulAut.conj c (burnsideJ55_frobP 0) from rfl,
      ← map_pow, burnsideJ55_frobA_pow5, map_one]
  · intro h
    apply burnsideJ55_frobA_ne_one
    have := congrArg (fun z => c⁻¹ * z * c) h
    simpa [mul_assoc] using this
  · rw [show c * burnsideJ55_frobP 1 * c⁻¹ = MulAut.conj c (burnsideJ55_frobP 1) from rfl,
      ← map_pow, burnsideJ55_frobB_pow4, map_one]
  · intro h
    apply burnsideJ55_frobB_sq_ne_one
    rw [show c * burnsideJ55_frobP 1 * c⁻¹ = MulAut.conj c (burnsideJ55_frobP 1) from rfl,
      ← map_pow] at h
    exact (map_eq_one_iff _ (MulAut.conj c).injective).1 h
  · have h := congrArg (MulAut.conj c) burnsideJ55_frob_conj
    rw [map_mul, map_mul, map_inv, map_pow] at h
    simpa [MulAut.conj_apply, mul_assoc] using h

end

@[expose] def burnsideJ55_Fst : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruR0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (1 : Fin 4060)

private theorem burnsideJ55_mem_Fst {p : Equiv.Perm (Fin 4060)} :
    p ∈ burnsideJ55_Fst ↔ p ∈ ruR0 ∧ p 1 = 1 := by
  unfold burnsideJ55_Fst
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

section

private theorem burnsideJ55_ruFGen_mem_Fst {k : ℕ} (hk : k < 2) : ruFGen k ∈ burnsideJ55_Fst :=
  burnsideJ55_mem_Fst.2 ⟨burnsideJ55_mem_ruR0.2 ⟨ruFGen_mem hk, ruFGen_zero hk⟩, ruFGen_one hk⟩

private theorem burnsideJ55_genF_le : genSubgroup 4060 ruFGArrs.size ruFGen ≤ burnsideJ55_Fst := by
  rw [genSubgroup, ruFGArrs_size, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact burnsideJ55_ruFGen_mem_Fst hi

private theorem burnsideJ55_Fst_trans {y z : Fin 4060} (h : ruFLab[(y : ℕ)]! = ruFLab[(z : ℕ)]!) :
    ∃ p ∈ burnsideJ55_Fst, p y = z := by
  have hor := orbit_eq_labels ruFGArrs_rep ruStabs_check.2.2.1 y
  have hz : z ∈ MulAction.orbit (genSubgroup 4060 ruFGArrs.size ruFGen) y := by
    rw [hor]
    exact h.symm
  obtain ⟨⟨g, hg⟩, rfl⟩ := hz
  exact ⟨g, burnsideJ55_genF_le hg, rfl⟩

end

@[expose] def burnsideJ55_fdOrb (x : Fin 4060) : Set (Fin 4060) :=
  {z | ∃ p ∈ ruR0, p 1 = 1 ∧ p x = z}

@[expose] noncomputable def burnsideJ55_inv (x : Fin 4060) : ℕ :=
  {w | ruAdj 0 w ∧ ruAdj 1 w ∧ ruAdj x w}.ncard

section

private theorem burnsideJ55_inv_eq_cnt {r : Fin 4060} (hr : isInvA 4060 (ruTreeArr r) (ruTI r)
    = true) :
    burnsideJ55_inv r = ruCommonCnt ruTI1 (ruTI r) := by
  unfold burnsideJ55_inv ruCommonCnt
  rw [← ncard_setOf_fin]
  congr 1
  ext w
  show (ruAdj 0 w ∧ ruAdj 1 w ∧ ruAdj r w) ↔
    (ruInD w && ruRowA ruTI1 w && ruRowA (ruTI r) w) = true
  rw [Bool.and_eq_true, Bool.and_eq_true, ruInD, beq_iff_eq, ← mem_range_ruB_iff,
    ← ruAdj_zero_iff, ruRowA_one, ruRowA_spec hr, and_assoc]

end

private theorem burnsideJ55_inv_apply {p : Equiv.Perm (Fin 4060)} (hp : p ∈ ruP) (h0 : p 0 = 0)
    (h1 : p 1 = 1) (x : Fin 4060) : burnsideJ55_inv (p x) = burnsideJ55_inv x := by
  unfold burnsideJ55_inv
  have e : {w | ruAdj 0 w ∧ ruAdj 1 w ∧ ruAdj (p x) w} =
      {w | (ruAdj 0 (p⁻¹ w) ∧ ruAdj 1 (p⁻¹ w) ∧ ruAdj x (p⁻¹ w))} := by
    ext w
    show (ruAdj 0 w ∧ ruAdj 1 w ∧ ruAdj (p x) w) ↔ _
    rw [← h0, ← h1, ruAdj_iff_inv hp, ruAdj_iff_inv hp, ruAdj_iff_inv hp, h0, h1]
    exact Iff.rfl
  rw [e]
  exact ncard_setOf_perm_inv p fun v => ruAdj 0 v ∧ ruAdj 1 v ∧ ruAdj x v

section

private theorem burnsideJ55_Fcls_iff (x : Fin 4060) :
    (ruAdj 0 x ∧ ruAdj 1 x) ↔
      (ruFLab[(x : ℕ)]! = 2 ∨ ruFLab[(x : ℕ)]! = 6 ∨ ruFLab[(x : ℕ)]! = 7) := by
  have h := allLt_spec ruFd_check.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, Bool.and_eq_true] at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rw [or_assoc] at h
  rw [← h, ruInD, beq_iff_eq, ← mem_range_ruB_iff, ← ruAdj_zero_iff, ruRowA_one]

end

@[expose] def burnsideJ55_r7 : Fin 4060 := ⟨2325, by norm_num⟩

@[expose] def burnsideJ55_r6 : Fin 4060 := ⟨149, by norm_num⟩

@[expose] def burnsideJ55_r2 : Fin 4060 := ⟨2, by norm_num⟩

section

private theorem burnsideJ55_inv_r2 : burnsideJ55_inv burnsideJ55_r2 = 281 :=
  (burnsideJ55_inv_eq_cnt (r := burnsideJ55_r2) ruFd_check.2.2.2.2.2.2.2.2.2.1).trans
    ruFd_check.2.2.2.2.2.2.2.2.2.2.2.2

private theorem burnsideJ55_inv_r6 : burnsideJ55_inv burnsideJ55_r6 = 345 :=
  (burnsideJ55_inv_eq_cnt (r := burnsideJ55_r6) ruFd_check.2.2.2.2.2.2.2.2.1).trans
    ruFd_check.2.2.2.2.2.2.2.2.2.2.2.1

private theorem burnsideJ55_inv_r7 : burnsideJ55_inv burnsideJ55_r7 = 217 :=
  (burnsideJ55_inv_eq_cnt (r := burnsideJ55_r7) ruFd_check.2.2.2.2.2.2.2.1).trans
    ruFd_check.2.2.2.2.2.2.2.2.2.2.1

end

@[expose] def burnsideJ55_val (L : ℕ) : ℕ := if L = 7 then 217 else if L = 6 then 345 else 281

section

private theorem burnsideJ55_inv_label {x : Fin 4060}
    (hx : ruAdj 0 x ∧ ruAdj 1 x) : burnsideJ55_inv x = burnsideJ55_val ruFLab[(x : ℕ)]! := by
  obtain ⟨-, -, -, -, l7, l6, l2, -⟩ := ruFd_check
  have key : ∀ r : Fin 4060, ruFLab[(r : ℕ)]! = ruFLab[(x : ℕ)]! →
      burnsideJ55_inv x = burnsideJ55_inv r := by
    intro r hr
    obtain ⟨p, hp, hpr⟩ := burnsideJ55_Fst_trans hr
    obtain ⟨hpR, hp1⟩ := burnsideJ55_mem_Fst.1 hp
    obtain ⟨hpP, hp0⟩ := burnsideJ55_mem_ruR0.1 hpR
    rw [← hpr, burnsideJ55_inv_apply hpP hp0 hp1]
  rcases (burnsideJ55_Fcls_iff x).1 hx with h | h | h
  ·
    have := key burnsideJ55_r2 (by rw [h]; exact l2)
    rw [this, burnsideJ55_inv_r2, h]
    simp [burnsideJ55_val]
  · have := key burnsideJ55_r6 (by rw [h]; exact l6)
    rw [this, burnsideJ55_inv_r6, h]
    simp [burnsideJ55_val]
  · have := key burnsideJ55_r7 (by rw [h]; exact l7)
    rw [this, burnsideJ55_inv_r7, h]
    simp [burnsideJ55_val]

end

section

private theorem burnsideJ55_fdOrb_eq {r : Fin 4060}
    (hr : ruAdj 0 r ∧ ruAdj 1 r)
    (hsep : ∀ x : Fin 4060, (ruAdj 0 x ∧ ruAdj 1 x) → burnsideJ55_inv x = burnsideJ55_inv r →
      ruFLab[(x : ℕ)]! = ruFLab[(r : ℕ)]!) :
    burnsideJ55_fdOrb r = {z : Fin 4060 | ruFLab[(z : ℕ)]! = ruFLab[(r : ℕ)]!} := by
  ext z
  constructor
  · rintro ⟨p, hp, hp1, rfl⟩
    have hpF : p ∈ burnsideJ55_Fst := burnsideJ55_mem_Fst.2 ⟨hp, hp1⟩
    obtain ⟨hpP, hp0⟩ := burnsideJ55_mem_ruR0.1 hp
    have hz : ruAdj 0 (p r) ∧ ruAdj 1 (p r) := by
      constructor
      · rw [← hp0, burnsideJ55_adj_conj hp]
        exact hr.1
      · rw [← hp1, burnsideJ55_adj_conj hp]
        exact hr.2
    exact hsep _ hz (burnsideJ55_inv_apply hpP hp0 hp1 r)
  · intro hz
    obtain ⟨p, hp, hpr⟩ := burnsideJ55_Fst_trans (y := r) (z := z) hz.symm
    obtain ⟨hpR, hp1⟩ := burnsideJ55_mem_Fst.1 hp
    exact ⟨p, hpR, hp1, hpr⟩

end

section

private theorem burnsideJ55_Fd_orbits :
    ∃ a b c : Fin 4060, (ruAdj 0 a ∧ ruAdj 1 a) ∧ (ruAdj 0 b ∧ ruAdj 1 b) ∧
      (ruAdj 0 c ∧ ruAdj 1 c) ∧
      {x | ruAdj 0 x ∧ ruAdj 1 x} =
        burnsideJ55_fdOrb a ∪ burnsideJ55_fdOrb b ∪ burnsideJ55_fdOrb c ∧
      (burnsideJ55_fdOrb a).ncard = 10 ∧ (burnsideJ55_fdOrb b).ncard = 80 ∧
      (burnsideJ55_fdOrb c).ncard = 640 ∧
      Disjoint (burnsideJ55_fdOrb a) (burnsideJ55_fdOrb b) ∧
      Disjoint (burnsideJ55_fdOrb a) (burnsideJ55_fdOrb c) ∧
      Disjoint (burnsideJ55_fdOrb b) (burnsideJ55_fdOrb c) := by
  obtain ⟨-, h7c, h6c, h2c, l7, l6, l2, -⟩ := ruFd_check
  have l7' : ruFLab[(burnsideJ55_r7 : ℕ)]! = 7 := l7
  have l6' : ruFLab[(burnsideJ55_r6 : ℕ)]! = 6 := l6
  have l2' : ruFLab[(burnsideJ55_r2 : ℕ)]! = 2 := l2
  have hC7 : ruAdj 0 burnsideJ55_r7 ∧ ruAdj 1 burnsideJ55_r7 :=
    (burnsideJ55_Fcls_iff _).2 (Or.inr (Or.inr l7'))
  have hC6 : ruAdj 0 burnsideJ55_r6 ∧ ruAdj 1 burnsideJ55_r6 :=
    (burnsideJ55_Fcls_iff _).2 (Or.inr (Or.inl l6'))
  have hC2 : ruAdj 0 burnsideJ55_r2 ∧ ruAdj 1 burnsideJ55_r2 :=
    (burnsideJ55_Fcls_iff _).2 (Or.inl l2')
  have hval : ∀ L, (L = 2 ∨ L = 6 ∨ L = 7) → ∀ L', (L' = 2 ∨ L' = 6 ∨ L' = 7) →
      burnsideJ55_val L = burnsideJ55_val L' → L = L' := by
    intro L hL L' hL' h
    rcases hL with rfl | rfl | rfl <;> rcases hL' with rfl | rfl | rfl <;>
      simp_all [burnsideJ55_val]
  have hsep : ∀ (r : Fin 4060), ruFLab[(r : ℕ)]! = 7 ∨ ruFLab[(r : ℕ)]! = 6 ∨
      ruFLab[(r : ℕ)]! = 2 → (ruAdj 0 r ∧ ruAdj 1 r) → ∀ x : Fin 4060, (ruAdj 0 x ∧ ruAdj 1 x) →
      burnsideJ55_inv x = burnsideJ55_inv r → ruFLab[(x : ℕ)]! = ruFLab[(r : ℕ)]! := by
    intro r _ hr x hx hinv
    rw [burnsideJ55_inv_label hx, burnsideJ55_inv_label hr] at hinv
    refine hval _ ?_ _ ?_ hinv
    · exact (burnsideJ55_Fcls_iff x).1 hx
    · exact (burnsideJ55_Fcls_iff r).1 hr
  have hO7 := burnsideJ55_fdOrb_eq hC7 (hsep _ (Or.inl l7') hC7)
  have hO6 := burnsideJ55_fdOrb_eq hC6 (hsep _ (Or.inr (Or.inl l6')) hC6)
  have hO2 := burnsideJ55_fdOrb_eq hC2 (hsep _ (Or.inr (Or.inr l2')) hC2)
  rw [l7'] at hO7
  rw [l6'] at hO6
  rw [l2'] at hO2
  refine ⟨burnsideJ55_r7, burnsideJ55_r6, burnsideJ55_r2, hC7, hC6, hC2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [Set.mem_union, Set.mem_union, hO7, hO6, hO2]
    simp only [Set.mem_setOf_eq]
    rw [burnsideJ55_Fcls_iff]
    constructor
    · rintro (h | h | h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
  · rw [hO7, ncard_labelClass]
    exact h7c
  · rw [hO6, ncard_labelClass]
    exact h6c
  · rw [hO2, ncard_labelClass]
    exact h2c
  · rw [hO7, hO6]
    exact Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_setOf_eq] at hx hx'
      omega
  · rw [hO7, hO2]
    exact Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_setOf_eq] at hx hx'
      omega
  · rw [hO6, hO2]
    exact Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_setOf_eq] at hx hx'
      omega

end

section

private theorem burnsideJ55_orbital_S {s : Fin 4060} (hs : s ∈ ruS) (x y : Fin 4060) :
    (∃ p ∈ ruP, p 0 = x ∧ p s = y) ↔ (x ≠ y ∧ ¬ ruAdj x y) := by
  constructor
  · rintro ⟨p, hp, rfl, rfl⟩
    refine ⟨fun h => hs.1 (p.injective h).symm, fun h => hs.2 ?_⟩
    rw [ruAdj_apply hp] at h
    exact (ruAdj_zero_iff s).1 h
  · rintro ⟨hxy, hadj⟩
    have ht0 : ruTreeElt (x : ℕ) 0 = x := ruTreeElt_apply_zero x
    have htP : ruTreeElt (x : ℕ) ∈ ruP := ruTreeElt_mem _
    have hyS : (ruTreeElt (x : ℕ))⁻¹ y ∈ ruS := by
      refine ⟨fun h => hxy ?_, fun h => hadj ?_⟩
      · have : y = ruTreeElt (x : ℕ) 0 := by
          rw [← h, burnsideJ55_perm_apply_inv]
        rw [this, ht0]
      · have h1 : ruAdj 0 ((ruTreeElt (x : ℕ))⁻¹ y) := (ruAdj_zero_iff _).2 h
        rw [← ruAdj_iff_inv htP, ht0] at h1
        exact h1
    obtain ⟨r, hrR, hrs⟩ : ∃ r ∈ ruR0, r s = (ruTreeElt (x : ℕ))⁻¹ y := by
      have := orbit_ruR0_of_mem_ruS hs
      rw [← this] at hyS
      obtain ⟨⟨r, hr⟩, hrs⟩ := hyS
      exact ⟨r, hr, hrs⟩
    refine ⟨ruTreeElt (x : ℕ) * r, mul_mem htP (ruR0_le_ruP hrR), ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, ruR0_apply_zero hrR, ht0]
    · rw [Equiv.Perm.mul_apply, hrs, burnsideJ55_perm_apply_inv]

end

section

private theorem burnsideJ55_orbSet_780 {s : Fin 4060} (hs : s ∈ ruS)
    {y : Fin 4060} (hy0 : ruAdj 0 y) (hys : ruAdj s y) :
    burnsideJ55_orbSet s y = {z | ruAdj 0 z ∧ ruAdj s z} := by
  ext z
  constructor
  · rintro ⟨p, hp, hps, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← ruR0_apply_zero hp, burnsideJ55_adj_conj hp]
      exact hy0
    · rw [← hps, burnsideJ55_adj_conj hp]
      exact hys
  · rintro ⟨hz0, hzs⟩
    exact burnsideJ55_trans_780 hs hy0 hys hz0 hzs

private theorem burnsideJ55_orbSet_D975 {s : Fin 4060} (hs : s ∈ ruS)
    {y : Fin 4060} (hy0 : ruAdj 0 y) (hys : ¬ ruAdj s y) :
    burnsideJ55_orbSet s y = {z | ruAdj 0 z ∧ ¬ ruAdj s z} := by
  ext z
  constructor
  · rintro ⟨p, hp, hps, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← ruR0_apply_zero hp, burnsideJ55_adj_conj hp]
      exact hy0
    · rw [← hps, burnsideJ55_adj_conj hp]
      exact hys
  · rintro ⟨hz0, hzs⟩
    exact burnsideJ55_trans_D975 hs hy0 hys hz0 hzs

private theorem burnsideJ55_orbSet_S975 {s : Fin 4060} (hs : s ∈ ruS)
    {y : Fin 4060} (hy0 : y ∈ ruS) (hys : ruAdj s y) :
    burnsideJ55_orbSet s y = {z | z ∈ ruS ∧ ruAdj s z} := by
  ext z
  constructor
  · rintro ⟨p, hp, hps, rfl⟩
    refine ⟨(ruR0_mem_ruS_iff hp y).2 hy0, ?_⟩
    rw [← hps, burnsideJ55_adj_conj hp]
    exact hys
  · rintro ⟨hz0, hzs⟩
    exact burnsideJ55_trans_S975 hs hy0 hys hz0 hzs

end

section

private theorem burnsideJ55_not_adj_of_mem_S {s : Fin 4060} (hs : s ∈ ruS) : ¬ ruAdj 0 s :=
  fun h => hs.2 ((ruAdj_zero_iff _).1 h)

private theorem burnsideJ55_mem_S_iff (n : Fin 4060) : n ∈ ruS ↔ (n ≠ 0 ∧ ¬ ruAdj 0 n) := by
  show (n ≠ 0 ∧ n ∉ Set.range ruB) ↔ (n ≠ 0 ∧ ¬ ruAdj 0 n)
  rw [ruAdj_zero_iff]

end

section

private theorem burnsideJ55_ncard_D_N {s : Fin 4060} (hs : s ∈ ruS) :
    {n | ruAdj 0 n ∧ ruAdj s n}.ncard = 780 :=
  ncard_common_of_not_ruAdj (fun h => hs.1 h.symm) (burnsideJ55_not_adj_of_mem_S hs)

private theorem burnsideJ55_ncard_D_notN {s : Fin 4060} (hs : s ∈ ruS) :
    {n | ruAdj 0 n ∧ ¬ ruAdj s n}.ncard = 975 := by
  have e : {n | ruAdj 0 n ∧ ¬ ruAdj s n} =
      {n | ruAdj 0 n} \ {n | ruAdj 0 n ∧ ruAdj s n} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 h1⟩
  rw [e, Set.ncard_diff (fun n hn => hn.1) (Set.toFinite _), ncard_ruAdj, burnsideJ55_ncard_D_N hs]

private theorem burnsideJ55_ncard_S_N {s : Fin 4060} (hs : s ∈ ruS) :
    {n | n ∈ ruS ∧ ruAdj s n}.ncard = 975 := by
  have e : {n | n ∈ ruS ∧ ruAdj s n} =
      {n | ruAdj s n} \ {n | ruAdj s n ∧ ruAdj 0 n} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_and, burnsideJ55_mem_S_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, fun _ => h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h2 h1⟩, h1⟩
      rintro rfl
      exact burnsideJ55_not_adj_of_mem_S hs ((ruAdj_comm _ _).1 h1)
  have hsub : {n | ruAdj s n ∧ ruAdj 0 n} ⊆ {n | ruAdj s n} := fun n hn => hn.1
  have h780 : {n | ruAdj s n ∧ ruAdj 0 n}.ncard = 780 := by
    have e2 : {n | ruAdj s n ∧ ruAdj 0 n} = {n | ruAdj 0 n ∧ ruAdj s n} := by
      ext n
      exact and_comm
    rw [e2]
    exact burnsideJ55_ncard_D_N hs
  rw [e, Set.ncard_diff hsub (Set.toFinite _), ncard_ruAdj, h780]

end

section

private theorem burnsideJ55_ncard_orbSet_D
    {s : Fin 4060} (hs : s ∈ ruS) {y : Fin 4060} (hy : ruAdj 0 y) :
    (burnsideJ55_orbSet s y).ncard = 780 ↔ ruAdj s y := by
  by_cases h : ruAdj s y
  · rw [burnsideJ55_orbSet_780 hs hy h, burnsideJ55_ncard_D_N hs]
    exact iff_of_true rfl h
  · rw [burnsideJ55_orbSet_D975 hs hy h, burnsideJ55_ncard_D_notN hs]
    exact iff_of_false (by norm_num) h

private theorem burnsideJ55_ncard_orbSet_S
    {s : Fin 4060} (hs : s ∈ ruS) {y : Fin 4060} (hy : y ∈ ruS) :
    (burnsideJ55_orbSet s y).ncard = 975 ↔ ruAdj s y := by
  constructor
  · intro h
    have h1 := burnsideJ55_unique_975 hs hy h
    have hy' : y ∈ burnsideJ55_orbSet s y := ⟨1, one_mem _, by simp [hs], rfl⟩
    rw [h1] at hy'
    exact hy'.2
  · intro h
    rw [burnsideJ55_orbSet_S975 hs hy h, burnsideJ55_ncard_S_N hs]

end

end ModelE

section Frob20

variable {X : Type} [Group X]

private theorem burnsideJ55_conj_pow_two {a b : X} (hba : b * a * b⁻¹ = a ^ 2) (j : ℕ) :
    b ^ j * a * (b ^ j)⁻¹ = a ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : b ^ (j + 1) * a * (b ^ (j + 1))⁻¹ = b * (b ^ j * a * (b ^ j)⁻¹) * b⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e, ih, ← conj_pow, hba, ← pow_mul, pow_succ 2 j, mul_comm]

private theorem burnsideJ55_frob20 [Finite X] (hcard : Nat.card X = 20) {a b : X} (ha5 : a ^ 5 = 1)
    (ha1 : a ≠ 1) (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1) (hba : b * a * b⁻¹ = a ^ 2) :
    Nonempty (X ≃* ↥(CFSG.Open.Sz 0)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hordA : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hordB : orderOf b = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := b) (by simpa using hb2)
      (by simpa using hb4)
    simpa using this
  set N : Subgroup X := Subgroup.zpowers a with hN
  set K : Subgroup X := Subgroup.zpowers b with hK
  have hNcard : Nat.card N = 5 := by rw [hN, Nat.card_zpowers, hordA]
  have hKcard : Nat.card K = 4 := by rw [hK, Nat.card_zpowers, hordB]
  have hsup : N ⊔ K = ⊤ := by
    have h5 : 5 ∣ Nat.card ↥(N ⊔ K) := hNcard ▸ Subgroup.card_dvd_of_le le_sup_left
    have h4 : 4 ∣ Nat.card ↥(N ⊔ K) := hKcard ▸ Subgroup.card_dvd_of_le le_sup_right
    have h20 : 20 ∣ Nat.card ↥(N ⊔ K) := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 4) h5 h4
      simpa using this
    have hle : Nat.card ↥(N ⊔ K) ≤ 20 := hcard ▸ Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card ↥(N ⊔ K) := Nat.card_pos
    have heq : Nat.card ↥(N ⊔ K) = 20 := by
      obtain ⟨m, hm⟩ := h20
      omega
    exact Subgroup.eq_top_of_card_eq _ (heq.trans hcard.symm)
  have hmemN : ∀ n : ℕ, a ^ n ∈ N := fun n => Subgroup.pow_mem _ (Subgroup.mem_zpowers a) n
  have hbN : ∀ y ∈ N, b * y * b⁻¹ ∈ N := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow, hba, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have haN : ∀ y ∈ N, a * y * a⁻¹ ∈ N := by
    intro y hy
    have : a * y * a⁻¹ = y := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      group
    rw [this]
    exact hy
  have hnorm : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)
      · intro hy
        have := N.mul_mem (N.mul_mem (N.inv_mem hx) hy) hx
        simpa [mul_assoc] using this
    ·
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hkn : ∀ (m : ℕ) (y : X), y ∈ N → b ^ m * y * (b ^ m)⁻¹ ∈ N := by
        intro m
        induction m with
        | zero => intro y hy; simpa using hy
        | succ m ih =>
          intro y hy
          have e : b ^ (m + 1) * y * (b ^ (m + 1))⁻¹ = b * (b ^ m * y * (b ^ m)⁻¹) * b⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            group
          rw [e]
          exact hbN _ (ih y hy)
      have hkn' : ∀ (k : ℤ) (y : X), y ∈ N → b ^ k * y * (b ^ k)⁻¹ ∈ N := by
        intro k y hy
        have hmod : b ^ k = b ^ (k % (orderOf b : ℤ)).toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [hordB]; norm_num)),
            zpow_mod_orderOf]
        rw [hmod]
        exact hkn _ y hy
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hkn' k y hy
      · intro hy
        have := hkn' (-k) _ hy
        simpa [zpow_neg, mul_assoc] using this
  refine CFSG.Quasithin.S152N2.frobenius20IsSz2 X hcard ⟨N, hnorm, hNcard, fun x hx => ?_⟩
  have hxa : x * a = a * x := hx a (Subgroup.mem_zpowers a)
  have hxmem : x ∈ ((K ⊔ N : Subgroup X) : Set X) := by
    rw [sup_comm, hsup]
    exact Subgroup.mem_top x
  rw [Subgroup.mul_normal] at hxmem
  obtain ⟨k, hkK, n, hnN, rfl⟩ := hxmem
  have hna : n * a = a * n := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hnN
    exact ((Commute.refl a).zpow_left m).eq
  have hka : k * a = a * k := by
    have h1 : k * n * a = a * (k * n) := hxa
    have h2 : (k * a) * n = (a * k) * n := by
      calc (k * a) * n = k * (a * n) := by rw [mul_assoc]
        _ = k * (n * a) := by rw [hna]
        _ = k * n * a := by rw [mul_assoc]
        _ = a * (k * n) := h1
        _ = (a * k) * n := by rw [mul_assoc]
    exact mul_right_cancel h2
  obtain ⟨j, hj, rfl⟩ : ∃ j : ℕ, j < 4 ∧ k = b ^ j := by
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hkK
    refine ⟨(z % (orderOf b : ℤ)).toNat, ?_, ?_⟩
    · have h4 : ((orderOf b : ℕ) : ℤ) = 4 := by rw [hordB]; norm_num
      have := Int.emod_lt_of_pos z (by rw [h4]; norm_num : (0 : ℤ) < orderOf b)
      rw [h4] at this ⊢
      omega
    · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [hordB]; norm_num)),
        zpow_mod_orderOf]
  have hconj : a ^ (2 ^ j) = a := by
    rw [← burnsideJ55_conj_pow_two hba j, hka]
    group
  have hj0 : j = 0 := by
    by_contra hne
    have h1 : a ^ (2 ^ j - 1) = 1 := by
      have : a ^ (2 ^ j) = a ^ (2 ^ j - 1) * a := by
        rw [← pow_succ]
        congr 1
        have : 0 < 2 ^ j := by positivity
        omega
      rw [this] at hconj
      exact mul_eq_right.1 hconj
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hordA] at h2
    interval_cases j <;> simp_all <;> omega
  subst hj0
  simpa using hnN

end Frob20

section IncGraph

variable {Y : Type} [Group Y] (M1 M2 : Subgroup Y)

theorem burnsideJ55_inc_adj_inl_inr (a : Y ⧸ M1) (b : Y ⧸ M2) :
    (ChIJK.incGraph M1 M2).Adj (Sum.inl a) (Sum.inr b) ↔
      ∃ y : Y, a = (y : Y ⧸ M1) ∧ b = (y : Y ⧸ M2) := by
  constructor
  · rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩)
    · exact ⟨y, Sum.inl.inj h1, Sum.inr.inj h2⟩
    · exact absurd h1 (by simp)
  · rintro ⟨y, rfl, rfl⟩
    exact Or.inl ⟨y, rfl, rfl⟩

theorem burnsideJ55_inc_not_adj_inl_inl (a b : Y ⧸ M1) :
    ¬ (ChIJK.incGraph M1 M2).Adj (Sum.inl a) (Sum.inl b) := by
  rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩) <;> simp at h2

theorem burnsideJ55_inc_not_adj_inr_inr (a b : Y ⧸ M2) :
    ¬ (ChIJK.incGraph M1 M2).Adj (Sum.inr a) (Sum.inr b) := by
  rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩) <;> simp at h1

private theorem burnsideJ55_inc_walk_even {x z : Y ⧸ M1 ⊕ Y ⧸ M2} (p : (ChIJK.incGraph M1
    M2).Walk x z) :
    Even p.length ↔ (x.isLeft = z.isLeft) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    have hab : a.isLeft ≠ b.isLeft := by
      rcases a with a | a <;> rcases b with b | b
      · exact absurd h (burnsideJ55_inc_not_adj_inl_inl M1 M2 a b)
      · simp
      · simp
      · exact absurd h (burnsideJ55_inc_not_adj_inr_inr M1 M2 a b)
    revert hab
    cases a.isLeft <;> cases b.isLeft <;> cases c.isLeft <;> simp

private theorem burnsideJ55_inc_dist_even {u v : Y ⧸ M1}
    (h : (ChIJK.incGraph M1 M2).Reachable (Sum.inl u) (Sum.inl v)) :
    Even ((ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v)) := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact (burnsideJ55_inc_walk_even M1 M2 p).2 rfl

private theorem burnsideJ55_inc_dist_lt_eight_iff (u v : Y ⧸ M1) :
    (0 < (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ∧
        (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) < 8) ↔
      (u ≠ v ∧ (ChIJK.incGraph M1 M2).Reachable (Sum.inl u) (Sum.inl v) ∧
        (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ≤ 6) := by
  constructor
  · rintro ⟨h0, h8⟩
    have hne : (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ≠ 0 := Nat.pos_iff_ne_zero.1 h0
    obtain ⟨hne', hr⟩ := SimpleGraph.dist_ne_zero_iff_ne_and_reachable.1 hne
    refine ⟨fun h => hne' (by rw [h]), hr, ?_⟩
    have he := burnsideJ55_inc_dist_even M1 M2 hr
    obtain ⟨k, hk⟩ := he
    omega
  · rintro ⟨hne, hr, h6⟩
    refine ⟨?_, by omega⟩
    exact hr.pos_dist_of_ne (fun h => hne (Sum.inl.inj h))

@[expose] def burnsideJ55_incIso (y : Y) :
    ChIJK.incGraph M1 M2 ≃g ChIJK.incGraph M1 M2 where
  toEquiv := Equiv.sumCongr (MulAction.toPerm y) (MulAction.toPerm y)
  map_rel_iff' := by
    intro a b
    have key : ∀ (a : Y ⧸ M1) (b : Y ⧸ M2),
        (ChIJK.incGraph M1 M2).Adj (Sum.inl (y • a)) (Sum.inr (y • b)) ↔
          (ChIJK.incGraph M1 M2).Adj (Sum.inl a) (Sum.inr b) := by
      intro a b
      rw [burnsideJ55_inc_adj_inl_inr, burnsideJ55_inc_adj_inl_inr]
      constructor
      · rintro ⟨x, h1, h2⟩
        refine ⟨y⁻¹ * x, ?_, ?_⟩
        · rw [← inv_smul_smul y a, h1]
          rfl
        · rw [← inv_smul_smul y b, h2]
          rfl
      · rintro ⟨x, rfl, rfl⟩
        exact ⟨y * x, rfl, rfl⟩
    rcases a with a | a <;> rcases b with b | b
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_toEmbedding]
      exact ⟨fun h => absurd h (burnsideJ55_inc_not_adj_inl_inl M1 M2 _ _),
        fun h => absurd h (burnsideJ55_inc_not_adj_inl_inl M1 M2 _ _)⟩
    · exact key a b
    · show (ChIJK.incGraph M1 M2).Adj (Sum.inr (y • a)) (Sum.inl (y • b)) ↔
        (ChIJK.incGraph M1 M2).Adj (Sum.inr a) (Sum.inl b)
      rw [SimpleGraph.adj_comm _ (Sum.inr (y • a)), SimpleGraph.adj_comm _ (Sum.inr a)]
      exact key b a
    · exact ⟨fun h => absurd h (burnsideJ55_inc_not_adj_inr_inr M1 M2 _ _),
        fun h => absurd h (burnsideJ55_inc_not_adj_inr_inr M1 M2 _ _)⟩

private theorem burnsideJ55_dist_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e :
    G ≃g H)
    (u v : V) : H.dist (e u) (e v) = G.dist u v := by
  have key : ∀ {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V),
      H.dist (e u) (e v) ≤ G.dist u v := by
    intro V W G H e u v
    by_cases hr : G.Reachable u v
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
      calc H.dist (e u) (e v) ≤ (p.map e.toHom).length := SimpleGraph.dist_le _
        _ = G.dist u v := by rw [SimpleGraph.Walk.length_map, hp]
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
      have : ¬ H.Reachable (e u) (e v) := fun h => hr (by simpa using h.map e.symm.toHom)
      rw [SimpleGraph.dist_eq_zero_of_not_reachable this]
  refine le_antisymm (key e u v) ?_
  have := key e.symm (e u) (e v)
  simpa using this

private theorem burnsideJ55_inc_dist_smul (y : Y) (u v : Y ⧸ M1) :
    (ChIJK.incGraph M1 M2).dist (Sum.inl (y • u)) (Sum.inl (y • v)) =
      (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) :=
  burnsideJ55_dist_iso (burnsideJ55_incIso M1 M2 y) (Sum.inl u) (Sum.inl v)

end IncGraph

section BurnsideJ55PartA

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Copied

private theorem burnsideJ55_faithful {G Ω : Type} [Group G] [MulAction G Ω]
    (h : ∀ g : G, (∀ ω : Ω, g • ω = ω) → g = 1) : FaithfulSMul G Ω := by
  refine ⟨fun {m₁ m₂} hm => ?_⟩
  have h1 : m₁⁻¹ * m₂ = 1 := by
    apply h
    intro ω
    rw [mul_smul, ← hm ω, inv_smul_smul]
  exact inv_mul_eq_one.mp h1

theorem burnsideJ55_subgroupOf_eq {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf (MulAction.stabilizer G ω) =
      MulAction.stabilizer (MulAction.stabilizer G ω) δ := by
  ext f
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

@[expose] noncomputable def burnsideJ55_stabEquiv {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    MulAction.stabilizer (MulAction.stabilizer G ω) δ ≃*
      ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) :=
  (MulEquiv.subgroupCongr (burnsideJ55_subgroupOf_eq ω δ)).symm.trans
    (Subgroup.subgroupOfEquivOfLe inf_le_left)

private theorem burnsideJ55_parabolic {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω)
    (h : ChIJK.IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
      (MulAction.stabilizer G ω))) :
    CFSG.Quasithin.RuRank3.IsSylowTwoParabolic
      (MulAction.stabilizer (MulAction.stabilizer G ω) δ) := by
  rw [← burnsideJ55_subgroupOf_eq]
  exact h

private theorem burnsideJ55_psl_of_stated {N : Type} [Group N]
    (h : CFSG.Open.StatedClassicalModel N .PSL 2 5 2) :
    Nonempty (N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 5 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 5 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 5 2 (by norm_num)]
  exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv
      (FiniteField.ringEquivOfCardEq hcard)))⟩

private theorem burnsideJ55_center_trivial {N : Type} [Group N]
    (e : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) :
    ∀ z : N, (∀ g : N, g * z = z * g) → z = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro z hz
  have h1 : e z ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg e (hz (e.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

private theorem burnsideJ55_isL225Plus {Y : Type} [Group Y] (h : ChIJK.IsL225Plus Y) :
    CFSG.Quasithin.RuRank3.IsL225Plus Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨N, hN, hidx, hmodel, P, n, hn4, ⟨eP⟩⟩ := h
  obtain ⟨eN⟩ := burnsideJ55_psl_of_stated hmodel
  have hNcard : Nat.card N = 7800 := by
    rw [Nat.card_congr eN.toEquiv,
      CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := 5) (m := 2) (by norm_num)
        (by norm_num)]
    norm_num
  have hYcard : Nat.card Y = 15600 := by
    have := Subgroup.card_mul_index N
    rw [hNcard, hidx] at this
    omega
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  have hPcard : Nat.card (P : Subgroup Y) = 2 ^ n := by
    rw [Nat.card_congr eP.toEquiv, CFSG.Semidihedral.card n (by omega)]
  have hn : n = 4 := by
    have hdvd : Nat.card (P : Subgroup Y) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card _
    rw [hPcard, hYcard] at hdvd
    by_contra hne
    have h5 : 5 ≤ n := by omega
    have h32 : 2 ^ 5 ∣ 15600 := (pow_dvd_pow 2 h5).trans hdvd
    norm_num at h32
  subst hn
  have hSyl : ∀ S : Sylow 2 Y, Nonempty (CFSG.Open.SemidihedralGroup 4 ≃* S) := by
    intro S
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P S
    exact ⟨eP.symm.trans ((P.equivSMul g).trans (MulEquiv.subgroupCongr (by rw [hg])))⟩
  refine ⟨N, hN, hidx, ⟨eN⟩, ?_, hSyl⟩
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hcN : ∀ m ∈ N, m * c = c * m := Subgroup.mem_centralizer_iff.mp hc
  have hZ' : ∀ z ∈ N, (∀ m ∈ N, m * z = z * m) → z = 1 := by
    intro z hz hzc
    have h1 : (⟨z, hz⟩ : N) = 1 :=
      burnsideJ55_center_trivial eN ⟨z, hz⟩ (fun g => Subtype.ext (hzc g g.2))
    exact congrArg Subtype.val h1
  have hcnot : c ∉ N := fun hcm => hc1 (hZ' c hcm (fun m hm => hcN m hm))
  have hc2 : c ^ 2 = 1 := by
    apply hZ' _ (Subgroup.sq_mem_of_index_two hidx c)
    intro m hm
    rw [pow_two, ← mul_assoc, hcN m hm, mul_assoc, hcN m hm, ← mul_assoc]
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hcz : ∀ y : Y, y * c = c * y := by
    intro y
    by_cases hy : y ∈ N
    · exact hcN y hy
    · have hyc : y * c ∈ N :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hy hcnot)
      have h1 := hcN (y * c) hyc
      have h2 : y = c * y * c := by
        calc y = y * (c * c) := by rw [hcc, mul_one]
          _ = y * c * c := by rw [mul_assoc]
          _ = c * (y * c) := h1
          _ = c * y * c := by rw [mul_assoc]
      calc y * c = (c * y * c) * c := by rw [← h2]
        _ = c * y * (c * c) := by rw [mul_assoc (c * y) c c]
        _ = c * y := by rw [hcc, mul_one]
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  have hcpg : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q, hQ⟩ := hcpg.exists_le_sylow
  have hcQ : c ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers c)
  obtain ⟨eQ⟩ := hSyl Q
  have hc'central : eQ.symm ⟨c, hcQ⟩ ∈ Subgroup.center (CFSG.Open.SemidihedralGroup 4) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply eQ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcz _)
  rw [CFSG.Semidihedral.center_eq_zpowers 4 (by norm_num)] at hc'central
  have hz2 : CFSG.Semidihedral.z 4 ^ 2 = 1 := CFSG.Semidihedral.z_sq 4 (by norm_num)
  have hc'ne : eQ.symm ⟨c, hcQ⟩ ≠ 1 := by
    intro h1
    apply hc1
    have := congrArg eQ h1
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val this
  have hc'z : eQ.symm ⟨c, hcQ⟩ = CFSG.Semidihedral.z 4 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'central
    rw [← hk] at hc'ne ⊢
    rw [← zpow_mod_orderOf, CFSG.Semidihedral.orderOf_z 4 (by norm_num)] at hc'ne ⊢
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      apply hc'ne
      push_cast
      rw [h0, zpow_zero]
    · push_cast
      rw [h1, zpow_one]
  have hzsq : CFSG.Semidihedral.z 4 =
      (CFSG.Semidihedral.r 4 ^ 2) ^ 2 := by
    rw [← pow_mul]
    rfl
  have hcsq : c = ((eQ (CFSG.Semidihedral.r 4 ^ 2) : Q) : Y) ^ 2 := by
    have h1 : (⟨c, hcQ⟩ : Q) = eQ (CFSG.Semidihedral.z 4) := by
      rw [← hc'z, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [hzsq, map_pow] at h2
    exact h2
  exact hcnot (hcsq ▸ Subgroup.sq_mem_of_index_two hidx _)

section

private theorem burnsideJ55_two_f4 {Y : Type} [Group Y]
    (h : ChIJK.IsTwoF4TwoGroup Y) :
    Nonempty (Y ≃* CFSG.Sporadic.Schreier.Tits.titsA) := by
  obtain ⟨Y0, _, hY0, ⟨e⟩⟩ := h
  obtain ⟨e0⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y0 2 1 hY0
  exact ⟨e.trans ((MulAut.congr e0).trans CFSG.Sporadic.Schreier.Tits.titsConjEquiv.symm)⟩

private theorem burnsideJ55_toRT {G Ω : Type} [Group G] [MulAction G Ω]
    (h : ChIJK.IsRudvalisRank3 G Ω) : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω := by
  obtain ⟨hne, hfaith, htrans, hall⟩ := h
  refine ⟨burnsideJ55_faithful hfaith, hne, htrans, fun ω => (hall ω).1, fun ω => ?_,
    fun ω => ?_, fun ω => ?_⟩
  · exact burnsideJ55_two_f4 (hall ω).2.1
  · obtain ⟨δ, hpar, hcard⟩ := (hall ω).2.2.1
    refine ⟨δ, ?_, burnsideJ55_parabolic ω δ hpar⟩
    rw [Nat.card_congr (burnsideJ55_stabEquiv ω δ).toEquiv]
    exact hcard
  · obtain ⟨γ, hγ⟩ := (hall ω).2.2.2
    exact ⟨γ, CFSG.Quasithin.RuRank3.IsL225Plus.of_mulEquiv (burnsideJ55_stabEquiv ω γ).symm
      (burnsideJ55_isL225Plus hγ)⟩

end

private theorem burnsideJ55_mem_deltaAt_iff {G Ω : Type} [Group G] [MulAction G Ω] (ω δ ρ τ : Ω) :
    τ ∈ ChIJK.DeltaAt G ω δ ρ ↔ CFSG.Quasithin.RuRank3.orbAdj G ω δ ρ τ := by
  constructor
  · rintro ⟨g, hg1, f, hf⟩
    refine ⟨g * f, ?_, ?_⟩
    · rw [mul_smul, show (f : G) • ω = ω from f.2, hg1]
    · rw [mul_smul]
      have hf' : (f : G) • δ = g⁻¹ • τ := hf
      rw [hf', smul_inv_smul]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨g, hg1, ?_⟩
    rw [← hg2, inv_smul_smul]
    exact MulAction.mem_orbit_self δ

private theorem burnsideJ55_mem_sigmaAt_iff {G Ω : Type} [Group G] [MulAction G Ω] (ω γ ρ τ : Ω) :
    τ ∈ ChIJK.SigmaAt G ω γ ρ ↔ CFSG.Quasithin.RuRank3.orbAdj G ω γ ρ τ := by
  constructor
  · rintro ⟨g, hg1, f, hf⟩
    refine ⟨g * f, ?_, ?_⟩
    · rw [mul_smul, show (f : G) • ω = ω from f.2, hg1]
    · rw [mul_smul]
      have hf' : (f : G) • γ = g⁻¹ • τ := hf
      rw [hf', smul_inv_smul]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨g, hg1, ?_⟩
    rw [← hg2, inv_smul_smul]
    exact MulAction.mem_orbit_self γ

open scoped MatrixGroups in
private theorem burnsideJ55_card_psl25 [Fact (Nat.Prime 5)] : Nat.card PSL(2, GaloisField 5 2)
    = 7800 := by
  have := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := 5) (m := 2) (by norm_num)
    (by norm_num)
  rw [this]
  norm_num

open scoped MatrixGroups in
private theorem burnsideJ55_card_isL225Plus [Fact (Nat.Prime 5)] {Y : Type*} [Group Y]
    (h : CFSG.Quasithin.RuRank3.IsL225Plus Y) : Nat.card Y = 15600 := by
  obtain ⟨K, -, hidx, ⟨e⟩, -, -⟩ := h
  have hK : Nat.card K = 7800 := by
    rw [Nat.card_congr e.toEquiv]
    exact burnsideJ55_card_psl25
  have := Subgroup.card_mul_index K
  rw [hK, hidx] at this
  omega

end Copied

private theorem burnsideJ55_subgroupOf_inf_eq {G Ω : Type} [Group G] [MulAction G Ω] (H :
    Subgroup G)
    (x : Ω) : (H ⊓ MulAction.stabilizer G x).subgroupOf H = MulAction.stabilizer ↥H x := by
  ext f
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

private theorem burnsideJ55_card_inf_mul_orbit {G Ω : Type} [Group G] [MulAction G Ω] (H :
    Subgroup G)
    (x : Ω) :
    Nat.card ↥(H ⊓ MulAction.stabilizer G x) * (MulAction.orbit ↥H x).ncard = Nat.card ↥H := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥H x)
  rw [MulAction.index_stabilizer] at h1
  have h2 : Nat.card ↥(MulAction.stabilizer ↥H x) = Nat.card ↥(H ⊓ MulAction.stabilizer G x) := by
    rw [← burnsideJ55_subgroupOf_inf_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1

section Transport

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

structure burnsideJ55_Tr (G Ω : Type) [Group G] [MulAction G Ω] (ω δ : Ω) where
  Φ : Ω ≃ Fin 4060
  σ : G →* Equiv.Perm (Fin 4060)
  hω : Φ ω = 0
  hδ : Φ δ = 1
  hadj : ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y)
  hact : ∀ g z, Φ (g • z) = σ g (Φ z)
  hinj : Function.Injective σ
  hrange : σ.range = ruP

section

private theorem burnsideJ55_exists_Tr {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) : Nonempty (burnsideJ55_Tr G Ω ω δ) := by
  have hrt := burnsideJ55_toRT hS.rank3
  have hδ : Nat.card (MulAction.stabilizer (MulAction.stabilizer G ω) δ) = 2 ^ 12 * 5 := by
    rw [Nat.card_congr (burnsideJ55_stabEquiv ω δ).toEquiv]
    exact hS.rub.2
  obtain ⟨Φ₀, hΦ₀⟩ := hrt.exists_graph_equiv_of ω δ hδ
  have hadj0 : ruAdj (Φ₀ ω) (Φ₀ δ) := (hΦ₀ ω δ).1 ⟨1, one_smul _ _, one_smul _ _⟩
  obtain ⟨g₁, hg₁, hg₁0, hg₁1⟩ := hadj0
  let Φ : Ω ≃ Fin 4060 := Φ₀.trans (g₁⁻¹ : Equiv.Perm (Fin 4060))
  have hΦ : ∀ z, Φ z = g₁⁻¹ (Φ₀ z) := fun z => rfl
  have hadj : ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y) := by
    intro z y
    rw [hΦ, hΦ, ruAdj_apply (inv_mem hg₁), hΦ₀]
  obtain ⟨hinj, hrange⟩ := hrt.range_conj_eq hadj
  refine ⟨⟨Φ, (Equiv.permCongrHom Φ).toMonoidHom.comp (MulAction.toPermHom G Ω), ?_, ?_, hadj,
    fun g z => ?_, hinj, hrange⟩⟩
  · rw [hΦ, ← hg₁0, burnsideJ55_perm_inv_apply]
  · rw [hΦ, ← hg₁1, burnsideJ55_perm_inv_apply]
  · show Φ (g • z) = Φ (g • Φ.symm (Φ z))
    rw [Equiv.symm_apply_apply]

end

private theorem burnsideJ55_mem_orbit_subgroup_iff {G Ω : Type} [Group G] [MulAction G Ω] {H :
    Subgroup G} (x z : Ω) :
    z ∈ MulAction.orbit ↥H x ↔ ∃ f ∈ H, f • x = z := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

theorem burnsideJ55_Tr.σ_mem (g : G) : T.σ g ∈ ruP := by
  rw [← T.hrange]
  exact ⟨g, rfl⟩

theorem burnsideJ55_Tr.exists_σ_eq {p : Equiv.Perm (Fin 4060)} (hp : p ∈ ruP) : ∃ g,
    T.σ g = p := by
  rw [← T.hrange] at hp
  exact hp

theorem burnsideJ55_Tr.mem_stabilizer_iff (g : G) (x : Ω) :
    g ∈ MulAction.stabilizer G x ↔ T.σ g (T.Φ x) = T.Φ x := by
  rw [MulAction.mem_stabilizer_iff, ← T.Φ.injective.eq_iff, T.hact]

theorem burnsideJ55_Tr.exists_stab_iff (a x z : Ω) :
    (∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G a, f • x = z) ↔
      ∃ p ∈ ruR0, p (T.Φ a) = T.Φ a ∧ p (T.Φ x) = T.Φ z := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hf
    refine ⟨T.σ f, burnsideJ55_mem_ruR0.2 ⟨T.σ_mem f, ?_⟩, ?_, ?_⟩
    · rw [← T.hω, ← T.hact, hf.1]
    · rw [← T.hact, hf.2]
    · rw [← T.hact]
  · rintro ⟨p, hp, hpa, hpx⟩
    obtain ⟨hpP, hp0⟩ := burnsideJ55_mem_ruR0.1 hp
    obtain ⟨f, rfl⟩ := T.exists_σ_eq hpP
    refine ⟨f, ?_, T.Φ.injective ?_⟩
    · rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · apply T.Φ.injective
        rw [T.hact, T.hω, hp0]
      · apply T.Φ.injective
        rw [T.hact, hpa]
    · rw [T.hact, hpx]

theorem burnsideJ55_Tr.mem_deltaAt_iff (ρ τ : Ω) :
    τ ∈ ChIJK.DeltaAt G ω δ ρ ↔ ruAdj (T.Φ ρ) (T.Φ τ) := by
  rw [burnsideJ55_mem_deltaAt_iff, T.hadj]

section

theorem burnsideJ55_Tr.mem_sigmaAt_iff {γ : Ω} (hs : T.Φ γ ∈ ruS) (ρ τ : Ω) :
    τ ∈ ChIJK.SigmaAt G ω γ ρ ↔ (T.Φ ρ ≠ T.Φ τ ∧ ¬ ruAdj (T.Φ ρ) (T.Φ τ)) := by
  rw [burnsideJ55_mem_sigmaAt_iff, ← burnsideJ55_orbital_S hs]
  constructor
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨T.σ g, T.σ_mem g, ?_, ?_⟩
    · rw [← T.hω, ← T.hact, hg1]
    · rw [← T.hact, hg2]
  · rintro ⟨p, hp, hp1, hp2⟩
    obtain ⟨g, rfl⟩ := T.exists_σ_eq hp
    refine ⟨g, T.Φ.injective ?_, T.Φ.injective ?_⟩
    · rw [T.hact, T.hω, hp1]
    · rw [T.hact, hp2]

end

theorem burnsideJ55_Tr.mem_orbit_stab_iff (x z : Ω) :
    z ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) x ↔
      T.Φ z ∈ MulAction.orbit ruR0 (T.Φ x) := by
  rw [burnsideJ55_mem_orbit_subgroup_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟨T.σ f, burnsideJ55_mem_ruR0.2 ⟨T.σ_mem f, ?_⟩⟩, ?_⟩
    · rw [← T.hω, ← T.hact, (MulAction.mem_stabilizer_iff.1 hf)]
    · show T.σ f (T.Φ x) = T.Φ (f • x)
      rw [← T.hact]
  · rintro ⟨⟨p, hp⟩, hpx⟩
    obtain ⟨hpP, hp0⟩ := burnsideJ55_mem_ruR0.1 hp
    obtain ⟨f, rfl⟩ := T.exists_σ_eq hpP
    refine ⟨f, ?_, T.Φ.injective ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      apply T.Φ.injective
      rw [T.hact, T.hω, hp0]
    · rw [T.hact]
      exact hpx

end

end Transport

section Transport2

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

section

theorem burnsideJ55_Tr.gamma_mem_S {γ : Ω} (hS : ChIJK.RudvalisSetting G Ω ω δ γ) : T.Φ
    γ ∈ ruS := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrt := burnsideJ55_toRT hS.rank3
  obtain ⟨ψ⟩ := hrt.twoF4 ω
  have hFcard : Nat.card (MulAction.stabilizer G ω) = 35942400 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsA]
  have hγcard : Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) = 15600 :=
    burnsideJ55_card_isL225Plus (burnsideJ55_isL225Plus hS.ruc)
  have horb : (MulAction.orbit ↥(MulAction.stabilizer G ω) γ).ncard = 2304 := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer (MulAction.stabilizer G ω) γ)
    rw [MulAction.index_stabilizer, hFcard,
      Nat.card_congr (burnsideJ55_stabEquiv ω γ).toEquiv, hγcard] at h1
    omega
  have himg : T.Φ '' MulAction.orbit ↥(MulAction.stabilizer G ω) γ =
      MulAction.orbit ruR0 (T.Φ γ) := by
    ext n
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (T.mem_orbit_stab_iff γ z).1 hz
    · intro hn
      obtain ⟨z, rfl⟩ := T.Φ.surjective n
      exact ⟨z, (T.mem_orbit_stab_iff γ z).2 hn, rfl⟩
  have hn : (MulAction.orbit ruR0 (T.Φ γ)).ncard = 2304 := by
    rw [← himg, Set.ncard_image_of_injective _ T.Φ.injective, horb]
  by_cases h0 : T.Φ γ = 0
  · exfalso
    rw [h0, orbit_ruR0_zero, Set.ncard_singleton] at hn
    omega
  by_cases hD : T.Φ γ ∈ Set.range ruB
  · exfalso
    rw [orbit_ruR0_of_mem_range hD, Set.ncard_range_of_injective ruB_injective,
      Nat.card_eq_fintype_card, Fintype.card_fin] at hn
    omega
  exact ⟨h0, hD⟩

end

end

end Transport2

section Part1

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

private theorem burnsideJ55_part1 {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) :
    (ChIJK.DeltaAt G ω δ ω).ncard = 1755 ∧ (ChIJK.SigmaAt G ω γ ω).ncard = 2304 ∧
      (∀ ρ ∈ ChIJK.DeltaAt G ω δ ω,
        (ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ ρ).ncard = 730) ∧
      (∀ ρ ∈ ChIJK.SigmaAt G ω γ ω,
        (ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ ρ).ncard = 780) := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hS
  have hs := T.gamma_mem_S hS
  have hD : ∀ ρ, ChIJK.DeltaAt G ω δ ρ = {z | ruAdj (T.Φ ρ) (T.Φ z)} := fun ρ =>
    Set.ext fun τ => T.mem_deltaAt_iff ρ τ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD, T.hω]
    exact (ncard_setOf_equiv T.Φ fun n => ruAdj 0 n).trans (ncard_ruAdj 0)
  · have e : ChIJK.SigmaAt G ω γ ω = {z | (fun n : Fin 4060 => n ≠ 0 ∧ ¬ ruAdj 0 n) (T.Φ z)} := by
      ext τ
      rw [T.mem_sigmaAt_iff hs, T.hω]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
    rw [e]
    exact (ncard_setOf_equiv T.Φ _).trans (ncard_not_ruAdj 0)
  · intro ρ hρ
    rw [hD ρ, hD ω, T.hω] at *
    have hρ' : ruAdj 0 (T.Φ ρ) := hρ
    have e : {z | ruAdj 0 (T.Φ z)} ∩ {z | ruAdj (T.Φ ρ) (T.Φ z)} =
        {z | (fun n : Fin 4060 => ruAdj 0 n ∧ ruAdj (T.Φ ρ) n) (T.Φ z)} := rfl
    rw [e]
    exact (ncard_setOf_equiv T.Φ _).trans (ncard_common_of_ruAdj hρ')
  · intro ρ hρ
    have hρ' := (T.mem_sigmaAt_iff hs ω ρ).1 hρ
    rw [T.hω] at hρ'
    rw [hD ρ, hD ω, T.hω]
    have e : {z | ruAdj 0 (T.Φ z)} ∩ {z | ruAdj (T.Φ ρ) (T.Φ z)} =
        {z | (fun n : Fin 4060 => ruAdj 0 n ∧ ruAdj (T.Φ ρ) n) (T.Φ z)} := rfl
    rw [e]
    exact (ncard_setOf_equiv T.Φ _).trans (ncard_common_of_not_ruAdj hρ'.1 hρ'.2)

end

end Part1

section Part3

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

private theorem burnsideJ55_part3 {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) :
    ∃ a ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ,
      ∃ b ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ,
      ∃ c ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ,
      ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ =
        MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a ∪
          MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b ∪
          MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c ∧
      (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a).ncard = 10 ∧
      (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b).ncard = 80 ∧
      (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c).ncard = 640 ∧
      Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b) ∧
      Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a)
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c) ∧
      Disjoint (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b)
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c) := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hS
  obtain ⟨a', b', c', ha, hb, hc, hU, h10, h80, h640, d1, d2, d3⟩ := burnsideJ55_Fd_orbits
  have hO : ∀ x : Ω, MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) x =
      T.Φ ⁻¹' burnsideJ55_fdOrb (T.Φ x) := by
    intro x
    ext z
    rw [burnsideJ55_mem_orbit_subgroup_iff, T.exists_stab_iff δ x z, T.hδ]
    exact Iff.rfl
  have hpt : ∀ x' : Fin 4060, T.Φ (T.Φ.symm x') = x' := fun x' => T.Φ.apply_symm_apply x'
  have hC : ∀ z, z ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ ↔
      (ruAdj 0 (T.Φ z) ∧ ruAdj 1 (T.Φ z)) := by
    intro z
    rw [Set.mem_inter_iff, T.mem_deltaAt_iff, T.mem_deltaAt_iff, T.hω, T.hδ]
  have hmem : ∀ x' : Fin 4060, (ruAdj 0 x' ∧ ruAdj 1 x') →
      T.Φ.symm x' ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ δ := by
    intro x' hx'
    rw [hC, hpt]
    exact hx'
  have hncard : ∀ x' : Fin 4060, (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓
      MulAction.stabilizer G δ) (T.Φ.symm x')).ncard = (burnsideJ55_fdOrb x').ncard := by
    intro x'
    rw [hO, hpt, Set.ncard_preimage_of_injective_subset_range T.Φ.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]
  refine ⟨T.Φ.symm a', hmem a' ha, T.Φ.symm b', hmem b' hb, T.Φ.symm c', hmem c' hc, ?_,
    (hncard a').trans h10, (hncard b').trans h80, (hncard c').trans h640, ?_, ?_, ?_⟩
  · ext z
    rw [hC, hO, hO, hO, hpt, hpt, hpt, Set.mem_union, Set.mem_union, Set.mem_preimage,
      Set.mem_preimage, Set.mem_preimage]
    have := Set.ext_iff.1 hU (T.Φ z)
    rw [Set.mem_union, Set.mem_union] at this
    exact this
  · rw [hO, hO, hpt, hpt]
    exact d1.preimage _
  · rw [hO, hO, hpt, hpt]
    exact d2.preimage _
  · rw [hO, hO, hpt, hpt]
    exact d3.preimage _

end

end Part3

section Part4

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

private theorem burnsideJ55_part4 {G Ω : Type} [Group G] [Finite G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) :
    (ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ).ncard = 780 ∧
      (∀ σ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ,
        ∀ τ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
      (ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ).ncard = 975 ∧
      (∀ σ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ,
        ∀ τ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
      (∀ σ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ,
        Nonempty (↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
          MulAction.stabilizer G σ) ≃* CFSG.Open.Sz 0)) ∧
      (∀ τ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ,
        ChIJK.IsSylowTwoIn (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
          MulAction.stabilizer G τ) (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hS
  have hs := T.gamma_mem_S hS
  have hnadj : ¬ ruAdj 0 (T.Φ γ) := fun h => hs.2 ((ruAdj_zero_iff _).1 h)
  have hHcard : Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) = 15600 :=
    burnsideJ55_card_isL225Plus (burnsideJ55_isL225Plus hS.ruc)
  have hC : ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ =
      T.Φ ⁻¹' {n | ruAdj 0 n ∧ ruAdj (T.Φ γ) n} := by
    ext z
    rw [Set.mem_inter_iff, T.mem_deltaAt_iff, T.mem_deltaAt_iff, T.hω]
    rfl
  have hSig : ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ =
      T.Φ ⁻¹' {n | ruAdj 0 n ∧ ¬ ruAdj (T.Φ γ) n} := by
    ext z
    rw [Set.mem_inter_iff, T.mem_deltaAt_iff, T.mem_sigmaAt_iff hs, T.hω]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => hnadj (h ▸ h1), h2⟩
  have hOH : ∀ x : Ω, MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) x =
      T.Φ ⁻¹' burnsideJ55_orbSet (T.Φ γ) (T.Φ x) := by
    intro x
    ext z
    rw [burnsideJ55_mem_orbit_subgroup_iff, T.exists_stab_iff γ x z]
    exact Iff.rfl
  have hpre : ∀ B : Set (Fin 4060), (T.Φ ⁻¹' B).ncard = B.ncard := fun B =>
    Set.ncard_preimage_of_injective_subset_range T.Φ.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)
  have hn780 : {n | ruAdj 0 n ∧ ruAdj (T.Φ γ) n}.ncard = 780 :=
    ncard_common_of_not_ruAdj (fun h => hs.1 h.symm) hnadj
  have hn1755 : {n | ruAdj 0 n}.ncard = 1755 := ncard_ruAdj 0
  have hn975 : {n | ruAdj 0 n ∧ ¬ ruAdj (T.Φ γ) n}.ncard = 975 := by
    have e : {n | ruAdj 0 n ∧ ¬ ruAdj (T.Φ γ) n} =
        {n | ruAdj 0 n} \ {n | ruAdj 0 n ∧ ruAdj (T.Φ γ) n} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun _ => h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 h1⟩
    rw [e, Set.ncard_diff (fun n hn => hn.1) (Set.toFinite _), hn1755, hn780]
  have hOrb780 : ∀ σ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ,
      MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) σ =
        ChIJK.DeltaAt G ω δ ω ∩ ChIJK.DeltaAt G ω δ γ := by
    intro σ hσ
    rw [hC] at hσ ⊢
    rw [hOH]
    rw [burnsideJ55_orbSet_780 hs hσ.1 hσ.2]
  have hOrb975 : ∀ σ ∈ ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ,
      MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) σ =
        ChIJK.DeltaAt G ω δ ω ∩ ChIJK.SigmaAt G ω γ γ := by
    intro σ hσ
    rw [hSig] at hσ ⊢
    rw [hOH]
    rw [burnsideJ55_orbSet_D975 hs hσ.1 hσ.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, hpre, hn780]
  · intro σ hσ τ hτ
    have := hOrb780 σ hσ
    have hτ' : τ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) σ := by
      rw [this]; exact hτ
    exact (burnsideJ55_mem_orbit_subgroup_iff σ τ).1 hτ'
  · rw [hSig, hpre, hn975]
  · intro σ hσ τ hτ
    have := hOrb975 σ hσ
    have hτ' : τ ∈ MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) σ := by
      rw [this]; exact hτ
    exact (burnsideJ55_mem_orbit_subgroup_iff σ τ).1 hτ'
  ·
    intro σ hσ
    have hσ' := hσ
    rw [hC] at hσ'
    obtain ⟨hσ0, hσs⟩ := hσ'
    have hcardX : Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
        MulAction.stabilizer G σ) = 20 := by
      have h1 := burnsideJ55_card_inf_mul_orbit (MulAction.stabilizer G ω ⊓
        MulAction.stabilizer G γ) σ
      rw [hOrb780 σ hσ, hC, hpre, hn780, hHcard] at h1
      omega
    obtain ⟨a, b, haR, hbR, has, hay, hbs, hby, ha5, ha1, hb4, hb2, hba⟩ :=
      burnsideJ55_frob_elements hs hσ0 hσs
    obtain ⟨ga, hga⟩ := T.exists_σ_eq (ruR0_le_ruP haR)
    obtain ⟨gb, hgb⟩ := T.exists_σ_eq (ruR0_le_ruP hbR)
    have hmem : ∀ (g : G) (q : Equiv.Perm (Fin 4060)), T.σ g = q → q 0 = 0 → q (T.Φ γ) = T.Φ γ →
        q (T.Φ σ) = T.Φ σ →
        g ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓ MulAction.stabilizer G σ := by
      intro g q hq h0 h1 h2
      subst hq
      rw [Subgroup.mem_inf, Subgroup.mem_inf, T.mem_stabilizer_iff, T.mem_stabilizer_iff,
        T.mem_stabilizer_iff, T.hω]
      exact ⟨⟨h0, h1⟩, h2⟩
    have hamem := hmem ga a hga (burnsideJ55_mem_ruR0.1 haR).2 has hay
    have hbmem := hmem gb b hgb (burnsideJ55_mem_ruR0.1 hbR).2 hbs hby
    refine burnsideJ55_frob20 hcardX (a := ⟨ga, hamem⟩) (b := ⟨gb, hbmem⟩) ?_ ?_ ?_ ?_ ?_
    · apply Subtype.ext
      apply T.hinj
      simp [hga, ha5]
    · intro h
      apply ha1
      have := congrArg (fun z : ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
        MulAction.stabilizer G σ) => T.σ (z : G)) h
      simpa [hga] using this
    · apply Subtype.ext
      apply T.hinj
      simp [hgb, hb4]
    · intro h
      apply hb2
      have := congrArg (fun z : ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
        MulAction.stabilizer G σ) => T.σ (z : G)) h
      simpa [hgb] using this
    · apply Subtype.ext
      apply T.hinj
      simp [hga, hgb, hba]
  ·
    intro τ hτ
    have hτ' := hτ
    rw [hSig] at hτ'
    obtain ⟨hτ0, hτs⟩ := hτ'
    have h1 := burnsideJ55_card_inf_mul_orbit (MulAction.stabilizer G ω ⊓
      MulAction.stabilizer G γ) τ
    rw [hOrb975 τ hτ, hSig, hpre, hn975, hHcard] at h1
    have hcardQ : Nat.card ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ ⊓
        MulAction.stabilizer G τ) = 16 := by omega
    refine ⟨inf_le_left, IsPGroup.of_card (n := 4) (by rw [hcardQ]; norm_num), ?_⟩
    rw [burnsideJ55_subgroupOf_inf_eq, MulAction.index_stabilizer, hOrb975 τ hτ, hSig, hpre, hn975]
    norm_num

end

end Part4

section Part5

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

private theorem burnsideJ55_part5 {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) :
    (ChIJK.DeltaAt G ω δ γ ∩ ChIJK.SigmaAt G ω γ ω).ncard = 975 ∧
      (∀ σ ∈ ChIJK.DeltaAt G ω δ γ ∩ ChIJK.SigmaAt G ω γ ω,
        ∀ τ ∈ ChIJK.DeltaAt G ω δ γ ∩ ChIJK.SigmaAt G ω γ ω,
          ∃ f ∈ MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ, f • σ = τ) ∧
      ∀ ρ ∈ ChIJK.SigmaAt G ω γ ω,
        (MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ).ncard = 975 →
          MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) ρ =
            ChIJK.DeltaAt G ω δ γ ∩ ChIJK.SigmaAt G ω γ ω := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hS
  have hs := T.gamma_mem_S hS
  have hnadj : ¬ ruAdj 0 (T.Φ γ) := fun h => hs.2 ((ruAdj_zero_iff _).1 h)
  have hS' : ∀ n : Fin 4060, n ∈ ruS ↔ (n ≠ 0 ∧ ¬ ruAdj 0 n) := fun n => by
    show (n ≠ 0 ∧ n ∉ Set.range ruB) ↔ (n ≠ 0 ∧ ¬ ruAdj 0 n)
    rw [ruAdj_zero_iff]
  have hset : ChIJK.DeltaAt G ω δ γ ∩ ChIJK.SigmaAt G ω γ ω =
      T.Φ ⁻¹' {n | n ∈ ruS ∧ ruAdj (T.Φ γ) n} := by
    ext z
    rw [Set.mem_inter_iff, T.mem_deltaAt_iff, T.mem_sigmaAt_iff hs, T.hω]
    show ruAdj (T.Φ γ) (T.Φ z) ∧ (0 ≠ T.Φ z ∧ ¬ ruAdj 0 (T.Φ z)) ↔
      (T.Φ z ∈ ruS ∧ ruAdj (T.Φ γ) (T.Φ z))
    rw [hS']
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2.symm, h3⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩
      exact ⟨h1, h2.symm, h3⟩
  have hOH : ∀ x : Ω, MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ) x =
      T.Φ ⁻¹' burnsideJ55_orbSet (T.Φ γ) (T.Φ x) := by
    intro x
    ext z
    rw [burnsideJ55_mem_orbit_subgroup_iff, T.exists_stab_iff γ x z]
    exact Iff.rfl
  have hpre : ∀ B : Set (Fin 4060), (T.Φ ⁻¹' B).ncard = B.ncard := fun B =>
    Set.ncard_preimage_of_injective_subset_range T.Φ.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)
  have hn975 : {n | n ∈ ruS ∧ ruAdj (T.Φ γ) n}.ncard = 975 := by
    have e : {n | n ∈ ruS ∧ ruAdj (T.Φ γ) n} =
        {n | ruAdj (T.Φ γ) n} \ {n | ruAdj (T.Φ γ) n ∧ ruAdj 0 n} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_and, hS']
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h3, fun _ => h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, h2 h1⟩, h1⟩
        rintro rfl
        exact hnadj ((ruAdj_comm _ _).1 h1)
    have hsub : {n | ruAdj (T.Φ γ) n ∧ ruAdj 0 n} ⊆ {n | ruAdj (T.Φ γ) n} := fun n hn => hn.1
    have h780 : {n | ruAdj (T.Φ γ) n ∧ ruAdj 0 n}.ncard = 780 := by
      have e2 : {n | ruAdj (T.Φ γ) n ∧ ruAdj 0 n} = {n | ruAdj 0 n ∧ ruAdj (T.Φ γ) n} := by
        ext n
        exact and_comm
      rw [e2]
      exact ncard_common_of_not_ruAdj (fun h => hs.1 h.symm) hnadj
    rw [e, Set.ncard_diff hsub (Set.toFinite _), ncard_ruAdj, h780]
  refine ⟨?_, ?_, ?_⟩
  · rw [hset, hpre, hn975]
  · intro σ hσ τ hτ
    rw [hset] at hσ hτ
    obtain ⟨p, hp, hps, hpy⟩ := burnsideJ55_trans_S975 hs hσ.1 hσ.2 hτ.1 hτ.2
    exact (T.exists_stab_iff γ σ τ).2 ⟨p, hp, hps, hpy⟩
  · intro ρ hρ hcard
    have hρ' := (T.mem_sigmaAt_iff hs ω ρ).1 hρ
    rw [T.hω] at hρ'
    have hρS : T.Φ ρ ∈ ruS := (hS' _).2 ⟨hρ'.1.symm, hρ'.2⟩
    rw [hOH, hpre] at hcard
    rw [hOH, hset, burnsideJ55_unique_975 hs hρS hcard]

end

end Part5

end BurnsideJ55PartA

section J513Facts

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

private theorem burnsideJ55_mem_Delta_iff_orbit {G Ω : Type} [Group G] [MulAction G Ω] (ω δ x : Ω) :
    x ∈ ChIJK.DeltaAt G ω δ ω ↔ x ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) δ := by
  rw [burnsideJ55_mem_deltaAt_iff, orbAdj_base_iff]

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

theorem burnsideJ55_Tr.mem_Delta_iff (x : Ω) : x ∈ ChIJK.DeltaAt G ω δ ω ↔ ruAdj 0 (T.Φ
    x) := by
  rw [T.mem_deltaAt_iff, T.hω]

theorem burnsideJ55_Tr.orbit_stabF_eq (τ x : Ω) :
    MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) x =
      T.Φ ⁻¹' burnsideJ55_orbSet (T.Φ τ) (T.Φ x) := by
  ext z
  rw [burnsideJ55_mem_orbit_subgroup_iff, Set.mem_preimage]
  have h := T.exists_stab_iff τ x z
  show _ ↔ ∃ p ∈ ruR0, p (T.Φ τ) = T.Φ τ ∧ p (T.Φ x) = T.Φ z
  rw [← h]
  constructor
  · rintro ⟨hh, hhm, rfl⟩
    exact ⟨(hh : G), Subgroup.mem_inf.2 ⟨hh.2, MulAction.mem_stabilizer_iff.1 hhm⟩, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.1 hf
    exact ⟨⟨f, hf1⟩, MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 hf2), rfl⟩

section

theorem burnsideJ55_Tr.adj_iff (x y : Ω) :
    (ChIJK.omegaGraph G ω δ).Adj x y ↔ ruAdj (T.Φ x) (T.Φ y) := by
  unfold ChIJK.omegaGraph
  rw [SimpleGraph.fromRel_adj, T.mem_deltaAt_iff, T.mem_deltaAt_iff]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact ruAdj_symm h
  · intro h
    refine ⟨fun hxy => ?_, Or.inl h⟩
    subst hxy
    exact not_ruAdj_self _ h

end

theorem burnsideJ55_Tr.adj_Delta_Delta {γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ ChIJK.FdOf G ω δ}
    (hRB : ChIJK.RuBuilding G Ω ω δ γ M2 φ) {a b : Ω}
    (ha : ruAdj 0 (T.Φ a)) (hb : ruAdj 0 (T.Φ b)) :
    ruAdj (T.Φ a) (T.Φ b) ↔
      (φ a ≠ φ b ∧
        (ChIJK.incGraph (ChIJK.FdOf G ω δ) M2).Reachable (Sum.inl (φ a)) (Sum.inl (φ b)) ∧
        (ChIJK.incGraph (ChIJK.FdOf G ω δ) M2).dist (Sum.inl (φ a)) (Sum.inl (φ b)) ≤ 6) := by
  have hδmem : δ ∈ ChIJK.DeltaAt G ω δ ω :=
    (T.mem_Delta_iff δ).2 (by rw [T.hδ]; exact ⟨1, one_mem _, rfl, rfl⟩)
  have haΔ : a ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) δ :=
    (burnsideJ55_mem_Delta_iff_orbit ω δ a).1 ((T.mem_Delta_iff a).2 ha)
  have hbΔ : b ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) δ :=
    (burnsideJ55_mem_Delta_iff_orbit ω δ b).1 ((T.mem_Delta_iff b).2 hb)
  obtain ⟨f, hf0⟩ := haΔ
  have hf : f • δ = a := hf0
  subst hf
  have hfb : f⁻¹ • b ∈ ChIJK.DeltaAt G ω δ ω := by
    rw [burnsideJ55_mem_Delta_iff_orbit]
    obtain ⟨g, hg0⟩ := hbΔ
    have hg : g • δ = b := hg0
    subst hg
    exact ⟨f⁻¹ * g, by show (f⁻¹ * g) • δ = f⁻¹ • g • δ; rw [mul_smul]⟩
  have hφa : φ (f • δ) = f • φ δ := hRB.equivariant f δ hδmem
  have hφb : φ (f⁻¹ • b) = f⁻¹ • φ b := by
    have hb' : b ∈ ChIJK.DeltaAt G ω δ ω := (T.mem_Delta_iff b).2 hb
    have := hRB.equivariant f⁻¹ b hb'
    exact this
  have key : ruAdj (T.Φ (f • δ)) (T.Φ b) ↔ f⁻¹ • b ∈ ChIJK.DeltaAt G ω δ δ := by
    rw [← T.hadj, burnsideJ55_mem_deltaAt_iff, ← orbAdj_smul ((f⁻¹ : ↥(MulAction.stabilizer G ω)) :
      G) ω δ]
    have e1 : ((f⁻¹ : ↥(MulAction.stabilizer G ω)) : G) • (f • δ) = δ := by
      show ((f⁻¹ : ↥(MulAction.stabilizer G ω)) : G) • ((f : G) • δ) = δ
      rw [smul_smul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, one_smul]
    have e2 : ((f⁻¹ : ↥(MulAction.stabilizer G ω)) : G) • b = f⁻¹ • b := rfl
    rw [e1, e2]
  rw [key, hRB.nbhd _ hfb, hφb, hRB.base]
  have e3 : ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸ ChIJK.FdOf G ω δ) =
      f⁻¹ • φ (f • δ) := by
    rw [hφa, hRB.base, inv_smul_smul]
  rw [e3, burnsideJ55_inc_dist_smul, ← burnsideJ55_inc_dist_lt_eight_iff]

section

theorem burnsideJ55_Tr.adj_Delta_Sigma {γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ ChIJK.FdOf G ω δ}
    (hRB : ChIJK.RuBuilding G Ω ω δ γ M2 φ) {a τ : Ω}
    (ha : ruAdj 0 (T.Φ a)) (hτ : T.Φ τ ∈ ruS) :
    ruAdj (T.Φ a) (T.Φ τ) ↔
      (MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) (φ a)).ncard = 780 := by
  have haD : a ∈ ChIJK.DeltaAt G ω δ ω := (T.mem_Delta_iff a).2 ha
  have hsub : MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) a ⊆
      ChIJK.DeltaAt G ω δ ω := by
    rintro z ⟨h, rfl⟩
    rw [burnsideJ55_mem_Delta_iff_orbit]
    obtain ⟨g, hg0⟩ := (burnsideJ55_mem_Delta_iff_orbit ω δ a).1 haD
    have hg : g • δ = a := hg0
    subst hg
    exact ⟨(h : ↥(MulAction.stabilizer G ω)) * g, by
      show ((h : ↥(MulAction.stabilizer G ω)) * g) • δ = (h : ↥(MulAction.stabilizer G ω)) • g • δ
      rw [mul_smul]⟩
  have himg : φ '' MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) a =
      MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) (φ a) := by
    ext w
    constructor
    · rintro ⟨z, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, (hRB.equivariant (h : ↥(MulAction.stabilizer G ω)) a haD).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h • a, ⟨h, rfl⟩, hRB.equivariant (h : ↥(MulAction.stabilizer G ω)) a haD⟩
  have hn : (MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) τ) (φ a)).ncard =
      (burnsideJ55_orbSet (T.Φ τ) (T.Φ a)).ncard := by
    rw [← himg, Set.InjOn.ncard_image (hRB.bij.injOn.mono hsub), T.orbit_stabF_eq,
      Set.ncard_preimage_of_injective_subset_range T.Φ.injective
        (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]
  rw [hn, burnsideJ55_ncard_orbSet_D hτ ha]
  exact ⟨ruAdj_symm, ruAdj_symm⟩

theorem burnsideJ55_Tr.adj_Sigma_Sigma {E : Subgroup ↥(MulAction.stabilizer G ω)}
    (V : ↥(MulAction.stabilizer G ω) ⧸ E → Ω) (hVinj : Function.Injective V)
    (hVeq : ∀ (g : ↥(MulAction.stabilizer G ω)) v, V (g • v) = g • V v)
    (hVmem : ∀ v, T.Φ (V v) ∈ ruS) (v w : ↥(MulAction.stabilizer G ω) ⧸ E) :
    ruAdj (T.Φ (V v)) (T.Φ (V w)) ↔
      (v ≠ w ∧ ((MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) v) w).ncard =
          975 ∨
        (MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) w) v).ncard = 975)) := by
  have hstab : ∀ v : ↥(MulAction.stabilizer G ω) ⧸ E,
      MulAction.stabilizer ↥(MulAction.stabilizer G ω) v =
        MulAction.stabilizer ↥(MulAction.stabilizer G ω) (V v) := by
    intro v
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← hVinj.eq_iff, hVeq]
  have hcard : ∀ v w : ↥(MulAction.stabilizer G ω) ⧸ E,
      (MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) v) w).ncard =
        (burnsideJ55_orbSet (T.Φ (V v)) (T.Φ (V w))).ncard := by
    intro v w
    have himg : V '' MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) v) w =
        MulAction.orbit ↥(MulAction.stabilizer ↥(MulAction.stabilizer G ω) (V v)) (V w) := by
      rw [← hstab v]
      ext z
      constructor
      · rintro ⟨y, ⟨h, rfl⟩, rfl⟩
        exact ⟨h, (hVeq (h : ↥(MulAction.stabilizer G ω)) w).symm⟩
      · rintro ⟨h, rfl⟩
        exact ⟨h • w, ⟨h, rfl⟩, hVeq (h : ↥(MulAction.stabilizer G ω)) w⟩
    rw [← Set.ncard_image_of_injective _ hVinj, himg, T.orbit_stabF_eq,
      Set.ncard_preimage_of_injective_subset_range T.Φ.injective
        (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]
  rw [hcard v w, hcard w v, burnsideJ55_ncard_orbSet_S (hVmem v) (hVmem w),
    burnsideJ55_ncard_orbSet_S (hVmem w) (hVmem v)]
  constructor
  · intro h
    refine ⟨fun hvw => not_ruAdj_self _ (by subst hvw; exact h), Or.inl h⟩
  · rintro ⟨-, h | h⟩
    · exact h
    · exact ruAdj_symm h

end

end

end J513Facts

section OmegaPrimeAdj

variable {F : Type} [Group F] (M1 M2 E : Subgroup F)

private theorem burnsideJ55_OP_none_inl (u : F ⧸ M1) :
    (ChIJK.OmegaPrime F M1 M2 E).Adj none (some (Sum.inl u)) := by
  unfold ChIJK.OmegaPrime
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl (Or.inl ⟨u, rfl, rfl⟩)⟩

private theorem burnsideJ55_OP_none_inr (v : F ⧸ E) :
    ¬ (ChIJK.OmegaPrime F M1 M2 E).Adj none (some (Sum.inr v)) := by
  unfold ChIJK.OmegaPrime
  rw [SimpleGraph.fromRel_adj]
  simp

private theorem burnsideJ55_OP_inr_none (v : F ⧸ E) :
    ¬ (ChIJK.OmegaPrime F M1 M2 E).Adj (some (Sum.inr v)) none := fun h =>
  burnsideJ55_OP_none_inr M1 M2 E v h.symm

private theorem burnsideJ55_OP_none_none : ¬ (ChIJK.OmegaPrime F M1 M2 E).Adj none none :=
  fun h => h.ne rfl

private theorem burnsideJ55_OP_inl_inl (u v : F ⧸ M1) :
    (ChIJK.OmegaPrime F M1 M2 E).Adj (some (Sum.inl u)) (some (Sum.inl v)) ↔
      (u ≠ v ∧ (ChIJK.incGraph M1 M2).Reachable (Sum.inl u) (Sum.inl v) ∧
        (ChIJK.incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) ≤ 6) := by
  unfold ChIJK.OmegaPrime
  rw [SimpleGraph.fromRel_adj]
  simp
  intro _ hr hd
  exact ⟨hr.symm, by rw [SimpleGraph.dist_comm]; exact hd⟩

private theorem burnsideJ55_OP_inl_inr (u : F ⧸ M1) (v : F ⧸ E) :
    (ChIJK.OmegaPrime F M1 M2 E).Adj (some (Sum.inl u)) (some (Sum.inr v)) ↔
      (MulAction.orbit ↥(MulAction.stabilizer F v) u).ncard = 780 := by
  unfold ChIJK.OmegaPrime
  rw [SimpleGraph.fromRel_adj]
  simp

private theorem burnsideJ55_OP_inr_inl (v : F ⧸ E) (u : F ⧸ M1) :
    (ChIJK.OmegaPrime F M1 M2 E).Adj (some (Sum.inr v)) (some (Sum.inl u)) ↔
      (MulAction.orbit ↥(MulAction.stabilizer F v) u).ncard = 780 := by
  rw [SimpleGraph.adj_comm, burnsideJ55_OP_inl_inr]

private theorem burnsideJ55_OP_inr_inr (v w : F ⧸ E) :
    (ChIJK.OmegaPrime F M1 M2 E).Adj (some (Sum.inr v)) (some (Sum.inr w)) ↔
      (v ≠ w ∧ ((MulAction.orbit ↥(MulAction.stabilizer F v) w).ncard = 975 ∨
        (MulAction.orbit ↥(MulAction.stabilizer F w) v).ncard = 975)) := by
  unfold ChIJK.OmegaPrime
  rw [SimpleGraph.fromRel_adj]
  simp

end OmegaPrimeAdj

private theorem burnsideJ55_stab_V {F Ω : Type} [Group F] [MulAction F Ω] {E : Subgroup F}
    (V : F ⧸ E → Ω) (hVinj : Function.Injective V) (hVeq : ∀ (g : F) v, V (g • v) = g • V v)
    (v : F ⧸ E) : MulAction.stabilizer F v = MulAction.stabilizer F (V v) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← hVinj.eq_iff, hVeq]

private theorem burnsideJ55_exists_V {F Ω : Type} [Group F] [MulAction F Ω] (γ : Ω) (E : Subgroup F)
    (hE : E = MulAction.stabilizer F γ) :
    ∃ V : F ⧸ E → Ω, Function.Injective V ∧ (∀ v, V v ∈ MulAction.orbit F γ) ∧
      (∀ x ∈ MulAction.orbit F γ, ∃ v, V v = x) ∧ (∀ (g : F) v, V (g • v) = g • V v) := by
  subst hE
  refine ⟨fun v => ((MulAction.orbitEquivQuotientStabilizer F γ).symm v : Ω), ?_, ?_, ?_, ?_⟩
  · intro v w h
    exact (MulAction.orbitEquivQuotientStabilizer F γ).symm.injective (Subtype.ext h)
  · intro v
    exact ((MulAction.orbitEquivQuotientStabilizer F γ).symm v).2
  · intro x hx
    exact ⟨MulAction.orbitEquivQuotientStabilizer F γ ⟨x, hx⟩, by simp⟩
  · intro g v
    induction v using QuotientGroup.induction_on with
    | H f =>
      show ((MulAction.orbitEquivQuotientStabilizer F γ).symm ((g * f : F) : F ⧸ _) : Ω) =
        g • ((MulAction.orbitEquivQuotientStabilizer F γ).symm (f : F ⧸ _) : Ω)
      rw [MulAction.orbitEquivQuotientStabilizer_symm_apply,
        MulAction.orbitEquivQuotientStabilizer_symm_apply, mul_smul]

private theorem burnsideJ55_graph_assembly {Ω P Q : Type} (A : SimpleGraph Ω)
    (B : SimpleGraph (Option (P ⊕ Q))) (Θ : Option (P ⊕ Q) → Ω) (hΘ : Function.Bijective Θ)
    (hadj : ∀ o₁ o₂, B.Adj o₁ o₂ ↔ A.Adj (Θ o₁) (Θ o₂)) : Nonempty (A ≃g B) :=
  ⟨⟨(Equiv.ofBijective Θ hΘ).symm, fun {a b} => by
    rw [hadj]
    show A.Adj ((Equiv.ofBijective Θ hΘ) ((Equiv.ofBijective Θ hΘ).symm a))
      ((Equiv.ofBijective Θ hΘ) ((Equiv.ofBijective Θ hΘ).symm b)) ↔ A.Adj a b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩⟩

section J513Main

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

private theorem burnsideJ55_J513 {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ ChIJK.FdOf G ω δ}
    (hRB : ChIJK.RuBuilding G Ω ω δ γ M2 φ) :
    Nonempty (ChIJK.omegaGraph G ω δ ≃g
      ChIJK.OmegaPrime ↥(MulAction.stabilizer G ω) (ChIJK.FdOf G ω δ) M2
        ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ).subgroupOf
          (MulAction.stabilizer G ω))) := by
  classical
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hRB.setting
  have hs := T.gamma_mem_S hRB.setting
  obtain ⟨V, hVinj, hVmem, hVsurj, hVeq⟩ := burnsideJ55_exists_V (F := ↥(MulAction.stabilizer G ω))
    γ ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ).subgroupOf (MulAction.stabilizer G ω))
    (burnsideJ55_subgroupOf_inf_eq (MulAction.stabilizer G ω) γ)
  have hOrb : ∀ x, x ∈ MulAction.orbit ↥(MulAction.stabilizer G ω) γ ↔ T.Φ x ∈ ruS := by
    intro x
    rw [T.mem_orbit_stab_iff γ x, orbit_ruR0_of_mem_ruS hs]
  have hVS : ∀ v, T.Φ (V v) ∈ ruS := fun v => (hOrb _).1 (hVmem v)
  haveI : Nonempty Ω := ⟨ω⟩
  have hDl : ∀ u, Function.invFunOn φ (ChIJK.DeltaAt G ω δ ω) u ∈ ChIJK.DeltaAt G ω δ ω ∧
      φ (Function.invFunOn φ (ChIJK.DeltaAt G ω δ ω) u) = u := fun u =>
    Function.invFunOn_pos (hRB.bij.surjOn (Set.mem_univ u))
  have hDladj : ∀ u, ruAdj 0 (T.Φ (Function.invFunOn φ (ChIJK.DeltaAt G ω δ ω) u)) := fun u =>
    (T.mem_Delta_iff _).1 (hDl u).1
  obtain ⟨Θ, hΘ0, hΘl, hΘr⟩ : ∃ Θ : Option (↥(MulAction.stabilizer G ω) ⧸ ChIJK.FdOf G ω δ ⊕
      ↥(MulAction.stabilizer G ω) ⧸ ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ).subgroupOf
        (MulAction.stabilizer G ω))) → Ω,
      Θ none = ω ∧ (∀ u, Θ (some (Sum.inl u)) = Function.invFunOn φ (ChIJK.DeltaAt G ω δ ω) u) ∧
        (∀ v, Θ (some (Sum.inr v)) = V v) :=
    ⟨fun o => match o with
      | none => ω
      | some (Sum.inl u) => Function.invFunOn φ (ChIJK.DeltaAt G ω δ ω) u
      | some (Sum.inr v) => V v, rfl, fun _ => rfl, fun _ => rfl⟩
  have hΦ0 : T.Φ ω = 0 := T.hω
  have hnoneΔ : ¬ ruAdj 0 (T.Φ ω) := by rw [hΦ0]; exact not_ruAdj_self 0
  have hnoneS : T.Φ ω ∉ ruS := by rw [hΦ0]; exact fun h => h.1 rfl
  have hΔS : ∀ x, ruAdj 0 (T.Φ x) → T.Φ x ∉ ruS := fun x hx hxS =>
    hxS.2 ((ruAdj_zero_iff _).1 hx)
  have hbij : Function.Bijective Θ := by
    constructor
    · rintro (_ | u | v) (_ | u' | v') h
      · rfl
      · rw [hΘ0, hΘl] at h
        have h1 := hDladj u'
        rw [← h] at h1
        exact absurd h1 hnoneΔ
      · rw [hΘ0, hΘr] at h
        have h1 := hVS v'
        rw [← h] at h1
        exact absurd h1 hnoneS
      · rw [hΘl, hΘ0] at h
        have h1 := hDladj u
        rw [h] at h1
        exact absurd h1 hnoneΔ
      · rw [hΘl, hΘl] at h
        have := congrArg φ h
        rw [(hDl u).2, (hDl u').2] at this
        rw [this]
      · rw [hΘl, hΘr] at h
        have h1 := hVS v'
        rw [← h] at h1
        exact absurd h1 (hΔS _ (hDladj u))
      · rw [hΘr, hΘ0] at h
        have h1 := hVS v
        rw [h] at h1
        exact absurd h1 hnoneS
      · rw [hΘr, hΘl] at h
        have h1 := hVS v
        rw [h] at h1
        exact absurd h1 (hΔS _ (hDladj u'))
      · rw [hΘr, hΘr] at h
        rw [hVinj h]
    · intro x
      by_cases h0 : T.Φ x = 0
      · exact ⟨none, by rw [hΘ0]; exact T.Φ.injective (by rw [hΦ0, h0])⟩
      by_cases hD : ruAdj 0 (T.Φ x)
      · refine ⟨some (Sum.inl (φ x)), ?_⟩
        rw [hΘl]
        have hx : x ∈ ChIJK.DeltaAt G ω δ ω := (T.mem_Delta_iff x).2 hD
        exact hRB.bij.injOn (hDl _).1 hx (hDl _).2
      · have hxS : T.Φ x ∈ ruS := ⟨h0, fun h => hD ((ruAdj_zero_iff _).2 h)⟩
        obtain ⟨v, hv⟩ := hVsurj x ((hOrb x).2 hxS)
        exact ⟨some (Sum.inr v), by rw [hΘr]; exact hv⟩
  refine burnsideJ55_graph_assembly _ _ Θ hbij ?_
  rintro (_ | u | v) (_ | u' | v')
  ·
    rw [hΘ0, T.adj_iff]
    exact iff_of_false (burnsideJ55_OP_none_none _ _ _) (not_ruAdj_self _)
  ·
    rw [hΘ0, hΘl, T.adj_iff, hΦ0]
    exact iff_of_true (burnsideJ55_OP_none_inl _ _ _ _) (hDladj u')
  ·
    rw [hΘ0, hΘr, T.adj_iff, hΦ0]
    exact iff_of_false (burnsideJ55_OP_none_inr _ _ _ _)
      (burnsideJ55_not_adj_of_mem_S (hVS v'))
  ·
    rw [hΘl, hΘ0, T.adj_iff, hΦ0]
    exact iff_of_true (burnsideJ55_OP_none_inl _ _ _ _).symm (ruAdj_symm (hDladj u))
  ·
    rw [hΘl, hΘl, T.adj_iff, burnsideJ55_OP_inl_inl,
      T.adj_Delta_Delta hRB (hDladj u) (hDladj u'), (hDl u).2, (hDl u').2]
  ·
    rw [hΘl, hΘr, T.adj_iff, burnsideJ55_OP_inl_inr,
      T.adj_Delta_Sigma hRB (hDladj u) (hVS v'), (hDl u).2,
      burnsideJ55_stab_V V hVinj hVeq v']
  ·
    rw [hΘr, hΘ0, T.adj_iff, hΦ0]
    exact iff_of_false (burnsideJ55_OP_inr_none _ _ _ _)
      (fun h => burnsideJ55_not_adj_of_mem_S (hVS v) (ruAdj_symm h))
  ·
    rw [hΘr, hΘl, T.adj_iff, ruAdj_comm (T.Φ (V v)), burnsideJ55_OP_inr_inl,
      T.adj_Delta_Sigma hRB (hDladj u') (hVS v), (hDl u').2,
      burnsideJ55_stab_V V hVinj hVeq v]
  ·
    rw [hΘr, hΘr, T.adj_iff, burnsideJ55_OP_inr_inr, T.adj_Sigma_Sigma V hVinj hVeq hVS]

end

end J513Main

section Octagon

variable {Y : Type} [Group Y] {X : Type} [MulAction Y X]

@[expose] def burnsideJ55_ballStep (Γ : X → X → Prop) (S : Set X) : Set X :=
  S ∪ {q | ∃ p ∈ S, Γ p q}

private theorem burnsideJ55_ballStep_subset (Γ : X → X → Prop) (S : Set X) :
    S ⊆ burnsideJ55_ballStep Γ S := Set.subset_union_left

private theorem burnsideJ55_ballStep_iterate_mono (Γ : X → X → Prop) (S : Set X) {k k' : ℕ}
    (h : k ≤ k') : (burnsideJ55_ballStep Γ)^[k] S ⊆ (burnsideJ55_ballStep Γ)^[k'] S := by
  induction k', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k' _ ih =>
    refine ih.trans ?_
    rw [Function.iterate_succ_apply']
    exact burnsideJ55_ballStep_subset Γ _

private theorem burnsideJ55_two_walk (M1 M2 : Subgroup Y) (a b : Y ⧸ M1) (y₁ y₂ : Y)
    (ha : a = (y₁ : Y ⧸ M1)) (hb : b = (y₂ : Y ⧸ M1)) (h : y₁⁻¹ * y₂ ∈ M2) :
    ∃ p : (ChIJK.incGraph M1 M2).Walk (Sum.inl a) (Sum.inl b), p.length = 2 := by
  have h1 : (ChIJK.incGraph M1 M2).Adj (Sum.inl a) (Sum.inr ((y₁ : Y) : Y ⧸ M2)) :=
    (burnsideJ55_inc_adj_inl_inr M1 M2 _ _).2 ⟨y₁, ha, rfl⟩
  have h2 : (ChIJK.incGraph M1 M2).Adj (Sum.inr ((y₁ : Y) : Y ⧸ M2)) (Sum.inl b) := by
    rw [SimpleGraph.adj_comm, burnsideJ55_inc_adj_inl_inr]
    exact ⟨y₂, hb, by rw [QuotientGroup.eq]; exact h⟩
  exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil), rfl⟩

private theorem burnsideJ55_octagon_ball_walk (x₀ : X) (M1 M2 : Subgroup Y)
    (hM1 : ∀ y, y ∈ M1 ↔ y • x₀ = x₀) (Γ : X → X → Prop)
    (hinv : ∀ (y : Y) a b, Γ (y • a) (y • b) ↔ Γ a b) (m₀ : Y) (hm₀ : m₀ ∈ M2)
    (hm₀Γ : Γ x₀ (m₀ • x₀)) (h3 : ∀ a b, Γ x₀ a → Γ x₀ b → ∃ f ∈ M1, f • a = b) :
    ∀ (k : ℕ) (q : X), q ∈ (burnsideJ55_ballStep Γ)^[k] {x₀} →
      ∃ (y : Y) (p : (ChIJK.incGraph M1 M2).Walk (Sum.inl ((1 : Y) : Y ⧸ M1))
        (Sum.inl (y : Y ⧸ M1))), y • x₀ = q ∧ p.length ≤ 2 * k := by
  intro k
  induction k with
  | zero =>
    intro q hq
    have hq' : q = x₀ := hq
    exact ⟨1, SimpleGraph.Walk.nil, by rw [hq', one_smul], by simp⟩
  | succ k ih =>
    intro q hq
    rw [Function.iterate_succ_apply'] at hq
    rcases hq with hq | ⟨p', hp', hΓ⟩
    · obtain ⟨y, p, hy, hl⟩ := ih q hq
      exact ⟨y, p, hy, by omega⟩
    · obtain ⟨y₁, w₁, hy₁, hl₁⟩ := ih p' hp'
      have hΓ' : Γ x₀ (y₁⁻¹ • q) := by
        have := (hinv y₁⁻¹ (y₁ • x₀) q).2 (by rw [hy₁]; exact hΓ)
        rwa [inv_smul_smul] at this
      obtain ⟨f, hf, hfq⟩ := h3 _ _ hm₀Γ hΓ'
      obtain ⟨p2, hp2⟩ := burnsideJ55_two_walk M1 M2 (y₁ : Y ⧸ M1)
        ((y₁ * f * m₀ : Y) : Y ⧸ M1) (y₁ * f) (y₁ * f * m₀)
        (by rw [QuotientGroup.eq]; simpa using hf) rfl
        (by
          have e : (y₁ * f)⁻¹ * (y₁ * f * m₀) = m₀ := by group
          rw [e]
          exact hm₀)
      refine ⟨y₁ * f * m₀, w₁.append p2, ?_, ?_⟩
      · rw [mul_smul, mul_smul, hfq, smul_inv_smul]
      · rw [SimpleGraph.Walk.length_append, hp2]
        omega

private theorem burnsideJ55_coset_smul_eq (x₀ : X) (M1 : Subgroup Y) (hM1 : ∀ y, y ∈ M1 ↔ y •
    x₀ = x₀)
    {a b : Y} (h : (a : Y ⧸ M1) = (b : Y ⧸ M1)) : a • x₀ = b • x₀ := by
  rw [QuotientGroup.eq] at h
  have := (hM1 _).1 h
  rw [mul_smul, inv_smul_eq_iff] at this
  exact this.symm

private theorem burnsideJ55_octagon_walk_ball (x₀ : X) (M1 M2 : Subgroup Y)
    (hM1 : ∀ y, y ∈ M1 ↔ y • x₀ = x₀) (Γ : X → X → Prop)
    (hinv : ∀ (y : Y) a b, Γ (y • a) (y • b) ↔ Γ a b)
    (h1 : ∀ m ∈ M2, m • x₀ = x₀ ∨ Γ x₀ (m • x₀)) {y : Y}
    (p : (ChIJK.incGraph M1 M2).Walk (Sum.inl ((1 : Y) : Y ⧸ M1)) (Sum.inl (y : Y ⧸ M1)))
    (hp : Even p.length) :
    y • x₀ ∈ (burnsideJ55_ballStep Γ)^[p.length / 2] {x₀} := by
  have key : ∀ i : ℕ, 2 * i ≤ p.length → ∃ z : Y, p.getVert (2 * i) = Sum.inl (z : Y ⧸ M1) ∧
      z • x₀ ∈ (burnsideJ55_ballStep Γ)^[i] {x₀} := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, ?_, ?_⟩
      · simp
      · show (1 : Y) • x₀ = x₀
        rw [one_smul]
    | succ i ih =>
      intro hi
      obtain ⟨z, hz, hzB⟩ := ih (by omega)
      have hadj1 := p.adj_getVert_succ (i := 2 * i) (by omega)
      have hadj2 := p.adj_getVert_succ (i := 2 * i + 1) (by omega)
      rw [hz] at hadj1
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Y ⧸ M2, p.getVert (2 * i + 1) = Sum.inr ℓ := by
        generalize p.getVert (2 * i + 1) = w at hadj1
        rcases w with w | w
        · exact absurd hadj1 (burnsideJ55_inc_not_adj_inl_inl M1 M2 _ _)
        · exact ⟨w, rfl⟩
      rw [hℓ] at hadj1 hadj2
      obtain ⟨b, hb⟩ : ∃ b : Y ⧸ M1, p.getVert (2 * i + 1 + 1) = Sum.inl b := by
        generalize p.getVert (2 * i + 1 + 1) = w at hadj2
        rcases w with w | w
        · exact ⟨w, rfl⟩
        · exact absurd hadj2 (burnsideJ55_inc_not_adj_inr_inr M1 M2 _ _)
      rw [hb] at hadj2
      obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨y₁, hy₁, hℓ1⟩ := (burnsideJ55_inc_adj_inl_inr M1 M2 _ _).1 hadj1
      obtain ⟨y₂, hy₂, hℓ2⟩ := (burnsideJ55_inc_adj_inl_inr M1 M2 _ _).1 hadj2.symm
      have hm : y₁⁻¹ * y₂ ∈ M2 := QuotientGroup.eq.1 (hℓ1.symm.trans hℓ2)
      have hzx : z • x₀ = y₁ • x₀ := burnsideJ55_coset_smul_eq x₀ M1 hM1 hy₁
      have hz'x : z' • x₀ = y₂ • x₀ := burnsideJ55_coset_smul_eq x₀ M1 hM1 hy₂
      have hy₂m : y₂ • x₀ = y₁ • ((y₁⁻¹ * y₂) • x₀) := by
        rw [← mul_smul, mul_inv_cancel_left]
      refine ⟨z', ?_, ?_⟩
      · show p.getVert (2 * i + 1 + 1) = Sum.inl (z' : Y ⧸ M1)
        exact hb
      · rw [Function.iterate_succ_apply', hz'x, hy₂m]
        rcases h1 _ hm with h | h
        · rw [h, ← hzx]
          exact Or.inl hzB
        · refine Or.inr ⟨z • x₀, hzB, ?_⟩
          rw [hzx]
          exact (hinv y₁ x₀ _).2 h
  obtain ⟨z, hz, hzB⟩ := key (p.length / 2) (by omega)
  have hlen : 2 * (p.length / 2) = p.length := by
    obtain ⟨k, hk⟩ := hp
    omega
  rw [hlen, SimpleGraph.Walk.getVert_length] at hz
  have hzy : (z : Y ⧸ M1) = (y : Y ⧸ M1) := (Sum.inl.inj hz).symm
  rw [← burnsideJ55_coset_smul_eq x₀ M1 hM1 hzy]
  exact hzB

private theorem burnsideJ55_octagon (x₀ : X) (M1 M2 : Subgroup Y) (hM1 : ∀ y, y ∈ M1 ↔ y • x₀ = x₀)
    (Γ : X → X → Prop) (hinv : ∀ (y : Y) a b, Γ (y • a) (y • b) ↔ Γ a b)
    (h1 : ∀ m ∈ M2, m • x₀ = x₀ ∨ Γ x₀ (m • x₀)) (m₀ : Y) (hm₀ : m₀ ∈ M2)
    (hm₀Γ : Γ x₀ (m₀ • x₀)) (h3 : ∀ a b, Γ x₀ a → Γ x₀ b → ∃ f ∈ M1, f • a = b) (y : Y) :
    (0 < (ChIJK.incGraph M1 M2).dist (Sum.inl ((1 : Y) : Y ⧸ M1)) (Sum.inl (y : Y ⧸ M1)) ∧
      (ChIJK.incGraph M1 M2).dist (Sum.inl ((1 : Y) : Y ⧸ M1)) (Sum.inl (y : Y ⧸ M1)) < 8) ↔
      (y • x₀ ≠ x₀ ∧ y • x₀ ∈ (burnsideJ55_ballStep Γ)^[3] {x₀}) := by
  rw [burnsideJ55_inc_dist_lt_eight_iff]
  constructor
  · rintro ⟨hne, hr, hd⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have hev := burnsideJ55_inc_dist_even M1 M2 hr
    refine ⟨fun h => hne ?_, ?_⟩
    · rw [QuotientGroup.eq]
      rw [inv_one, one_mul]
      exact (hM1 y).2 h
    · have := burnsideJ55_octagon_walk_ball x₀ M1 M2 hM1 Γ hinv h1 p (by rw [hp]; exact hev)
      refine burnsideJ55_ballStep_iterate_mono Γ {x₀} (k := p.length / 2) (by omega) this
  · rintro ⟨hne, hB⟩
    obtain ⟨y', p, hy', hl⟩ :=
      burnsideJ55_octagon_ball_walk x₀ M1 M2 hM1 Γ hinv m₀ hm₀ hm₀Γ h3 3 _ hB
    have hcos : (y' : Y ⧸ M1) = (y : Y ⧸ M1) := by
      rw [QuotientGroup.eq, hM1, mul_smul, ← hy', inv_smul_smul]
    rw [← hcos]
    refine ⟨?_, ⟨p⟩, (SimpleGraph.dist_le p).trans (by omega)⟩
    intro h
    apply hne
    have h' : (1 : Y)⁻¹ * y' ∈ M1 := QuotientGroup.eq.1 h
    rw [inv_one, one_mul] at h'
    rw [← hy']
    exact (hM1 y').1 h'

end Octagon

private theorem burnsideJ55_mem_ballStep {X : Type} (Γ : X → X → Prop) (S : Set X) (q : X) :
    q ∈ burnsideJ55_ballStep Γ S ↔ q ∈ S ∨ ∃ p ∈ S, Γ p q := Iff.rfl

section Ball

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3

section

private theorem burnsideJ55_ballL (k : ℕ) :
    (∀ x ∈ titsStepL^[k] [0], x < 1755) ∧
      ∀ q : Fin 1755, q ∈ (burnsideJ55_ballStep titsPointGraph.Adj)^[k] {0} ↔
        (q : ℕ) ∈ titsStepL^[k] [0] := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hx
      omega
    · intro q
      simp only [Function.iterate_zero, id_eq, Set.mem_singleton_iff, List.mem_singleton]
      exact ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
  | succ k ih =>
    obtain ⟨hlt, hset⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [titsStepL, List.mem_append, List.mem_flatMap] at hx
      rcases hx with hx | ⟨p, hp, hx⟩
      · exact hlt x hx
      · exact mem_nbr_lt (x := ⟨p, hlt p hp⟩) hx
    · intro q
      rw [titsStepL, List.mem_append, List.mem_flatMap, burnsideJ55_mem_ballStep, hset q]
      constructor
      · rintro (h | ⟨p, hp, hadj⟩)
        · exact Or.inl h
        · refine Or.inr ⟨p, (hset p).1 hp, ?_⟩
          rw [adj_iff_mem_nbr] at hadj
          exact hadj
      · rintro (h | ⟨p, hp, hq⟩)
        · exact Or.inl h
        · refine Or.inr ⟨⟨p, hlt p hp⟩, (hset ⟨p, hlt p hp⟩).2 hp, ?_⟩
          rw [adj_iff_mem_nbr]
          exact hq

private theorem burnsideJ55_ball_iff (j : Fin 1755) :
    j ∈ (burnsideJ55_ballStep titsPointGraph.Adj)^[3] {0} ↔ titsBallArr[(j : ℕ)]! = true := by
  rw [(burnsideJ55_ballL 3).2 j]
  have h1 : titsBallArr[(j : ℕ)]! = titsBallL3.contains (j : ℕ) := by
    simp [titsBallArr]
  rw [h1, List.contains_iff_mem]
  rfl

end

end Ball

section TitsSide

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3

section

@[expose] noncomputable def burnsideJ55_eM {F : Type} [Group F] (ρ : F →* Equiv.Perm (Fin 1755))
    (hinj : Function.Injective ρ) (hrange : ρ.range = CFSG.Sporadic.Schreier.Tits.titsA) : F ≃* ↥twoF4M :=
  (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (hrange.trans twoF4M_eq_titsA.symm))

end

section

open scoped Pointwise in
private theorem burnsideJ55_tits_side {F : Type} [Group F] (ρ : F →* Equiv.Perm (Fin 1755))
    (hinj : Function.Injective ρ) (hrange : ρ.range = CFSG.Sporadic.Schreier.Tits.titsA) (H : Subgroup F)
    (hH : ∀ f, f ∈ H ↔ ρ f 0 = 0) :
    ∃ T' M2 : Subgroup F, IsYAmalgamPair T' H M2 ∧
      ∀ y : F, (0 < (ChIJK.incGraph H M2).dist (Sum.inl ((1 : F) : F ⧸ H)) (Sum.inl (y : F ⧸ H)) ∧
          (ChIJK.incGraph H M2).dist (Sum.inl ((1 : F) : F ⧸ H)) (Sum.inl (y : F ⧸ H)) < 8) ↔
        (ρ y 0 ≠ 0 ∧ titsBallArr[((ρ y 0 : Fin 1755) : ℕ)]! = true) := by
  have hmem : ∀ f, ρ f ∈ CFSG.Sporadic.Schreier.Tits.titsA := fun f =>
    hrange ▸ MonoidHom.mem_range.2 ⟨f, rfl⟩
  have hlift : ∀ a ∈ CFSG.Sporadic.Schreier.Tits.titsA, ∃ f, ρ f = a := fun a ha =>
    MonoidHom.mem_range.1 (hrange ▸ ha)
  have hpair := IsYAmalgamPair.map (burnsideJ55_eM ρ hinj hrange).symm
    (CFSG.Quasithin.Fan86.Model.isYAmalgamPair_lattice twoF4Lattice)
  have hP1 : twoF4Lattice.P₁.map (burnsideJ55_eM ρ hinj hrange).symm.toMonoidHom = H := by
    ext f
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, twoF4Lattice_P₁, Subgroup.mem_subgroupOf]
    exact (J47.mem_twoF4H_iff (hmem f)).trans (hH f).symm
  rw [hP1] at hpair
  set M2 := twoF4Lattice.P₂.map (burnsideJ55_eM ρ hinj hrange).symm.toMonoidHom with hM2def
  have hM2 : ∀ m : F, m ∈ M2 ↔ ρ m • titsLine 0 = titsLine 0 := by
    intro m
    rw [hM2def, Subgroup.mem_map_equiv, MulEquiv.symm_symm, twoF4Lattice_P₂,
      Subgroup.mem_subgroupOf]
    exact J47.mem_twoF4N_iff (hmem m)
  refine ⟨_, M2, hpair, fun y => ?_⟩
  letI : MulAction F (Fin 1755) := MulAction.compHom (Fin 1755) ρ
  have hsmul : ∀ (y : F) (x : Fin 1755), y • x = ρ y x := fun _ _ => rfl
  have h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) :=
    mem_titsLine.2 ⟨0, titsKappa_zero, titsBeta_zero⟩
  have hline : ∀ m : F, ρ m • titsLine 0 = titsLine 0 → ρ m 0 ∈ titsLine 0 := by
    intro m hm
    have := Finset.smul_mem_smul_finset (a := ρ m) h00
    rw [hm] at this
    exact this
  have hΓline : ∀ p : Fin 1755, p ≠ 0 → p ∈ titsLine 0 → titsPointGraph.Adj 0 p :=
    fun p hp hl => adj_iff_line.2 ⟨hp.symm, 0, h00, hl⟩
  have h1 : ∀ m ∈ M2, m • (0 : Fin 1755) = 0 ∨ titsPointGraph.Adj 0 (m • (0 : Fin 1755)) := by
    intro m hm
    have hl := hline m ((hM2 m).1 hm)
    by_cases h : ρ m 0 = 0
    · exact Or.inl h
    · exact Or.inr (hΓline _ h hl)
  obtain ⟨m₀, hm₀⟩ := hlift J47.a1P J47.a1P_mem_A
  have hm₀M : m₀ ∈ M2 := by
    rw [hM2, hm₀]
    exact J47.a1P_line
  have hm₀Γ : titsPointGraph.Adj 0 (m₀ • (0 : Fin 1755)) := by
    rw [hsmul, hm₀, J47.a1P_zero]
    have hl := hline m₀ ((hM2 m₀).1 hm₀M)
    rw [hm₀, J47.a1P_zero] at hl
    exact hΓline 1 (by decide) hl
  have h3 : ∀ a b : Fin 1755, titsPointGraph.Adj 0 a → titsPointGraph.Adj 0 b →
      ∃ f ∈ H, f • a = b := by
    intro a b ha hb
    have hb' : b ∈ MulAction.orbit titsH a := by
      rw [orbit_titsH_of_adj ha]
      exact hb
    obtain ⟨⟨g, hg⟩, hgb⟩ := hb'
    obtain ⟨hgD, hg0⟩ := mem_titsH_iff.1 hg
    obtain ⟨f, hf⟩ := hlift g (titsD_le_titsA hgD)
    refine ⟨f, (hH f).2 (by rw [hf]; exact hg0), ?_⟩
    rw [hsmul, hf]
    exact hgb
  have key := burnsideJ55_octagon (Y := F) (X := Fin 1755) (0 : Fin 1755) H M2 hH
    titsPointGraph.Adj (fun y a b => mem_titsGraphAut.1 (titsA_le_titsGraphAut (hmem y)) a b)
    h1 m₀ hm₀M hm₀Γ h3 y
  exact key.trans (and_congr Iff.rfl (burnsideJ55_ball_iff _))

end

end TitsSide

private theorem burnsideJ55_exists_phi {F Ω : Type} [Group F] [MulAction F Ω] (δ : Ω) (H :
    Subgroup F)
    (hH : ∀ f, f ∈ H ↔ f • δ = δ) (D : Set Ω) (hD : ∀ z, z ∈ D ↔ ∃ g : F, g • δ = z) :
    ∃ φ : Ω → F ⧸ H, Set.BijOn φ D Set.univ ∧ (∀ f : F, ∀ z ∈ D, φ (f • z) = f • φ z) ∧
      φ δ = ((1 : F) : F ⧸ H) ∧ ∀ g : F, φ (g • δ) = (g : F ⧸ H) := by
  classical
  let φ : Ω → F ⧸ H := fun z =>
    if h : ∃ g : F, g • δ = z then ((Classical.choose h : F) : F ⧸ H) else ((1 : F) : F ⧸ H)
  have hφ : ∀ g : F, φ (g • δ) = (g : F ⧸ H) := by
    intro g
    have h : ∃ g' : F, g' • δ = g • δ := ⟨g, rfl⟩
    have key : ∀ c : F, c • δ = g • δ → c⁻¹ * g ∈ H := by
      intro c hc
      rw [hH, mul_smul, ← hc, inv_smul_smul]
    simp only [φ, dif_pos h]
    rw [QuotientGroup.eq]
    exact key _ (Classical.choose_spec h)
  have hφ1 : φ δ = ((1 : F) : F ⧸ H) := by
    have := hφ 1
    rwa [one_smul] at this
  refine ⟨φ, ⟨Set.mapsTo_univ _ _, ?_, ?_⟩, ?_, hφ1, hφ⟩
  · intro z₁ hz₁ z₂ hz₂ h
    obtain ⟨g₁, rfl⟩ := (hD z₁).1 hz₁
    obtain ⟨g₂, rfl⟩ := (hD z₂).1 hz₂
    rw [hφ, hφ, QuotientGroup.eq, hH, mul_smul, inv_smul_eq_iff] at h
    exact h.symm
  · intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g • δ, (hD _).2 ⟨g, rfl⟩, hφ g⟩
  · intro f z hz
    obtain ⟨g, rfl⟩ := (hD z).1 hz
    rw [← mul_smul, hφ, hφ]
    rfl

section FSide

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier (ruP)

section

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ : Ω} (T : burnsideJ55_Tr G Ω ω δ)

theorem burnsideJ55_Tr.σ_mem_ruR0 (f : ↥(MulAction.stabilizer G ω)) : T.σ f ∈ ruR0 :=
  burnsideJ55_mem_ruR0.2 ⟨T.σ_mem f, by
    rw [← T.hω, ← T.hact, MulAction.mem_stabilizer_iff.1 f.2]⟩

@[expose] noncomputable def burnsideJ55_Tr.σ0 : ↥(MulAction.stabilizer G ω) →* ruR0 :=
  (T.σ.comp (MulAction.stabilizer G ω).subtype).codRestrict ruR0 T.σ_mem_ruR0

section

@[expose] noncomputable def burnsideJ55_Tr.ρ : ↥(MulAction.stabilizer G ω) →* Equiv.Perm (Fin 1755) :=
  (Subgroup.subtype CFSG.Sporadic.Schreier.Tits.titsA).comp (ruR0Equiv.toMonoidHom.comp T.σ0)

theorem burnsideJ55_Tr.ρ_mem (f : ↥(MulAction.stabilizer G ω)) : T.ρ f ∈
    CFSG.Sporadic.Schreier.Tits.titsA :=
  (ruR0Equiv (T.σ0 f) : ↥CFSG.Sporadic.Schreier.Tits.titsA).2

theorem burnsideJ55_Tr.σ_ruB (f : ↥(MulAction.stabilizer G ω)) (j : Fin 1755) :
    T.σ f (ruB j) = ruB (T.ρ f j) :=
  ruR0Equiv_ruB (T.σ0 f) j

theorem burnsideJ55_Tr.ρ_injective : Function.Injective T.ρ := by
  intro f g h
  have h1 : T.σ0 f = T.σ0 g := ruR0Equiv.injective (Subtype.ext h)
  have h2 : T.σ f = T.σ g := congrArg Subtype.val h1
  exact Subtype.ext (T.hinj h2)

theorem burnsideJ55_Tr.ρ_range : T.ρ.range = CFSG.Sporadic.Schreier.Tits.titsA := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact T.ρ_mem f
  · intro a ha
    obtain ⟨hrP, hr0⟩ := burnsideJ55_mem_ruR0.1 (ruR0Equiv.symm ⟨a, ha⟩).2
    obtain ⟨g, hg⟩ := T.exists_σ_eq hrP
    have hgω : g ∈ MulAction.stabilizer G ω := by
      rw [T.mem_stabilizer_iff, T.hω, hg]
      exact hr0
    refine ⟨⟨g, hgω⟩, ?_⟩
    have h1 : T.σ0 ⟨g, hgω⟩ = ruR0Equiv.symm ⟨a, ha⟩ := Subtype.ext hg
    show ((ruR0Equiv (T.σ0 ⟨g, hgω⟩) : ↥CFSG.Sporadic.Schreier.Tits.titsA) : Equiv.Perm (Fin 1755)) = a
    rw [h1, MulEquiv.apply_symm_apply]

theorem burnsideJ55_Tr.mem_Fd_iff (f : ↥(MulAction.stabilizer G ω)) :
    f ∈ (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
        (MulAction.stabilizer G ω) ↔ T.ρ f 0 = 0 := by
  have h1 : T.σ f 1 = 1 ↔ T.ρ f 0 = 0 := by
    rw [← ruB_zero, T.σ_ruB, ruB_injective.eq_iff]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, T.mem_stabilizer_iff (f : G) δ, T.hδ, h1]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

end

section

include T in
theorem burnsideJ55_Tr.mem_D_iff (z : Ω) :
    z ∈ ChIJK.DeltaAt G ω δ ω ↔ ∃ g : ↥(MulAction.stabilizer G ω), g • δ = z := by
  rw [T.mem_deltaAt_iff, T.hω, ruAdj_zero_iff, ← orbit_ruR0_one, ← T.hδ,
    ← T.mem_orbit_stab_iff]
  exact MulAction.mem_orbit_iff

end

end

section

private theorem burnsideJ55_ball_adj (j : Fin 1755) :
    (j ≠ 0 ∧ titsBallArr[(j : ℕ)]! = true) ↔ ruAdj 1 (ruB j) := by
  have h := allLt_spec ruBall_check j.2
  have hrow : ruRowA ruTI1 ruDArr[(j : ℕ)]! = true ↔ ruAdj 1 (ruB j) := by
    rw [← ruB_val]
    exact ruRowA_one _
  rw [beq_iff_eq, Bool.eq_iff_iff, Bool.or_eq_true, beq_iff_eq, hrow] at h
  rw [h]
  constructor
  · rintro ⟨hj, hj' | hadj⟩
    · exact absurd (Fin.ext hj') hj
    · exact hadj
  · intro hadj
    refine ⟨?_, Or.inr hadj⟩
    intro hj0
    rw [hj0, ruB_zero] at hadj
    exact not_ruAdj_self 1 hadj

end

section

private theorem burnsideJ55_part2 {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
    (hS : ChIJK.RudvalisSetting G Ω ω δ γ) :
    ∃ (T' M2 : Subgroup ↥(MulAction.stabilizer G ω)),
      CFSG.Quasithin.IsYAmalgamPair T'
        ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
          (MulAction.stabilizer G ω)) M2 ∧
      ∃ φ : Ω → ↥(MulAction.stabilizer G ω) ⧸
          (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
            (MulAction.stabilizer G ω),
        Set.BijOn φ (ChIJK.DeltaAt G ω δ ω) Set.univ ∧
        (∀ f : ↥(MulAction.stabilizer G ω), ∀ ρ ∈ ChIJK.DeltaAt G ω δ ω,
          φ (f • ρ) = f • φ ρ) ∧
        φ δ = ((1 : ↥(MulAction.stabilizer G ω)) : ↥(MulAction.stabilizer G ω) ⧸
          (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
            (MulAction.stabilizer G ω)) ∧
        ∀ ρ ∈ ChIJK.DeltaAt G ω δ ω, (ρ ∈ ChIJK.DeltaAt G ω δ δ ↔
          (0 < (ChIJK.incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) ∧
            (ChIJK.incGraph ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
              (MulAction.stabilizer G ω)) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ ρ)) < 8)) := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hS
  obtain ⟨T', M2, hpair, hdist⟩ := burnsideJ55_tits_side T.ρ T.ρ_injective T.ρ_range _ T.mem_Fd_iff
  refine ⟨T', M2, hpair, ?_⟩
  obtain ⟨φ, hbij, heq, hδ, hφ⟩ := burnsideJ55_exists_phi (F := ↥(MulAction.stabilizer G ω))
    (Ω := Ω) δ ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
      (MulAction.stabilizer G ω))
    (fun f => by rw [burnsideJ55_subgroupOf_eq, MulAction.mem_stabilizer_iff])
    (ChIJK.DeltaAt G ω δ ω) T.mem_D_iff
  refine ⟨φ, hbij, heq, hδ, fun z hz => ?_⟩
  obtain ⟨g, rfl⟩ := (T.mem_D_iff z).1 hz
  have e1 : T.Φ (g • δ) = ruB (T.ρ g 0) := by
    rw [show g • δ = (g : G) • δ from rfl, T.hact, T.hδ, ← ruB_zero, T.σ_ruB]
  rw [hδ, hφ g, hdist g, T.mem_deltaAt_iff, e1, T.hδ]
  exact (burnsideJ55_ball_adj _).symm

end

end FSide

end BurnsideJ55

section

theorem as_J_5_5 : J_5_5 := by
  intro G _ _ Ω _ _ ω δ γ hS
  exact ⟨burnsideJ55_part1 hS, burnsideJ55_part2 hS, burnsideJ55_part3 hS,
    burnsideJ55_part4 hS, burnsideJ55_part5 hS⟩

end

@[expose] def J_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω),
    RudvalisSetting G Ω ω δ γ →
      ∀ σ : Ω ≃ Ω, ((∀ ρ τ : Ω, τ ∈ DeltaAt G ω δ ρ ↔ σ τ ∈ DeltaAt G ω δ (σ ρ)) ↔
        ∃ g : G, ∀ ρ : Ω, σ ρ = g • ρ)

section BurnsideJ11b

private theorem burnsideJ11b_faithful {G Ω : Type} [Group G] [MulAction G Ω]
    (h : ∀ g : G, (∀ ω : Ω, g • ω = ω) → g = 1) : FaithfulSMul G Ω := by
  refine ⟨fun {m₁ m₂} hm => ?_⟩
  have h1 : m₁⁻¹ * m₂ = 1 := by
    apply h
    intro ω
    rw [mul_smul, ← hm ω, inv_smul_smul]
  exact inv_mul_eq_one.mp h1

private theorem burnsideJ11b_subgroupOf_eq {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    (MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf (MulAction.stabilizer G ω) =
      MulAction.stabilizer (MulAction.stabilizer G ω) δ := by
  ext f
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨f.2, h⟩⟩

noncomputable def burnsideJ11b_stabEquiv {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω) :
    MulAction.stabilizer (MulAction.stabilizer G ω) δ ≃*
      ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) :=
  (MulEquiv.subgroupCongr (burnsideJ11b_subgroupOf_eq ω δ)).symm.trans
    (Subgroup.subgroupOfEquivOfLe inf_le_left)

private theorem burnsideJ11b_parabolic {G Ω : Type} [Group G] [MulAction G Ω] (ω δ : Ω)
    (h : ChIJK.IsParabolicTwoSub ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ).subgroupOf
      (MulAction.stabilizer G ω))) :
    CFSG.Quasithin.RuRank3.IsSylowTwoParabolic
      (MulAction.stabilizer (MulAction.stabilizer G ω) δ) := by
  rw [← burnsideJ11b_subgroupOf_eq]
  exact h

private theorem burnsideJ11b_psl_of_stated {N : Type} [Group N]
    (h : CFSG.Open.StatedClassicalModel N .PSL 2 5 2) :
    Nonempty (N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 5 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 5 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 5 2 (by norm_num)]
  exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv
      (FiniteField.ringEquivOfCardEq hcard)))⟩

private theorem burnsideJ11b_center_trivial {N : Type} [Group N]
    (e : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) :
    ∀ z : N, (∀ g : N, g * z = z * g) → z = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro z hz
  have h1 : e z ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 5 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg e (hz (e.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

private theorem burnsideJ11b_isL225Plus {Y : Type} [Group Y] (h : ChIJK.IsL225Plus Y) :
    CFSG.Quasithin.RuRank3.IsL225Plus Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨N, hN, hidx, hmodel, P, n, hn4, ⟨eP⟩⟩ := h
  obtain ⟨eN⟩ := burnsideJ11b_psl_of_stated hmodel
  have hNcard : Nat.card N = 7800 := by
    rw [Nat.card_congr eN.toEquiv,
      CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := 5) (m := 2) (by norm_num)
        (by norm_num)]
    norm_num
  have hYcard : Nat.card Y = 15600 := by
    have := Subgroup.card_mul_index N
    rw [hNcard, hidx] at this
    omega
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  have hPcard : Nat.card (P : Subgroup Y) = 2 ^ n := by
    rw [Nat.card_congr eP.toEquiv, CFSG.Semidihedral.card n (by omega)]
  have hn : n = 4 := by
    have hdvd : Nat.card (P : Subgroup Y) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card _
    rw [hPcard, hYcard] at hdvd
    by_contra hne
    have h5 : 5 ≤ n := by omega
    have h32 : 2 ^ 5 ∣ 15600 := (pow_dvd_pow 2 h5).trans hdvd
    norm_num at h32
  subst hn
  have hSyl : ∀ S : Sylow 2 Y, Nonempty (CFSG.Open.SemidihedralGroup 4 ≃* S) := by
    intro S
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P S
    exact ⟨eP.symm.trans ((P.equivSMul g).trans (MulEquiv.subgroupCongr (by rw [hg])))⟩
  refine ⟨N, hN, hidx, ⟨eN⟩, ?_, hSyl⟩
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hcN : ∀ m ∈ N, m * c = c * m := Subgroup.mem_centralizer_iff.mp hc
  have hZ' : ∀ z ∈ N, (∀ m ∈ N, m * z = z * m) → z = 1 := by
    intro z hz hzc
    have h1 : (⟨z, hz⟩ : N) = 1 :=
      burnsideJ11b_center_trivial eN ⟨z, hz⟩ (fun g => Subtype.ext (hzc g g.2))
    exact congrArg Subtype.val h1
  have hcnot : c ∉ N := fun hcm => hc1 (hZ' c hcm (fun m hm => hcN m hm))
  have hc2 : c ^ 2 = 1 := by
    apply hZ' _ (Subgroup.sq_mem_of_index_two hidx c)
    intro m hm
    rw [pow_two, ← mul_assoc, hcN m hm, mul_assoc, hcN m hm, ← mul_assoc]
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hcz : ∀ y : Y, y * c = c * y := by
    intro y
    by_cases hy : y ∈ N
    · exact hcN y hy
    · have hyc : y * c ∈ N :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hy hcnot)
      have h1 := hcN (y * c) hyc
      have h2 : y = c * y * c := by
        calc y = y * (c * c) := by rw [hcc, mul_one]
          _ = y * c * c := by rw [mul_assoc]
          _ = c * (y * c) := h1
          _ = c * y * c := by rw [mul_assoc]
      calc y * c = (c * y * c) * c := by rw [← h2]
        _ = c * y * (c * c) := by rw [mul_assoc (c * y) c c]
        _ = c * y := by rw [hcc, mul_one]
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  have hcpg : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q, hQ⟩ := hcpg.exists_le_sylow
  have hcQ : c ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers c)
  obtain ⟨eQ⟩ := hSyl Q
  have hc'central : eQ.symm ⟨c, hcQ⟩ ∈ Subgroup.center (CFSG.Open.SemidihedralGroup 4) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply eQ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcz _)
  rw [CFSG.Semidihedral.center_eq_zpowers 4 (by norm_num)] at hc'central
  have hz2 : CFSG.Semidihedral.z 4 ^ 2 = 1 := CFSG.Semidihedral.z_sq 4 (by norm_num)
  have hc'ne : eQ.symm ⟨c, hcQ⟩ ≠ 1 := by
    intro h1
    apply hc1
    have := congrArg eQ h1
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val this
  have hc'z : eQ.symm ⟨c, hcQ⟩ = CFSG.Semidihedral.z 4 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'central
    rw [← hk] at hc'ne ⊢
    rw [← zpow_mod_orderOf, CFSG.Semidihedral.orderOf_z 4 (by norm_num)] at hc'ne ⊢
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      apply hc'ne
      push_cast
      rw [h0, zpow_zero]
    · push_cast
      rw [h1, zpow_one]
  have hzsq : CFSG.Semidihedral.z 4 =
      (CFSG.Semidihedral.r 4 ^ 2) ^ 2 := by
    rw [← pow_mul]
    rfl
  have hcsq : c = ((eQ (CFSG.Semidihedral.r 4 ^ 2) : Q) : Y) ^ 2 := by
    have h1 : (⟨c, hcQ⟩ : Q) = eQ (CFSG.Semidihedral.z 4) := by
      rw [← hc'z, MulEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    rw [hzsq, map_pow] at h2
    exact h2
  exact hcnot (hcsq ▸ Subgroup.sq_mem_of_index_two hidx _)

private theorem burnsideJ11b_two_f4 {Y : Type} [Group Y]
    (h : ChIJK.IsTwoF4TwoGroup Y) :
    Nonempty (Y ≃* CFSG.Sporadic.Schreier.Tits.titsA) := by
  obtain ⟨Y0, _, hY0, ⟨e⟩⟩ := h
  obtain ⟨e0⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y0 2 1 hY0
  exact ⟨e.trans ((MulAut.congr e0).trans CFSG.Sporadic.Schreier.Tits.titsConjEquiv.symm)⟩

private theorem burnsideJ11b_toRT {G Ω : Type} [Group G] [MulAction G Ω]
    (h : ChIJK.IsRudvalisRank3 G Ω) : CFSG.Quasithin.RuRank3.IsRudvalisRank3 G Ω := by
  obtain ⟨hne, hfaith, htrans, hall⟩ := h
  refine ⟨burnsideJ11b_faithful hfaith, hne, htrans, fun ω => (hall ω).1, fun ω => ?_,
    fun ω => ?_, fun ω => ?_⟩
  · exact burnsideJ11b_two_f4 (hall ω).2.1
  · obtain ⟨δ, hpar, hcard⟩ := (hall ω).2.2.1
    refine ⟨δ, ?_, burnsideJ11b_parabolic ω δ hpar⟩
    rw [Nat.card_congr (burnsideJ11b_stabEquiv ω δ).toEquiv]
    exact hcard
  · obtain ⟨γ, hγ⟩ := (hall ω).2.2.2
    exact ⟨γ, CFSG.Quasithin.RuRank3.IsL225Plus.of_mulEquiv (burnsideJ11b_stabEquiv ω γ).symm
      (burnsideJ11b_isL225Plus hγ)⟩

private theorem burnsideJ11b_mem_deltaAt_iff {G Ω : Type} [Group G] [MulAction G Ω] (ω δ ρ τ : Ω) :
    τ ∈ ChIJK.DeltaAt G ω δ ρ ↔ CFSG.Quasithin.RuRank3.orbAdj G ω δ ρ τ := by
  constructor
  · rintro ⟨g, hg1, f, hf⟩
    refine ⟨g * f, ?_, ?_⟩
    · rw [mul_smul, show (f : G) • ω = ω from f.2, hg1]
    · rw [mul_smul]
      have hf' : (f : G) • δ = g⁻¹ • τ := hf
      rw [hf', smul_inv_smul]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨g, hg1, ?_⟩
    rw [← hg2, inv_smul_smul]
    exact MulAction.mem_orbit_self δ

end BurnsideJ11b

section

theorem as_J_5_6 : J_5_6 := by
  intro G _ _ Ω _ _ ω δ γ hS σ
  have hrt := burnsideJ11b_toRT hS.rank3
  have hδ : Nat.card (MulAction.stabilizer (MulAction.stabilizer G ω) δ) = 2 ^ 12 * 5 := by
    rw [Nat.card_congr (burnsideJ11b_stabEquiv ω δ).toEquiv]
    exact hS.rub.2
  obtain ⟨hinv, hex⟩ := hrt.aut_eq ω δ hδ
  have hmem := burnsideJ11b_mem_deltaAt_iff (G := G) ω δ
  constructor
  · intro hσ
    obtain ⟨g, hg, -⟩ := hex σ (fun z y => by
      rw [← hmem, ← hmem]
      exact (hσ z y).symm)
    exact ⟨g, fun ρ => (hg ρ).symm⟩
  · rintro ⟨g, hg⟩ ρ τ
    rw [hmem, hmem, hg ρ, hg τ]
    exact (hinv g ρ τ).symm

end

@[expose] def J_5_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω],
    IsRudvalisRank3 G Ω → NativeSporadic.IsSporadic G .Ru

section

theorem as_J_5_14 : J_5_14 := by
  intro G _ _ Ω _ _ h
  exact CFSG.Quasithin.RuRank3.statementJ514 G Ω (burnsideJ11b_toRT h)

end

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      (thetaAt G ω δ δ = {u | u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
          (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard = 2 ^ 9} ∧
        2 * 2 ^ 9 = (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard) ∧
      (∀ u ∈ thetaAt G ω δ δ,
        ∃! l : ↥(MulAction.stabilizer G ω) ⧸ M2,
          (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) ∧
          (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l)) ∧
      (∀ u ∈ thetaAt G ω δ δ, ∀ l : ↥(MulAction.stabilizer G ω) ⧸ M2,
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l) →
          ∃! u' : Ω, u' ∈ DeltaAt G ω δ ω ∧
            (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l) ∧
            u' ≠ δ ∧ u' ≠ u) ∧
      ∀ u ∈ thetaAt G ω δ δ, ∀ (l : ↥(MulAction.stabilizer G ω) ⧸ M2) (u' : Ω),
        u' ∈ DeltaAt G ω δ ω →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l) →
        (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l) → u' ≠ δ → u' ≠ u →
          u' ∈ thetaAt G ω δ δ ∧
          ∀ w ∈ thetaAt G ω δ δ,
            (DeltaAt G ω δ w ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ =
              (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) \
                (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) ↔ w = u')

section BurnsideJ57

section BurnsideJ57All

open CFSG.ASVolI.ChIJK

section BurnsideJ57PartA

open CFSG.Quasithin.H13.F45Ru

section BurnsideJ57Generic

variable {V : Type} {Γ : SimpleGraph V}

private theorem burnsideJ57_walk_parity (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {x z : V} (p : Γ.Walk x z) : Even p.length ↔ col x = col z := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    have := hc a b h
    revert this
    cases col a <;> cases col b <;> cases col c <;> simp

private theorem burnsideJ57_dist_parity (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {x z : V} (hr : Γ.Reachable x z) : Even (Γ.dist x z) ↔ col x = col z := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]
  exact burnsideJ57_walk_parity col hc p

private theorem burnsideJ57_layers_iso {W : Type} {Γ' : SimpleGraph W} (e : Γ ≃g Γ') {m : ℕ} {b : V}
    {lay : V → ℕ} (hL : Layers Γ m b lay) : Layers Γ' m (e b) (fun x => lay (e.symm x)) where
  root := by simpa using hL.root
  le x := hL.le _
  parent x hx := by
    have hne : e.symm x ≠ b := fun h => hx (by rw [← h, e.apply_symm_apply])
    obtain ⟨y, hy, hl⟩ := hL.parent _ hne
    refine ⟨e y, ?_, by simpa using hl⟩
    have := e.map_rel_iff.2 hy
    simpa using this
  lip x y h := hL.lip _ _ (by simpa using e.symm.map_rel_iff.2 h)
  uniq x y z h1 h2 hxy hxz hy hz := by
    have := hL.uniq (e.symm x) (e.symm y) (e.symm z) h1 h2 (by simpa using e.symm.map_rel_iff.2 hxy)
      (by simpa using e.symm.map_rel_iff.2 hxz) hy hz
    exact e.symm.injective this

private theorem burnsideJ57_lay_adj (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y) {m : ℕ}
    {b : V} {lay : V → ℕ} (hL : Layers Γ m b lay) {x y : V} (h : Γ.Adj x y) :
    lay y = lay x + 1 ∨ lay x = lay y + 1 := by
  have h1 := hL.lip x y h
  have h2 := hL.lip y x h.symm
  have hne : lay x ≠ lay y := by
    intro heq
    have hx := burnsideJ57_dist_parity col hc (hL.reachable x)
    have hy := burnsideJ57_dist_parity col hc (hL.reachable y)
    rw [hL.dist_eq] at hx hy
    rw [heq] at hx
    have := hc x y h
    revert hx hy this
    cases col b <;> cases col x <;> cases col y <;> simp
  omega

private theorem burnsideJ57_geo_lay {m : ℕ} {b : V} {lay : V → ℕ} (hL : Layers Γ m b lay) {z : V}
    (p : Γ.Walk b z) (hp : p.length = lay z) {i : ℕ} (hi : i ≤ p.length) :
    lay (p.getVert i) = i := by
  have h1 := hL.lay_le_length (p.take i)
  have h2 := hL.lay_le_length (p.drop i)
  rw [SimpleGraph.Walk.take_length, hL.root] at h1
  rw [SimpleGraph.Walk.drop_length] at h2
  have e : i ⊓ p.length = i := inf_eq_left.2 hi
  rw [e] at h1
  omega

private theorem burnsideJ57_geo_unique {m : ℕ} {b : V} {lay : V → ℕ} (hL : Layers Γ m b lay) {z : V}
    (hz : lay z < m) (p q : Γ.Walk b z) (hp : p.length = lay z) (hq : q.length = lay z) :
    p = q := by
  have hl : p.length = q.length := hp.trans hq.symm
  refine SimpleGraph.Walk.ext_getVert_le_length hl ?_
  have key : ∀ k, k ≤ p.length → p.getVert (p.length - k) = q.getVert (p.length - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, SimpleGraph.Walk.getVert_length, hl, SimpleGraph.Walk.getVert_length]
    | succ k ih =>
      intro hk
      have e1 := ih (by omega)
      have hi : p.length - k = (p.length - (k + 1)) + 1 := by omega
      rw [hi] at e1
      have a1 := p.adj_getVert_succ (i := p.length - (k + 1)) (by omega)
      have a2 := q.adj_getVert_succ (i := p.length - (k + 1)) (by omega)
      rw [e1] at a1
      have hlp := burnsideJ57_geo_lay hL p hp (i := p.length - (k + 1) + 1) (by omega)
      have hlp' := burnsideJ57_geo_lay hL p hp (i := p.length - (k + 1)) (by omega)
      have hlq' := burnsideJ57_geo_lay hL q hq (i := p.length - (k + 1)) (by omega)
      have hlq := burnsideJ57_geo_lay hL q hq (i := p.length - (k + 1) + 1) (by omega)
      refine hL.uniq (q.getVert (p.length - (k + 1) + 1)) (p.getVert (p.length - (k + 1)))
        (q.getVert (p.length - (k + 1))) ?_ ?_ a1.symm a2.symm ?_ ?_
      · omega
      · omega
      · omega
      · omega
  intro i hi
  have := key (p.length - i) (by omega)
  rwa [Nat.sub_sub_self hi] at this

private theorem burnsideJ57_J59_abs {b : V} {lay : V → ℕ} (hL : Layers Γ 8 b lay) {y : V} {e : ℕ}
    (he : Γ.dist b y = e) (h0 : 0 < e) (h8 : e < 8) :
    ∃! y', Γ.Adj y y' ∧ Γ.dist b y' = e - 1 := by
  rw [hL.dist_eq] at he
  have hy : y ≠ b := fun h => by
    have := hL.root
    rw [h] at he
    omega
  obtain ⟨y', hy', hl⟩ := hL.parent y hy
  refine ⟨y', ⟨hy', by rw [hL.dist_eq]; omega⟩, fun z hz => ?_⟩
  obtain ⟨hz1, hz2⟩ := hz
  rw [hL.dist_eq] at hz2
  exact hL.uniq y z y' (by omega) (by omega) hz1 hy' (by omega) hl

private theorem burnsideJ57_seq (r : ℕ) (d : ℕ → ℕ) (hr6 : r ≤ 6) (h8 : ∀ i, i ≤ r → d i ≤ 8)
    (hdr : d r = 8) (hstep : ∀ i, i < r → d (i + 1) = d i + 1 ∨ d i = d (i + 1) + 1)
    (hlip : ∀ i j, i ≤ j → j ≤ r → d j ≤ d i + (j - i) ∧ d i ≤ d j + (j - i))
    (hpar : ∀ i, i ≤ r → (d i + i) % 2 = d 0 % 2)
    (hcont : ∀ i, i < r → d i < d (i + 1) → ∀ k, i + k ≤ r → d i + k ≤ 8 → d (i + k) = d i + k)
    (h2 : ∀ i, i ≤ r → d i + (r - i) = 8 → ∀ k, i + k ≤ r → d (i + k) = d i + k) :
    (d 0 = 4 → ((r = 4 ∧ ∀ k, k ≤ 4 → d k = d 0 + k) ∨
      (r = 6 ∧ (∀ k, k ≤ 4 → d k = d 0 + k) ∧ d 5 = 7) ∨
      (r = 6 ∧ d 1 = 3 ∧ ∀ k, k ≤ 5 → d (1 + k) = d 1 + k))) ∧
    (d 0 = 6 → ((∀ i, 0 < i → i ≤ r → 7 ≤ d i) ∨
      (d 4 = 6 ∧ ∀ i, i ≤ r → i ≠ 0 → i ≠ 4 → 7 ≤ d i) ∨
      (d 1 = 5 ∧ ∀ i, i ≤ r → i ≠ 1 → 6 ≤ d i) ∨
      (d 2 = 4 ∧ r = 6 ∧ ∀ k, k ≤ 4 → d (2 + k) = d 2 + k))) := by
  have hl0 := hlip 0 r (Nat.zero_le _) le_rfl
  have hp0 := hpar r le_rfl
  constructor
  · intro h0
    have hr4 : 4 ≤ r := by omega
    have hre : r = 4 ∨ r = 6 := by omega
    rcases hre with rfl | rfl
    · left
      refine ⟨rfl, fun k hk => ?_⟩
      have := h2 0 (by omega) (by omega) k (by omega)
      simpa using this
    · have hd1 : d 1 = d 0 + 1 ∨ d 0 = d 1 + 1 := hstep 0 (by omega)
      rcases hd1 with hd1 | hd1
      · right; left
        have hall : ∀ k, k ≤ 4 → d k = d 0 + k := fun k hk => by
          have := hcont 0 (by omega) (by show d 0 < d 1; omega) k (by omega) (by omega)
          simpa using this
        refine ⟨rfl, hall, ?_⟩
        have h4 := hall 4 le_rfl
        have h5 : d 5 = d 4 + 1 ∨ d 4 = d 5 + 1 := hstep 4 (by omega)
        have h5' := h8 5 (by omega)
        omega
      · right; right
        refine ⟨rfl, by omega, fun k hk => ?_⟩
        exact h2 1 (by omega) (by omega) k (by omega)
  · intro h0
    have hr2 : 2 ≤ r := by omega
    have hre : r = 2 ∨ r = 4 ∨ r = 6 := by omega
    have hd1 : d 1 = d 0 + 1 ∨ d 0 = d 1 + 1 := hstep 0 (by omega)
    rcases hd1 with hd1 | hd1
    ·
      have hd2 : d 2 = d 0 + 2 := by
        have := hcont 0 (by omega) (by show d 0 < d 1; omega) 2 (by omega) (by omega)
        simpa using this
      rcases hre with rfl | rfl | rfl
      · left
        intro i hi hi2
        interval_cases i <;> omega
      · left
        have h3 : d 3 = d 2 + 1 ∨ d 2 = d 3 + 1 := hstep 2 (by omega)
        have h3' := h8 3 (by omega)
        have h4 : d 4 = d 3 + 1 ∨ d 3 = d 4 + 1 := hstep 3 (by omega)
        intro i hi hi4
        interval_cases i <;> omega
      · have h3 : d 3 = d 2 + 1 ∨ d 2 = d 3 + 1 := hstep 2 (by omega)
        have h3' := h8 3 (by omega)
        have h4 : d 4 = d 3 + 1 ∨ d 3 = d 4 + 1 := hstep 3 (by omega)
        have h4' := h8 4 (by omega)
        have h5 : d 5 = d 4 + 1 ∨ d 4 = d 5 + 1 := hstep 4 (by omega)
        have h5' := h8 5 (by omega)
        have h6 : d 6 = d 5 + 1 ∨ d 5 = d 6 + 1 := hstep 5 (by omega)
        by_cases h44 : d 4 = 6
        · right; left
          have e5 : d (4 + 1) = d 4 + 1 := by
            have := h2 4 (by omega) (by omega) 1 (by omega)
            simpa using this
          have e5' : d 5 = d 4 + 1 := e5
          refine ⟨h44, fun i hi hi0 hi4 => ?_⟩
          interval_cases i <;> omega
        · left
          intro i hi hi6
          interval_cases i <;> omega
    ·
      have hd2 : d 2 = d 1 + 1 ∨ d 1 = d 2 + 1 := hstep 1 (by omega)
      rcases hd2 with hd2 | hd2
      ·
        right; right; left
        have hr4 : 4 ≤ r := by
          by_contra hlt
          have : r = 2 := by omega
          subst this
          omega
        have h2' : d 2 = d 1 + 1 := by
          have := hcont 1 (by omega) (by show d 1 < d 2; omega) 1 (by omega) (by omega)
          simpa using this
        have h3 : d 3 = d 1 + 2 := by
          have := hcont 1 (by omega) (by show d 1 < d 2; omega) 2 (by omega) (by omega)
          simpa using this
        have h4 : d 4 = d 1 + 3 := by
          have := hcont 1 (by omega) (by show d 1 < d 2; omega) 3 (by omega) (by omega)
          simpa using this
        refine ⟨by omega, fun i hi hi1 => ?_⟩
        rcases hre with rfl | rfl | rfl
        · omega
        · interval_cases i <;> omega
        · have h5 : d 5 = d 4 + 1 ∨ d 4 = d 5 + 1 := hstep 4 (by omega)
          have h5' := h8 5 (by omega)
          interval_cases i <;> omega
      ·
        right; right; right
        have hr6' : r = 6 := by
          have := hlip 2 r (by omega) le_rfl
          omega
        subst hr6'
        refine ⟨by omega, rfl, fun k hk => ?_⟩
        exact h2 2 (by omega) (by omega) k (by omega)

private theorem burnsideJ57_J510_abs (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y) {b : V}
    {lay : V → ℕ} (hL : Layers Γ 8 b lay) {u v : V} (p : Γ.Walk u v)
    (hp : p.length = Γ.dist u v) (hv : Γ.dist b v = 8) (hr6 : p.length ≤ 6) :
    (p.getVert 0 = u ∧ p.length ≤ 6 ∧ dseq Γ b p 0 = Γ.dist b u ∧
      (∀ i, i ≤ p.length → dseq Γ b p i ≤ 8) ∧ dseq Γ b p p.length = 8) ∧
    (∀ i, i < p.length → dseq Γ b p i < dseq Γ b p (i + 1) →
      WalkIncreases Γ b p i (min (i + 8 - dseq Γ b p i) p.length)) ∧
    (∀ i, i ≤ p.length → dseq Γ b p i + (p.length - i) = 8 →
      WalkIncreases Γ b p i p.length) ∧
    (Γ.dist b u = 4 → ((p.length = 4 ∧ WalkIncreases Γ b p 0 4) ∨
      (p.length = 6 ∧ WalkIncreases Γ b p 0 4 ∧ dseq Γ b p 5 = 7) ∨
      (p.length = 6 ∧ dseq Γ b p 1 = 3 ∧ WalkIncreases Γ b p 1 6))) ∧
    (Γ.dist b u = 6 → ((∀ i, 0 < i → i ≤ p.length → 7 ≤ dseq Γ b p i) ∨
      (dseq Γ b p 4 = 6 ∧ ∀ i, i ≤ p.length → i ≠ 0 → i ≠ 4 → 7 ≤ dseq Γ b p i) ∨
      (dseq Γ b p 1 = 5 ∧ ∀ i, i ≤ p.length → i ≠ 1 → 6 ≤ dseq Γ b p i) ∨
      (dseq Γ b p 2 = 4 ∧ WalkIncreases Γ b p 2 6))) := by
  set r := p.length with hr
  set d : ℕ → ℕ := fun i => Γ.dist b (p.getVert i) with hd
  have hdseq : ∀ i, dseq Γ b p i = d i := fun i => rfl
  have hdl : ∀ x, Γ.dist b x = lay x := hL.dist_eq
  have hstep : ∀ i, i < r → d (i + 1) = d i + 1 ∨ d i = d (i + 1) + 1 := by
    intro i hi
    have := burnsideJ57_lay_adj col hc hL (p.adj_getVert_succ hi)
    simp only [hd, hdl]
    omega
  have h8 : ∀ i, i ≤ r → d i ≤ 8 := by
    intro i _
    simp only [hd, hdl]
    exact hL.le _
  have hdr : d r = 8 := by
    show Γ.dist b (p.getVert p.length) = 8
    rw [SimpleGraph.Walk.getVert_length]
    exact hv
  have hlip' : ∀ k i, i + k ≤ r → d (i + k) ≤ d i + k ∧ d i ≤ d (i + k) + k := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hstep (i + k) (by omega)
      rw [← add_assoc]
      omega
  have hlip : ∀ i j, i ≤ j → j ≤ r → d j ≤ d i + (j - i) ∧ d i ≤ d j + (j - i) := by
    intro i j hij hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := hlip' k i (by omega)
    simpa using this
  have hpar : ∀ i, i ≤ r → (d i + i) % 2 = d 0 % 2 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep i (by omega)
      omega
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hnb : ∀ i, i + 2 ≤ r → p.getVert (i + 2) ≠ p.getVert i := by
    intro i hi h
    have := hpath.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h
    omega
  have hcont : ∀ i, i < r → d i < d (i + 1) → ∀ k, i + k ≤ r → d i + k ≤ 8 →
      d (i + k) = d i + k := by
    intro i hi hlt k
    have claim : ∀ k, ∀ j, j ≤ k → i + j ≤ r → d i + j ≤ 8 → d (i + j) = d i + j := by
      intro k
      induction k with
      | zero =>
        intro j hj _ _
        have : j = 0 := by omega
        subst this
        simp
      | succ k ih =>
        intro j hj hjr hj8
        by_cases hjk : j ≤ k
        · exact ih j hjk hjr hj8
        have hj' : j = k + 1 := by omega
        subst hj'
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          have := hstep i hi
          simp only [Nat.zero_add]
          omega
        · have e1 := ih k le_rfl (by omega) (by omega)
          have e0 : d (i + k - 1) = d i + (k - 1) := by
            have := ih (k - 1) (by omega) (by omega) (by omega)
            rwa [show i + (k - 1) = i + k - 1 by omega] at this
          have hy1 : 1 ≤ lay (p.getVert (i + k)) := by
            have : Γ.dist b (p.getVert (i + k)) = d (i + k) := rfl
            rw [hdl] at this
            omega
          have hy8 : lay (p.getVert (i + k)) < 8 := by
            have : Γ.dist b (p.getVert (i + k)) = d (i + k) := rfl
            rw [hdl] at this
            omega
          have hprev : lay (p.getVert (i + k - 1)) + 1 = lay (p.getVert (i + k)) := by
            have a : Γ.dist b (p.getVert (i + k - 1)) = d (i + k - 1) := rfl
            have c : Γ.dist b (p.getVert (i + k)) = d (i + k) := rfl
            rw [hdl] at a c
            omega
          have hadj1 : Γ.Adj (p.getVert (i + k)) (p.getVert (i + k - 1)) := by
            have := p.adj_getVert_succ (i := i + k - 1) (by omega)
            have e : i + k - 1 + 1 = i + k := by omega
            rw [e] at this
            exact this.symm
          have hadj2 : Γ.Adj (p.getVert (i + k)) (p.getVert (i + k + 1)) :=
            p.adj_getVert_succ (i := i + k) (by omega)
          have hs := hstep (i + k) (by omega)
          rcases hs with hs | hs
          · rw [← add_assoc]
            omega
          · exfalso
            have hnext : lay (p.getVert (i + k + 1)) + 1 = lay (p.getVert (i + k)) := by
              have a : Γ.dist b (p.getVert (i + k + 1)) = d (i + k + 1) := rfl
              have c : Γ.dist b (p.getVert (i + k)) = d (i + k) := rfl
              rw [hdl] at a c
              omega
            have := hL.uniq _ _ _ hy1 hy8 hadj2 hadj1 hnext hprev
            have hb := hnb (i + k - 1) (by omega)
            have e : i + k - 1 + 2 = i + k + 1 := by omega
            rw [e] at hb
            exact hb (this)
    exact fun hk hk8 => claim k k le_rfl hk hk8
  have h2 : ∀ i, i ≤ r → d i + (r - i) = 8 → ∀ k, i + k ≤ r → d (i + k) = d i + k := by
    intro i hi hid k hk
    rcases Nat.eq_or_lt_of_le hi with hir | hir
    · have : k = 0 := by omega
      subst this
      simp
    · have h1 := hlip (i + 1) r (by omega) le_rfl
      have h2' := hstep i hir
      have hlt : d i < d (i + 1) := by omega
      exact hcont i hir hlt k hk (by omega)
  have hwi : ∀ i i', i ≤ i' → i' ≤ r → (∀ k, k ≤ i' - i → d (i + k) = d i + k) →
      WalkIncreases Γ b p i i' := fun i i' h1 h2 h3 => ⟨h1, h2, h3⟩
  obtain ⟨hseq3, hseq4⟩ := burnsideJ57_seq r d hr6 h8 hdr hstep hlip hpar hcont h2
  have hd0 : dseq Γ b p 0 = Γ.dist b u := by
    show Γ.dist b (p.getVert 0) = Γ.dist b u
    rw [SimpleGraph.Walk.getVert_zero]
  have hd0' : d 0 = Γ.dist b u := (hdseq 0).symm.trans hd0
  simp only [hdseq]
  refine ⟨⟨SimpleGraph.Walk.getVert_zero p, hr6, hd0', h8, hdr⟩, ?_, ?_, ?_, ?_⟩
  · intro i hi hlt
    have hi8 := h8 i hi.le
    have hm1 : min (i + 8 - d i) r ≤ i + 8 - d i := min_le_left _ _
    have hm2 : min (i + 8 - d i) r ≤ r := min_le_right _ _
    have hm3 : i ≤ min (i + 8 - d i) r := le_min (by omega) hi.le
    refine hwi i _ hm3 hm2 (fun k hk => ?_)
    exact hcont i hi hlt k (by omega) (by omega)
  · intro i hi hid
    rcases Nat.eq_or_lt_of_le hi with hir | hir
    · rw [hir]
      refine hwi r r le_rfl le_rfl (fun k hk => ?_)
      have : k = 0 := by omega
      subst this
      simp
    · refine hwi i r hi le_rfl (fun k hk => ?_)
      exact h2 i hi hid k (by omega)
  · intro h4
    have h4' : d 0 = 4 := hd0'.trans h4
    rcases hseq3 h4' with ⟨h1, h2'⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩
    · left
      exact ⟨h1, hwi 0 4 (by omega) (by omega) (fun k hk => by simpa using h2' k (by omega))⟩
    · right; left
      exact ⟨h1, hwi 0 4 (by omega) (by omega) (fun k hk => by simpa using h2' k (by omega)), h3⟩
    · right; right
      exact ⟨h1, h2', hwi 1 6 (by omega) (by omega) (fun k hk => h3 k (by omega))⟩
  · intro h6
    have h6' : d 0 = 6 := hd0'.trans h6
    rcases hseq4 h6' with h | h | h | ⟨h1, h6'', h2'⟩
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right
      exact ⟨h1, hwi 2 6 (by omega) (by omega) (fun k hk => h2' k (by omega))⟩

private theorem burnsideJ57_J58_abs {Ω : Type} (x : V) {lay : V → ℕ} (hL : Layers Γ 8 x lay) (L : Set Ω)
    (f : Ω → V) (hf : Set.InjOn f L) (hlt : ∀ v ∈ L, Γ.dist x (f v) < 8) :
    ∃ pmap : Ω → Σ z, Γ.Walk x z,
      (∀ v ∈ L, (pmap v).1 = f v ∧ (pmap v).2.length = Γ.dist x (f v) ∧
        ∀ q : Γ.Walk x (f v), q.length = Γ.dist x (f v) →
          (⟨f v, q⟩ : Σ z, Γ.Walk x z) = pmap v) ∧
      Set.BijOn pmap L (GeoFrom Γ x (f '' L)) := by
  classical
  have hex : ∀ z, ∃ w : Γ.Walk x z, w.length = Γ.dist x z :=
    fun z => (hL.reachable z).exists_walk_length_eq_dist
  let pmap : Ω → Σ z, Γ.Walk x z := fun v =>
    if h : v ∈ L then ⟨f v, Classical.choose (hex (f v))⟩ else ⟨x, SimpleGraph.Walk.nil⟩
  have hp1 : ∀ v ∈ L, pmap v = ⟨f v, Classical.choose (hex (f v))⟩ := fun v hv => dif_pos hv
  have hmain : ∀ v ∈ L, (pmap v).1 = f v ∧ (pmap v).2.length = Γ.dist x (f v) ∧
      ∀ q : Γ.Walk x (f v), q.length = Γ.dist x (f v) →
        (⟨f v, q⟩ : Σ z, Γ.Walk x z) = pmap v := by
    intro v hv
    rw [hp1 v hv]
    refine ⟨rfl, Classical.choose_spec (hex (f v)), fun q hq => ?_⟩
    have hz : lay (f v) < 8 := by rw [← hL.dist_eq]; exact hlt v hv
    have := burnsideJ57_geo_unique hL hz q (Classical.choose (hex (f v)))
      (by rw [← hL.dist_eq]; exact hq)
      (by rw [← hL.dist_eq]; exact Classical.choose_spec (hex (f v)))
    rw [this]
  refine ⟨pmap, hmain, ?_, ?_, ?_⟩
  · intro v hv
    rw [hp1 v hv]
    exact ⟨⟨v, hv, rfl⟩, Classical.choose_spec (hex (f v))⟩
  · intro v hv v' hv' h
    have h1 := (hmain v hv).1
    have h2 := (hmain v' hv').1
    apply hf hv hv'
    rw [← h1, ← h2, h]
  · rintro ⟨z, q⟩ ⟨⟨v, hv, rfl⟩, hq⟩
    exact ⟨v, hv, ((hmain v hv).2.2 q hq).symm⟩

end BurnsideJ57Generic

section BurnsideJ57Count

variable {V : Type} (Γ : SimpleGraph V) (b : V)

@[expose] def burnsideJ57_Winc (n : ℕ) (y : V) : Set (Σ z, Γ.Walk y z) :=
  {q | q.2.length = n ∧ ∀ j, j ≤ n → Γ.dist b (q.2.getVert j) = Γ.dist b y + j}

@[expose] def burnsideJ57_consW {Γ : SimpleGraph V} {y y' : V} (h : Γ.Adj y y')
    (q : Σ z, Γ.Walk y' z) : Σ z, Γ.Walk y z :=
  ⟨q.1, SimpleGraph.Walk.cons h q.2⟩

variable {Γ b}

private theorem burnsideJ57_winc_zero (y : V) :
    burnsideJ57_Winc Γ b 0 y = {⟨y, SimpleGraph.Walk.nil⟩} := by
  ext ⟨z, w⟩
  simp only [burnsideJ57_Winc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hl, -⟩
    cases w with
    | nil => rfl
    | cons h w' => simp at hl
  · intro h
    cases h
    refine ⟨rfl, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simp

theorem burnsideJ57_consW_getVert_one {y y' : V} (h : Γ.Adj y y') (q : Σ z, Γ.Walk y' z) :
    (burnsideJ57_consW h q).2.getVert 1 = y' := by
  simp [burnsideJ57_consW]

theorem burnsideJ57_consW_mem {n : ℕ} {y y' : V} (h : Γ.Adj y y')
    (hd : Γ.dist b y' = Γ.dist b y + 1) {q : Σ z, Γ.Walk y' z}
    (hq : q ∈ burnsideJ57_Winc Γ b n y') :
    burnsideJ57_consW h q ∈ burnsideJ57_Winc Γ b (n + 1) y := by
  obtain ⟨hl, hj⟩ := hq
  refine ⟨by simp [burnsideJ57_consW, hl], fun j hjn => ?_⟩
  rcases j with _ | j
  · simp [burnsideJ57_consW]
  · simp only [burnsideJ57_consW, SimpleGraph.Walk.getVert_cons_succ]
    have := hj j (by omega)
    omega

noncomputable def burnsideJ57_firstEquiv (n : ℕ) (y : V) (S : Finset V)
    (hS : ∀ y' ∈ S, Γ.Adj y y' ∧ Γ.dist b y' = Γ.dist b y + 1) :
    (Σ y' : ↥S, ↥(burnsideJ57_Winc Γ b n y')) ≃
      ↥{q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S} :=
  Equiv.ofBijective
    (fun x => ⟨burnsideJ57_consW (hS x.1.1 x.1.2).1 x.2.1,
      burnsideJ57_consW_mem (hS x.1.1 x.1.2).1 (hS x.1.1 x.1.2).2 x.2.2, by
        rw [burnsideJ57_consW_getVert_one]
        exact x.1.2⟩)
    (by
      constructor
      · rintro ⟨⟨y₁, hy₁⟩, ⟨⟨z₁, w₁⟩, hq₁⟩⟩ ⟨⟨y₂, hy₂⟩, ⟨⟨z₂, w₂⟩, hq₂⟩⟩ h
        have h' := congrArg Subtype.val h
        have e1 : y₁ = y₂ := by
          have := congrArg (fun q : Σ z, Γ.Walk y z => q.2.getVert 1) h'
          simpa [burnsideJ57_consW] using this
        subst e1
        have e2 : z₁ = z₂ := (Sigma.mk.inj_iff.1 h').1
        subst e2
        have e3 : w₁ = w₂ := by
          have hl : w₁.length = w₂.length := by
            have h1 : w₁.length = n + 1 - 1 := by simpa using hq₁.1
            have h2 : w₂.length = n + 1 - 1 := by simpa using hq₂.1
            omega
          refine SimpleGraph.Walk.ext_getVert_le_length hl fun k _ => ?_
          have := congrArg (fun q : Σ z, Γ.Walk y z => q.2.getVert (k + 1)) h'
          simpa [burnsideJ57_consW] using this
        subst e3
        rfl
      · rintro ⟨⟨z, w⟩, hw, hS1⟩
        cases w with
        | nil => simp [burnsideJ57_Winc] at hw
        | @cons _ y' _ h w' =>
          have hy' : y' ∈ S := by simpa using hS1
          have hd1 : Γ.dist b y' = Γ.dist b y + 1 := by
            have := hw.2 1 (by simp [hw.1])
            simpa using this
          refine ⟨⟨⟨y', hy'⟩, ⟨⟨z, w'⟩, ?_, ?_⟩⟩, rfl⟩
          · have := hw.1
            simpa using this
          · intro j hj
            have := hw.2 (j + 1) (by have := hw.1; simp at this; omega)
            simp only [SimpleGraph.Walk.getVert_cons_succ] at this
            show Γ.dist b (w'.getVert j) = Γ.dist b y' + j
            omega)

variable (Γ b) in
@[expose] def burnsideJ57_Fp (y : V) : Set V :=
  {y' | Γ.Adj y y' ∧ Γ.dist b y' = Γ.dist b y + 1}

private theorem burnsideJ57_winc_first_mem {n : ℕ} {y : V} {q : Σ z, Γ.Walk y z}
    (hq : q ∈ burnsideJ57_Winc Γ b (n + 1) y) : q.2.getVert 1 ∈ burnsideJ57_Fp Γ b y := by
  obtain ⟨hl, hd⟩ := hq
  refine ⟨?_, hd 1 (by omega)⟩
  have := q.2.adj_getVert_succ (i := 0) (by omega)
  rwa [SimpleGraph.Walk.getVert_zero] at this

private theorem burnsideJ57_winc_finite [Finite V] (n : ℕ) : ∀ y, Finite ↥(burnsideJ57_Winc Γ b n y) := by
  induction n with
  | zero =>
    intro y
    rw [burnsideJ57_winc_zero]
    exact (Set.finite_singleton _).to_subtype
  | succ n ih =>
    intro y
    classical
    haveI : ∀ y', Finite ↥(burnsideJ57_Winc Γ b n y') := ih
    set S : Finset V := (Set.toFinite (burnsideJ57_Fp Γ b y)).toFinset with hSdef
    have hS : ∀ y' ∈ S, Γ.Adj y y' ∧ Γ.dist b y' = Γ.dist b y + 1 := by
      intro y' hy'
      simpa [hSdef, burnsideJ57_Fp] using hy'
    have e := burnsideJ57_firstEquiv (b := b) n y S hS
    haveI : Finite ↥{q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S} :=
      Finite.of_equiv _ e
    have heq : {q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S} =
        burnsideJ57_Winc Γ b (n + 1) y := by
      ext q
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro hq
      have := burnsideJ57_winc_first_mem hq
      simpa [hSdef] using this
    rwa [heq] at this

private theorem burnsideJ57_winc_card_first [Finite V] (n : ℕ) (y : V) (S : Finset V)
    (hS : ∀ y' ∈ S, Γ.Adj y y' ∧ Γ.dist b y' = Γ.dist b y + 1) :
    {q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S}.ncard =
      ∑ y' ∈ S, (burnsideJ57_Winc Γ b n y').ncard := by
  classical
  haveI : ∀ y', Finite ↥(burnsideJ57_Winc Γ b n y') := burnsideJ57_winc_finite n
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (burnsideJ57_firstEquiv (b := b) n y S hS),
    Nat.card_sigma]
  rw [← Finset.sum_coe_sort S (fun y' => (burnsideJ57_Winc Γ b n y').ncard)]
  simp only [Nat.card_coe_set_eq]

private theorem burnsideJ57_Fp_ncard [Finite V] (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {lay : V → ℕ} (hL : Layers Γ 8 b lay) {y : V} (hy : 0 < Γ.dist b y) (hy8 : Γ.dist b y < 8) :
    (burnsideJ57_Fp Γ b y).ncard + 1 = (Γ.neighborSet y).ncard := by
  have hback : {y' | Γ.Adj y y' ∧ Γ.dist b y' + 1 = Γ.dist b y}.ncard = 1 := by
    obtain ⟨y1, ⟨h1, h2⟩, huniq⟩ := burnsideJ57_J59_abs hL (e := Γ.dist b y) rfl hy hy8
    have : {y' | Γ.Adj y y' ∧ Γ.dist b y' + 1 = Γ.dist b y} = {y1} := by
      ext y'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ha, hd⟩
        exact huniq y' ⟨ha, by omega⟩
      · rintro rfl
        exact ⟨h1, by omega⟩
    rw [this, Set.ncard_singleton]
  have hsplit : Γ.neighborSet y =
      {y' | Γ.Adj y y' ∧ Γ.dist b y' + 1 = Γ.dist b y} ∪ burnsideJ57_Fp Γ b y := by
    ext y'
    simp only [SimpleGraph.mem_neighborSet, Set.mem_union, Set.mem_setOf_eq, burnsideJ57_Fp]
    constructor
    · intro h
      have := burnsideJ57_lay_adj col hc hL h
      have e1 := hL.dist_eq y
      have e2 := hL.dist_eq y'
      rcases this with h3 | h3
      · right; exact ⟨h, by omega⟩
      · left; exact ⟨h, by omega⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint {y' | Γ.Adj y y' ∧ Γ.dist b y' + 1 = Γ.dist b y}
      (burnsideJ57_Fp Γ b y) := by
    rw [Set.disjoint_left]
    rintro y' ⟨_, h1⟩ ⟨_, h2⟩
    omega
  rw [hsplit, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hback]
  omega

private theorem burnsideJ57_Fp_base : burnsideJ57_Fp Γ b b = Γ.neighborSet b := by
  ext y'
  simp only [burnsideJ57_Fp, SimpleGraph.mem_neighborSet, Set.mem_setOf_eq, SimpleGraph.dist_self,
    zero_add]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, SimpleGraph.dist_eq_one_iff_adj.2 h⟩

@[expose] def burnsideJ57_Nf : ℕ → ℕ
  | 0 => 1
  | n + 1 => (if Even (n + 1) then 4 else 2) * burnsideJ57_Nf n

private theorem burnsideJ57_count_A [Finite V] (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {lay : V → ℕ} (hL : Layers Γ 8 b lay)
    (hdeg5 : ∀ x, col x = col b → (Γ.neighborSet x).ncard = 5)
    (hdeg3 : ∀ x, col x ≠ col b → (Γ.neighborSet x).ncard = 3) :
    ∀ n, n ≤ 7 → ∀ y, Γ.dist b y + n = 8 →
      (burnsideJ57_Winc Γ b n y).ncard = burnsideJ57_Nf n := by
  intro n
  induction n with
  | zero =>
    intro _ y _
    rw [burnsideJ57_winc_zero, Set.ncard_singleton]
    rfl
  | succ n ih =>
    intro hn y hy
    classical
    set S : Finset V := (Set.toFinite (burnsideJ57_Fp Γ b y)).toFinset with hSdef
    have hS : ∀ y' ∈ S, Γ.Adj y y' ∧ Γ.dist b y' = Γ.dist b y + 1 := by
      intro y' hy'
      simpa [hSdef, burnsideJ57_Fp] using hy'
    have hset : {q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S} =
        burnsideJ57_Winc Γ b (n + 1) y := by
      ext q
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro hq
      have := burnsideJ57_winc_first_mem hq
      simpa [hSdef] using this
    rw [← hset, burnsideJ57_winc_card_first n y S hS]
    have hterm : ∀ y' ∈ S, (burnsideJ57_Winc Γ b n y').ncard = burnsideJ57_Nf n := fun y' hy' =>
      ih (by omega) y' (by have := (hS y' hy').2; omega)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
    have hcard : S.card = (burnsideJ57_Fp Γ b y).ncard :=
      (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
    have hFp := burnsideJ57_Fp_ncard col hc hL (y := y) (by omega) (by omega)
    have hpar := burnsideJ57_dist_parity col hc (hL.reachable y)
    show S.card * burnsideJ57_Nf n = (if Even (n + 1) then 4 else 2) * burnsideJ57_Nf n
    by_cases he : Even (n + 1)
    · have hev : Even (Γ.dist b y) := by
        rw [Nat.even_iff] at he ⊢
        omega
      have hcol := hpar.1 hev
      have := hdeg5 y (hcol.symm)
      rw [if_pos he]
      rw [hcard]
      congr 1
      omega
    · have hev : ¬ Even (Γ.dist b y) := by
        rw [Nat.even_iff] at he ⊢
        omega
      have hcol : col b ≠ col y := fun h => hev (hpar.2 h)
      have := hdeg3 y (fun h => hcol h.symm)
      rw [if_neg he]
      rw [hcard]
      congr 1
      omega

private theorem burnsideJ57_count_B [Finite V] (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {lay : V → ℕ} (hL : Layers Γ 8 b lay)
    (hdeg5 : ∀ x, col x = col b → (Γ.neighborSet x).ncard = 5)
    (hdeg3 : ∀ x, col x ≠ col b → (Γ.neighborSet x).ncard = 3) {n : ℕ} (hn : n ≤ 7) {y : V}
    (hy : Γ.dist b y + (n + 1) = 8) {y' : V} (hy' : y' ∈ burnsideJ57_Fp Γ b y) :
    {q ∈ burnsideJ57_Winc Γ b (n + 1) y | y' ∉ q.2.support}.ncard =
      ((burnsideJ57_Fp Γ b y).ncard - 1) * burnsideJ57_Nf n := by
  classical
  set S : Finset V := (Set.toFinite (burnsideJ57_Fp Γ b y)).toFinset with hSdef
  have hyS : y' ∈ S := by simpa [hSdef] using hy'
  have hS : ∀ y'' ∈ S.erase y', Γ.Adj y y'' ∧ Γ.dist b y'' = Γ.dist b y + 1 := by
    intro y'' hy''
    have := Finset.mem_of_mem_erase hy''
    simpa [hSdef, burnsideJ57_Fp] using this
  have hset : {q ∈ burnsideJ57_Winc Γ b (n + 1) y | y' ∉ q.2.support} =
      {q ∈ burnsideJ57_Winc Γ b (n + 1) y | q.2.getVert 1 ∈ S.erase y'} := by
    ext q
    simp only [Set.mem_setOf_eq, Finset.mem_erase]
    constructor
    · rintro ⟨hq, hnot⟩
      refine ⟨hq, ?_, by simpa [hSdef] using burnsideJ57_winc_first_mem hq⟩
      intro h1
      exact hnot (h1 ▸ SimpleGraph.Walk.getVert_mem_support _ _)
    · rintro ⟨hq, hne, -⟩
      refine ⟨hq, fun hmem => ?_⟩
      obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hmem
      have hd := hq.2 j (by have := hq.1; omega)
      have hd' : Γ.dist b y' = Γ.dist b y + 1 := hy'.2
      rw [hj, hd'] at hd
      have : j = 1 := by omega
      subst this
      exact hne hj
  rw [hset, burnsideJ57_winc_card_first n y (S.erase y') hS]
  have hterm : ∀ y'' ∈ S.erase y', (burnsideJ57_Winc Γ b n y'').ncard = burnsideJ57_Nf n :=
    fun y'' hy'' =>
      burnsideJ57_count_A col hc hL hdeg5 hdeg3 n hn y'' (by have := (hS y'' hy'').2; omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hyS]
  have hcard : S.card = (burnsideJ57_Fp Γ b y).ncard :=
    (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
  rw [hcard]

private theorem burnsideJ57_J511_abs [Finite V] (col : V → Bool) (hc : ∀ x y, Γ.Adj x y → col x ≠ col y)
    {lay : V → ℕ} (hL : Layers Γ 8 b lay)
    (hdeg5 : ∀ x, col x = col b → (Γ.neighborSet x).ncard = 5)
    (hdeg3 : ∀ x, col x ≠ col b → (Γ.neighborSet x).ncard = 3) {y : V} {e : ℕ}
    (hy : Γ.dist b y = e) (he8 : e < 8) :
    (e = 0 → (NgeoSet Γ b y e).ncard = 5120 ∧
      ∀ y' ∈ Γ.neighborSet y, Γ.dist b y' = e + 1 →
        {q ∈ NgeoSet Γ b y e | y' ∉ q.2.support}.ncard = 4096) ∧
    (0 < e → Even e → (NgeoSet Γ b y e).ncard = 8 ^ ((8 - e) / 2) ∧
      ∀ y' ∈ Γ.neighborSet y, Γ.dist b y' = e + 1 →
        {q ∈ NgeoSet Γ b y e | y' ∉ q.2.support}.ncard = 6 * 8 ^ ((6 - e) / 2)) ∧
    (Odd e → (NgeoSet Γ b y e).ncard = 2 * 8 ^ ((7 - e) / 2) ∧
      ∀ y' ∈ Γ.neighborSet y, Γ.dist b y' = e + 1 →
        {q ∈ NgeoSet Γ b y e | y' ∉ q.2.support}.ncard = 8 ^ ((7 - e) / 2)) := by
  classical
  have hN : NgeoSet Γ b y e = burnsideJ57_Winc Γ b (8 - e) y := by
    subst hy
    rfl
  have hNf : ∀ n, n ≤ 7 → burnsideJ57_Winc Γ b n y ≠ ∅ → True := fun _ _ _ => trivial
  have hneighbor : ∀ y' ∈ Γ.neighborSet y, Γ.dist b y' = e + 1 →
      y' ∈ burnsideJ57_Fp Γ b y := fun y' hy' hd => ⟨hy', by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro he0
    subst he0
    have hyb : y = b := by
      have hr := hL.reachable y
      exact (hr.dist_eq_zero_iff.1 (by simpa using hy)).symm
    subst hyb
    rw [hN]
    simp only [Nat.sub_zero]
    have hFp : (burnsideJ57_Fp Γ y y).ncard = 5 := by
      rw [burnsideJ57_Fp_base]
      exact hdeg5 y rfl
    refine ⟨?_, fun y' hy' hd => ?_⟩
    · set S : Finset V := (Set.toFinite (burnsideJ57_Fp Γ y y)).toFinset with hSdef
      have hS : ∀ y' ∈ S, Γ.Adj y y' ∧ Γ.dist y y' = Γ.dist y y + 1 := by
        intro y' hy'
        simpa [hSdef, burnsideJ57_Fp] using hy'
      have hset : {q ∈ burnsideJ57_Winc Γ y 8 y | q.2.getVert 1 ∈ S} =
          burnsideJ57_Winc Γ y 8 y := by
        ext q
        simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
        intro hq
        have := burnsideJ57_winc_first_mem (n := 7) hq
        simpa [hSdef] using this
      rw [show (8 : ℕ) = 7 + 1 from rfl, ← hset, burnsideJ57_winc_card_first 7 y S hS]
      have hterm : ∀ y' ∈ S, (burnsideJ57_Winc Γ y 7 y').ncard = burnsideJ57_Nf 7 := fun y' hy' =>
        burnsideJ57_count_A col hc hL hdeg5 hdeg3 7 le_rfl y' (by have := (hS y' hy').2; omega)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
      have hcard : S.card = (burnsideJ57_Fp Γ y y).ncard :=
        (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
      rw [hcard, hFp]
      decide
    · rw [show (8 : ℕ) = 7 + 1 from rfl,
        burnsideJ57_count_B col hc hL hdeg5 hdeg3 (n := 7) le_rfl (by simp)
          (hneighbor y' hy' hd), hFp]
      decide
  · intro he0 hev
    have hn : 8 - e ≤ 7 := by omega
    have hA := burnsideJ57_count_A col hc hL hdeg5 hdeg3 (8 - e) hn y (by omega)
    have hFp := burnsideJ57_Fp_ncard col hc hL (y := y) (by omega) (by omega)
    have hpar := burnsideJ57_dist_parity col hc (hL.reachable y)
    have hev' : Even (Γ.dist b y) := by rw [hy]; exact hev
    have hdeg := hdeg5 y (hpar.1 hev').symm
    have hFp4 : (burnsideJ57_Fp Γ b y).ncard = 4 := by omega
    rw [hN]
    refine ⟨?_, fun y' hy' hd => ?_⟩
    · rw [hA]
      rw [Nat.even_iff] at hev
      interval_cases e <;> first | omega | decide
    · have := burnsideJ57_count_B col hc hL hdeg5 hdeg3 (n := 7 - e) (by omega) (y := y)
        (by omega) (hneighbor y' hy' hd)
      rw [show 8 - e = 7 - e + 1 by omega, this, hFp4]
      rw [Nat.even_iff] at hev
      interval_cases e <;> first | omega | decide
  · intro hodd
    have hn : 8 - e ≤ 7 := by
      rcases hodd with ⟨k, hk⟩
      omega
    have he0 : 0 < e := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hA := burnsideJ57_count_A col hc hL hdeg5 hdeg3 (8 - e) hn y (by omega)
    have hFp := burnsideJ57_Fp_ncard col hc hL (y := y) (by omega) (by omega)
    have hpar := burnsideJ57_dist_parity col hc (hL.reachable y)
    have hev' : ¬ Even (Γ.dist b y) := by
      rw [hy]
      exact Nat.not_even_iff_odd.2 hodd
    have hcol : col b ≠ col y := fun h => hev' (hpar.2 h)
    have hdeg := hdeg3 y (fun h => hcol h.symm)
    have hFp2 : (burnsideJ57_Fp Γ b y).ncard = 2 := by omega
    rw [hN]
    refine ⟨?_, fun y' hy' hd => ?_⟩
    · rw [hA]
      rw [Nat.odd_iff] at hodd
      interval_cases e <;> first | omega | decide
    · have := burnsideJ57_count_B col hc hL hdeg5 hdeg3 (n := 7 - e) (by omega) (y := y)
        (by omega) (hneighbor y' hy' hd)
      rw [show 8 - e = 7 - e + 1 by omega, this, hFp2]
      rw [Nat.odd_iff] at hodd
      interval_cases e <;> first | omega | decide

end BurnsideJ57Count

end BurnsideJ57PartA

section BurnsideJ57PartB

open CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

structure burnsideJ57_OctBase {A B : Type} (Γ : SimpleGraph (A ⊕ B)) : Prop where
  bip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight
  layers : ∀ x, ∃ lay, Layers Γ 8 x lay

structure burnsideJ57_OctDeg {A B : Type} (Γ : SimpleGraph (A ⊕ B)) : Prop where
  deg5 : ∀ a, (Γ.neighborSet (Sum.inl a)).ncard = 5
  deg3 : ∀ c, (Γ.neighborSet (Sum.inr c)).ncard = 3

structure burnsideJ57_OctCard {A B : Type} (Γ : SimpleGraph (A ⊕ B)) (b : A) : Prop where
  card2 : {a : A | Γ.dist (Sum.inl b) (Sum.inl a) = 2}.ncard = 10
  card4 : {a : A | Γ.dist (Sum.inl b) (Sum.inl a) = 4}.ncard = 80
  card6 : {a : A | Γ.dist (Sum.inl b) (Sum.inl a) = 6}.ncard = 640
  card8 : {a : A | Γ.dist (Sum.inl b) (Sum.inl a) = 8}.ncard = 1024

structure burnsideJ57_Oct12 {A B : Type} (Γ : SimpleGraph (A ⊕ B)) (b : A) : Prop where
  q12 : ∀ a : A, (Γ.dist (Sum.inl b) (Sum.inl a) = 2 ∨ Γ.dist (Sum.inl b) (Sum.inl a) = 4 ∨
      Γ.dist (Sum.inl b) (Sum.inl a) = 6) →
    {c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧ 0 < Γ.dist (Sum.inl a) (Sum.inl c) ∧
        Γ.dist (Sum.inl a) (Sum.inl c) < 8}.ncard ≤ 2 ^ 9 ∧
      ({c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧ 0 < Γ.dist (Sum.inl a) (Sum.inl c) ∧
        Γ.dist (Sum.inl a) (Sum.inl c) < 8}.ncard = 2 ^ 9 ↔ Γ.dist (Sum.inl b) (Sum.inl a) = 2)

structure burnsideJ57_Oct7 {A B : Type} (Γ : SimpleGraph (A ⊕ B)) (b : A) : Prop where
  q7 : ∀ (x y x' : A) (l : B), Γ.dist (Sum.inl b) (Sum.inl x) = 2 →
    Γ.dist (Sum.inl b) (Sum.inl y) = 2 → Γ.Adj (Sum.inl b) (Sum.inr l) →
    Γ.Adj (Sum.inl x) (Sum.inr l) → Γ.Adj (Sum.inl x') (Sum.inr l) → x' ≠ b → x' ≠ x →
    ({c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧ 0 < Γ.dist (Sum.inl y) (Sum.inl c) ∧
        Γ.dist (Sum.inl y) (Sum.inl c) < 8} =
      {c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧
        ¬ (0 < Γ.dist (Sum.inl x) (Sum.inl c) ∧ Γ.dist (Sum.inl x) (Sum.inl c) < 8)} ↔ y = x')

private theorem burnsideJ57_oct_bip (x y : Vtx) (h : octGraph.Adj x y) : x.isRight ≠ y.isRight := by
  cases x <;> cases y <;> first | exact h.elim | simp

section Oct

private theorem burnsideJ57_oct_cards :
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 2}.ncard = 10 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 4}.ncard = 80 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 6}.ncard = 640 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 8}.ncard = 1024 :=
  Certificates.certificate7340.2.2

private theorem burnsideJ57_oct_deg :
    (∀ p : Fin 1755, (octGraph.neighborSet (Sum.inl p)).ncard = 5) ∧
    ∀ v : Fin 2925, (octGraph.neighborSet (Sum.inr v)).ncard = 3 :=
  ⟨Certificates.certificate7340.1, Certificates.certificate7340.2.1⟩

end Oct

section OctLam

private theorem burnsideJ57_oct_q12
    (j : Fin 1755)
    (hj : octGraph.dist (Sum.inl 0) (Sum.inl j) = 2 ∨ octGraph.dist (Sum.inl 0) (Sum.inl j) = 4 ∨
      octGraph.dist (Sum.inl 0) (Sum.inl j) = 6) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      ≤ 2 ^ 9 ∧
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      = 2 ^ 9 ↔ octGraph.dist (Sum.inl 0) (Sum.inl j) = 2) :=
  Certificates.certificate7341 j hj

end OctLam

section OctTheta

private theorem burnsideJ57_oct_q7
    (x y x' : Fin 1755) (l : Fin 2925)
    (hx : octGraph.dist (Sum.inl 0) (Sum.inl x) = 2)
    (hy : octGraph.dist (Sum.inl 0) (Sum.inl y) = 2)
    (h0 : octGraph.Adj (Sum.inl 0) (Sum.inr l)) (hxl : octGraph.Adj (Sum.inl x) (Sum.inr l))
    (hx'l : octGraph.Adj (Sum.inl x') (Sum.inr l)) (hx'0 : x' ≠ 0) (hx'x : x' ≠ x) :
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl y) (Sum.inl c) ∧ octGraph.dist (Sum.inl y) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (Sum.inl x) (Sum.inl c) ∧ octGraph.dist (Sum.inl x) (Sum.inl c) < 8)} ↔
      y = x') :=
  Certificates.certificate7342 x y x' l hx hy h0 hxl hx'l hx'0 hx'x

end OctTheta

section OctAll

private theorem burnsideJ57_oct_layers_all
    : ∀ x : Vtx, ∃ lay, Layers octGraph 8 x lay :=
  Certificates.certificate4160.2.1

private theorem burnsideJ57_octBase_oct
    : burnsideJ57_OctBase octGraph where
  bip := burnsideJ57_oct_bip
  layers := burnsideJ57_oct_layers_all

end OctAll

section OctData

private theorem burnsideJ57_octDeg_oct
    : burnsideJ57_OctDeg octGraph where
  deg5 := burnsideJ57_oct_deg.1
  deg3 := burnsideJ57_oct_deg.2

private theorem burnsideJ57_octCard_oct
    : burnsideJ57_OctCard octGraph (0 : Fin 1755) where
  card2 := burnsideJ57_oct_cards.1
  card4 := burnsideJ57_oct_cards.2.1
  card6 := burnsideJ57_oct_cards.2.2.1
  card8 := burnsideJ57_oct_cards.2.2.2

end OctData

section OctData12

private theorem burnsideJ57_oct12_oct
    : burnsideJ57_Oct12 octGraph (0 : Fin 1755) where
  q12 := fun a ha => burnsideJ57_oct_q12 a ha

end OctData12

section OctData7

private theorem burnsideJ57_oct7_oct
    : burnsideJ57_Oct7 octGraph (0 : Fin 1755) where
  q7 := fun x y x' l hx hy h0 hxl hx'l hx'0 hx'x =>
    burnsideJ57_oct_q7 x y x' l hx hy h0 hxl hx'l hx'0 hx'x

end OctData7

end BurnsideJ57PartB

section BurnsideJ57PartC

open CFSG.Quasithin.H13.F45Ru

section Transport

variable {A B A' B' : Type} {Γ : SimpleGraph (A ⊕ B)} {Γ' : SimpleGraph (A' ⊕ B')}

@[expose] def burnsideJ57_isoOf (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c))) :
    Γ ≃g Γ' where
  toEquiv := Equiv.sumCongr eA eB
  map_rel_iff' := by
    intro x y
    rcases x with a | c <;> rcases y with a' | c'
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_toEmbedding]
      exact ⟨fun h => ((hbip' _ _ h) rfl).elim, fun h => ((hbip _ _ h) rfl).elim⟩
    · exact (hadj a c').symm
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_toEmbedding]
      rw [SimpleGraph.adj_comm Γ', SimpleGraph.adj_comm Γ]
      exact (hadj a' c).symm
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_toEmbedding]
      exact ⟨fun h => ((hbip' _ _ h) rfl).elim, fun h => ((hbip _ _ h) rfl).elim⟩

private theorem burnsideJ57_dist_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (u v : V) : H.dist (e u) (e v) = G.dist u v := by
  have key : ∀ {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V),
      H.dist (e u) (e v) ≤ G.dist u v := by
    intro V W G H e u v
    by_cases hr : G.Reachable u v
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
      calc H.dist (e u) (e v) ≤ (p.map e.toHom).length := SimpleGraph.dist_le _
        _ = G.dist u v := by rw [SimpleGraph.Walk.length_map, hp]
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
      have : ¬ H.Reachable (e u) (e v) := fun h => hr (by simpa using h.map e.symm.toHom)
      rw [SimpleGraph.dist_eq_zero_of_not_reachable this]
  refine le_antisymm (key e u v) ?_
  have := key e.symm (e u) (e v)
  simpa using this

private theorem burnsideJ57_ncard_equiv {α β : Type} (e : α ≃ β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ a, P a ↔ Q (e a)) : {a | P a}.ncard = {b | Q b}.ncard := by
  have : {b | Q b} = e '' {a | P a} := by
    ext b
    constructor
    · intro hb
      exact ⟨e.symm b, (h _).2 (by simpa using hb), by simp⟩
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
  rw [this, Set.ncard_image_of_injective _ e.injective]

private theorem burnsideJ57_iso_neighborSet {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (x : V) : H.neighborSet (e x) = e '' G.neighborSet x := by
  ext z
  constructor
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    have : H.Adj (e x) (e (e.symm z)) := by simpa using hz
    exact e.map_adj_iff.1 this
  · rintro ⟨w, hw, rfl⟩
    exact e.map_adj_iff.2 hw

private theorem burnsideJ57_OctBase_of_iso (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    (H : burnsideJ57_OctBase Γ') : burnsideJ57_OctBase Γ := by
  set e := burnsideJ57_isoOf eA eB hbip hbip' hadj with he
  refine ⟨hbip, fun x => ?_⟩
  obtain ⟨lay, hl⟩ := H.layers (e x)
  refine ⟨fun z => lay (e z), ?_⟩
  have := burnsideJ57_layers_iso e.symm hl
  simpa using this

private theorem burnsideJ57_OctDeg_of_iso (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    (H : burnsideJ57_OctDeg Γ') : burnsideJ57_OctDeg Γ := by
  set e := burnsideJ57_isoOf eA eB hbip hbip' hadj with he
  refine ⟨fun a => ?_, fun c => ?_⟩
  · have h := H.deg5 (eA a)
    have h1 : e (Sum.inl a) = Sum.inl (eA a) := rfl
    rw [← h1, burnsideJ57_iso_neighborSet, Set.ncard_image_of_injective _ e.injective] at h
    exact h
  · have h := H.deg3 (eB c)
    have h1 : e (Sum.inr c) = Sum.inr (eB c) := rfl
    rw [← h1, burnsideJ57_iso_neighborSet, Set.ncard_image_of_injective _ e.injective] at h
    exact h

private theorem burnsideJ57_dist_iso_points (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    (x y : A) : Γ'.dist (Sum.inl (eA x)) (Sum.inl (eA y)) = Γ.dist (Sum.inl x) (Sum.inl y) :=
  burnsideJ57_dist_iso (burnsideJ57_isoOf eA eB hbip hbip' hadj) (Sum.inl x) (Sum.inl y)

private theorem burnsideJ57_OctCard_of_iso (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    {b : A} {b' : A'} (hb : eA b = b') (H : burnsideJ57_OctCard Γ' b') :
    burnsideJ57_OctCard Γ b := by
  have hd := burnsideJ57_dist_iso_points eA eB hbip hbip' hadj
  have hd0 : ∀ y : A, Γ'.dist (Sum.inl b') (Sum.inl (eA y)) = Γ.dist (Sum.inl b) (Sum.inl y) := by
    intro y
    rw [← hb]
    exact hd b y
  have hsetA : ∀ S : Set A, ∀ S' : Set A', (∀ a, a ∈ S ↔ eA a ∈ S') → S.ncard = S'.ncard :=
    fun S S' h => burnsideJ57_ncard_equiv eA _ _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← H.card2]
    exact hsetA _ _ fun a => by simp only [Set.mem_setOf_eq, hd0]
  · rw [← H.card4]
    exact hsetA _ _ fun a => by simp only [Set.mem_setOf_eq, hd0]
  · rw [← H.card6]
    exact hsetA _ _ fun a => by simp only [Set.mem_setOf_eq, hd0]
  · rw [← H.card8]
    exact hsetA _ _ fun a => by simp only [Set.mem_setOf_eq, hd0]

private theorem burnsideJ57_Oct12_of_iso (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    {b : A} {b' : A'} (hb : eA b = b') (H : burnsideJ57_Oct12 Γ' b') :
    burnsideJ57_Oct12 Γ b := by
  have hd := burnsideJ57_dist_iso_points eA eB hbip hbip' hadj
  have hd0 : ∀ y : A, Γ'.dist (Sum.inl b') (Sum.inl (eA y)) = Γ.dist (Sum.inl b) (Sum.inl y) := by
    intro y
    rw [← hb]
    exact hd b y
  have hsetA : ∀ S : Set A, ∀ S' : Set A', (∀ a, a ∈ S ↔ eA a ∈ S') → S.ncard = S'.ncard :=
    fun S S' h => burnsideJ57_ncard_equiv eA _ _ h
  refine ⟨fun a ha => ?_⟩
  have ha' : Γ'.dist (Sum.inl b') (Sum.inl (eA a)) = 2 ∨ Γ'.dist (Sum.inl b') (Sum.inl (eA a)) = 4 ∨
      Γ'.dist (Sum.inl b') (Sum.inl (eA a)) = 6 := by simpa only [hd0] using ha
  obtain ⟨h1, h2⟩ := H.q12 (eA a) ha'
  have hc : {c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧ 0 < Γ.dist (Sum.inl a) (Sum.inl c) ∧
      Γ.dist (Sum.inl a) (Sum.inl c) < 8}.ncard =
      {c : A' | Γ'.dist (Sum.inl b') (Sum.inl c) = 8 ∧ 0 < Γ'.dist (Sum.inl (eA a)) (Sum.inl c) ∧
      Γ'.dist (Sum.inl (eA a)) (Sum.inl c) < 8}.ncard :=
    hsetA _ _ fun c => by simp only [Set.mem_setOf_eq, hd0, hd]
  rw [hc]
  refine ⟨h1, ?_⟩
  rw [h2, hd0]

private theorem burnsideJ57_Oct7_of_iso (eA : A ≃ A') (eB : B ≃ B')
    (hbip : ∀ x y, Γ.Adj x y → x.isRight ≠ y.isRight)
    (hbip' : ∀ x y, Γ'.Adj x y → x.isRight ≠ y.isRight)
    (hadj : ∀ a c, Γ.Adj (Sum.inl a) (Sum.inr c) ↔ Γ'.Adj (Sum.inl (eA a)) (Sum.inr (eB c)))
    {b : A} {b' : A'} (hb : eA b = b') (H : burnsideJ57_Oct7 Γ' b') :
    burnsideJ57_Oct7 Γ b := by
  have hd := burnsideJ57_dist_iso_points eA eB hbip hbip' hadj
  have hd0 : ∀ y : A, Γ'.dist (Sum.inl b') (Sum.inl (eA y)) = Γ.dist (Sum.inl b) (Sum.inl y) := by
    intro y
    rw [← hb]
    exact hd b y
  refine ⟨fun x y x' l hx hy h0 hxl hx'l hx'0 hx'x => ?_⟩
  have hx2 : Γ'.dist (Sum.inl b') (Sum.inl (eA x)) = 2 := by rw [hd0]; exact hx
  have hy2 : Γ'.dist (Sum.inl b') (Sum.inl (eA y)) = 2 := by rw [hd0]; exact hy
  have h0' : Γ'.Adj (Sum.inl b') (Sum.inr (eB l)) := by
    rw [← hb]
    exact (hadj b l).1 h0
  have hxl' := (hadj x l).1 hxl
  have hx'l' := (hadj x' l).1 hx'l
  have hx'0' : eA x' ≠ b' := fun h => hx'0 (eA.injective (h.trans hb.symm))
  have hx'x' : eA x' ≠ eA x := fun h => hx'x (eA.injective h)
  have key := H.q7 (eA x) (eA y) (eA x') (eB l) hx2 hy2 h0' hxl' hx'l' hx'0' hx'x'
  have himg : ∀ S : Set A, ∀ S' : Set A', (∀ a, a ∈ S ↔ eA a ∈ S') → eA '' S = S' := by
    intro S S' h
    ext a'
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro ha'
      exact ⟨eA.symm a', (h _).2 (by simpa using ha'), by simp⟩
  have e1 := himg {c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧ 0 < Γ.dist (Sum.inl y) (Sum.inl c) ∧
      Γ.dist (Sum.inl y) (Sum.inl c) < 8}
    {c : A' | Γ'.dist (Sum.inl b') (Sum.inl c) = 8 ∧ 0 < Γ'.dist (Sum.inl (eA y)) (Sum.inl c) ∧
      Γ'.dist (Sum.inl (eA y)) (Sum.inl c) < 8} (fun c => by simp only [Set.mem_setOf_eq, hd0, hd])
  have e2 := himg {c : A | Γ.dist (Sum.inl b) (Sum.inl c) = 8 ∧
      ¬ (0 < Γ.dist (Sum.inl x) (Sum.inl c) ∧ Γ.dist (Sum.inl x) (Sum.inl c) < 8)}
    {c : A' | Γ'.dist (Sum.inl b') (Sum.inl c) = 8 ∧
      ¬ (0 < Γ'.dist (Sum.inl (eA x)) (Sum.inl c) ∧ Γ'.dist (Sum.inl (eA x)) (Sum.inl c) < 8)}
    (fun c => by simp only [Set.mem_setOf_eq, hd0, hd])
  rw [← e1, ← e2, Set.image_eq_image eA.injective, eA.injective.eq_iff] at key
  exact key

end Transport

section CosetIso

variable {F X Y : Type} [Group F]

private theorem burnsideJ57_incGraph_equiv (M1 M2 : Subgroup F) (P : F →* Equiv.Perm X)
    (Λ : F →* Equiv.Perm Y) (inc : X → Y → Prop) (x₀ : X) (y₀ : Y)
    (hinc : ∀ f x y, inc (P f x) (Λ f y) ↔ inc x y) (h0 : inc x₀ y₀)
    (hM1 : ∀ f, f ∈ M1 ↔ P f x₀ = x₀) (hM2 : ∀ f, f ∈ M2 ↔ Λ f y₀ = y₀)
    (hPtr : ∀ x, ∃ f, P f x₀ = x) (hΛtr : ∀ y, ∃ f, Λ f y₀ = y)
    (hflag : ∀ x, inc x y₀ → ∃ m ∈ M2, P m x₀ = x) :
    ∃ (eA : F ⧸ M1 ≃ X) (eB : F ⧸ M2 ≃ Y), (∀ f : F, eA (f : F ⧸ M1) = P f x₀) ∧
      (∀ f : F, eB (f : F ⧸ M2) = Λ f y₀) ∧
      ∀ a c, (incGraph M1 M2).Adj (Sum.inl a) (Sum.inr c) ↔ inc (eA a) (eB c) := by
  have hfa : ∀ a b : F, a⁻¹ * b ∈ M1 → P a x₀ = P b x₀ := by
    intro a b hab
    have h := (hM1 _).1 hab
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply] at h
    have := congrArg (P a) h
    simpa using this.symm
  have hfb : ∀ a b : F, a⁻¹ * b ∈ M2 → Λ a y₀ = Λ b y₀ := by
    intro a b hab
    have h := (hM2 _).1 hab
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply] at h
    have := congrArg (Λ a) h
    simpa using this.symm
  let fa : F ⧸ M1 → X := Quotient.lift (fun f => P f x₀) (fun a b hab =>
    hfa a b (QuotientGroup.leftRel_apply.1 hab))
  let fb : F ⧸ M2 → Y := Quotient.lift (fun f => Λ f y₀) (fun a b hab =>
    hfb a b (QuotientGroup.leftRel_apply.1 hab))
  have hfa' : ∀ f : F, fa (f : F ⧸ M1) = P f x₀ := fun f => rfl
  have hfb' : ∀ f : F, fb (f : F ⧸ M2) = Λ f y₀ := fun f => rfl
  have hinjA : Function.Injective fa := by
    intro a b hab
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hfa', hfa'] at hab
    rw [QuotientGroup.eq, hM1]
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [← hab]
    simp
  have hinjB : Function.Injective fb := by
    intro a b hab
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hfb', hfb'] at hab
    rw [QuotientGroup.eq, hM2]
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [← hab]
    simp
  have hsurjA : Function.Surjective fa := fun x => by
    obtain ⟨f, hf⟩ := hPtr x
    exact ⟨f, by rw [hfa', hf]⟩
  have hsurjB : Function.Surjective fb := fun y => by
    obtain ⟨f, hf⟩ := hΛtr y
    exact ⟨f, by rw [hfb', hf]⟩
  refine ⟨Equiv.ofBijective fa ⟨hinjA, hsurjA⟩, Equiv.ofBijective fb ⟨hinjB, hsurjB⟩, hfa', hfb',
    ?_⟩
  intro a c
  obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨f', rfl⟩ := QuotientGroup.mk_surjective c
  rw [burnsideJ55_inc_adj_inl_inr]
  show _ ↔ inc (fa (f : F ⧸ M1)) (fb (f' : F ⧸ M2))
  rw [hfa', hfb']
  constructor
  · rintro ⟨y, h1, h2⟩
    have e1 : fa (f : F ⧸ M1) = fa (y : F ⧸ M1) := by rw [h1]
    have e2 : fb (f' : F ⧸ M2) = fb (y : F ⧸ M2) := by rw [h2]
    rw [hfa', hfa'] at e1
    rw [hfb', hfb'] at e2
    rw [e1, e2, hinc]
    exact h0
  · intro hi
    have := (hinc f'⁻¹ _ _).2 hi
    have hx : inc (P (f'⁻¹ * f) x₀) y₀ := by
      simpa [map_mul, Equiv.Perm.mul_apply] using this
    obtain ⟨m, hm, hmx⟩ := hflag _ hx
    refine ⟨f' * m, ?_, ?_⟩
    · rw [QuotientGroup.eq, hM1]
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      have h2 := hmx
      simp only [map_mul, Equiv.Perm.mul_apply] at h2
      rw [h2]
      simp
    · rw [QuotientGroup.eq]
      have : f'⁻¹ * (f' * m) = m := by group
      rw [this]
      exact hm

end CosetIso

end BurnsideJ57PartC

section BurnsideJ57Pair

open CFSG.Quasithin CFSG.QuasithinUnique

private theorem burnsideJ57_pair_conj {Y : Type} [Group Y] [Finite Y] {T T' P Q Q' : Subgroup Y}
    (h : IsYAmalgamPair T P Q) (h' : IsYAmalgamPair T' P Q') :
    ∃ u ∈ P, ∀ x : Y, x ∈ Q' ↔ u⁻¹ * x * u ∈ Q := by
  have hTP : T ≤ P := Subgroup.le_normalizer.trans ((h.2.2 P).mpr (Or.inl rfl)).2
  have hT'P : T' ≤ P := Subgroup.le_normalizer.trans ((h'.2.2 P).mpr (Or.inl rfl)).2
  have hS : IsSylowTwoOf T P := CFSG.Quasithin.F7.isSylowTwoOf_mono_right h.1 hTP le_top
  have hS' : IsSylowTwoOf T' P := CFSG.Quasithin.F7.isSylowTwoOf_mono_right h'.1 hT'P le_top
  obtain ⟨u, hu, hconj⟩ := IsSylowTwoOf.exists_conj hS hS'
  have hY := IsYAmalgamPair.map (MulAut.conj u) h
  have hPmap : P.map (MulAut.conj u).toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [MulAut.conj_apply] using P.mul_mem (P.mul_mem hu hp) (P.inv_mem hu)
    · intro hx
      refine ⟨u⁻¹ * x * u, P.mul_mem (P.mul_mem (P.inv_mem hu) hx) hu, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  rw [← hconj, hPmap] at hY
  obtain ⟨hmax, hN⟩ := (hY.2.2 (Q.map (MulAut.conj u).toMonoidHom)).mpr (Or.inr rfl)
  have hQ' : Q.map (MulAut.conj u).toMonoidHom = Q' := by
    rcases (h'.2.2 (Q.map (MulAut.conj u).toMonoidHom)).mp ⟨hmax, hN⟩ with h1 | h1
    · exact absurd h1.symm hY.2.1
    · exact h1
  refine ⟨u, hu, fun x => ?_⟩
  rw [← hQ']
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hq
  · intro hx
    exact ⟨u⁻¹ * x * u, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end BurnsideJ57Pair

section BurnsideJ57Flag

open CFSG.Sporadic.Schreier.Tits

private theorem burnsideJ57_flag_trans
    (p p' : Fin 1755) (ℓ ℓ' : Fin 2925) (hp : p ∈ titsLine ℓ)
    (hp' : p' ∈ titsLine ℓ') :
    ∃ g : ↥titsA, g.1 p = p' ∧ titsLineHom g ℓ = ℓ' := by
  obtain ⟨j, hjκ, hjβ⟩ := mem_titsLine.1 hp
  obtain ⟨j', hj'κ, hj'β⟩ := mem_titsLine.1 hp'
  obtain ⟨g₁, hg₁⟩ := titsDFlag_transitive j
  obtain ⟨g₂, hg₂⟩ := titsDFlag_transitive j'
  let a₁ : ↥titsA := Subgroup.inclusion titsD_le_titsA g₁
  let a₂ : ↥titsA := Subgroup.inclusion titsD_le_titsA g₂
  have h1 : titsFlagHom a₁ 0 = j := hg₁
  have h2 : titsFlagHom a₂ 0 = j' := hg₂
  have hflag : titsFlagHom (a₂ * a₁⁻¹) j = j' := by
    rw [map_mul, Equiv.Perm.mul_apply, map_inv, ← h1]
    simpa using h2
  refine ⟨a₂ * a₁⁻¹, ?_, ?_⟩
  · have := titsBeta_flag (a₂ * a₁⁻¹) j
    rw [hflag, hj'β, hjβ] at this
    exact this.symm
  · have := titsKappa_flag (a₂ * a₁⁻¹) j
    rw [hflag, hj'κ, hjκ] at this
    exact this.symm

end BurnsideJ57Flag

section BurnsideJ57Std

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3

open scoped Pointwise in
private theorem burnsideJ57_std_pair
    {F : Type} [Group F] (ρ : F →* Equiv.Perm (Fin 1755))
    (hinj : Function.Injective ρ) (hrange : ρ.range = CFSG.Sporadic.Schreier.Tits.titsA)
    (H : Subgroup F) (hH : ∀ f, f ∈ H ↔ ρ f 0 = 0) :
    ∃ T0 M2s : Subgroup F, IsYAmalgamPair T0 H M2s ∧
      ∀ m : F, m ∈ M2s ↔ ρ m • titsLine 0 = titsLine 0 := by
  have hmem : ∀ f, ρ f ∈ CFSG.Sporadic.Schreier.Tits.titsA := fun f =>
    hrange ▸ MonoidHom.mem_range.2 ⟨f, rfl⟩
  have hpair := IsYAmalgamPair.map (burnsideJ55_eM ρ hinj hrange).symm
    (CFSG.Quasithin.Fan86.Model.isYAmalgamPair_lattice twoF4Lattice)
  have hP1 : twoF4Lattice.P₁.map (burnsideJ55_eM ρ hinj hrange).symm.toMonoidHom = H := by
    ext f
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, twoF4Lattice_P₁, Subgroup.mem_subgroupOf]
    exact (J47.mem_twoF4H_iff (hmem f)).trans (hH f).symm
  rw [hP1] at hpair
  refine ⟨_, twoF4Lattice.P₂.map (burnsideJ55_eM ρ hinj hrange).symm.toMonoidHom, hpair, ?_⟩
  intro m
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, twoF4Lattice_P₂, Subgroup.mem_subgroupOf]
  exact J47.mem_twoF4N_iff (hmem m)

end BurnsideJ57Std

section BurnsideJ57Bridge

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuRank3 CFSG.Quasithin.H13.F45Ru CFSG.RuF45

open scoped Pointwise in
private theorem burnsideJ57_rho_iso
    {F : Type} [Group F] [Finite F] (ρ : F →* Equiv.Perm (Fin 1755))
    (hinj : Function.Injective ρ) (hrange : ρ.range = CFSG.Sporadic.Schreier.Tits.titsA)
    (M1 M2 : Subgroup F) (hM1 : ∀ f, f ∈ M1 ↔ ρ f 0 = 0) (hY : ∃ T', IsYAmalgamPair T' M1 M2) :
    ∃ (eA : F ⧸ M1 ≃ Fin 1755) (eB : F ⧸ M2 ≃ Fin 2925), eA ((1 : F) : F ⧸ M1) = 0 ∧
      ∀ a c, (incGraph M1 M2).Adj (Sum.inl a) (Sum.inr c) ↔
        octGraph.Adj (Sum.inl (eA a)) (Sum.inr (eB c)) := by
  have hL : ∀ v : Fin 2925, ∃ g : ↥CFSG.Sporadic.Schreier.Tits.titsA,
      g • (Sum.inr 0 : Vtx) = Sum.inr v :=
    (Certificates.certificate4160.2.2).2.2
  have hmem : ∀ f, ρ f ∈ CFSG.Sporadic.Schreier.Tits.titsA := fun f =>
    hrange ▸ MonoidHom.mem_range.2 ⟨f, rfl⟩
  have hlift : ∀ a ∈ CFSG.Sporadic.Schreier.Tits.titsA, ∃ f, ρ f = a := fun a ha =>
    MonoidHom.mem_range.1 (hrange ▸ ha)
  obtain ⟨T0, M2s, hstd, hM2s⟩ := burnsideJ57_std_pair ρ hinj hrange M1 hM1
  obtain ⟨T', hT'⟩ := hY
  obtain ⟨u, hu, hconj⟩ := burnsideJ57_pair_conj hstd hT'
  let Λ : F →* Equiv.Perm (Fin 2925) :=
    titsLineHom.comp (ρ.codRestrict CFSG.Sporadic.Schreier.Tits.titsA hmem)
  have hΛline : ∀ f v, titsLine (Λ f v) = ρ f • titsLine v := fun f v => titsLine_lineHom _ _
  have h00' : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) :=
    mem_titsLine.2 ⟨0, titsKappa_zero, titsBeta_zero⟩
  have hM2s' : ∀ m, m ∈ M2s ↔ Λ m 0 = 0 := by
    intro m
    rw [hM2s, ← hΛline m 0]
    exact titsLine_injective.eq_iff
  let ℓ₁ : Fin 2925 := Λ u 0
  have hM2 : ∀ m, m ∈ M2 ↔ Λ m ℓ₁ = ℓ₁ := by
    intro m
    rw [hconj, hM2s']
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply, ℓ₁]
    constructor
    · intro h
      have := congrArg (Λ u) h
      simpa using this
    · intro h
      simp [h]
  have hu0 : ρ u 0 = 0 := (hM1 u).1 hu
  have h0 : (0 : Fin 1755) ∈ titsLine ℓ₁ := by
    show (0 : Fin 1755) ∈ titsLine (Λ u 0)
    rw [hΛline]
    have := Finset.smul_mem_smul_finset (a := ρ u) h00'
    simpa [Equiv.Perm.smul_def, hu0] using this
  have hinc : ∀ (f : F) (x : Fin 1755) (y : Fin 2925),
      (ρ f x ∈ titsLine (Λ f y)) ↔ x ∈ titsLine y := by
    intro f x y
    rw [hΛline]
    exact Finset.smul_mem_smul_finset_iff (ρ f)
  have hPtr : ∀ x : Fin 1755, ∃ f : F, ρ f 0 = x := by
    intro x
    obtain ⟨g, hg⟩ := titsA_pretransitive.exists_smul_eq 0 x
    obtain ⟨f, hf⟩ := hlift g.1 g.2
    refine ⟨f, ?_⟩
    rw [hf]
    exact hg
  have hΛtr : ∀ y : Fin 2925, ∃ f : F, Λ f ℓ₁ = y := by
    intro y
    obtain ⟨g, hg⟩ := hL y
    obtain ⟨f, hf⟩ := hlift g.1 g.2
    refine ⟨f * u⁻¹, ?_⟩
    have hΛf : Λ f = titsLineHom g := by
      show titsLineHom ⟨ρ f, hmem f⟩ = titsLineHom g
      rw [show (⟨ρ f, hmem f⟩ : ↥CFSG.Sporadic.Schreier.Tits.titsA) = g from Subtype.ext hf]
    show (Λ (f * u⁻¹)) (Λ u 0) = y
    rw [map_mul, Equiv.Perm.mul_apply, map_inv]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hΛf]
    exact Sum.inr.inj hg
  have hflag : ∀ x : Fin 1755, x ∈ titsLine ℓ₁ → ∃ m ∈ M2, ρ m 0 = x := by
    intro x hx
    obtain ⟨g, hg1, hg2⟩ := burnsideJ57_flag_trans 0 x ℓ₁ ℓ₁ h0 hx
    obtain ⟨f, hf⟩ := hlift g.1 g.2
    refine ⟨f, ?_, by rw [hf]; exact hg1⟩
    rw [hM2]
    have hΛf : Λ f = titsLineHom g := by
      show titsLineHom ⟨ρ f, hmem f⟩ = titsLineHom g
      rw [show (⟨ρ f, hmem f⟩ : ↥CFSG.Sporadic.Schreier.Tits.titsA) = g from Subtype.ext hf]
    rw [hΛf]
    exact hg2
  obtain ⟨eA, eB, hfa, hfb, hadj⟩ := burnsideJ57_incGraph_equiv M1 M2 ρ Λ
    (fun p v => p ∈ titsLine v) 0 ℓ₁ hinc h0 hM1 hM2 hPtr hΛtr hflag
  refine ⟨eA, eB, ?_, fun a c => (hadj a c).trans octGraph_adj_inl_inr.symm⟩
  rw [hfa 1]
  simp

private theorem burnsideJ57_incGraph_bip {F : Type} [Group F] (M1 M2 : Subgroup F) (x y : F ⧸ M1 ⊕ F ⧸ M2)
    (h : (incGraph M1 M2).Adj x y) : x.isRight ≠ y.isRight := by
  rcases x with a | a <;> rcases y with b | b
  · exact absurd h (burnsideJ55_inc_not_adj_inl_inl M1 M2 a b)
  · simp
  · simp
  · exact absurd h (burnsideJ55_inc_not_adj_inr_inr M1 M2 a b)

end BurnsideJ57Bridge

section BurnsideJ57Ru

variable {G Ω : Type} [Group G] [MulAction G Ω]

private theorem burnsideJ57_mem_deltaAt_iff (ω δ ρ τ : Ω) :
    τ ∈ DeltaAt G ω δ ρ ↔ ∃ g : G, g • ω = ρ ∧ g • δ = τ := by
  constructor
  · rintro ⟨g, hg1, f, hf⟩
    refine ⟨g * f, ?_, ?_⟩
    · rw [mul_smul, show (f : G) • ω = ω from f.2, hg1]
    · rw [mul_smul]
      have hf' : (f : G) • δ = g⁻¹ • τ := hf
      rw [hf', smul_inv_smul]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨g, hg1, ?_⟩
    rw [← hg2, inv_smul_smul]
    exact MulAction.mem_orbit_self δ

private theorem burnsideJ57_deltaAt_smul (ω δ ρ τ : Ω) (h : G) :
    h • τ ∈ DeltaAt G ω δ (h • ρ) ↔ τ ∈ DeltaAt G ω δ ρ := by
  rw [burnsideJ57_mem_deltaAt_iff, burnsideJ57_mem_deltaAt_iff]
  constructor
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨h⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hg1, inv_smul_smul]
    · rw [mul_smul, hg2, inv_smul_smul]
  · rintro ⟨g, hg1, hg2⟩
    exact ⟨h * g, by rw [mul_smul, hg1], by rw [mul_smul, hg2]⟩

private theorem burnsideJ57_mem_D (ω δ z : Ω) :
    z ∈ DeltaAt G ω δ ω ↔ ∃ g : ↥(MulAction.stabilizer G ω), g • δ = z := by
  rw [burnsideJ57_mem_deltaAt_iff]
  constructor
  · rintro ⟨g, hg1, hg2⟩
    exact ⟨⟨g, MulAction.mem_stabilizer_iff.2 hg1⟩, hg2⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, MulAction.mem_stabilizer_iff.1 g.2, hg⟩

private theorem burnsideJ57_inc_dist_smul {Y : Type} [Group Y] (M1 M2 : Subgroup Y) (y : Y) (u v : Y ⧸ M1) :
    (incGraph M1 M2).dist (Sum.inl (y • u)) (Sum.inl (y • v)) =
      (incGraph M1 M2).dist (Sum.inl u) (Sum.inl v) :=
  burnsideJ57_dist_iso (burnsideJ55_incIso M1 M2 y) (Sum.inl u) (Sum.inl v)

variable {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}

private theorem burnsideJ57_delta_mem_D (ω δ : Ω) : δ ∈ DeltaAt G ω δ ω :=
  (burnsideJ57_mem_D ω δ δ).2 ⟨1, one_smul _ _⟩

private theorem burnsideJ57_D_smul (f : ↥(MulAction.stabilizer G ω)) {v : Ω} (hv : v ∈ DeltaAt G ω δ ω) :
    f • v ∈ DeltaAt G ω δ ω := by
  obtain ⟨g, rfl⟩ := (burnsideJ57_mem_D ω δ v).1 hv
  exact (burnsideJ57_mem_D ω δ _).2 ⟨f * g, mul_smul _ _ _⟩

private theorem burnsideJ57_delta_iff (hRB : RuBuilding G Ω ω δ γ M2 φ) {u v : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) (hv : v ∈ DeltaAt G ω δ ω) :
    v ∈ DeltaAt G ω δ u ↔
      (0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) ∧
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) < 8) := by
  obtain ⟨f, rfl⟩ := (burnsideJ57_mem_D ω δ u).1 hu
  have h1 : v ∈ DeltaAt G ω δ ((f : G) • δ) ↔ (f : G)⁻¹ • v ∈ DeltaAt G ω δ δ := by
    have := burnsideJ57_deltaAt_smul ω δ δ ((f : G)⁻¹ • v) (f : G)
    rw [smul_inv_smul] at this
    exact this
  have hv' : f⁻¹ • v ∈ DeltaAt G ω δ ω := burnsideJ57_D_smul f⁻¹ hv
  have h2 := hRB.nbhd _ hv'
  have e1 : φ (f⁻¹ • v) = f⁻¹ • φ v := hRB.equivariant f⁻¹ v hv
  have e2 : φ (f • δ) = f • φ δ := hRB.equivariant f δ (burnsideJ57_delta_mem_D ω δ)
  have h3 : (f : G)⁻¹ • v = f⁻¹ • v := rfl
  have hfu : (f : G) • δ = f • δ := rfl
  rw [hfu] at h1
  rw [h1, h3, h2, e1, e2]
  have := burnsideJ57_inc_dist_smul (FdOf G ω δ) M2 f (φ δ) (f⁻¹ • φ v)
  rw [smul_inv_smul] at this
  rw [← this]

theorem burnsideJ57_OctBase.dist_le {A B : Type} {Γ : SimpleGraph (A ⊕ B)}
    (H : burnsideJ57_OctBase Γ) (b : A) (x : A ⊕ B) :
    Γ.Reachable (Sum.inl b) x ∧ Γ.dist (Sum.inl b) x ≤ 8 := by
  obtain ⟨lay, hL⟩ := H.layers (Sum.inl b)
  exact ⟨hL.reachable x, by rw [hL.dist_eq]; exact hL.le x⟩

private theorem burnsideJ57_lambda_iff (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u v : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) (hv : v ∈ DeltaAt G ω δ ω) :
    v ∈ LambdaAt G ω δ γ u ↔
      ((0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) ∧
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) < 8) ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ v)) = 8) := by
  have hmem : v ∈ LambdaAt G ω δ γ u ↔ (v ∈ DeltaAt G ω δ ω ∧ v ∈ DeltaAt G ω δ u) ∧
      v ∈ SigmaAt G ω γ δ := Iff.rfl
  rw [hmem, burnsideJ57_delta_iff hRB hu hv, hSig]
  obtain ⟨hr, hle⟩ := hOct.dist_le (φ δ) (Sum.inl (φ v))
  have hnb := hRB.nbhd v hv
  have hne : δ ≠ v ↔ (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ v)) ≠ 0 := by
    constructor
    · intro h h0
      have : (Sum.inl (φ δ) : _ ⊕ _) = Sum.inl (φ v) := (hr.dist_eq_zero_iff).1 h0
      exact h (hRB.bij.injOn (burnsideJ57_delta_mem_D ω δ) hv (Sum.inl.inj this))
    · intro h h'
      subst h'
      exact h (by simp)
  rw [hne, hnb]
  constructor
  · rintro ⟨⟨-, h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h2⟩, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨hv, h1, h2⟩, by omega, by omega⟩

private theorem burnsideJ57_lambda_ncard (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) :
    (LambdaAt G ω δ γ u).ncard =
      {c : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ |
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl c) = 8 ∧
        0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) ∧
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) < 8}.ncard := by
  have hsub : LambdaAt G ω δ γ u ⊆ DeltaAt G ω δ ω := fun v hv => hv.1.1
  rw [← (hRB.bij.injOn.mono hsub).ncard_image]
  congr 1
  ext c
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := (burnsideJ57_lambda_iff hRB hSig hOct hu (hsub hv)).1 hv
    exact ⟨this.2, this.1.1, this.1.2⟩
  · rintro ⟨h8, h1, h2⟩
    obtain ⟨v, hvD, hvc⟩ := hRB.bij.surjOn (Set.mem_univ c)
    refine ⟨v, (burnsideJ57_lambda_iff hRB hSig hOct hu hvD).2 ?_, hvc⟩
    rw [hvc]
    exact ⟨⟨h1, h2⟩, h8⟩

end BurnsideJ57Ru

section BurnsideJ57Main

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}

private theorem burnsideJ57_J59 (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (y : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2) (e : ℕ)
    (hd : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e) (h0 : 0 < e) (h8 : e < 8) :
    ∃! y', (incGraph (FdOf G ω δ) M2).Adj y y' ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e - 1 := by
  obtain ⟨lay, hL⟩ := hOct.layers (Sum.inl (φ δ))
  exact burnsideJ57_J59_abs hL hd h0 h8

private theorem burnsideJ57_J511 [Finite G] (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (hDeg : burnsideJ57_OctDeg (incGraph (FdOf G ω δ) M2))
    (y : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2) (e : ℕ)
    (hy : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e) (he8 : e < 8) :
    (e = 0 →
      (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 5120 ∧
      ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
          {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
            y' ∉ q.2.support}.ncard = 4096) ∧
    (0 < e → Even e →
      (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 8 ^ ((8 - e) / 2) ∧
      ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
          {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
            y' ∉ q.2.support}.ncard = 6 * 8 ^ ((6 - e) / 2)) ∧
    (Odd e →
      (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 2 * 8 ^ ((7 - e) / 2) ∧
      ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
          {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
            y' ∉ q.2.support}.ncard = 8 ^ ((7 - e) / 2)) := by
  obtain ⟨lay, hL⟩ := hOct.layers (Sum.inl (φ δ))
  haveI : Finite (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ) := inferInstance
  haveI : Finite (↥(MulAction.stabilizer G ω) ⧸ M2) := inferInstance
  refine burnsideJ57_J511_abs (b := Sum.inl (φ δ)) (fun x => x.isRight) hOct.bip hL ?_ ?_ hy he8
  · intro x hx
    rcases x with a | c
    · exact hDeg.deg5 a
    · simp at hx
  · intro x hx
    rcases x with a | c
    · simp at hx
    · exact hDeg.deg3 c

private theorem burnsideJ57_J510 (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u v : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) (hv : v ∈ LambdaAt G ω δ γ u)
    (p : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)))
    (hp : p.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v))) :
    (p.getVert 0 = Sum.inl (φ u) ∧ p.length ≤ 6 ∧
      dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 =
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) ∧
      (∀ i, i ≤ p.length → dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i ≤ 8) ∧
      dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p p.length = 8) ∧
    (∀ i, i < p.length →
      dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i <
        dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p (i + 1) →
      WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i
        (min (i + 8 - dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) p.length)) ∧
    (∀ i, i ≤ p.length →
      dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i + (p.length - i) = 8 →
      WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i p.length) ∧
    ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 4 →
      ((p.length = 4 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4) ∨
        (p.length = 6 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4 ∧
          dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 5 = 7) ∨
        (p.length = 6 ∧ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 3 ∧
          WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 6))) ∧
    ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 6 →
      ((∀ i, 0 < i → i ≤ p.length →
          7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
        (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 4 = 6 ∧
          ∀ i, i ≤ p.length → i ≠ 0 → i ≠ 4 →
            7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
        (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 5 ∧
          ∀ i, i ≤ p.length → i ≠ 1 →
            6 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
        (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 = 4 ∧
          WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 6))) := by
  have hvD : v ∈ DeltaAt G ω δ ω := hv.1.1
  have hlam := (burnsideJ57_lambda_iff hRB hSig hOct hu hvD).1 hv
  obtain ⟨lay, hL⟩ := hOct.layers (Sum.inl (φ δ))
  have hpar := burnsideJ57_dist_parity (fun x => x.isRight) hOct.bip
    (Γ := incGraph (FdOf G ω δ) M2) (x := Sum.inl (φ u)) (z := Sum.inl (φ v))
    ((hOct.layers (Sum.inl (φ u))).elim fun lay' hL' => hL'.reachable _)
  have hev : Even ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v))) :=
    hpar.2 rfl
  have hr6 : p.length ≤ 6 := by
    have h1 := hlam.1.2
    rw [Nat.even_iff] at hev
    omega
  exact burnsideJ57_J510_abs (fun x => x.isRight) hOct.bip hL p hp hlam.2 hr6

private theorem burnsideJ57_J58 (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) :
    ∃ pmap : Ω → Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
        ↥(MulAction.stabilizer G ω) ⧸ M2),
        (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b,
      (∀ v ∈ LambdaAt G ω δ γ u,
        (pmap v).1 = Sum.inl (φ v) ∧
        (pmap v).2.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) ∧
        ∀ q : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)),
          q.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) →
            (⟨Sum.inl (φ v), q⟩ : Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
              ↥(MulAction.stabilizer G ω) ⧸ M2),
                (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b) = pmap v) ∧
      Set.BijOn pmap (LambdaAt G ω δ γ u)
        (GeoFrom (incGraph (FdOf G ω δ) M2) (Sum.inl (φ u))
          ((fun v => (Sum.inl (φ v) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
            ↥(MulAction.stabilizer G ω) ⧸ M2)) '' LambdaAt G ω δ γ u)) := by
  obtain ⟨lay, hL⟩ := hOct.layers (Sum.inl (φ u))
  refine burnsideJ57_J58_abs (Sum.inl (φ u)) hL (LambdaAt G ω δ γ u)
    (fun v => (Sum.inl (φ v) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
      ↥(MulAction.stabilizer G ω) ⧸ M2)) ?_ ?_
  · intro v hv v' hv' h
    exact hRB.bij.injOn hv.1.1 hv'.1.1 (Sum.inl.inj h)
  · intro v hv
    exact ((burnsideJ57_lambda_iff hRB hSig hOct hu hv.1.1).1 hv).1.2

private theorem burnsideJ57_J512 (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (h12 : burnsideJ57_Oct12 (incGraph (FdOf G ω δ) M2) (φ δ)) (d : ℕ)
    (hd : d = 2 ∨ d = 4 ∨ d = 6) {u : Ω} (hu : u ∈ DeltaAt G ω δ ω)
    (hdu : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = d) :
    (LambdaAt G ω δ γ u).ncard ≤ 2 ^ 9 ∧ ((LambdaAt G ω δ γ u).ncard = 2 ^ 9 ↔ d = 2) := by
  rw [burnsideJ57_lambda_ncard hRB hSig hOct hu]
  have := h12.q12 (φ u) (by rw [hdu]; exact hd)
  rw [hdu] at this
  exact this

end BurnsideJ57Main

section BurnsideJ57Count3

private theorem burnsideJ57_partition {X : Type} [Finite X] {L2 L4 L6 Oa Ob Oc : Set X}
    (c2 : L2.ncard = 10) (c4 : L4.ncard = 80) (c6 : L6.ncard = 640)
    (do_ab : Disjoint Oa Ob) (do_ac : Disjoint Oa Oc) (do_bc : Disjoint Ob Oc)
    (ca : Oa.ncard = 10) (cb : Ob.ncard = 80) (cc : Oc.ncard = 640)
    (ha : Oa ⊆ L2 ∨ Oa ⊆ L4 ∨ Oa ⊆ L6) (hb : Ob ⊆ L2 ∨ Ob ⊆ L4 ∨ Ob ⊆ L6)
    (hc : Oc ⊆ L2 ∨ Oc ⊆ L4 ∨ Oc ⊆ L6) : Oa = L2 ∧ Ob = L4 ∧ Oc = L6 := by
  have hOc : Oc = L6 := by
    rcases hc with h | h | h
    · have := Set.ncard_le_ncard h (Set.toFinite _)
      omega
    · have := Set.ncard_le_ncard h (Set.toFinite _)
      omega
    · exact Set.eq_of_subset_of_ncard_le h (by omega) (Set.toFinite _)
  have hempty : ∀ (A B : Set X), Disjoint A B → A ⊆ B → A.ncard = 0 := by
    intro A B hd hsub
    have : A = ∅ := Set.eq_empty_of_subset_empty fun x hx =>
      (Set.disjoint_left.1 hd hx (hsub hx)).elim
    rw [this, Set.ncard_empty]
  have hOb : Ob = L4 := by
    rcases hb with h | h | h
    · have := Set.ncard_le_ncard h (Set.toFinite _)
      omega
    · exact Set.eq_of_subset_of_ncard_le h (by omega) (Set.toFinite _)
    · rw [← hOc] at h
      have := hempty Ob Oc do_bc h
      omega
  have hOa : Oa = L2 := by
    rcases ha with h | h | h
    · exact Set.eq_of_subset_of_ncard_le h (by omega) (Set.toFinite _)
    · rw [← hOb] at h
      have := hempty Oa Ob do_ab h
      omega
    · rw [← hOc] at h
      have := hempty Oa Oc do_ac h
      omega
  exact ⟨hOa, hOb, hOc⟩

end BurnsideJ57Count3

section BurnsideJ57Theta

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}

private theorem burnsideJ57_orbit_dist (hRB : RuBuilding G Ω ω δ γ M2 φ) {w : Ω}
    (hw : w ∈ DeltaAt G ω δ ω) {z : Ω}
    (hz : z ∈ MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) w) :
    z ∈ DeltaAt G ω δ ω ∧ (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ z)) =
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := hz
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
  let f : ↥(MulAction.stabilizer G ω) := ⟨h, hh1⟩
  change f • w ∈ DeltaAt G ω δ ω ∧ (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ))
    (Sum.inl (φ (f • w))) = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w))
  refine ⟨burnsideJ57_D_smul f hw, ?_⟩
  have e : φ (f • w) = f • φ w := hRB.equivariant f w hw
  have hfδ : f • δ = δ := MulAction.mem_stabilizer_iff.1 hh2
  have hδ : f • φ δ = φ δ := by
    have := hRB.equivariant f δ (burnsideJ57_delta_mem_D ω δ)
    rw [hfδ] at this
    exact this.symm
  rw [e]
  have := burnsideJ57_inc_dist_smul (FdOf G ω δ) M2 f (φ δ) (φ w)
  rw [hδ] at this
  exact this

private theorem burnsideJ57_layer_ncard (hRB : RuBuilding G Ω ω δ γ M2 φ) (k : ℕ) :
    {w : Ω | w ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = k}.ncard =
    {c : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ |
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl c) = k}.ncard := by
  have hsub : {w : Ω | w ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = k} ⊆
      DeltaAt G ω δ ω := fun w hw => hw.1
  rw [← (hRB.bij.injOn.mono hsub).ncard_image]
  congr 1
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw.2
  · intro hc
    obtain ⟨w, hwD, hwc⟩ := hRB.bij.surjOn (Set.mem_univ c)
    refine ⟨w, ⟨hwD, ?_⟩, hwc⟩
    rw [hwc]
    exact hc

private theorem burnsideJ57_dist_246 (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {x : Ω}
    (hx : x ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ) :
    (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ x)) = 2 ∨
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ x)) = 4 ∨
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ x)) = 6 := by
  have hnb := (hRB.nbhd x hx.1).1 hx.2
  have hpar := burnsideJ57_dist_parity (fun x => x.isRight) hOct.bip
    (Γ := incGraph (FdOf G ω δ) M2) (x := Sum.inl (φ δ)) (z := Sum.inl (φ x))
    (hOct.dist_le (φ δ) (Sum.inl (φ x))).1
  have hev := hpar.2 rfl
  rw [Nat.even_iff] at hev
  omega

end BurnsideJ57Theta

section BurnsideJ57Theta2

variable {G Ω : Type} [Group G] [Finite G] [MulAction G Ω] [Finite Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}

private theorem burnsideJ57_theta_char
    (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (hCard : burnsideJ57_OctCard (incGraph (FdOf G ω δ) M2) (φ δ)) (w : Ω) :
    w ∈ thetaAt G ω δ δ ↔ (w ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2) := by
  obtain ⟨a, haS, b', hbS, c, hcS, hunion, ha, hb, hc, hab, hac, hbc⟩ :=
    (as_J_5_5 G Ω ω δ γ hRB.setting).2.2.1
  have hL2 : {w : Ω | w ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2}.ncard = 10 :=
    (burnsideJ57_layer_ncard hRB 2).trans hCard.card2
  have hL4 : {w : Ω | w ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 4}.ncard = 80 :=
    (burnsideJ57_layer_ncard hRB 4).trans hCard.card4
  have hL6 : {w : Ω | w ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 6}.ncard = 640 :=
    (burnsideJ57_layer_ncard hRB 6).trans hCard.card6
  have horb : ∀ x ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
      MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) x ⊆
        {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2} ∨
      MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) x ⊆
        {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 4} ∨
      MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) x ⊆
        {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 6} := by
    intro x hx
    rcases burnsideJ57_dist_246 hRB hOct hx with h | h | h
    · left
      exact fun z hz => ⟨(burnsideJ57_orbit_dist hRB hx.1 hz).1,
        (burnsideJ57_orbit_dist hRB hx.1 hz).2.trans h⟩
    · right; left
      exact fun z hz => ⟨(burnsideJ57_orbit_dist hRB hx.1 hz).1,
        (burnsideJ57_orbit_dist hRB hx.1 hz).2.trans h⟩
    · right; right
      exact fun z hz => ⟨(burnsideJ57_orbit_dist hRB hx.1 hz).1,
        (burnsideJ57_orbit_dist hRB hx.1 hz).2.trans h⟩
  obtain ⟨hOa, hOb, hOc⟩ := burnsideJ57_partition hL2 hL4 hL6 hab hac hbc ha hb hc
    (horb a haS) (horb b' hbS) (horb c hcS)
  constructor
  · rintro ⟨hwS, h10⟩
    refine ⟨hwS, ?_⟩
    have hw' : w ∈ MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a ∪
        MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b' ∪
        MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c := hunion ▸ hwS
    rcases hw' with (h | h) | h
    · have : w ∈ {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2} := hOa ▸ h
      exact this.2
    · exfalso
      have := MulAction.orbit_eq_iff.2 h
      rw [this, hb] at h10
      omega
    · exfalso
      have := MulAction.orbit_eq_iff.2 h
      rw [this, hc] at h10
      omega
  · rintro ⟨hwS, hd⟩
    refine ⟨hwS, ?_⟩
    have hw' : w ∈ MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) a ∪
        MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) b' ∪
        MulAction.orbit ↥(MulAction.stabilizer G ω ⊓ MulAction.stabilizer G δ) c := hunion ▸ hwS
    rcases hw' with (h | h) | h
    · rw [MulAction.orbit_eq_iff.2 h, ha]
    · exfalso
      have : w ∈ {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 4} := hOb ▸ h
      have := this.2
      omega
    · exfalso
      have : w ∈ {w : Ω | w ∈ DeltaAt G ω δ ω ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 6} := hOc ▸ h
      have := this.2
      omega

end BurnsideJ57Theta2

section BurnsideJ57Seven

variable {G Ω : Type} [Group G] [MulAction G Ω] {ω δ γ : Ω}
  {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
  {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ}

private theorem burnsideJ57_sigma_iff (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {v : Ω}
    (hv : v ∈ DeltaAt G ω δ ω) :
    v ∈ SigmaAt G ω γ δ ↔
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ v)) = 8 := by
  rw [hSig]
  obtain ⟨hr, hle⟩ := hOct.dist_le (φ δ) (Sum.inl (φ v))
  have hnb := hRB.nbhd v hv
  have hne : δ ≠ v ↔ (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ v)) ≠ 0 := by
    constructor
    · intro h h0
      have : (Sum.inl (φ δ) : _ ⊕ _) = Sum.inl (φ v) := (hr.dist_eq_zero_iff).1 h0
      exact h (hRB.bij.injOn (burnsideJ57_delta_mem_D ω δ) hv (Sum.inl.inj this))
    · intro h h'
      subst h'
      exact h (by simp)
  rw [hne, hnb]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

private theorem burnsideJ57_card_DS (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (hCard : burnsideJ57_OctCard (incGraph (FdOf G ω δ) M2) (φ δ)) :
    (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard = 1024 := by
  have hsub : DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ ⊆ DeltaAt G ω δ ω := Set.inter_subset_left
  rw [← (hRB.bij.injOn.mono hsub).ncard_image]
  have : φ '' (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) = {c : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ |
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl c) = 8} := by
    ext c
    constructor
    · rintro ⟨v, ⟨hvD, hvS⟩, rfl⟩
      exact (burnsideJ57_sigma_iff hRB hSig hOct hvD).1 hvS
    · intro hc
      obtain ⟨v, hvD, hvc⟩ := hRB.bij.surjOn (Set.mem_univ c)
      refine ⟨v, ⟨hvD, (burnsideJ57_sigma_iff hRB hSig hOct hvD).2 ?_⟩, hvc⟩
      rw [hvc]
      exact hc
  rw [this]
  exact hCard.card8

private theorem burnsideJ57_lambda_image (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) :
    φ '' LambdaAt G ω δ γ u = {c : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ |
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl c) = 8 ∧
      0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) < 8} := by
  ext c
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := (burnsideJ57_lambda_iff hRB hSig hOct hu hv.1.1).1 hv
    exact ⟨this.2, this.1.1, this.1.2⟩
  · rintro ⟨h8, h1, h2⟩
    obtain ⟨v, hvD, hvc⟩ := hRB.bij.surjOn (Set.mem_univ c)
    refine ⟨v, (burnsideJ57_lambda_iff hRB hSig hOct hu hvD).2 ?_, hvc⟩
    rw [hvc]
    exact ⟨⟨h1, h2⟩, h8⟩

private theorem burnsideJ57_compl_image (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) :
    φ '' ((DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) \ LambdaAt G ω δ γ u) =
      {c : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ |
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl c) = 8 ∧
        ¬ (0 < (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) ∧
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl c) < 8)} := by
  ext c
  constructor
  · rintro ⟨v, ⟨⟨hvD, hvS⟩, hvL⟩, rfl⟩
    refine ⟨(burnsideJ57_sigma_iff hRB hSig hOct hvD).1 hvS, fun h => hvL ?_⟩
    exact (burnsideJ57_lambda_iff hRB hSig hOct hu hvD).2
      ⟨h, (burnsideJ57_sigma_iff hRB hSig hOct hvD).1 hvS⟩
  · rintro ⟨h8, hn⟩
    obtain ⟨v, hvD, hvc⟩ := hRB.bij.surjOn (Set.mem_univ c)
    have h8' : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ v)) = 8 := by
      rw [hvc]
      exact h8
    refine ⟨v, ⟨⟨hvD, (burnsideJ57_sigma_iff hRB hSig hOct hvD).2 h8'⟩, fun hL => ?_⟩, hvc⟩
    have := (burnsideJ57_lambda_iff hRB hSig hOct hu hvD).1 hL
    rw [hvc] at this
    exact hn this.1

private theorem burnsideJ57_dist_two (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    {a : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hne : a ≠ φ δ)
    {l : ↥(MulAction.stabilizer G ω) ⧸ M2}
    (h0 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l))
    (h1 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl a) (Sum.inr l)) :
    (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl a) = 2 := by
  have hle : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl a) ≤ 2 :=
    SimpleGraph.dist_le (SimpleGraph.Walk.cons h0 (SimpleGraph.Walk.cons h1.symm
      SimpleGraph.Walk.nil))
  obtain ⟨hr, -⟩ := hOct.dist_le (φ δ) (Sum.inl a)
  have hev := (burnsideJ57_dist_parity (fun x => x.isRight) hOct.bip hr).2 rfl
  rw [Nat.even_iff] at hev
  have hpos : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl a) ≠ 0 := by
    intro h
    exact hne (Sum.inl.inj ((hr.dist_eq_zero_iff).1 h)).symm
  omega

private theorem burnsideJ57_J57_a (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (hCard : burnsideJ57_OctCard (incGraph (FdOf G ω δ) M2) (φ δ))
    (h12 : burnsideJ57_Oct12 (incGraph (FdOf G ω δ) M2) (φ δ))
    (hθ : ∀ w, w ∈ thetaAt G ω δ δ ↔ (w ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2)) :
    thetaAt G ω δ δ = {u | u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
        (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard = 2 ^ 9} ∧
      2 * 2 ^ 9 = (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ).ncard := by
  refine ⟨?_, by rw [burnsideJ57_card_DS hRB hSig hOct hCard]; norm_num⟩
  ext u
  rw [hθ u, Set.mem_setOf_eq]
  have hset : ∀ u : Ω, DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ = LambdaAt G ω δ γ u :=
    fun u => by
      unfold LambdaAt
      rw [Set.inter_comm (DeltaAt G ω δ u)]
  rw [hset u]
  constructor
  · rintro ⟨huS, hd⟩
    refine ⟨huS, ?_⟩
    exact ((burnsideJ57_J512 hRB hSig hOct h12 2 (Or.inl rfl) huS.1 hd).2).2 rfl
  · rintro ⟨huS, hcard⟩
    refine ⟨huS, ?_⟩
    rcases burnsideJ57_dist_246 hRB hOct huS with hd | hd | hd
    · exact hd
    · exfalso
      have := (((burnsideJ57_J512 hRB hSig hOct h12 4 (Or.inr (Or.inl rfl)) huS.1 hd).2).1 hcard)
      omega
    · exfalso
      have := (((burnsideJ57_J512 hRB hSig hOct h12 6 (Or.inr (Or.inr rfl)) huS.1 hd).2).1 hcard)
      omega

private theorem burnsideJ57_J57_c (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) (hd : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ))
      (Sum.inl (φ u)) = 2) :
    ∃! l : ↥(MulAction.stabilizer G ω) ⧸ M2,
      (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) ∧
      (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l) := by
  obtain ⟨lay, hL⟩ := hOct.layers (Sum.inl (φ δ))
  have hlay : lay (Sum.inl (φ u)) = 2 := by rw [← hL.dist_eq]; exact hd
  have hne : (Sum.inl (φ u) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
      ↥(MulAction.stabilizer G ω) ⧸ M2) ≠ Sum.inl (φ δ) := by
    intro h
    have : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 0 := by
      rw [h]; simp
    omega
  have hadj1 : ∀ l : ↥(MulAction.stabilizer G ω) ⧸ M2,
      (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l) → lay (Sum.inr l) = 1 := by
    intro l hl
    rw [← hL.dist_eq]
    exact SimpleGraph.dist_eq_one_iff_adj.2 hl
  obtain ⟨y, hy, hly⟩ := hL.parent (Sum.inl (φ u)) hne
  rcases y with a | l
  · exact ((hOct.bip _ _ hy) rfl).elim
  · refine ⟨l, ⟨?_, hy⟩, fun l' hl' => ?_⟩
    · have h1 : lay (Sum.inr l) = 1 := by omega
      have : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inr l) = 1 := by
        rw [hL.dist_eq]; exact h1
      exact SimpleGraph.dist_eq_one_iff_adj.1 this
    · have h1 := hadj1 l' hl'.1
      have := hL.uniq (Sum.inl (φ u)) (Sum.inr l') (Sum.inr l) (by omega) (by omega) hl'.2 hy
        (by omega) hly
      exact Sum.inr.inj this

private theorem burnsideJ57_J57_d (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (hDeg : burnsideJ57_OctDeg (incGraph (FdOf G ω δ) M2)) {u : Ω}
    (hu : u ∈ DeltaAt G ω δ ω) (hd : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ))
      (Sum.inl (φ u)) = 2) {l : ↥(MulAction.stabilizer G ω) ⧸ M2}
    (hl0 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l))
    (hl1 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l)) :
    ∃! u' : Ω, u' ∈ DeltaAt G ω δ ω ∧
      (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l) ∧ u' ≠ δ ∧ u' ≠ u := by
  classical
  have hneφ : φ u ≠ φ δ := by
    intro h
    have : (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 0 := by
      rw [h]
      simp
    omega
  have hN := hDeg.deg3 l
  have hP2 : ({Sum.inl (φ δ), Sum.inl (φ u)} : Set (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
      ↥(MulAction.stabilizer G ω) ⧸ M2)).ncard = 2 :=
    Set.ncard_pair (fun h => hneφ (Sum.inl.inj h).symm)
  have hPN : ({Sum.inl (φ δ), Sum.inl (φ u)} : Set (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
      ↥(MulAction.stabilizer G ω) ⧸ M2)) ⊆ (incGraph (FdOf G ω δ) M2).neighborSet (Sum.inr l) := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hl0.symm
    · exact hl1.symm
  have hdiff : ((incGraph (FdOf G ω δ) M2).neighborSet (Sum.inr l) \
      {Sum.inl (φ δ), Sum.inl (φ u)}).ncard = 1 := by
    rw [Set.ncard_diff hPN (Set.toFinite _), hN, hP2]
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 hdiff
  have hzmem : z ∈ (incGraph (FdOf G ω δ) M2).neighborSet (Sum.inr l) \
      {Sum.inl (φ δ), Sum.inl (φ u)} := by
    rw [hz]
    exact Set.mem_singleton z
  rcases z with a3 | c3
  · obtain ⟨u', hu'D, hu'a⟩ := hRB.bij.surjOn (Set.mem_univ a3)
    have hadj : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl a3) (Sum.inr l) := hzmem.1.symm
    refine ⟨u', ⟨hu'D, ?_, ?_, ?_⟩, ?_⟩
    · rw [hu'a]
      exact hadj
    · intro h
      exact hzmem.2 (Or.inl (by rw [← hu'a, h]))
    · intro h
      exact hzmem.2 (Or.inr (by rw [← hu'a, h]; exact Set.mem_singleton _))
    · rintro u'' ⟨hu''D, hu''adj, hu''δ, hu''u⟩
      have hmemN : (Sum.inl (φ u'') : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
          ↥(MulAction.stabilizer G ω) ⧸ M2) ∈
          (incGraph (FdOf G ω δ) M2).neighborSet (Sum.inr l) := hu''adj.symm
      have hnotP : (Sum.inl (φ u'') : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
          ↥(MulAction.stabilizer G ω) ⧸ M2) ∉
          ({Sum.inl (φ δ), Sum.inl (φ u)} : Set (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
          ↥(MulAction.stabilizer G ω) ⧸ M2)) := by
        rintro (h | h)
        · exact hu''δ (hRB.bij.injOn hu''D (burnsideJ57_delta_mem_D ω δ) (Sum.inl.inj h))
        · exact hu''u (hRB.bij.injOn hu''D hu (Sum.inl.inj h))
      have hin : (Sum.inl (φ u'') : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
          ↥(MulAction.stabilizer G ω) ⧸ M2) ∈
          (incGraph (FdOf G ω δ) M2).neighborSet (Sum.inr l) \
          {Sum.inl (φ δ), Sum.inl (φ u)} := ⟨hmemN, hnotP⟩
      rw [hz] at hin
      have : φ u'' = a3 := Sum.inl.inj (Set.mem_singleton_iff.1 hin)
      exact hRB.bij.injOn hu''D hu'D (this.trans hu'a.symm)
  · exact ((hOct.bip _ _ hzmem.1) rfl).elim

private theorem burnsideJ57_J57_e (hRB : RuBuilding G Ω ω δ γ M2 φ)
    (hSig : ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ)
    (hOct : burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2))
    (h7 : burnsideJ57_Oct7 (incGraph (FdOf G ω δ) M2) (φ δ))
    (hθ : ∀ w, w ∈ thetaAt G ω δ δ ↔ (w ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ ∧
      (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ w)) = 2)) {u : Ω}
    (hu : u ∈ thetaAt G ω δ δ) {l : ↥(MulAction.stabilizer G ω) ⧸ M2} {u' : Ω}
    (hu'D : u' ∈ DeltaAt G ω δ ω)
    (hl0 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ δ)) (Sum.inr l))
    (hl1 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u)) (Sum.inr l))
    (hl2 : (incGraph (FdOf G ω δ) M2).Adj (Sum.inl (φ u')) (Sum.inr l)) (hu'δ : u' ≠ δ)
    (hu'u : u' ≠ u) :
    u' ∈ thetaAt G ω δ δ ∧ ∀ w ∈ thetaAt G ω δ δ,
      (DeltaAt G ω δ w ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ =
        (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) \ (DeltaAt G ω δ u ∩ DeltaAt G ω δ ω ∩
          SigmaAt G ω γ δ) ↔ w = u') := by
  obtain ⟨huS, hud⟩ := (hθ u).1 hu
  have hφu'δ : φ u' ≠ φ δ := fun h =>
    hu'δ (hRB.bij.injOn hu'D (burnsideJ57_delta_mem_D ω δ) h)
  have hd' := burnsideJ57_dist_two hOct hφu'δ hl0 hl2
  have hu'θ : u' ∈ thetaAt G ω δ δ :=
    (hθ u').2 ⟨⟨hu'D, (hRB.nbhd u' hu'D).2 ⟨by omega, by omega⟩⟩, hd'⟩
  refine ⟨hu'θ, fun w hw => ?_⟩
  obtain ⟨hwS, hwd⟩ := (hθ w).1 hw
  have hset : ∀ x : Ω, DeltaAt G ω δ x ∩ DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ =
      LambdaAt G ω δ γ x := fun x => by
    unfold LambdaAt
    rw [Set.inter_comm (DeltaAt G ω δ x)]
  rw [hset w, hset u]
  have hsubw : LambdaAt G ω δ γ w ⊆ DeltaAt G ω δ ω := fun v hv => hv.1.1
  have hsubc : (DeltaAt G ω δ ω ∩ SigmaAt G ω γ δ) \ LambdaAt G ω δ γ u ⊆ DeltaAt G ω δ ω :=
    fun v hv => hv.1.1
  have himg := (hRB.bij.injOn.image_eq_image_iff hsubw hsubc).symm
  rw [himg, burnsideJ57_lambda_image hRB hSig hOct hwS.1,
    burnsideJ57_compl_image hRB hSig hOct huS.1]
  have key := h7.q7 (φ u) (φ w) (φ u') l hud hwd hl0 hl1 hl2 hφu'δ
    (fun h => hu'u (hRB.bij.injOn hu'D huS.1 h))
  rw [key]
  exact ⟨fun h => hRB.bij.injOn hwS.1 hu'D h, fun h => by rw [h]⟩

end BurnsideJ57Seven

section BurnsideJ57Data

open CFSG.Quasithin.H13.F45Ru in
private theorem burnsideJ57_building_iso
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    ∃ (eA : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ≃ Fin 1755)
      (eB : ↥(MulAction.stabilizer G ω) ⧸ M2 ≃ Fin 2925), eA (φ δ) = 0 ∧
      ∀ a c, (incGraph (FdOf G ω δ) M2).Adj (Sum.inl a) (Sum.inr c) ↔
        octGraph.Adj (Sum.inl (eA a)) (Sum.inr (eB c)) := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hRB.setting
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_rho_iso T.ρ T.ρ_injective T.ρ_range (FdOf G ω δ) M2
    T.mem_Fd_iff hRB.amalgam
  exact ⟨eA, eB, by rw [hRB.base]; exact hb, hadj⟩

private theorem burnsideJ57_sigma_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    ∀ v, v ∈ SigmaAt G ω γ δ ↔ δ ≠ v ∧ v ∉ DeltaAt G ω δ δ := by
  obtain ⟨T⟩ := burnsideJ55_exists_Tr hRB.setting
  intro v
  have hs := T.gamma_mem_S hRB.setting
  rw [T.mem_sigmaAt_iff hs, T.mem_deltaAt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (congrArg T.Φ h), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (T.Φ.injective h), h2⟩

private theorem burnsideJ57_octBase_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    burnsideJ57_OctBase (incGraph (FdOf G ω δ) M2) := by
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_building_iso hRB
  exact burnsideJ57_OctBase_of_iso eA eB (burnsideJ57_incGraph_bip _ _) burnsideJ57_oct_bip hadj
    burnsideJ57_octBase_oct

private theorem burnsideJ57_octDeg_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    burnsideJ57_OctDeg (incGraph (FdOf G ω δ) M2) := by
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_building_iso hRB
  exact burnsideJ57_OctDeg_of_iso eA eB (burnsideJ57_incGraph_bip _ _) burnsideJ57_oct_bip hadj
    burnsideJ57_octDeg_oct

private theorem burnsideJ57_octCard_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    burnsideJ57_OctCard (incGraph (FdOf G ω δ) M2) (φ δ) := by
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_building_iso hRB
  exact burnsideJ57_OctCard_of_iso eA eB (burnsideJ57_incGraph_bip _ _) burnsideJ57_oct_bip hadj hb
    burnsideJ57_octCard_oct

private theorem burnsideJ57_oct12_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    burnsideJ57_Oct12 (incGraph (FdOf G ω δ) M2) (φ δ) := by
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_building_iso hRB
  exact burnsideJ57_Oct12_of_iso eA eB (burnsideJ57_incGraph_bip _ _) burnsideJ57_oct_bip hadj hb
    burnsideJ57_oct12_oct

private theorem burnsideJ57_oct7_of_building
    {G Ω : Type} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] {ω δ γ : Ω} {M2 : Subgroup ↥(MulAction.stabilizer G ω)}
    {φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ} (hRB : RuBuilding G Ω ω δ γ M2 φ) :
    burnsideJ57_Oct7 (incGraph (FdOf G ω δ) M2) (φ δ) := by
  obtain ⟨eA, eB, hb, hadj⟩ := burnsideJ57_building_iso hRB
  exact burnsideJ57_Oct7_of_iso eA eB (burnsideJ57_incGraph_bip _ _) burnsideJ57_oct_bip hadj hb
    burnsideJ57_oct7_oct

end BurnsideJ57Data

end BurnsideJ57All

end BurnsideJ57

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_7 : J_5_7 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB
  have hSig := burnsideJ57_sigma_of_building hRB
  have hOct := burnsideJ57_octBase_of_building hRB
  have hDeg := burnsideJ57_octDeg_of_building hRB
  have hCard := burnsideJ57_octCard_of_building hRB
  have h12 := burnsideJ57_oct12_of_building hRB
  have h7 := burnsideJ57_oct7_of_building hRB
  have hθ := burnsideJ57_theta_char hRB hOct hCard
  refine ⟨burnsideJ57_J57_a hRB hSig hOct hCard h12 hθ, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨huS, hd⟩ := (hθ u).1 hu
    exact burnsideJ57_J57_c hRB hOct huS.1 hd
  · intro u hu l hl0 hl1
    obtain ⟨huS, hd⟩ := (hθ u).1 hu
    exact burnsideJ57_J57_d hRB hOct hDeg huS.1 hd hl0 hl1
  · intro u hu l u' hu'D hl0 hl1 hl2 hu'δ hu'u
    exact burnsideJ57_J57_e hRB hSig hOct h7 hθ hu hu'D hl0 hl1 hl2 hu'δ hu'u

end

@[expose] def J_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ,
        ∃ pmap : Ω → Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
            ↥(MulAction.stabilizer G ω) ⧸ M2),
            (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b,
          (∀ v ∈ LambdaAt G ω δ γ u,
            (pmap v).1 = Sum.inl (φ v) ∧
            (pmap v).2.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) ∧
            ∀ q : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)),
              q.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) →
                (⟨Sum.inl (φ v), q⟩ : Σ b : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
                  ↥(MulAction.stabilizer G ω) ⧸ M2),
                    (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) b) = pmap v) ∧
          Set.BijOn pmap (LambdaAt G ω δ γ u)
            (GeoFrom (incGraph (FdOf G ω δ) M2) (Sum.inl (φ u))
              ((fun v => (Sum.inl (φ v) : ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕
                ↥(MulAction.stabilizer G ω) ⧸ M2)) '' LambdaAt G ω δ γ u))

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_8 : J_5_8 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB u hu
  exact burnsideJ57_J58 hRB (burnsideJ57_sigma_of_building hRB)
    (burnsideJ57_octBase_of_building hRB) hu.1

end

@[expose] def J_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ y : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2),
        ∀ e : ℕ, (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e → 0 < e → e < 8 →
          ∃! y', (incGraph (FdOf G ω δ) M2).Adj y y' ∧
            (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e - 1

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_9 : J_5_9 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB y e hd h0 h8
  exact burnsideJ57_J59 (burnsideJ57_octBase_of_building hRB) y e hd h0 h8

end

@[expose] def J_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ u ∈ DeltaAt G ω δ ω ∩ DeltaAt G ω δ δ, ∀ v ∈ LambdaAt G ω δ γ u,
        ∀ p : (incGraph (FdOf G ω δ) M2).Walk (Sum.inl (φ u)) (Sum.inl (φ v)),
          p.length = (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ u)) (Sum.inl (φ v)) →
            (p.getVert 0 = Sum.inl (φ u) ∧ p.length ≤ 6 ∧
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 =
                (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) ∧
              (∀ i, i ≤ p.length → dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i ≤ 8) ∧
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p p.length = 8) ∧
            (∀ i, i < p.length →
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i <
                dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p (i + 1) →
              WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i
                (min (i + 8 - dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) p.length)) ∧
            (∀ i, i ≤ p.length →
              dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i + (p.length - i) = 8 →
              WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i p.length) ∧
            ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 4 →
              ((p.length = 4 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4) ∨
                (p.length = 6 ∧ WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 0 4 ∧
                  dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 5 = 7) ∨
                (p.length = 6 ∧ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 3 ∧
                  WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 6))) ∧
            ((incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = 6 →
              ((∀ i, 0 < i → i ≤ p.length →
                  7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 4 = 6 ∧
                  ∀ i, i ≤ p.length → i ≠ 0 → i ≠ 4 →
                    7 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 1 = 5 ∧
                  ∀ i, i ≤ p.length → i ≠ 1 →
                    6 ≤ dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p i) ∨
                (dseq (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 = 4 ∧
                  WalkIncreases (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) p 2 6)))

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_10 : J_5_10 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB u hu v hv p hp
  exact burnsideJ57_J510 hRB (burnsideJ57_sigma_of_building hRB)
    (burnsideJ57_octBase_of_building hRB) hu.1 hv p hp

end

@[expose] def J_5_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ y : (↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ ⊕ ↥(MulAction.stabilizer G ω) ⧸ M2),
        ∀ e : ℕ, (incGraph (FdOf G ω δ) M2).Reachable (Sum.inl (φ δ)) y →
          (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y = e → e < 8 →
          (e = 0 →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 5120 ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 4096) ∧
          (0 < e → Even e →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 8 ^ ((8 - e) / 2) ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 6 * 8 ^ ((6 - e) / 2)) ∧
          (Odd e →
            (NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e).ncard = 2 * 8 ^ ((7 - e) / 2) ∧
            ∀ y' ∈ (incGraph (FdOf G ω δ) M2).neighborSet y,
              (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) y' = e + 1 →
                {q ∈ NgeoSet (incGraph (FdOf G ω δ) M2) (Sum.inl (φ δ)) y e |
                  y' ∉ q.2.support}.ncard = 8 ^ ((7 - e) / 2))

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_11 : J_5_11 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB y e _ hd he8
  exact burnsideJ57_J511 (burnsideJ57_octBase_of_building hRB) (burnsideJ57_octDeg_of_building hRB)
    y e hd he8

end

@[expose] def J_5_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      ∀ d : ℕ, (d = 2 ∨ d = 4 ∨ d = 6) → ∀ u ∈ DeltaAt G ω δ ω,
        (incGraph (FdOf G ω δ) M2).dist (Sum.inl (φ δ)) (Sum.inl (φ u)) = d →
          (LambdaAt G ω δ γ u).ncard ≤ 2 ^ 9 ∧ ((LambdaAt G ω δ γ u).ncard = 2 ^ 9 ↔ d = 2)

section
open CFSG.ASVolI.ChIJK

theorem as_J_5_12 : J_5_12 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB d hd u hu hdu
  exact burnsideJ57_J512 hRB (burnsideJ57_sigma_of_building hRB)
    (burnsideJ57_octBase_of_building hRB) (burnsideJ57_oct12_of_building hRB) d hd hu hdu

end

@[expose] def J_5_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Finite Ω] [MulAction G Ω] (ω δ γ : Ω)
    (M2 : Subgroup ↥(MulAction.stabilizer G ω))
    (φ : Ω → ↥(MulAction.stabilizer G ω) ⧸ FdOf G ω δ), RuBuilding G Ω ω δ γ M2 φ →
      Nonempty (omegaGraph G ω δ ≃g
        OmegaPrime ↥(MulAction.stabilizer G ω) (FdOf G ω δ) M2
          ((MulAction.stabilizer G ω ⊓ MulAction.stabilizer G γ).subgroupOf
            (MulAction.stabilizer G ω)))

section

theorem as_J_5_13 : J_5_13 := by
  intro G _ _ Ω _ _ ω δ γ M2 φ hRB
  exact burnsideJ55_J513 hRB

end

end CFSG.ASVolI
