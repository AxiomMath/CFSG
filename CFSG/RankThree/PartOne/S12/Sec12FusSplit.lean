module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S12.Sec12FusGen

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

structure Out1214a (p : ℕ) (c : G) (I P Q : Subgroup G) : Prop where
  Q_norm : Q ≤ P ∧ (Q.subgroupOf P).Normal
  P_gen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f
  C_cyc : IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P)

structure Out1214b (p : ℕ) (c : G) (L E I P Q : Subgroup G) : Prop extends Out1214a p c I P Q where
  omega : omegaOne p P = E
  QE : Q ⊓ E = E ⊓ L
  BZ : E ⊓ L = omegaOne p ((Subgroup.center ↥P).map P.subtype)

structure Out1214c (p : ℕ) (c : G) (L E I P Q : Subgroup G) : Prop extends
    Out1214b p c L E I P Q where
  trans : ∀ U V : Subgroup G, U ≤ P → V ≤ P → Nat.card U = p → Nat.card V = p →
    ¬ U ≤ Q → ¬ V ≤ Q → ∃ u ∈ P, V = conjBy u U

namespace Sec12Fus

theorem q_normal {p : ℕ} {E : Subgroup G} {b : G} {I X P Q : Subgroup G}
    (hC : Choice1212 p E b I X P Q) : Q ≤ P ∧ (Q.subgroupOf P).Normal := by
  have hQP : Q ≤ P := by
    rw [hC.Q_eq]
    exact sup_le inf_le_right inf_le_left
  have hA : ((Subgroup.centralizer (I : Set G) ⊓ P).subgroupOf P).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxC, hxP⟩ := hx
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, (y * x * y⁻¹ : ↥P).2⟩
    intro i hi
    have hyN : (y : G) ∈ Subgroup.normalizer (I : Set G) := hC.P_norm y.2
    have hyN' : (y : G)⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).inv_mem hyN
    have hi' : (y : G)⁻¹ * i * (y : G) ∈ I := by
      have := (Subgroup.mem_normalizer_iff.1 hyN' i).1 hi
      simpa [mul_assoc] using this
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ hi'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc i * ((y : G) * x * (y : G)⁻¹) = (y : G) * (((y : G)⁻¹ * i * (y : G)) * x) * (y : G)⁻¹ := by
          group
      _ = (y : G) * (x * ((y : G)⁻¹ * i * (y : G))) * (y : G)⁻¹ := by rw [hc]
      _ = ((y : G) * x * (y : G)⁻¹) * i := by group
  have hB : ((P ⊓ I).subgroupOf P).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxP, hxI⟩ := hx
    refine ⟨(y * x * y⁻¹ : ↥P).2, ?_⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (I : Set G) := hC.P_norm y.2
    have := (Subgroup.mem_normalizer_iff.1 hyN x).1 hxI
    simpa using this
  refine ⟨hQP, ?_⟩
  rw [hC.Q_eq, Subgroup.subgroupOf_sup inf_le_right inf_le_left]
  have := hA
  have := hB
  exact Subgroup.sup_normal _ _

end Sec12Fus

@[expose] def KF1214Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f

@[expose] def KF1214Cyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      (∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) →
      IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P)

@[expose] def KF1214Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214a p c I P Q → omegaOne p P = E

@[expose] def KF1214Center : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214a p c I P Q → omegaOne p P = E →
      Q ⊓ E = E ⊓ L ∧ E ⊓ L = omegaOne p ((Subgroup.center ↥P).map P.subtype)

@[expose] def KF1214Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214b p c L E I P Q →
      ∀ U V : Subgroup G, U ≤ P → V ≤ P → Nat.card U = p → Nat.card V = p →
        ¬ U ≤ Q → ¬ V ≤ Q → ∃ u ∈ P, V = conjBy u U

@[expose] def KF1214HSyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214c p c L E I P Q → IsSylowOf p (P ⊓ cNormalizer c) (cNormalizer c)

theorem kf1214Struct_of_parts (hGen : KF1214Gen) (hCyc : KF1214Cyc) (hOmega : KF1214Omega)
    (hCenter : KF1214Center) (hTrans : KF1214Trans) (hHSyl : KF1214HSyl) : KF1214Struct := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF
  have hQ := Sec12Fus.q_normal hC
  have hgen := hGen G p A c L E ctx b K I X P Q hL hC hF
  have hcyc := hCyc G p A c L E ctx b K I X P Q hL hC hF hgen
  have ha : Out1214a p c I P Q := ⟨hQ, hgen, hcyc⟩
  have homega := hOmega G p A c L E ctx b K I X P Q hL hC hF ha
  obtain ⟨hQE, hBZ⟩ := hCenter G p A c L E ctx b K I X P Q hL hC hF ha homega
  have hb : Out1214b p c L E I P Q := ⟨ha, homega, hQE, hBZ⟩
  have htrans := hTrans G p A c L E ctx b K I X P Q hL hC hF hb
  have hc : Out1214c p c L E I P Q := ⟨hb, htrans⟩
  exact ⟨hQ, hgen, hcyc, homega, hQE, hBZ, htrans,
    hHSyl G p A c L E ctx b K I X P Q hL hC hF hc⟩

@[expose] def KF1215Sp4Frat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤ → RowModel p L 7 →
      ∀ g ∈ cNormalizer c, g * c * g⁻¹ ≠ c⁻¹ →
        ∃ n ∈ torusNormalizer E ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) ⊓ cNormalizer c,
          n * c * n⁻¹ = g * c * g⁻¹

@[expose] def KF1215Sp4Inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤ → RowModel p L 7 →
      ∀ g ∈ cNormalizer c, g * c * g⁻¹ ≠ c⁻¹

theorem kf1215Sp4_of_parts (hFrat : KF1215Sp4Frat) (hInv : KF1215Sp4Inv)
    (hClass : KF1215Class) : KF1215Sp4 := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 g hg
  refine node1215_core ctx hL hC hF hout hClass (fun g' hg' => ?_) hg
  by_cases hinv : g' * c * g'⁻¹ = c⁻¹
  · exact absurd hinv (hInv G p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 g' hg')
  · exact hFrat G p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 g' hg' hinv

end CFSG.RankThree.PartOne
