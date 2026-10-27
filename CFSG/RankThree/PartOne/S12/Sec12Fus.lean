module

public import CFSG.RankThree.PartOne.S12.FusionRest
public import CFSG.RankThree.PartOne.S12.InputsEleven
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G]

structure Fus12Ctx (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) : Prop where
  hyp : Sec12Hyp G p A c L E
  facts : Sec12Facts G p A c L E
  notFive : ¬ Outcome152Five p E A (lieGenerated p E)
  core : torusWeylHasPCore p E
  ten : pCoreFixed p E = E ⊓ L ∧ Nat.card E = p * Nat.card ↥(E ⊓ L) ∧
    ¬ p ∣ Nat.card (Subgroup.center L)
  eleven : Nonempty (↥(CFSG.pCore p ↥(torusWeyl E)) ≃* ↥(E ⊓ L)) ∧
    (∀ e e' : E, (e : G) ∉ L → (e' : G) ∉ L →
      ∃! φ : ↥(CFSG.pCore p ↥(torusWeyl E)),
        ∃ k : ℤ, ((φ : ↥(torusWeyl E)) : MulAut E) e = e' ^ k) ∧
    (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊔
      torusImage E (cNormalizer c) = torusWeyl E ∧
    (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓
      torusImage E (cNormalizer c) = ⊥
  twelve : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) ∨ (p = 5 ∧ RowModel p L 12)

@[expose] def kLayer (L : Subgroup G) (b : G) : Subgroup G :=
  inSubgroup (fun K _ => layer K) (L ⊓ Subgroup.centralizer ({b} : Set G))

@[expose] def LayerModel (p : ℕ) (L K : Subgroup G) (m : ℕ) : Prop :=
  (∀ f : ℕ, 1 ≤ f → p ∣ 2 ^ f + 1 →
      (StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f ∨
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) →
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 2 (m * f)) ∧
  (∀ f : ℕ, 1 ≤ f → p ∣ 2 ^ f + 1 →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f →
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSp 2 2 (m * f)) ∧
  ((∃ r : ℕ, 1 ≤ r ∧ r ≤ 8 ∧ RowModel p L r) →
      ∃ g : ℕ, 1 ≤ g ∧ p ∣ 2 ^ g - 1 ∧
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 (m * g))

@[expose] noncomputable def xPreimage (p : ℕ) (E : Subgroup G) : Subgroup G :=
  (((CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype).comap
    E.normalizerMonoidHom).map (Subgroup.normalizer (E : Set G)).subtype

structure Layer1212 (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (b : G)
    (K I : Subgroup G) : Prop where
  b_mem : b ∈ A ∧ b ∈ L ∧ b ≠ 1
  K_eq : K = kLayer L b
  K_qs : CFSG.IsQuasisimple K
  K_center : ¬ p ∣ Nat.card (Subgroup.center K)
  K_model : LayerModel p L K 1
  C_A : A ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers b ⊔ Subgroup.zpowers c
  A_K : Nat.card ↥(A ⊓ K) = p
  two : ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
    S = ⁅S, A⁆
  I_mem : I ∈ thetaComponentsAt p b
  K_le : K ≤ I

structure Choice1212 (p : ℕ) (E : Subgroup G) (b : G) (I X P Q : Subgroup G) : Prop where
  X_sylow : IsSylowOf p X (xPreimage p E) ∧ E ≤ X
  P_sylow : IsSylowOf p P (Subgroup.centralizer ({b} : Set G)) ∧ X ≤ P
  Q_eq : Q = (Subgroup.centralizer (I : Set G) ⊓ P) ⊔ (P ⊓ I)
  P_norm : P ≤ Subgroup.normalizer (I : Set G)

structure Field1213 (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (K I : Subgroup G) : Prop where
  ne : K ≠ I
  comm : ⁅I, Subgroup.zpowers c⁆ = I
  star0 : I ∈ sectionTenAt p (sectionTenZeroStar p A) b
  two : I ∈ sectionTenTwo p A
  field : InducesFieldAut p c I
  model : LayerModel p L I p

structure Out1214 (p : ℕ) (c : G) (L E : Subgroup G) (I P Q : Subgroup G) : Prop where
  Q_norm : Q ≤ P ∧ (Q.subgroupOf P).Normal
  P_gen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f
  C_cyc : IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P)
  omega : omegaOne p P = E
  QE : Q ⊓ E = E ⊓ L
  BZ : E ⊓ L = omegaOne p ((Subgroup.center ↥P).map P.subtype)
  trans : ∀ U V : Subgroup G, U ≤ P → V ≤ P → Nat.card U = p → Nat.card V = p →
    ¬ U ≤ Q → ¬ V ≤ Q → ∃ u ∈ P, V = conjBy u U
  H_sylow : IsSylowOf p (P ⊓ cNormalizer c) (cNormalizer c)

@[expose] def KF1212Layer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∃ (b : G) (K I : Subgroup G), Layer1212 p A c L E b K I

@[expose] def KF1213Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q →
      InducesFieldAut p c I → LayerModel p L I p

@[expose] def KF1214Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q

@[expose] def KF1214U5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ¬ RowModel p L 12

@[expose] def KF1215Frat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → ¬ RowModel p L 7 →
      ∀ g ∈ cNormalizer c, ∃ n ∈ torusNormalizer E ⊓ Subgroup.normalizer
        (Subgroup.zpowers b : Set G) ⊓ cNormalizer c, n * c * n⁻¹ = g * c * g⁻¹

@[expose] def KF1215Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      ∀ n : G, n ∈ cNormalizer c → n ∈ Subgroup.normalizer (I : Set G) → n * c * n⁻¹ = c

@[expose] def KF1215Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤ → RowModel p L 7 →
      ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q

@[expose] def Node1212Choice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I : Subgroup G), Layer1212 p A c L E b K I →
      ∃ X P Q : Subgroup G, Choice1212 p E b I X P Q

@[expose] def Node1213Move : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q →
      K ≠ I ∧ ⁅I, Subgroup.zpowers c⁆ = I

@[expose] def Node1213Max : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → K ≠ I →
      ⁅I, Subgroup.zpowers c⁆ = I → I ∈ sectionTenAt p (sectionTenZeroStar p A) b

@[expose] def Node1213Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → K ≠ I →
      ⁅I, Subgroup.zpowers c⁆ = I → I ∈ sectionTenAt p (sectionTenZeroStar p A) b →
      I ∈ sectionTenTwo p A

@[expose] def Node1213Field : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → K ≠ I →
      ⁅I, Subgroup.zpowers c⁆ = I → I ∈ sectionTenAt p (sectionTenZeroStar p A) b →
      I ∈ sectionTenTwo p A → InducesFieldAut p c I

@[expose] def Node1214Syl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) →
    ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤

@[expose] def Node1215Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤ → ¬ RowModel p L 7 →
      ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q

theorem quotient_abelian_of_sup_zpowers {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal) {f : G} (hf : f ∈ P) (hP : P = Q ⊔ Subgroup.zpowers f) :
    ∀ x y : ↥P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P := by
  let φ : ↥P →* ↥P ⧸ Q.subgroupOf P := QuotientGroup.mk' (Q.subgroupOf P)
  have hall : ∀ y : ↥P, φ y ∈ Subgroup.zpowers (φ ⟨f, hf⟩) := by
    intro y
    have hy : (y : G) ∈ Q ⊔ Subgroup.zpowers f := by
      rw [← hP]
      exact y.2
    rw [Subgroup.sup_eq_closure] at hy
    have key : ∃ hyP : (y : G) ∈ P, φ ⟨y, hyP⟩ ∈ Subgroup.zpowers (φ ⟨f, hf⟩) := by
      refine Subgroup.closure_induction
        (p := fun x _ => ∃ hxP : x ∈ P, φ ⟨x, hxP⟩ ∈ Subgroup.zpowers (φ ⟨f, hf⟩)) ?_ ?_ ?_ ?_ hy
      · rintro x (hx | hx)
        · refine ⟨hQP hx, ?_⟩
          have : φ ⟨x, hQP hx⟩ = 1 :=
            (QuotientGroup.eq_one_iff (⟨x, hQP hx⟩ : ↥P)).2 (Subgroup.mem_subgroupOf.2 hx)
          rw [this]
          exact Subgroup.one_mem _
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          have hxP : f ^ k ∈ P := Subgroup.zpow_mem _ hf k
          refine ⟨hxP, ⟨k, ?_⟩⟩
          have : (⟨f ^ k, hxP⟩ : ↥P) = (⟨f, hf⟩ : ↥P) ^ k := by
            apply Subtype.ext
            simp
          rw [this, map_zpow]
      · exact ⟨P.one_mem, by
          have : φ ⟨1, P.one_mem⟩ = 1 := map_one φ
          rw [this]
          exact Subgroup.one_mem _⟩
      · rintro x y - - ⟨hxP, hx⟩ ⟨hyP, hy⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        have : φ ⟨x * y, P.mul_mem hxP hyP⟩ = φ ⟨x, hxP⟩ * φ ⟨y, hyP⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      · rintro x - ⟨hxP, hx⟩
        refine ⟨P.inv_mem hxP, ?_⟩
        have : φ ⟨x⁻¹, P.inv_mem hxP⟩ = (φ ⟨x, hxP⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact Subgroup.inv_mem _ hx
    obtain ⟨hyP, hy'⟩ := key
    exact hy'
  intro x y
  have hcomm : φ x * φ y = φ y * φ x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hall x)
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 (hall y)
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  have : φ (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  exact (QuotientGroup.eq_one_iff _).1 this

theorem Fus12Ctx.c_not_mem [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) : c ∉ L := by
  intro hcL
  have h := ctx.hyp
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hzc : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hLc l.2) c (Set.mem_singleton c)
    exact this.symm
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have := h.A_elem
  have hcpow : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c h.c_mem
  have hcp : orderOf c = p := orderOf_eq_prime hcpow h.c_ne_one
  set z : ↥(Subgroup.center ↥L) := ⟨⟨c, hcL⟩, hzc⟩ with hz
  have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard z
  have h1 : orderOf z = orderOf (⟨c, hcL⟩ : ↥L) := (Subgroup.orderOf_coe z).symm
  have h2 : orderOf (⟨c, hcL⟩ : ↥L) = orderOf c := (Subgroup.orderOf_coe (⟨c, hcL⟩ : ↥L)).symm
  rw [h1, h2, hcp] at hdvd
  exact ctx.ten.2.2 hdvd

theorem node12FusionRest_of_steps
    (hLay : KF1212Layer) (hCh : Node1212Choice) (hMove : Node1213Move) (hMax : Node1213Max)
    (hTwo : Node1213Two) (hFld : Node1213Field) (hTyp : KF1213Type) (hStr : KF1214Struct)
    (hU5 : KF1214U5) (hSyl : Node1214Syl) (hGen : Node1215Gen) (hSp4 : KF1215Sp4) :
    Node12FusionRest := by
  intro G _ _ p A c L E h hF hT hX h10 h11 h12
  have ctx : Fus12Ctx G p A c L E := ⟨h, hF, hT, hX, h10, h11, h12⟩
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) := by
    rcases h12 with h | ⟨-, h⟩
    · exact h
    · exact absurd h hn12
  obtain ⟨b, K, I, hL⟩ := hLay G p A c L E ctx
  obtain ⟨X, P, Q, hC⟩ := hCh G p A c L E ctx b K I hL
  obtain ⟨hne, hcomm⟩ := hMove G p A c L E ctx b K I X P Q hL hC
  have hmax := hMax G p A c L E ctx b K I X P Q hL hC hne hcomm
  have htwo := hTwo G p A c L E ctx b K I X P Q hL hC hne hcomm hmax
  have hfield := hFld G p A c L E ctx b K I X P Q hL hC hne hcomm hmax htwo
  have hmodel := hTyp G p A c L E ctx b K I X P Q hL hC hfield
  have hF13 : Field1213 p A c L b K I := ⟨hne, hcomm, hmax, htwo, hfield, hmodel⟩
  have hout := hStr G p A c L E ctx b K I X P Q hL hC hF13
  have hsyl := hSyl G p A c L E ctx hnH b K I X P Q hL hC hF13 hout
  have hfus : ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q := by
    by_cases h7 : RowModel p L 7
    · exact hSp4 G p A c L E ctx b K I X P Q hL hC hF13 hout hsyl h7
    · exact hGen G p A c L E ctx b K I X P Q hL hC hF13 hout hsyl h7
  obtain ⟨f, hfP, hPf⟩ := hout.P_gen
  have hcP : c ∈ P := hC.P_sylow.2 (hC.X_sylow.2 (h.A_le_E h.c_mem))
  have hcQ : c ∉ Q := by
    intro hcQ
    have hcE : c ∈ E := h.A_le_E h.c_mem
    have : c ∈ Q ⊓ E := ⟨hcQ, hcE⟩
    rw [hout.QE] at this
    exact ctx.c_not_mem this.2
  exact ⟨P, Q, hsyl, hout.Q_norm.1, hout.Q_norm.2,
    quotient_abelian_of_sup_zpowers hout.Q_norm.1 hout.Q_norm.2 hfP hPf, hcP, hcQ, hfus⟩

end CFSG.RankThree.PartOne
