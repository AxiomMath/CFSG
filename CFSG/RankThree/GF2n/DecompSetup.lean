module

public import CFSG.RankThree.GF2n.QuotPair
public import CFSG.RankThree.GF2n.Tim77Prop24Two
public import CFSG.RankThree.GF2n.Tim78P210Basic
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender Matrix
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure DecompSetup (A Ab L Lb M : Subgroup G) : Prop where
  comm_A : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  comm_Ab : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x
  L_le : L ≤ A
  Lb_le : Lb ≤ Ab
  ne : L ≠ A
  Lb_ne : Lb ≠ Ab
  L_le_M : L ≤ M
  Lb_le_M : Lb ≤ M
  sq_A : ∀ x ∈ A, x * x ∈ L
  sq_Ab : ∀ x ∈ Ab, x * x ∈ Lb
  comm_M : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x
  sq_M : ∀ x ∈ M, x * x = 1
  exists_mul : ∀ m ∈ M, ∃ l ∈ L, ∃ lb ∈ Lb, m = l * lb
  A_le_normalizer : A ≤ Subgroup.normalizer (M : Set G)
  Ab_le_normalizer : Ab ≤ Subgroup.normalizer (M : Set G)
  comm_L : ∀ y ∈ A, ∀ m ∈ M, y * m * y⁻¹ * m⁻¹ ∈ L
  comm_Lb : ∀ y ∈ Ab, ∀ m ∈ M, y * m * y⁻¹ * m⁻¹ ∈ Lb
  cent : ∀ a ∈ A, a ∉ L → ∀ m ∈ M, a * m = m * a → m ∈ L
  cent_b : ∀ b ∈ Ab, b ∉ Lb → ∀ m ∈ M, b * m = m * b → m ∈ Lb
  inf : A ⊓ Ab = ⊥
  card : Nat.card A = Nat.card Ab

namespace DecompSetup

variable {A Ab L Lb M : Subgroup G} (S : DecompSetup A Ab L Lb M)
include S

omit [Finite G] in
theorem symm : DecompSetup Ab A Lb L M where
  comm_A := S.comm_Ab
  comm_Ab := S.comm_A
  L_le := S.Lb_le
  Lb_le := S.L_le
  ne := S.Lb_ne
  Lb_ne := S.ne
  L_le_M := S.Lb_le_M
  Lb_le_M := S.L_le_M
  sq_A := S.sq_Ab
  sq_Ab := S.sq_A
  comm_M := S.comm_M
  sq_M := S.sq_M
  exists_mul := fun m hm => by
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul m hm
    exact ⟨lb, hlb, l, hl, S.comm_M _ (S.L_le_M hl) _ (S.Lb_le_M hlb)⟩
  A_le_normalizer := S.Ab_le_normalizer
  Ab_le_normalizer := S.A_le_normalizer
  comm_L := S.comm_Lb
  comm_Lb := S.comm_L
  cent := S.cent_b
  cent_b := S.cent
  inf := by rw [inf_comm]; exact S.inf
  card := S.card.symm

omit [Finite G] in
theorem sup_le_normalizer : A ⊔ Ab ≤ Subgroup.normalizer (M : Set G) :=
  sup_le S.A_le_normalizer S.Ab_le_normalizer

omit [Finite G] in
theorem isCommutative_M : IsMulCommutative ↥M :=
  ⟨⟨fun a b => Subtype.ext (S.comm_M a a.2 b b.2)⟩⟩

omit [Finite G] in
theorem eq_one_of_commute {a b m : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab) (hbL : b ∉ Lb)
    (hm : m ∈ M) (hma : a * m = m * a) (hmb : b * m = m * b) : m = 1 := by
  have h3 : m ∈ A ⊓ Ab := Subgroup.mem_inf.mpr
    ⟨S.L_le (S.cent a ha haL m hm hma), S.Lb_le (S.cent_b b hb hbL m hm hmb)⟩
  rwa [S.inf, Subgroup.mem_bot] at h3

omit [Finite G] in
theorem commutator_injective {a : G} (ha : a ∈ A) (haL : a ∉ L) :
    Function.Injective fun n : ↥Lb =>
      (⟨a * n * a⁻¹ * (n : G)⁻¹, S.comm_L a ha n (S.Lb_le_M n.2)⟩ : ↥L) := by
  intro n₁ n₂ h
  have h' : a * (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = a * n₂ * a⁻¹ * (n₂ : G)⁻¹ := congrArg Subtype.val h
  have h2 : (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = n₂ * a⁻¹ * (n₂ : G)⁻¹ := by
    calc (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = a⁻¹ * (a * n₁ * a⁻¹ * (n₁ : G)⁻¹) := by group
      _ = a⁻¹ * (a * n₂ * a⁻¹ * (n₂ : G)⁻¹) := by rw [h']
      _ = n₂ * a⁻¹ * (n₂ : G)⁻¹ := by group
  have hc : a * ((n₂ : G)⁻¹ * n₁) = ((n₂ : G)⁻¹ * n₁) * a := by
    calc a * ((n₂ : G)⁻¹ * n₁) = a * ((n₂ : G)⁻¹ * (n₁ * a⁻¹ * (n₁ : G)⁻¹) * n₁ * a) := by group
      _ = a * ((n₂ : G)⁻¹ * (n₂ * a⁻¹ * (n₂ : G)⁻¹) * n₁ * a) := by rw [h2]
      _ = ((n₂ : G)⁻¹ * n₁) * a := by group
  have hm : (n₂ : G)⁻¹ * n₁ ∈ M := M.mul_mem (M.inv_mem (S.Lb_le_M n₂.2)) (S.Lb_le_M n₁.2)
  have hL := S.cent a ha haL _ hm hc
  have h1 : (n₂ : G)⁻¹ * n₁ ∈ A ⊓ Ab :=
    Subgroup.mem_inf.mpr ⟨S.L_le hL, S.Lb_le (Lb.mul_mem (Lb.inv_mem n₂.2) n₁.2)⟩
  rw [S.inf, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact Subtype.ext h1.symm

theorem card_Lb_eq : Nat.card Lb = Nat.card L := by
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  exact le_antisymm (Nat.card_le_card_of_injective _ (S.commutator_injective ha haL))
    (Nat.card_le_card_of_injective _ (S.symm.commutator_injective hb hbL))

theorem exists_commutator_eq {a l : G} (ha : a ∈ A) (haL : a ∉ L) (hl : l ∈ L) :
    ∃ n ∈ Lb, a * n * a⁻¹ * n⁻¹ = l := by
  obtain ⟨n, hn⟩ :=
    ((S.commutator_injective ha haL).bijective_of_nat_card_le S.card_Lb_eq.ge).2 ⟨l, hl⟩
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

section Quot

variable [(M.subgroupOf (A ⊔ Ab)).Normal]

local notation "πm" => QuotientGroup.mk' (Subgroup.subgroupOf M (A ⊔ Ab))

omit S [Finite G] in
theorem mk_eq_one_iff (y : ↥(A ⊔ Ab)) : πm y = 1 ↔ (y : G) ∈ M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit S [Finite G] in
theorem pow_mem_of_mk {y : ↥(A ⊔ Ab)} {k : ℕ} (hk : (πm y) ^ k = 1) : ((y : G) ^ k) ∈ M := by
  rw [← map_pow, mk_eq_one_iff] at hk
  simpa using hk

variable (P : QuotPair ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
  ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))))
include P

end Quot

end DecompSetup

end CFSG.RankThree.GF2n
