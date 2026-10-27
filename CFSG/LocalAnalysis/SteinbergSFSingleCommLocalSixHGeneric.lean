module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem sixH_g3_hc {Ω : Type*} [Group Ω] {V : Subgroup Ω} {a b : Ω} (ha : a ∈ V) (hb : b ∈ V)
    (hsq : ∀ x ∈ V, ∀ y ∈ V, (x * x) * y = y * (x * x)) :
    (a * a)⁻¹ * (b * b)⁻¹ * ((a * b) * (a * b)) = a⁻¹ * b⁻¹ * a * b := by
  have hQa : a * (b * b)⁻¹ = (b * b)⁻¹ * a :=
    ((show Commute (b * b) a from hsq b hb a ha).symm.inv_right).eq
  calc (a * a)⁻¹ * (b * b)⁻¹ * ((a * b) * (a * b))
      = (a * a)⁻¹ * ((b * b)⁻¹ * a) * (b * a * b) := by group
    _ = (a * a)⁻¹ * (a * (b * b)⁻¹) * (b * a * b) := by rw [← hQa]
    _ = a⁻¹ * b⁻¹ * a * b := by group

theorem sixH_g3_core {Ω : Type*} [Group Ω] {V : Subgroup Ω} {a b : Ω} (ha : a ∈ V) (hb : b ∈ V)
    (hsq : ∀ x ∈ V, ∀ y ∈ V, (x * x) * y = y * (x * x)) (hbb : b * b = a * a) :
    (b⁻¹ * a) * (b⁻¹ * a) = a⁻¹ * b⁻¹ * a * b := by
  have hRa : a * ((a * b) * (a * b)) = ((a * b) * (a * b)) * a :=
    (show Commute ((a * b) * (a * b)) a from hsq (a * b) (V.mul_mem ha hb) a ha).symm.eq
  have hba : (b * a) * (b * a) = (a * b) * (a * b) := by
    calc (b * a) * (b * a) = a⁻¹ * (((a * b) * (a * b)) * a) := by group
      _ = a⁻¹ * (a * ((a * b) * (a * b))) := by rw [hRa]
      _ = (a * b) * (a * b) := by group
  have hcw : Commute (b * b) (b * a) :=
    ((Commute.refl b).mul_left (Commute.refl b)).mul_right
      (show Commute (b * b) a from hsq b hb a ha)
  have hcomm : (b * a) * (b * b)⁻¹ = (b * b)⁻¹ * (b * a) := hcw.symm.inv_right.eq
  have hinv : (b * b)⁻¹ = (a * a)⁻¹ := by rw [hbb]
  have hc := sixH_g3_hc ha hb hsq
  calc (b⁻¹ * a) * (b⁻¹ * a)
      = (b * b)⁻¹ * (((b * a) * (b * b)⁻¹) * (b * a)) := by group
    _ = (b * b)⁻¹ * (((b * b)⁻¹ * (b * a)) * (b * a)) := by rw [hcomm]
    _ = ((b * b)⁻¹ * (b * b)⁻¹) * ((b * a) * (b * a)) := by group
    _ = ((b * b)⁻¹ * (b * b)⁻¹) * ((a * b) * (a * b)) := by rw [hba]
    _ = ((a * a)⁻¹ * (b * b)⁻¹) * ((a * b) * (a * b)) := by rw [hinv]
    _ = a⁻¹ * b⁻¹ * a * b := hc

theorem sixH_g3_quadratic {Ω : Type*} [Group Ω] {V : Subgroup Ω} {t : Ω} (ht : t * t = 1)
    (hN : t ∈ normalizer (V : Set Ω)) (hsq : ∀ x ∈ V, ∀ y ∈ V, (x * x) * y = y * (x * x))
    (hsqt : ∀ x ∈ V, (x * x) * t = t * (x * x)) {x : Ω} (hx : x ∈ V) :
    (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) =
      x⁻¹ * (t⁻¹ * x * t)⁻¹ * x * (t⁻¹ * x * t) := by
  have hb : t⁻¹ * x * t ∈ V := (Subgroup.mem_normalizer_iff''.mp hN x).mp hx
  have hbb : (t⁻¹ * x * t) * (t⁻¹ * x * t) = x * x := by
    have h2 : (x * x) * t = t * (x * x) := hsqt x hx
    calc (t⁻¹ * x * t) * (t⁻¹ * x * t) = t⁻¹ * (x * x) * t := by group
      _ = t⁻¹ * ((x * x) * t) := by group
      _ = t⁻¹ * (t * (x * x)) := by rw [h2]
      _ = x * x := by group
  have hL : t⁻¹ * (x⁻¹ * t * x) = (t⁻¹ * x * t)⁻¹ * x := by group
  rw [hL]
  exact sixH_g3_core hx hb hsq hbb

theorem sixH_g4_normalizer {G : Type*} [Group G] {Ω N T : Subgroup G}
    (hN : Ω ≤ normalizer (N : Set G)) (hT : Ω ≤ normalizer (T : Set G)) :
    Ω ≤ normalizer ((centralizer (N : Set G) ⊓ T : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Ω, ∀ h ∈ Subgroup.centralizer (N : Set G),
      g * h * g⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
    intro g hg h hh
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hm : g⁻¹ * n * g ∈ N := (Subgroup.mem_normalizer_iff''.mp (hN hg) n).mp hn
    have hcomm : (g⁻¹ * n * g) * h = h * (g⁻¹ * n * g) :=
      (Subgroup.mem_centralizer_iff.mp hh) (g⁻¹ * n * g) hm
    calc n * (g * h * g⁻¹) = g * ((g⁻¹ * n * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
      _ = g * h * g⁻¹ * n := by group
  intro ω hω
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hC, hT'⟩
    exact ⟨key ω hω h hC, (Subgroup.mem_normalizer_iff.mp (hT hω) h).mp hT'⟩
  · rintro ⟨hC, hT'⟩
    have hC' := key ω⁻¹ (Ω.inv_mem hω) _ hC
    rw [show ω⁻¹ * (ω * h * ω⁻¹) * ω⁻¹⁻¹ = h by group] at hC'
    exact ⟨hC', (Subgroup.mem_normalizer_iff.mp (hT hω) h).mpr hT'⟩

theorem sixH_g6_exists_maximal {Γ : Type} [Group Γ] [Finite Γ] {X S₀ : Subgroup Γ}
    (hS₀X : S₀ ≤ X) [IsElementaryAbelian 2 S₀] :
    ∃ S : Subgroup Γ, S₀ ≤ S ∧
      Maximal (fun S' : Subgroup Γ => S' ≤ X ∧ IsElementaryAbelian 2 S') S := by
  have hfin : Finite (Subgroup Γ) :=
    Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ)) SetLike.coe_injective
  have hne : {S : Subgroup Γ | S₀ ≤ S ∧ S ≤ X ∧ IsElementaryAbelian 2 S}.Nonempty :=
    ⟨S₀, le_rfl, hS₀X, inferInstance⟩
  obtain ⟨S, hS⟩ :=
    (Set.toFinite {S : Subgroup Γ | S₀ ≤ S ∧ S ≤ X ∧ IsElementaryAbelian 2 S}).exists_maximal hne
  obtain ⟨⟨h0S, hSX, hSE⟩, hmaxS⟩ := hS
  refine ⟨S, h0S, ⟨⟨hSX, hSE⟩, fun T hT hST => ?_⟩⟩
  exact hmaxS ⟨h0S.trans hST, hT.1, hT.2⟩ hST

theorem sixH_g7_quot_mem {Γ : Type} [Group Γ] {P N B : Subgroup Γ} [(N.subgroupOf P).Normal]
    {y : Γ} (hy : y ∈ P)
    (hx : (QuotientGroup.mk' (N.subgroupOf P) ⟨y, hy⟩ : ↥P ⧸ N.subgroupOf P) ∈
      (B.subgroupOf P).map (QuotientGroup.mk' (N.subgroupOf P))) :
    ∃ b : Γ, b ∈ B ∧ b⁻¹ * y ∈ N := by
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hx
  refine ⟨(a : Γ), Subgroup.mem_subgroupOf.mp ha, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hae
  exact Subgroup.mem_subgroupOf.mp hae

theorem sixH_g8_mem_sup_mul {G : Type} [Group G] {N A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) {z : G} (hz : z ∈ N ⊔ A) :
    ∃ n ∈ N, ∃ a ∈ A, z = n * a := by
  have hAN : A ≤ normalizer (N : Set G) := fun a ha => Subgroup.mem_normalizer_iff.mpr fun n =>
    ⟨hA a ha n, fun hn => by simpa [mul_assoc] using hA a⁻¹ (A.inv_mem ha) _ hn⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N A hAN] at hz
  obtain ⟨n, hn, a, ha, hna⟩ := Set.mem_mul.mp hz
  exact ⟨n, hn, a, ha, hna.symm⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
