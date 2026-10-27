module

public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

section Named

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152EndCover (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y M X : Subgroup G, Ctx152 A LB Y M X →
    ∀ (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
      Data152 A LB X c' L' d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G) ∈
        scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) (piOf 2) →
      L' ≤ (S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ⊔ X →
        ¬ X ⊓ L' ≤ oTwoOddIn X

end Named

@[expose] def KS152HJAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L P Q : Subgroup Γ) (p : ℕ), p.Prime → p ≠ 2 →
    Group.IsPerfect ↥L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    IsPGroup 2 Q → P ≤ Subgroup.normalizer (Q : Set Γ) →
    ((IsElementaryAbelian p ↥P ∧ Nat.card P = p ^ 2) ∨
      (CFSG.IsExtraspecialPGroup p ↥P ∧ Nat.card P = p ^ 3)) →
    L ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup Γ) : Set Γ) →
    L ≤ Subgroup.normalizer (Q : Set Γ) →
      ∀ l ∈ L, ∀ u ∈ P, ⁅l, u⁆ ∈ Q

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem mem_oTwoOddIn_of_commutator_mem {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup p P)
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X) {x : G} (hx : x ∈ X)
    (hcomm : ∀ u ∈ P, ⁅x, u⁆ ∈ CFSG.Open.pCoreOf 2 X) : x ∈ oTwoOddIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥X with hN
  set π := QuotientGroup.mk' N with hπ
  set P' := P.subgroupOf X with hP'
  have hP'p : IsPGroup p P' := hP.comap_subtype
  have hNp : ¬ p ∣ Nat.card N := by
    intro hpN
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
    rw [← hN] at hk
    rw [hk] at hpN
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hpN)
    exact hp2 this
  have hlift := (CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting
    (G := ↥X) (p := p) (N := N) hNp hP'p).2.2
  set x' : ↥X := ⟨x, hx⟩ with hx'
  have hx'c : π x' ∈ Subgroup.centralizer ((P'.map π : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have huP : (u : G) ∈ P := Subgroup.mem_subgroupOf.mp hu
    have hc : ⁅x, (u : G)⁆ ∈ CFSG.Open.pCoreOf 2 X := hcomm u huP
    rw [CFSG.Open.pCoreOf] at hc
    obtain ⟨n, hnN, hn⟩ := hc
    have hn' : n = ⁅x', u⁆ := by
      apply Subtype.ext
      change X.subtype n = _
      rw [hn]
      simp [hx', commutatorElement_def]
    have h1 : π ⁅x', u⁆ = 1 := by
      rw [← hn']
      exact (QuotientGroup.eq_one_iff n).mpr hnN
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hlift] at hx'c
  obtain ⟨y, hy, hyx⟩ := hx'c
  have hyG : (y : G) ∈ X ⊓ Subgroup.centralizer (P : Set G) := by
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp hy ⟨u, hPX hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
    exact congrArg Subtype.val h
  obtain ⟨z, hz, hzy⟩ := hC hyG
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy'] at hz
  have hπy : π y ∈ CFSG.oddCore (↥X ⧸ N) := hz
  rw [hyx] at hπy
  exact ⟨x', hπy, rfl⟩

end Coprime

section End

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Step152EndCoverR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152EndCover A (lB A)

end End

end CFSG.RankThree.PartTwo.Sec15
