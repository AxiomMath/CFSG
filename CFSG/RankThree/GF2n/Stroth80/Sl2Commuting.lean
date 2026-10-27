module

public import CFSG.RankThree.GF2n.Stroth80.Sl2Irreducible

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix MatrixGroups
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive (restrictEnd)

theorem trivial_of_irreducible_commuting {G H : Type} [Group G] [Group H] {M : Type}
    [AddCommGroup M] [Finite M] (hH : Group.IsPerfect H) (ρ₁ : G →* AddMonoid.End M)
    (ρ₂ : H →* AddMonoid.End M) (hcomm : ∀ g h x, ρ₁ g (ρ₂ h x) = ρ₂ h (ρ₁ g x))
    (hirr : ∀ T : AddSubgroup M, (∀ g, ∀ x ∈ T, ρ₁ g x ∈ T) → T = ⊥ ∨ T = ⊤) :
    ∀ h x, ρ₂ h x = x := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · intro h x
    exact Subsingleton.elim _ _
  obtain ⟨C, hmemC⟩ : ∃ C : Subring (AddMonoid.End M),
      ∀ z, z ∈ C ↔ ∀ g, ρ₁ g * z = z * ρ₁ g :=
    ⟨Subring.centralizer (Set.range fun g => ρ₁ g), fun z => by
      rw [Subring.mem_centralizer_iff]
      exact ⟨fun H' g => H' _ ⟨g, rfl⟩, fun H' y hy => by
        obtain ⟨g, rfl⟩ := hy
        exact H' g⟩⟩
  have hinj : ∀ t : M →+ M, (t : AddMonoid.End M) ∈ C → (t : AddMonoid.End M) ≠ 0 →
      Function.Injective t := by
    intro t ht ht0
    have key : ∀ g x, t (ρ₁ g x) = ρ₁ g (t x) := fun g x => by
      have := congrArg (fun f : AddMonoid.End M => f x) ((hmemC t).1 ht g)
      exact this.symm
    have hk : AddMonoidHom.ker t = ⊥ := by
      rcases hirr (AddMonoidHom.ker t) (fun g x hx => by
          rw [AddMonoidHom.mem_ker] at hx ⊢
          rw [key, hx, map_zero]) with h | h
      · exact h
      · exfalso
        apply ht0
        refine AddMonoidHom.ext fun x => ?_
        have hx : x ∈ AddMonoidHom.ker t := by
          rw [h]
          exact AddSubgroup.mem_top x
        exact AddMonoidHom.mem_ker.1 hx
    intro x y hxy
    have hmem : x - y ∈ AddMonoidHom.ker t := by
      rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
    rw [hk, AddSubgroup.mem_bot] at hmem
    exact sub_eq_zero.1 hmem
  have hne : (1 : AddMonoid.End M) ≠ 0 := by
    intro h1
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    apply hx
    exact congrArg (fun f : AddMonoid.End M => f x) h1
  have hdom : ∀ a b : AddMonoid.End M, a ∈ C → b ∈ C → a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b ha _ hab
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · refine Or.inr (AddMonoidHom.ext fun x => ?_)
      have h0 : ∀ y, a (b y) = 0 := fun y => congrArg (fun f : AddMonoid.End M => f y) hab
      show b x = 0
      apply hinj a ha ha0
      show a (b x) = a 0
      rw [map_zero]
      exact h0 x
  haveI : Nontrivial C := ⟨⟨1, 0, fun h1 => hne (congrArg Subtype.val h1)⟩⟩
  haveI : NoZeroDivisors C := ⟨fun {a b} hab => by
    have hab' : a.1 * b.1 = 0 := congrArg Subtype.val hab
    rcases hdom a.1 b.1 a.2 b.2 hab' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)⟩
  haveI : IsDomain C := NoZeroDivisors.to_isDomain C
  haveI : Finite C := by
    have : Finite (AddMonoid.End M) :=
      Finite.of_injective (fun f : AddMonoid.End M => (f : M → M)) DFunLike.coe_injective
    infer_instance
  have hmulC : ∀ a b : C, a * b = b * a := by
    classical
    letI : Fintype C := Fintype.ofFinite C
    letI : DivisionRing C := Fintype.divisionRingOfIsDomain C
    letI : Field C := littleWedderburn C
    intro a b
    exact mul_comm a b
  have hρ : ∀ h, ρ₂ h ∈ C := fun h =>
    (hmemC _).2 fun g => AddMonoidHom.ext fun x => hcomm g h x
  have hcommut : ∀ h h' : H, ρ₂ h * ρ₂ h' = ρ₂ h' * ρ₂ h := by
    intro h h'
    exact congrArg Subtype.val (hmulC ⟨ρ₂ h, hρ h⟩ ⟨ρ₂ h', hρ h'⟩)
  have hker : commutator H ≤ (ρ₂.toHomUnits).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Units.ext
    exact hcommut a b
  intro h x
  have hh : ρ₂.toHomUnits h = 1 := by
    refine MonoidHom.mem_ker.1 (hker ?_)
    rw [hH.commutator_eq_top]
    exact Subgroup.mem_top h
  have hρh : ρ₂ h = 1 := congrArg Units.val hh
  exact congrArg (fun f : AddMonoid.End M => f x) hρh

theorem sl2_commuting_trivial {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {Y : Type} [AddCommGroup Y] (ρ₁ ρ₂ : SL(2, K) →* AddMonoid.End Y)
    (hcomm : ∀ g h a, ρ₁ g (ρ₂ h a) = ρ₂ h (ρ₁ g a))
    (S : AddSubgroup Y) [Finite S] (hS2 : ∀ a ∈ S, a + a = 0)
    (hScard : Nat.card S = Nat.card K ^ 2)
    (h₁ : ∀ g, ∀ a ∈ S, ρ₁ g a ∈ S) (h₂ : ∀ h, ∀ a ∈ S, ρ₂ h a ∈ S) :
    (∀ g, ∀ a ∈ S, ρ₁ g a = a) ∨ (∀ h, ∀ a ∈ S, ρ₂ h a = a) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨g₀, a₀, ha₀, hg₀⟩, ⟨h₀, b₀, hb₀, hh₀⟩⟩ := hcon
  have hS2' : ∀ a : S, a + a = 0 := fun a => Subtype.ext (hS2 a a.2)
  have hρ₁' : ∃ g, restrictEnd ρ₁ S h₁ g ≠ 1 := by
    refine ⟨g₀, fun h => hg₀ ?_⟩
    have := DFunLike.congr_fun h ⟨a₀, ha₀⟩
    exact congrArg Subtype.val this
  have hirr := sl2_irreducible_of_nontrivial hK hS2' hScard (restrictEnd ρ₁ S h₁) hρ₁'
  have hcomm' : ∀ g h (x : S), restrictEnd ρ₁ S h₁ g (restrictEnd ρ₂ S h₂ h x) =
      restrictEnd ρ₂ S h₂ h (restrictEnd ρ₁ S h₁ g x) := fun g h x => Subtype.ext (hcomm g h x)
  have hall := trivial_of_irreducible_commuting
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (restrictEnd ρ₁ S h₁) (restrictEnd ρ₂ S h₂) hcomm' hirr
  exact hh₀ (congrArg Subtype.val (hall h₀ ⟨b₀, hb₀⟩))

end CFSG.RankThree.GF2n.Stroth80
