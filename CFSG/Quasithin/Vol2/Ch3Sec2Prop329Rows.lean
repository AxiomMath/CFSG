module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.H13.StatementsL5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)

@[expose] def Row329Alt7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L : Subgroup (MulAut V)),
    AlternatingNatural L ⊤ ⊥ 7 → IsFFModule (Subgroup.normalizer (L : Set (MulAut V)))

@[expose] def Row329G2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L : Subgroup (MulAut V)),
    G2NaturalDerived L ⊤ ⊥ 1 → IsFFModule (Subgroup.normalizer (L : Set (MulAut V)))

@[expose] def Row329Orth : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    ∀ m : ℕ, 2 ≤ m → BinaryOrthogonalFour L ⊤ ⊥ m → LieModel ↥L .PSL 2 2 (2 * m)

@[expose] def Row329Nine : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    ∀ m : ℕ, 1 ≤ m → BinaryNineTensor L ⊤ ⊥ m →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ (2 * m) ∧
        (LieModel ↥L .PSL 3 2 (2 * m) ∨ Nonempty (↥L ≃* ↥(StatedSL 3 K))) ∧
        Nat.card V = 2 ^ (9 * m) ∧
        ∃ π : ↥(StatedSL 3 K) →* ↥L,
          (FFModel.twistTensor m (StatedSL 3 K)).RealizesVia L ⊤ ⊥ π ∧
            NoGraphAutomorphism π (Subgroup.normalizer (L : Set (MulAut V)))

@[expose] def Row329M12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    M12Ten L ⊤ ⊥ → Nat.card V = 2 ^ 10 ∧
      (Nonempty (↥G ≃* MulAut ↥NativeSporadic.M12) ∨ ((2 : ℚ) : WithTop ℚ) ≤ qhatOf G)

@[expose] def Row329HatM22 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L : Subgroup (MulAut V)), Mhat22Twelve L ⊤ ⊥ →
    Group.IsPerfect ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* NativeSporadic.M22) ∧ Nat.card V = 2 ^ 12

@[expose] def Row329M22 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    (MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥) →
      Nonempty (↥L ≃* NativeSporadic.M22) ∧ Nat.card V = 2 ^ 10 ∧
        (MathieuCocode22 L ⊤ ⊥ → ((2 : ℚ) : WithTop ℚ) < qOf G)

@[expose] def Row329M23 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥) →
      Nonempty (↥L ≃* NativeSporadic.M23) ∧ Nat.card V = 2 ^ 11

@[expose] def Row329M24 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥) →
      Nonempty (↥L ≃* NativeSporadic.M24) ∧ Nat.card V = 2 ^ 11

namespace Prop329

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    Nontrivial Q := by
  obtain ⟨-, -, a, b, hab⟩ := h
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [Subsingleton.elim x y]

theorem nonempty_mulEquiv_of_simple {V : Type*} [CommGroup V] {D : FFModel}
    {L : Subgroup (MulAut V)} {U Z : Subgroup V} (hs : IsSimpleGroup D.Gam)
    (hnt : Nontrivial ↥L) (h : D.Realizes L U Z) : Nonempty (↥L ≃* D.Gam) := by
  obtain ⟨π, hπ⟩ := h
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · exact ⟨(MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hk, hπ.1⟩).symm⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnt
    apply hab
    obtain ⟨γ, rfl⟩ := hπ.1 a
    obtain ⟨δ, rfl⟩ := hπ.1 b
    rw [(MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top γ),
      (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top δ)]

theorem nontrivial_of_b4Hyp {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) : Nontrivial ↥L :=
  nontrivial_of_isQuasisimple hHyp.2.2.1

end Prop329

end CFSG.Quasithin.H13
