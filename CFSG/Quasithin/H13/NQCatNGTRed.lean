module

public import CFSG.Quasithin.H13.NQCatNGTInst
public import CFSG.Quasithin.H13.NQCatNGTG2
public import CFSG.Quasithin.H13.A5W1619b
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.G2A5Seven
public import CFSG.Quasithin.Background.G2L2Seven
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.U3L14E
public import CFSG.Quasithin.SteinbergCBSevenSylowAFive
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19F
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19N
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Y
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Comp
public import CFSG.Quasithin.Vol2.Ch6Sec1Lin2Excl
public import CFSG.Quasithin.Vol2.Ch6Skeleton
public import CFSG.Quasithin.Vol2.Ch6Sp

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

local notation "StSL" => CFSG.Assembly.LowTwoRank.StatedSL

local notation "StSp" => CFSG.Assembly.LowTwoRank.StatedSp

theorem factNoGraphTwist_of_sections
    (hsec : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ J X : Subgroup (MulAut V), B53Hyp J →
      (B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) → X ≤ J →
      (∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) → CFSG.IsQuasisimple ↥X →
      ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
      (Nonempty (↥X ≃* ↥(StSL 3 F)) ∨ Nonempty (↥X ≃* ↥(StSp 2 F))) →
      ∀ g : MulAut V, g ∈ Subgroup.normalizer (J : Set (MulAut V)) →
        g ∈ Subgroup.normalizer (X : Set (MulAut V)) →
        ∃ U Z : Subgroup V, U.map g.toMonoidHom = U ∧ Z.map g.toMonoidHom = Z ∧
          ((∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
              ∃ π : ↥(StSL 3 K) →* ↥X, NatTransfer X U Z (StSL 3 K) π) ∨
            ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
              ∃ π : ↥(StSp 2 K) →* ↥X, NatTransfer X U Z (StSp 2 K) π)) :
    H13.A5.FactNoGraphTwist := by
  intro V _ _ hV2 J X hJ hcases hXJ hXn hXq F _ _ n hn hF hXiso S M hS hSM hMX hmax g hgJ hgX
    hgS
  by_contra hne
  have hne' : M ≠ M.map (MulAut.conj g).toMonoidHom := fun h => hne h.symm
  obtain ⟨hS₁, hM₁X, hmax₁⟩ := conj_maximal hgX hgS hSM hMX hmax
  have hmod : (Nonempty (↥X ≃* ↥(StSL 3 F)) ∨ Nonempty (↥X ≃* ↥(StSp 2 F))) → False := by
    intro hX
    obtain ⟨U, Z, hgU, hgZ, hdata⟩ := hsec V hV2 J X hJ hcases hXJ hXn hXq F n hn hF hX g hgJ hgX
    rcases hdata with ⟨K, _, _, f, hK, hf, π, hT⟩ | ⟨K, _, _, f, hK, hf, π, hT⟩
    · exact no_swap_sl3 hK hf hT hS ⟨hSM, hMX, hmax⟩ ⟨hS₁, hM₁X, hmax₁⟩ hne' g hgU hgZ rfl
    · exact no_swap_sp4 hK hf hT hS ⟨hSM, hMX, hmax⟩ ⟨hS₁, hM₁X, hmax₁⟩ hne' g hgU hgZ rfl
  rcases hXiso with h | h | ⟨⟨e⟩⟩
  · exact hmod (Or.inl h)
  · exact hmod (Or.inr h)
  · have : Finite (MulAut V) :=
      Finite.of_injective (fun (h : MulAut V) (v : V) => h v) fun a b hab =>
        MulEquiv.ext (congrFun hab)
    exact no_swap_g2 hn hF e hS ⟨hSM, hMX, hmax⟩ ⟨hS₁, hM₁X, hmax₁⟩ hne' (MulAut.conj g) rfl

end CFSG.Quasithin.H13.NQCat.NGT
