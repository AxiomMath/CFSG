module

public import CFSG.Quasithin.EmptyFaithful.LRed6Real
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin

namespace LRed6

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def G2FixBound : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ Wm : Subgroup (Multiplicative (quasithinZorn K)), Wm ≤ zornO0 K → zornR K ≤ Wm →
      Nat.card ↥Wm = 32 →
      Nat.card {γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ //
        ∀ m ∈ Wm, zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m * m⁻¹ ∈ zornR K} ≤ 2

theorem card_zornR (K : Type) [Field K] : Nat.card ↥(zornR K) = Nat.card K := by
  have hbij : Function.Bijective (fun x : ↥(zornR K) => (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1) := by
    constructor
    · intro x y hxy
      obtain ⟨cx, hcx⟩ := x.2
      obtain ⟨cy, hcy⟩ := y.2
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      have h1 : (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1 = cx := by
        rw [show Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) = (cx, 0, 0, cx) from hcx]
      have h2 : (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).1 = cy := by
        rw [show Multiplicative.toAdd (y : Multiplicative (quasithinZorn K)) = (cy, 0, 0, cy) from hcy]
      have : cx = cy := by rw [← h1, ← h2]; exact hxy
      rw [show Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) = (cx, 0, 0, cx) from hcx,
        show Multiplicative.toAdd (y : Multiplicative (quasithinZorn K)) = (cy, 0, 0, cy) from hcy, this]
    · intro c
      exact ⟨⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

variable {V : Type*} [CommGroup V]

theorem g2_card_le (hres : G2FixBound) {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : G2NaturalDerived L U Z 1) {W : Subgroup V} [Finite ↥W] (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥)
    (hW : Nat.card ↥W = 16) :
    Nat.card {x : ↥L // ∀ w ∈ W, ((x : ↥L) : MulAut V) w = w} ≤ 2 := by
  obtain ⟨K, hK, hKf, hKc, π, hπ⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hKc
  have hcp : CharP K 2 := FFC.charP_two_of_card_pow hKc
  have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
        ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
  have hbij : Function.Bijective π :=
    ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ hle) hπ, hπ.1⟩
  obtain ⟨Wm₀, hWm₀, hker₀, hcardWm₀, hfix₀, -, -⟩ := exists_preimage hπ hWU hWZ
  let Wm : Subgroup (Multiplicative (quasithinZorn K)) := Wm₀
  have hWm : Wm ≤ zornO0 K := hWm₀
  have hker : zornR K ≤ Wm := hker₀
  have hcard32 : Nat.card ↥Wm = 32 := by
    show Nat.card ↥Wm₀ = 32
    rw [hcardWm₀, hW]
    show 16 * Nat.card ↥(zornR K) = 32
    rw [card_zornR, hK2]
  have hfix : ∀ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, (∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w) →
      ∀ m ∈ Wm, zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m * m⁻¹ ∈ zornR K :=
    fun γ hγ m hm => hfix₀ γ hγ m hm
  have hS : Nat.card {γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ //
      ∀ m ∈ Wm, zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m * m⁻¹ ∈ zornR K} ≤ 2 :=
    hres K hK2 Wm hWm hker hcard32
  have h1 : Nat.card {γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ //
      ∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w} ≤
      Nat.card {γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ //
      ∀ m ∈ Wm, zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m * m⁻¹ ∈ zornR K} := by
    refine Nat.card_le_card_of_injective (fun γ => ⟨γ.1, hfix γ.1 γ.2⟩) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    exact Subtype.ext hab'
  have h2 : Nat.card {x : ↥L // ∀ w ∈ W, ((x : ↥L) : MulAut V) w = w} =
      Nat.card {γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ //
      ∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w} := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨π γ.1, γ.2⟩) ⟨?_, ?_⟩)
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext (hbij.1 hab')
    · intro x
      obtain ⟨γ, hγ⟩ := hbij.2 x.1
      exact ⟨⟨γ, by rw [hγ]; exact x.2⟩, Subtype.ext hγ⟩
  rw [h2]
  exact h1.trans hS

end LRed6

end CFSG.Quasithin
