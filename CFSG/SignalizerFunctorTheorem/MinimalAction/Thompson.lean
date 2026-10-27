module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator
public import CFSG.SignalizerFunctorTheorem.MinimalAction.AbelianCase
public import CFSG.SignalizerFunctorTheorem.MinimalAction.Baer
public import Mathlib.Order.CompletePartialOrder

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G]

@[expose] def conjAut (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    MulAut X where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp x.2
    simpa using h⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem coe_conjAut (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x : X) : ((conjAut X hg x : X) : G) = g * (x : G) * g⁻¹ := rfl

@[expose] def conjHom (X S : Subgroup G) (h : S ≤ Subgroup.normalizer (X : Set G)) :
    S →* MulAut X where
  toFun a := conjAut X (h a.2)
  map_one' := by ext; simp [coe_conjAut]
  map_mul' a b := by ext; simp [coe_conjAut, mul_assoc]

theorem coe_conjHom (X S : Subgroup G) (h : S ≤ Subgroup.normalizer (X : Set G))
    (a : S) (x : X) : ((conjHom X S h a x : X) : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

variable [Finite G]

theorem centralizes_of_commutators_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q X : Subgroup G} (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hX : IsPGroup p X)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G))
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ⁅a, b⁆ * c = c * ⁅a, b⁆) :
    X ≤ Subgroup.centralizer (Q : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hodd : Odd (Nat.card X) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hcomm' : ∀ x y z : X, ⁅x, y⁆ * z = z * ⁅x, y⁆ := fun x y z => by
    apply Subtype.ext
    exact hcomm x x.2 y y.2 z z.2
  obtain ⟨inst, hadd⟩ := exists_baer_addCommGroup hodd hcomm'
  let := inst
  let φ : MulAut X →* AddMonoid.End X :=
    { toFun := fun α => AddMonoidHom.mk' (fun v => α v) (fun v w => hadd α.toMonoidHom v w)
      map_one' := by ext; rfl
      map_mul' := fun α β => by ext; rfl }
  have hφ : ∀ (α : MulAut X) (v : X), φ α v = α v := fun α v => rfl
  have hfin : Finite (MulAut X) := MulEquiv.finite_left
  let ρP := conjHom X P hPX
  let ρQ := conjHom X Q hQX
  have hPg : IsPGroup p ρP.range := hP.of_surjective ρP.rangeRestrict ρP.rangeRestrict_surjective
  have hQg : Nat.Coprime p (Nat.card ρQ.range) :=
    hQ.coprime_dvd_right (Subgroup.card_range_dvd ρQ)
  have hPQg : ρP.range ≤ Subgroup.normalizer (ρQ.range : Set (MulAut X)) := by
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨b, rfl⟩
    have hmem : (a : G) * b * (a : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hPQ a.2) b).mp b.2
    have hcomm : ρP a * ρQ b = ρQ ⟨(a : G) * b * (a : G)⁻¹, hmem⟩ * ρP a := by
      ext x
      simp [ρP, ρQ, coe_conjHom, mul_assoc]
    exact ⟨_, (mul_inv_eq_iff_eq_mul.mpr hcomm).symm⟩
  have hfix : ∀ v : X, (∀ α ∈ ρP.range, φ α v = v) → ∀ β ∈ ρQ.range, φ β v = v := by
    intro v hv β hβ
    have hvC : (v : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := congrArg (fun w : X => (w : G)) (hv (ρP ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩)
      simp only [hφ, ρP, coe_conjHom] at h
      calc a * (v : G) = a * (v : G) * a⁻¹ * a := by group
        _ = (v : G) * a := by rw [h]
    have hvQ : (v : G) ∈ Subgroup.centralizer (Q : Set G) := hC ⟨v.2, hvC⟩
    obtain ⟨b, rfl⟩ := hβ
    apply Subtype.ext
    simp only [hφ, ρQ, coe_conjHom]
    have := Subgroup.mem_centralizer_iff.mp hvQ b b.2
    calc (b : G) * (v : G) * (b : G)⁻¹ = (v : G) * b * (b : G)⁻¹ := by rw [this]
      _ = v := by group
  have hmain := abelian_case hp ⟨k, hk⟩ φ hPg hQg hPQg hfix
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h := congrArg (fun w : X => (w : G)) (hmain (ρQ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ ⟨v, hv⟩)
  simp only [hφ, ρQ, coe_conjHom] at h
  calc b * v = b * v * b⁻¹ * b := by group
    _ = v * b := by rw [h]

theorem thompson_main {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q X : Subgroup G} (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hX : IsPGroup p X)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G)) :
    X ≤ Subgroup.centralizer (Q : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  suffices h : ∀ n : ℕ, ∀ X : Subgroup G, Nat.card X = n → IsPGroup p X →
      P ≤ Subgroup.normalizer (X : Set G) → Q ≤ Subgroup.normalizer (X : Set G) →
      X ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G) →
      X ≤ Subgroup.centralizer (Q : Set G) from h _ X rfl hX hPX hQX hC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn hX hPX hQX hC
    by_cases hXQ : ⁅X, Q⁆ = ⊥
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXQ
    have hBX : Q ⊔ P ≤ Subgroup.normalizer (X : Set G) := sup_le hQX hPX
    have hBQ : Q ⊔ P ≤ Subgroup.normalizer (Q : Set G) :=
      sup_le Subgroup.le_normalizer hPQ
    have hind : ∀ R : Subgroup G, R < X → Q ⊔ P ≤ Subgroup.normalizer (R : Set G) →
        ⁅R, Q⁆ = ⊥ := by
      intro R hRX hRB
      have hcard : Nat.card R < n := hn ▸ CFSG.natCard_lt_of_subgroup_lt hRX
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (ih (Nat.card R) hcard R rfl (hX.to_le hRX.le) (le_sup_right.trans hRB)
          (le_sup_left.trans hRB) (fun g hg => hC ⟨hRX.le hg.1, hg.2⟩))
    have hXcop : Nat.Coprime (Nat.card Q) (Nat.card X) := by
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      rw [hk]
      exact hQ.symm.pow_right k
    have hXQX : ⁅X, Q⁆ = X :=
      GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime (Q ⊔ P) X Q hBX hBQ hQX
        hXcop hXQ (fun R hRX hRB hRQ => by
          by_contra hXR
          exact hRQ (hind R (lt_of_le_not_ge hRX hXR) hRB))
    have hXbot : X ≠ ⊥ := fun h => hXQ (by rw [h]; exact Subgroup.commutator_bot_left Q)
    have hX'lt : ⁅X, X⁆ < X :=
      GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups X X hX hX
        Subgroup.le_normalizer hXbot
    have hBX' : Q ⊔ P ≤ Subgroup.normalizer ((⁅X, X⁆ : Subgroup G) : Set G) :=
      GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ X X hBX hBX
    have hX'Q : ⁅⁅X, X⁆, Q⁆ = ⊥ := hind _ hX'lt hBX'
    have hXX' : ⁅X, ⁅X, X⁆⁆ = ⊥ := by
      have h1 : ⁅⁅X, ⁅X, X⁆⁆, Q⁆ = ⊥ := by
        refine le_bot_iff.mp ?_
        rw [← hX'Q]
        refine Subgroup.commutator_mono ?_ le_rfl
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          (GorensteinWalter.le_normalizer_commutator_of_le_normalizer X X X
            Subgroup.le_normalizer Subgroup.le_normalizer)
      have h2 : ⁅⁅⁅X, X⁆, Q⁆, X⁆ = ⊥ := by rw [hX'Q]; exact Subgroup.commutator_bot_left X
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q) (H₂ := X)
        (H₃ := ⁅X, X⁆) h1 h2
      rwa [Subgroup.commutator_comm Q X, hXQX] at h3
    have hcomm : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
      intro a ha b hb c hc
      have hcent : X ≤ Subgroup.centralizer ((⁅X, X⁆ : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXX'
      exact Subgroup.mem_centralizer_iff.mp (hcent hc) _
        (Subgroup.commutator_mem_commutator ha hb)
    exact centralizes_of_commutators_central hp hp2 hP hQ hPQ hX hPX hQX hC hcomm

end CFSG.SignalizerFunctorTheorem.MinimalAction
