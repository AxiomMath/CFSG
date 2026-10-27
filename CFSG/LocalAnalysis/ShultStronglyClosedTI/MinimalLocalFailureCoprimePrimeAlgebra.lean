module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeAlgebraCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFrobenius
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open
open CFSG.ShultStronglyClosedTI.CyclicSemiregular
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type*} [Group G]

theorem regular_restrict_subgroup {Q X A : Subgroup G}
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a⁻¹ * x * a ∈ X)
    (hreg : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b) :
    ∀ a ∈ ((Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) \ {1},
        ∃! x : (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G),
          (x : G)⁻¹ * a * x = b := by
  intro a ha b hb
  obtain ⟨x, hx, huniq⟩ := hreg a ⟨ha.1.1, ha.2⟩ b ⟨hb.1.1, hb.2⟩
  have hxA : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hca : c * a * c⁻¹ = a := by
      rw [(Subgroup.mem_centralizer_iff.mp ha.1.2) c hc, mul_inv_cancel_right]
    have hcb : c⁻¹ * b * c = b := by
      rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.mp hb.1.2) c hc, inv_mul_cancel_left]
    let x' : X := ⟨c⁻¹ * x * c, hAX c hc x x.2⟩
    have hx' : (x' : G)⁻¹ * a * x' = b := by
      change (c⁻¹ * x * c)⁻¹ * a * (c⁻¹ * x * c) = b
      calc
        (c⁻¹ * x * c)⁻¹ * a * (c⁻¹ * x * c) = c⁻¹ * ((x : G)⁻¹ * (c * a * c⁻¹) * x) * c := by
          group
        _ = b := by rw [hca, hx, hcb]
    have hxx : (c⁻¹ * x * c : G) = x := congrArg Subtype.val (huniq x' hx')
    calc c * (x : G) = c * (c⁻¹ * x * c) := by rw [hxx]
      _ = x * c := by group
  refine ⟨⟨x, x.2, hxA⟩, hx, ?_⟩
  intro y hy
  have hyx : (y : G) = x := congrArg Subtype.val (huniq ⟨y, y.2.1⟩ hy)
  exact Subtype.ext hyx

theorem centralizer_zpowers_eq (w : G) :
    Subgroup.centralizer (Subgroup.zpowers w : Set G) = Subgroup.centralizer ({w} : Set G) := by
  ext v
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h w (Subgroup.mem_zpowers w)).symm
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (((Commute.symm h).zpow_left k)).eq

theorem modEq_of_forall_two_pow_eq [Finite G] {X : Subgroup G} [IsCyclic X] {e : ℕ}
    (hXcard : Nat.card X = 2 ^ e - 1) {a b : ℕ}
    (hab : ∀ x ∈ X, x ^ (2 ^ a) = x ^ (2 ^ b)) : a ≡ b [MOD e] := by
  have he : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    rw [he0, pow_zero, Nat.sub_self] at hXcard
    exact (Nat.card_pos (α := X)).ne' hXcard
  obtain ⟨ξ, hξ⟩ := IsCyclic.exists_generator (α := X)
  have hξord : orderOf (ξ : G) = 2 ^ e - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hξ, hXcard]
  have hcop : ∀ c : ℕ, Nat.Coprime (2 ^ e - 1) (2 ^ c) := fun c =>
    Nat.Coprime.pow_right c (Nat.coprime_two_right.mpr (odd_two_pow_sub_one he))
  have key : ∀ c d : ℕ, c ≤ d → 2 ^ c ≡ 2 ^ d [MOD 2 ^ e - 1] → c ≡ d [MOD e] := by
    intro c d hcd hmod
    have h1 := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hcd)).mp hmod
    have h2 : 2 ^ d - 2 ^ c = 2 ^ c * (2 ^ (d - c) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hcd]
    rw [h2] at h1
    exact (Nat.modEq_iff_dvd' hcd).mpr
      (two_pow_sub_one_dvd_iff.mp ((hcop c).dvd_of_dvd_mul_left h1))
  have hmod : 2 ^ a ≡ 2 ^ b [MOD 2 ^ e - 1] := by
    rw [← hξord, ← pow_eq_pow_iff_modEq]
    exact hab ξ ξ.2
  rcases le_total a b with hle | hle
  · exact key a b hle hmod
  · exact (key b a hle hmod.symm).symm

theorem le_centralizer_of_dvd [Finite G] {X : Subgroup G} {e j : ℕ}
    (hXcard : Nat.card X = 2 ^ e - 1) {y : G} (hy : ∀ x ∈ X, y⁻¹ * x * y = x ^ (2 ^ j))
    (hej : e ∣ j) : X ≤ Subgroup.centralizer ({y} : Set G) := by
  intro x hx
  apply mem_centralizer_of_conj_eq
  rw [hy x hx, pow_two_pow_eq_self_iff]
  obtain ⟨r, hr⟩ := two_pow_sub_one_dvd_iff.mpr hej
  have hx1 : x ^ (2 ^ e - 1) = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : X))
    rw [hXcard] at h
    simpa using congrArg Subtype.val h
  rw [hr, pow_mul, hx1, one_pow]

theorem faithful_on_torus {Q X P : Subgroup G}
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {s : G} (hs : s ∈ (Q : Set G) \ {1}) (hPs : ∀ y ∈ P, y⁻¹ * s * y = s)
    (hfaith : ∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1)
    {y : G} (hyP : y ∈ P) (hyX : X ≤ Subgroup.centralizer ({y} : Set G)) : y = 1 := by
  apply hfaith y hyP
  intro v hv
  apply mem_centralizer_of_conj_eq
  by_cases hv1 : v = 1
  · rw [hv1]
    group
  obtain ⟨x, hx, -⟩ := hXregular s hs v ⟨hv, hv1⟩
  have hxy : y⁻¹ * (x : G) * y = x := conj_eq_of_mem_centralizer (hyX x.2)
  calc y⁻¹ * v * y = (y⁻¹ * x * y)⁻¹ * (y⁻¹ * s * y) * (y⁻¹ * x * y) := by rw [← hx]; group
    _ = v := by rw [hxy, hPs y hyP, hx]

variable [Finite G]

theorem card_fixed_of_two_pow {Q X : Subgroup G} [IsCyclic X] {e : ℕ}
    (hQcard : Nat.card Q = 2 ^ e) (hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {s : G} (hs : s ∈ (Q : Set G) \ {1}) {w : G} (hws : w⁻¹ * s * w = s)
    (hwX : ∀ x ∈ X, w⁻¹ * x * w ∈ X) {j : ℕ} (hj : ∀ x ∈ X, w⁻¹ * x * w = x ^ (2 ^ j)) :
    Nat.card (Q ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 2 ^ Nat.gcd e j := by
  set E := Q ⊓ Subgroup.centralizer ({w} : Set G)
  set X₀ := X ⊓ Subgroup.centralizer ({w} : Set G)
  have hn : Nat.card X = 2 ^ e - 1 := by rw [hXcard, hQcard]
  have hcent : ∀ x ∈ X, x ∈ Subgroup.centralizer ({w} : Set G) ↔ x ^ (2 ^ j - 1) = 1 := by
    intro x hx
    rw [← pow_two_pow_eq_self_iff, ← hj x hx]
    exact ⟨conj_eq_of_mem_centralizer, mem_centralizer_of_conj_eq⟩
  have hX₀card : Nat.card X₀ = 2 ^ Nat.gcd e j - 1 := by
    have hgcd : Nat.gcd (Nat.card X) (2 ^ j - 1) = 2 ^ Nat.gcd e j - 1 := by
      rw [hn, Nat.pow_sub_one_gcd_pow_sub_one]
    rw [← hgcd, ← card_pow_eq_one_eq_gcd (A := X)]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, Subtype.ext ((hcent x x.2.1).mp x.2.2)⟩
        invFun := fun x => ⟨x.1, x.1.2, (hcent x.1 x.1.2).mpr (congrArg Subtype.val x.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hreg := regular_restrict (Q := Q) hwX hXregular
  have hSE : ∀ x ∈ X₀, ∀ a ∈ (E : Set G) \ {1}, x⁻¹ * a * x ∈ (E : Set G) \ {1} := by
    intro x hx a ha
    refine ⟨⟨hXQ x hx.1 a ha.1.1, ?_⟩, conj_ne_one ha.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) ha.1.2) hx.2
  have hsE : s ∈ (E : Set G) \ {1} := ⟨⟨hs.1, mem_centralizer_of_conj_eq hws⟩, hs.2⟩
  have hE : Nat.card X₀ = Nat.card E - 1 := by
    rw [card_eq_of_regular hSE hreg hsE, card_diff_one]
  have hpos : 0 < Nat.card E := Nat.card_pos
  have h1 : 1 ≤ 2 ^ Nat.gcd e j := Nat.one_le_two_pow
  omega

theorem frobenius_action_structure {Q X P : Subgroup G} {e : ℕ}
    (hQ : IsElemAbelian 2 Q) (hQcard : Nat.card Q = 2 ^ e) (he : 1 ≤ e)
    (hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q) (hXcyclic : IsCyclic X)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    (hPQ : ∀ y ∈ P, ∀ v ∈ Q, y⁻¹ * v * y ∈ Q) (hPX : ∀ y ∈ P, ∀ x ∈ X, y⁻¹ * x * y ∈ X)
    {s : G} (hs : s ∈ (Q : Set G) \ {1}) (hPs : ∀ y ∈ P, y⁻¹ * s * y = s)
    (hfaith : ∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1) :
    IsCyclic P ∧ Nat.card P ∣ e ∧
      ∀ W : Subgroup G, W ≤ P →
        Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) = 2 ^ (e / Nat.card W) := by
  have hn : Nat.card X = 2 ^ e - 1 := by rw [hXcard, hQcard]
  have he0 : e ≠ 0 := by omega
  let : NeZero e := ⟨he0⟩
  choose j hj using fun y : P =>
    exists_two_pow_conj_eq hQ hQcard he hXQ hXcyclic hXregular (hPQ y y.2) (hPX y y.2)
  have hjmul : ∀ y₁ y₂ : P, j (y₁ * y₂) ≡ j y₁ + j y₂ [MOD e] := by
    intro y₁ y₂
    refine modEq_of_forall_two_pow_eq hn fun x hx => ?_
    rw [← hj (y₁ * y₂) x hx]
    calc ((y₁ * y₂ : P) : G)⁻¹ * x * ((y₁ * y₂ : P) : G) =
          (y₂ : G)⁻¹ * ((y₁ : G)⁻¹ * x * y₁) * y₂ := by
          simp only [Subgroup.coe_mul]
          group
      _ = x ^ 2 ^ (j y₁ + j y₂) := by
          rw [hj y₁ x hx, inv_mul_pow_mul, hj y₂ x hx, ← pow_mul, ← pow_add, add_comm]
  have hjone : j 1 ≡ 0 [MOD e] := by
    refine modEq_of_forall_two_pow_eq hn fun x hx => ?_
    rw [← hj 1 x hx]
    simp
  let φ : P →* Multiplicative (ZMod e) :=
    { toFun := fun y => Multiplicative.ofAdd (j y : ZMod e)
      map_one' := by
        change Multiplicative.ofAdd (j 1 : ZMod e) = Multiplicative.ofAdd 0
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hjone, Nat.cast_zero]
      map_mul' := fun y₁ y₂ => by
        change Multiplicative.ofAdd (j (y₁ * y₂) : ZMod e) =
          Multiplicative.ofAdd ((j y₁ : ZMod e) + (j y₂ : ZMod e))
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr (hjmul y₁ y₂), Nat.cast_add] }
  have hφ : ∀ y : P, φ y = Multiplicative.ofAdd (j y : ZMod e) := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hφ] at hy
    have hy0 : (j y : ZMod e) = 0 := by simpa using hy
    have hdvd : e ∣ j y := (ZMod.natCast_eq_zero_iff _ _).mp hy0
    exact Subtype.ext (faithful_on_torus hXregular hs hPs hfaith y.2
      (le_centralizer_of_dvd hn (hj y) hdvd))
  have hcyc : IsCyclic P := isCyclic_of_injective φ hφinj
  have hcard : Nat.card P ∣ e := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv] at h
    simpa [Nat.card_zmod] using h
  refine ⟨hcyc, hcard, fun W hWP => ?_⟩
  have : IsCyclic (W.subgroupOf P) := inferInstance
  have hWcyc : IsCyclic W :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWP).surjective
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := W)
  have hWeq : W = Subgroup.zpowers (w : G) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hw ⟨g, hg⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact (Subgroup.zpowers_le).mpr w.2
  have hwP : (w : G) ∈ P := hWP w.2
  let wP : P := ⟨w, hwP⟩
  have hcardW : Nat.card W = e / Nat.gcd e (j wP) := by
    rw [hWeq, Nat.card_zpowers, ← Subgroup.orderOf_mk (w : G) hwP, ← orderOf_injective φ hφinj,
      hφ, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe _ he0]
  have hfix := card_fixed_of_two_pow hQcard hXQ hXcard hXregular hs (hPs w hwP)
    (hPX w hwP) (hj wP)
  rw [hWeq, centralizer_zpowers_eq, hfix, ← hWeq, hcardW,
    Nat.div_div_self (Nat.gcd_dvd_left e (j wP)) he0]

end CFSG.ShultStronglyClosedTI.CoprimePrime
