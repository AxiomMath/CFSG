module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.Timmesfeld.Transvection.FrameResidue

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres

@[expose] def OddFrameBC2Statement :
    Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) →
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hFn : Nat.card F = (2 ^ n) ^ 2),
    2 ≤ n → (∀ A ∈ Δ, Nat.card A = 2 ^ n) →
  ∀ (r : ℕ) (hr : 2 ≤ r) (hm : 4 ≤ 2 * r) (P Q : Fin (2 * r / 2) → Subgroup H),
    IsMaxFrame Δ P Q → ¬ IsSmallFrame Δ P Q (cLastIdx r hr) →
  ∀ R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H, R.HasFrameImages Δ P Q →
    (R.toHom hFn (even_two_mul r) hm).range ⊔ residueGroup Δ P Q (cLastIdx r hr) = ⊤ →
    (∀ X ∈ frameResidue Δ P Q (cLastIdx r hr),
      ∃ g ∈ residueGroup Δ P Q (cLastIdx r hr), conjSub (P (cLastIdx r hr)) g = X) →
  ∀ θ₀ : SU (unitaryInvolution F 2 n) 3 →* H,
    θ₀.range = residueGroup Δ P Q (cLastIdx r hr) → θ₀.ker ≤ Subgroup.center _ →
    Odd (Nat.card θ₀.ker) →
    θ₀.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm →
    (∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ₀) →
    OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ₀ →
  ∃ θ : SU (unitaryInvolution F 2 n) 3 →* H,
    θ.range = residueGroup Δ P Q (cLastIdx r hr) ∧
    θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm ∧
    ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
          (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
        (CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
      (oddFrameMap hFn hr (R.toHom hFn (even_two_mul r) hm) θ)

end CFSG.Timmesfeld.Transvection
