module

public import CFSG.Quasithin.Background.F918Z8Sz4
public import CFSG.Quasithin.Background.F918Z8Sz6Bb
public import CFSG.Quasithin.Background.F918Z8Sz7Pa
public import CFSG.Quasithin.Background.F918Z8Sz7Qb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Count

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem rAV_quarter {A : Subgroup (MulAut Y)} {W M : Subgroup Y} (hAW : A ≤ stabSub W)
    (hAM : A ≤ stabSub M) (hW : Nat.card ↥W = Nat.card ↥M ^ 4)
    (hC : Nat.card ↥(W ⊓ fixV A) = Nat.card ↥(M ⊓ fixV A) ^ 4)
    (hker : A ⊓ centSub M = A ⊓ centSub W) :
    rAV (autSub A M) * 4 = rAV (autSub A W) :=
  rAV_quarter_proved hAW hAM hW hC hker

theorem suz_off_sec {A X : Subgroup (MulAut Y)} (hAel : IsElemAbelian2 A) {M I J : Subgroup Y}
    (hJI : J ≤ I) (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) (hcubic : commSeries A 3 = ⊥)
    (hrat : rAV (autSub A M) ≤ ((1 / 2 : ℚ))) (hfaith : A ⊓ centSec I J = A ⊓ centSub M)
    (hnt : ¬ A ≤ centSec I J) :
    qhatOf (autSec (X ⊔ A) I J) ≤ ((1 / 2 : ℚ) : WithTop ℚ) :=
  suz_off_sec_proved hAel hJI hIM hAM hAI hAJ hcubic hrat hfaith hnt

theorem suz_b4hyp {Γ : Subgroup (MulAut Y)} (hA21 : AsA21SQTKSection)
    (hΓ : IsQuotientOfSQTKTC ↥Γ) (hexp : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)}
    (hXΓ : X ≤ Γ) (hAΓ : A ≤ Γ) (hXq : CFSG.IsQuasisimple ↥X) (hAel : IsElemAbelian2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))) {I J : Subgroup Y} (hJI : J ≤ I)
    (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J) (hAI : A ≤ stabSub I) (hAJ : A ≤ stabSub J)
    (hirr : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ t ∈ T, x t ∈ T) → T = J ∨ T = I)
    (hnt : ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) :
    B4Hyp (autSec (X ⊔ A) I J) (autSec X I J) :=
  suz_b4hyp_proved hA21 hΓ hexp hXΓ hAΓ hXq hAel hAX hJI hXI hXJ hAI hAJ hirr hnt

end Count

section Field

variable {Y : Type} [CommGroup Y] [Finite Y] {Λ : Subgroup (MulAut Y)}

theorem suz_field {W : Subgroup Y} {n m : ℕ}
    (hΛ : Nat.card ↥Λ = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)) (hn3 : 3 ≤ n)
    {P : Subgroup (MulAut Y)} {t : MulAut Y} (htord : orderOf t = 2 ^ n - 1)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    {X : Subgroup (MulAut Y)} {I J : Subgroup Y} (hJI : J < I) (hIM : I ≤ W ⊓ fixV P)
    (htI : ∀ w ∈ I, t w ∈ I) (htJ : ∀ w ∈ J, t w ∈ J) (hXI : X ≤ stabSub I)
    (hXJ : X ≤ stabSub J) (hXt : ∀ x ∈ X, t * x = x * t)
    (hnat : BinaryNaturalSL (autSec X I J) ⊤ ⊥ 3 m) :
    1 ≤ m ∧ Nat.card ↥Λ ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) :=
  suz_field_proved hΛ hn3 htord hfree hJI hIM htI htJ hXI hXJ hXt hnat

end Field

section Statements

@[expose] def SuzSingle : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y)
    (A X K : Subgroup (MulAut Y)) (W : Subgroup Y), SuzData Γ Λ S V A X K W →
      ∀ a ∈ A, conjAutSub a K = K

@[expose] def SuzXirr : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y)
    (A X K : Subgroup (MulAut Y)) (W : Subgroup Y), SuzData Γ Λ S V A X K W → X = K →
    ∀ (n : ℕ) (P : Subgroup (MulAut Y)) (t : MulAut Y), 3 ≤ n → n % 2 = 1 → IsSylowTwoOf P Λ →
      t ∈ Λ → t ∈ Subgroup.normalizer (P : Set (MulAut Y)) → orderOf t = 2 ^ n - 1 →
      (∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥) →
      rAV (autSub A (W ⊓ fixV P)) ≤ ((1 / 2 : ℚ)) →
      ∀ I J : Subgroup Y, J < I → I ≤ W ⊓ fixV P → X ≤ stabSub I → X ≤ stabSub J →
        A ≤ stabSub I → A ≤ stabSub J → (∀ w ∈ I, t w ∈ I) → (∀ w ∈ J, t w ∈ J) →
        (∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
          (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I) →
        (∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) →
        A ⊓ centSec I J = A ⊓ centSub (W ⊓ fixV P) →
        ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) → T = J ∨ T = I

end Statements

section Applied

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem suz_single (hS : SuzSingle) {A X K : Subgroup (MulAut Y)} {W : Subgroup Y}
    (d : SuzData Γ Λ S V A X K W) : ∀ a ∈ A, conjAutSub a K = K :=
  hS Y Γ Λ S V A X K W d

theorem suz_xirr (hI : SuzXirr) {A X K : Subgroup (MulAut Y)} {W : Subgroup Y}
    (d : SuzData Γ Λ S V A X K W) (hXK : X = K) {n : ℕ} {P : Subgroup (MulAut Y)} {t : MulAut Y}
    (hn3 : 3 ≤ n) (hnodd : n % 2 = 1) (hP : IsSylowTwoOf P Λ) (htΛ : t ∈ Λ)
    (htN : t ∈ Subgroup.normalizer (P : Set (MulAut Y))) (htord : orderOf t = 2 ^ n - 1)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → W ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    (hrat : rAV (autSub A (W ⊓ fixV P)) ≤ ((1 / 2 : ℚ))) {I J : Subgroup Y} (hJI : J < I)
    (hIM : I ≤ W ⊓ fixV P) (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J) (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) (htI : ∀ w ∈ I, t w ∈ I) (htJ : ∀ w ∈ J, t w ∈ J)
    (hirrΞ : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
      (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I)
    (hnt : ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J)
    (hfaith : A ⊓ centSec I J = A ⊓ centSub (W ⊓ fixV P)) :
    ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) → T = J ∨ T = I :=
  hI Y Γ Λ S V A X K W d hXK n P t hn3 hnodd hP htΛ htN htord hfree hrat I J hJI hIM hXI hXJ hAI hAJ
    htI htJ hirrΞ hnt hfaith

end Applied

end CFSG.Quasithin
