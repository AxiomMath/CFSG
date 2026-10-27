module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.E1Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

namespace E3

open CFSG.Open

universe u

section Rank

variable {G : Type*} [Group G]

@[expose] noncomputable def mQuot (V U : Subgroup G) : ℕ := padicValNat 2 (U.relIndex V)

theorem mQuot_eq_rkIdx (V U : Subgroup G) : mQuot V U = rkIdx (U.subgroupOf V) := rfl

variable [Finite G]

theorem relIndex_ne_zero' (V U : Subgroup G) : U.relIndex V ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

omit [Finite G] in
theorem mQuot_self (V : Subgroup G) : mQuot V V = 0 := by
  simp [mQuot, Subgroup.relIndex_self]

theorem mQuot_mono {V U U' : Subgroup G} (h : U ≤ U') : mQuot V U' ≤ mQuot V U :=
  padicValNat_two_le_of_dvd (relIndex_ne_zero' V U) (Subgroup.relIndex_dvd_of_le_left V h)

theorem mQuot_add {V U U' : Subgroup G} (hUU' : U ≤ U') (hU'V : U' ≤ V) :
    mQuot V U = mQuot U' U + mQuot V U' := by
  unfold mQuot
  rw [← Subgroup.relIndex_mul_relIndex U U' V hUU' hU'V,
    padicValNat.mul (relIndex_ne_zero' U' U) (relIndex_ne_zero' V U')]

theorem relIndex_eq_two_pow {V : Subgroup G} (hV : IsPGroup 2 V) (U : Subgroup G) :
    U.relIndex V = 2 ^ mQuot V U := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hV
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hn ▸ Subgroup.relIndex_dvd_card (H := U) (K := V))
  unfold mQuot
  rw [hk, padicValNat.prime_pow]

theorem card_eq_two_pow_mul {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) :
    Nat.card V = 2 ^ mQuot V U * Nat.card U := by
  have h := Subgroup.relIndex_mul_card (H := U) (K := V)
  rw [inf_eq_left.2 hUV, relIndex_eq_two_pow hV] at h
  exact h.symm

theorem mQuot_eq_zero_iff {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) :
    mQuot V U = 0 ↔ U = V := by
  constructor
  · intro h
    have h1 : U.relIndex V = 1 := by rw [relIndex_eq_two_pow hV, h, pow_zero]
    exact le_antisymm hUV (Subgroup.relIndex_eq_one.1 h1)
  · rintro rfl
    exact mQuot_self _

end Rank

section Module

variable {W : Type*} [CommGroup W]

@[expose] noncomputable def mParam (X : Subgroup (MulAut W)) : ℕ :=
  if Even (Nat.card X) then
    sInf {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))}
  else rk W

@[expose] def aSet (k : ℕ) (X : Subgroup (MulAut W)) : Set (Subgroup (MulAut W)) :=
  {A | A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    ∀ B : Subgroup (MulAut W), B ≤ A → mQuot A B < k → fixV B = fixV A}

@[expose] noncomputable def aParam (X : Subgroup (MulAut W)) : ℕ :=
  if Even (Nat.card X) then sSup {k : ℕ | 0 < k ∧ (aSet k X).Nonempty} else 0

@[expose] def gammaCheck (k : ℕ) (P : Subgroup (MulAut W)) : Subgroup W :=
  ⨆ (X : Subgroup (MulAut W)) (_ : X ≤ P) (_ : mQuot P X ≤ k), fixV X

end Module

section Internal

open scoped Pointwise commutatorElement

variable {G : Type u} [Group G]

@[expose] noncomputable def rParam (V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ {U : Subgroup G | U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)}, (mQuot V U : ℕ∞)

@[expose] noncomputable def sParam {V : Subgroup G} (hV : IsElemAbelian 2 V) : ℕ :=
  (min (rParam V) ((mParam (autI hV ⊤) : ℕ) : ℕ∞)).toNat

@[expose] def gammaSet (V : Subgroup G) (i : ℕ) (X : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ X ∧ ∃ g : G, A ≤ conjSubgroup V g ∧ mQuot (conjSubgroup V g) A = i}

@[expose] def wClos (V : Subgroup G) (i : ℕ) (X : Subgroup G) : Subgroup G :=
  ⨆ A ∈ gammaSet V i X, A

@[expose] def cClos (V : Subgroup G) (i : ℕ) (X : Subgroup G) : Subgroup G :=
  X ⊓ Subgroup.centralizer (wClos V i X : Set G)

@[expose] noncomputable def wParam (T V : Subgroup G) : ℕ∞ :=
  ⨅ j ∈ {j : ℕ | ¬ wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)}, (j : ℕ∞)

@[expose] def IsWOffenderAt (T V : Subgroup G) (g : G) : Prop :=
  ⁅V, conjSubgroup V g⁆ ≠ ⊥ ∧
    wParam T V = (mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) : ℕ∞)

@[expose] def IsWOffender (T V A : Subgroup G) : Prop :=
  ∃ g : G, A = conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ∧ IsWOffenderAt T V g

@[expose] noncomputable def nPrime {M : Type*} [Group M] (X : Subgroup M) : ℕ :=
  sSup {c : ℕ | ∃ Y B S : Subgroup M, Y ≤ B ∧ B ≤ X ∧ IsCyclic Y ∧ Nat.card Y = 2 ^ c - 1 ∧
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧ IsSylowIn 2 S X ∧
    (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M)}

structure HypE322 (T V : Subgroup G) : Prop where
  sylow : IsSylowIn 2 T ⊤
  le : V ≤ T
  normal : T ≤ Subgroup.normalizer (V : Set G)

@[expose] def HypE324 (T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  0 < wParam T V ∨ ¬ IsFFModule (autI hV ⊤)

structure HypE336 {G : Type} [Group G] [Finite G] (T V M : Subgroup G) : Prop where
  hyp322 : HypE322 T V
  qtke : quasithinIsQTKECat G
  unique : IsUniqueM
    (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M
  local_structure : ∀ H : Subgroup G, IsHStar T M H → 1 < E1.nParam H →
    H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) ∧
      H ⊓ M ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (H ⊓ M)

end Internal

end E3

end CFSG.Quasithin
