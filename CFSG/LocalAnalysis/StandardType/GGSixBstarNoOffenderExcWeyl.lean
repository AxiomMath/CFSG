module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGWeylNoOffender (τ : Tag) (p : ℕ) : Prop :=
  ∀ A : Subgroup (WeylGroup τ), IsElemAbelian p A → A ≠ ⊥ →
    Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, TableBExc.torusAct τ p a x = x} <
      p ^ τ.rank

namespace NoOffExc

section Faithful

variable {τ : Tag} {p : ℕ}

theorem liftMod_single [Fact p.Prime] (j : Fin τ.rank) :
    TableBExc.liftMod τ p (Pi.single j 1) = Pi.single j 1 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  funext k
  by_cases hk : k = j
  · subst hk
    simp [TableBExc.liftMod, ZMod.val_one]
  · simp [TableBExc.liftMod, hk]

theorem eq_one_of_torusAct [Fact p.Prime] (hp2 : p ≠ 2) {w : WeylGroup τ}
    (hw : ∀ x, TableBExc.torusAct τ p w x = x) : w = 1 := by
  apply CFSG.LieType.RootSystem.weylAction_injective (isFiniteType_cartan τ)
  rw [map_one]
  set X := LinearMap.toMatrixAlgEquiv'
    (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w) with hXdef
  have hk : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hX : X ^ orderOf w = 1 := by
    rw [hXdef, ← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  have hmod : ∀ i j, (p : ℤ) ∣ (X - 1) i j := by
    intro i j
    have h1 := congrFun (hw (Pi.single j 1)) i
    rw [TableBExc.torusAct, liftMod_single] at h1
    simp only [TableBExc.redMod] at h1
    rw [Matrix.sub_apply, hXdef, LinearMap.toMatrixAlgEquiv'_apply, Matrix.one_apply,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← smul_def]
    push_cast
    rw [h1]
    simp [Pi.single_apply]
  have hX1 := int_matrix_eq_one_of_pow_eq_one hp2 hk hX hmod
  exact (LinearMap.toMatrixAlgEquiv').injective (by rw [← hXdef, hX1, map_one])

theorem torusPerm_injective [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective (TableBExc.torusPerm τ p) := by
  intro w w' h
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : w'⁻¹ * w = 1 := eq_one_of_torusAct hp2 fun x => by
    rw [TableBExc.torusAct_mul, ← TableBExc.torusPerm_apply, ← TableBExc.torusPerm_apply, h,
      ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.coe_one, id]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end Faithful

section Reduction

variable {τ : Tag} {p : ℕ}

theorem card_fix_map_conj [NeZero p] (A : Subgroup (WeylGroup τ)) (g : WeylGroup τ) :
    Nat.card {x : Fin τ.rank → ZMod p //
      ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, TableBExc.torusAct τ p a x = x} =
    Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, TableBExc.torusAct τ p a x = x} := by
  have hgx : ∀ x, TableBExc.torusAct τ p g (TableBExc.torusAct τ p g⁻¹ x) = x := fun x => by
    rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
  have hgx' : ∀ x, TableBExc.torusAct τ p g⁻¹ (TableBExc.torusAct τ p g x) = x := fun x => by
    rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
  have hconj : ∀ (a : WeylGroup τ) (x : Fin τ.rank → ZMod p),
      TableBExc.torusAct τ p (g * a * g⁻¹) x =
        TableBExc.torusAct τ p g (TableBExc.torusAct τ p a (TableBExc.torusAct τ p g⁻¹ x)) :=
    fun a x => by rw [TableBExc.torusAct_mul, TableBExc.torusAct_mul]
  have key : ∀ (a : WeylGroup τ) (x : Fin τ.rank → ZMod p),
      TableBExc.torusAct τ p (g * a * g⁻¹) x = x ↔
        TableBExc.torusAct τ p a (TableBExc.torusAct τ p g⁻¹ x) =
          TableBExc.torusAct τ p g⁻¹ x := by
    intro a x
    rw [hconj]
    constructor
    · intro h
      have h2 := congrArg (TableBExc.torusAct τ p g⁻¹) h
      rwa [hgx'] at h2
    · intro h
      rw [h, hgx]
  refine Nat.card_congr
    { toFun := fun x => ⟨TableBExc.torusAct τ p g⁻¹ x.1, fun a ha =>
        (key a x.1).mp (x.2 _ (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))⟩
      invFun := fun y => ⟨TableBExc.torusAct τ p g y.1, fun b hb => by
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
        change TableBExc.torusAct τ p (g * a * g⁻¹) _ = _
        rw [hconj, hgx', y.2 a ha]⟩
      left_inv := fun x => Subtype.ext (hgx x.1)
      right_inv := fun y => Subtype.ext (hgx' y.1) }

theorem ggWeylNoOffender_of_not_dvd (hp : p.Prime) (h : ¬ p ∣ Nat.card (WeylGroup τ)) :
    GGWeylNoOffender τ p := by
  have : Fact p.Prime := ⟨hp⟩
  intro A hA hA1
  exfalso
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have ha1' : (a : WeylGroup τ) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have hord : orderOf (a : WeylGroup τ) = p := orderOf_eq_prime (hA.2 a a.2) ha1'
  exact h (hord ▸ orderOf_dvd_natCard (a : WeylGroup τ))

theorem ggWeylNoOffender_of_sylow (hp : p.Prime) {S : Subgroup (WeylGroup τ)}
    (hidx : ¬ p ∣ S.index)
    (hS : ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, TableBExc.torusAct τ p a x = x} <
        p ^ τ.rank) :
    GGWeylNoOffender τ p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro A hA hA1
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hA)
  have hne : A.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  have h := hS _ hg (isElemAbelian_map_conj hA g) hne
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fix_map_conj] at h

theorem card_fixAll_le [NeZero p] {A : Subgroup (WeylGroup τ)} {a : WeylGroup τ} (ha : a ∈ A) :
    Nat.card {x : Fin τ.rank → ZMod p // ∀ b ∈ A, TableBExc.torusAct τ p b x = x} ≤
      Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p a x = x} :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2 a ha⟩) fun x y h =>
    Subtype.ext (by simpa using congrArg Subtype.val h)

theorem sLevel_cyclic (hp : p.Prime) {w : WeylGroup τ} (hw : orderOf w = p) {k : ℕ}
    (hfix : Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p w x = x} ≤ p ^ k)
    (hk : k + 1 < τ.rank) :
    ∀ A : Subgroup (WeylGroup τ), A ≤ Subgroup.zpowers w → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, TableBExc.torusAct τ p a x = x} <
        p ^ τ.rank := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro A hAS _ hA1
  have hcardS : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hw]
  have : Finite (Subgroup.zpowers w) :=
    Nat.finite_of_card_ne_zero (by rw [hcardS]; exact hp.ne_zero)
  have hdvd : Nat.card A ∣ p := hcardS ▸ Subgroup.card_dvd_of_le hAS
  have hcardA : Nat.card A = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq A h) hA1
    · exact h
  have hAeq : A = Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge hAS (by rw [hcardA, hcardS])
  have hwA : w ∈ A := hAeq ▸ Subgroup.mem_zpowers w
  calc Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, TableBExc.torusAct τ p a x = x}
      ≤ p * p ^ k := Nat.mul_le_mul hcardA.le ((card_fixAll_le hwA).trans hfix)
    _ = p ^ (k + 1) := by ring
    _ < p ^ τ.rank := Nat.pow_lt_pow_right hp.one_lt hk

theorem prime_eq_of_dvd_smooth (hp : p.Prime) {a b c d : ℕ}
    (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))))
  · exact Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))))

theorem index_eq_of_card {S : Subgroup (WeylGroup τ)} {s w i : ℕ} (hS : Nat.card S = s)
    (hW : Nat.card (WeylGroup τ) = w) (h : s * i = w) (hs : 0 < s) : S.index = i := by
  have h1 := Subgroup.card_mul_index S
  rw [hS, hW, ← h] at h1
  exact Nat.eq_of_mul_eq_mul_left hs h1

end Reduction

section Words

variable (τ : Tag) (p : ℕ)

@[expose] def rootRefl (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  a - (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * a j) • Pi.single i 1

@[expose] def rootWord (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  ω.foldr (rootRefl τ p) a

variable {τ p}

theorem rootRefl_eq_torusAct [NeZero p] (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) :
    rootRefl τ p i a = TableBExc.torusAct τ p (simple τ i) a := by
  rw [TableBExc.torusAct, simple_smul]
  funext k
  simp only [rootRefl, TableBExc.redMod, TableBExc.liftMod, reflect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  rw [ZMod.natCast_zmod_val]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.natCast_zmod_val]
  · by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]

theorem rootWord_eq_torusAct [NeZero p] (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) :
    rootWord τ p ω a = TableBExc.torusAct τ p ((coxeterSystem τ).wordProd ω) a := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, ← ih, ← rootRefl_eq_torusAct]
    rfl

theorem card_fix_torusAct_eq [NeZero p] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (ω : List (Fin τ.rank)) :
    Nat.card {x : Fin τ.rank → ZMod p //
      TableBExc.torusAct τ p ((coxeterSystem τ).wordProd ω) x = x} =
    Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusWord τ p ω x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [TableBExc.torusWord_eq_torusAct hsymm])

end Words

section Orders


theorem card_weyl_E6 : Nat.card (WeylGroup .E6) = 51840 := by
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E6_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

theorem card_weyl_E7 : Nat.card (WeylGroup .E7) = 2903040 := by
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E7_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

theorem card_weyl_E8 : Nat.card (WeylGroup .E8) = 696729600 := by
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E8_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

end Orders

end NoOffExc

end CFSG.StandardType
