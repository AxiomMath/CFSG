module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGExcPlusWeylModel (τ : Tag) (p : ℕ) {L' : Type} [Group L']
    (A : Subgroup (MulAut L')) : Prop :=
  ∃ (Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p)) (w : Fin τ.rank → L'),
    (∀ i, GGTorusWeylElt p A (w i)) ∧
    (∀ i (a b : A), (b : MulAut L') = MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ →
      Multiplicative.toAdd (Φ b) =
        TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a))) ∧
    ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup τ, ∀ a b : A,
        (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
          Multiplicative.toAdd (Φ b) = TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a))

@[expose] def GGExcPlusWeylModelSCr (τ : Tag) (p r : ℕ) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → GGExcPlusWeylModel τ p A

theorem torusAct_simple_involutive (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) (TableBExc.torusAct τ p (simple τ i) x) = x := by
  rw [← TableBExc.torusAct_mul, (coxeterSystem τ).simple_mul_simple_self, TableBExc.torusAct_one]

theorem ggExcPlus_torusAct_simple_eq (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) x =
      x - (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j) • Pi.single i 1 := by
  funext k
  simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_zmod_val, ZMod.cast_id', id_eq]
  congr 2
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

private theorem torusAct_simple_eq_self_iff (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) x = x ↔
      ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j = 0 := by
  rw [ggExcPlus_torusAct_simple_eq]
  constructor
  · intro h
    have h' := congrFun h i
    simpa using h'
  · intro h
    rw [h, zero_smul, sub_zero]

theorem card_fix_torusAct_simple (τ : Tag) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (i : Fin τ.rank) :
    Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} * p =
      p ^ τ.rank := by
  classical
  let f : (Fin τ.rank → ZMod p) →+ ZMod p :=
    { toFun := fun x => ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hsurj : Function.Surjective f := by
    intro t
    refine ⟨(t * (2 : ZMod p)⁻¹) • Pi.single i 1, ?_⟩
    change ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * ((t * (2 : ZMod p)⁻¹) • Pi.single i 1 :
      Fin τ.rank → ZMod p) j = t
    rw [Finset.sum_eq_single i]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Tag.cartan_self]
      push_cast
      rw [show (2 : ZMod p) * (t * 2⁻¹) = t * (2 * 2⁻¹) by ring, mul_inv_cancel₀ h2, mul_one]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  have hfix : Nat.card {x : Fin τ.rank → ZMod p //
      TableBExc.torusAct τ p (simple τ i) x = x} = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [torusAct_simple_eq_self_iff, AddMonoidHom.mem_ker]
      rfl)
  have hidx : f.ker.index = p := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
      Nat.card_zmod]
  rw [hfix]
  calc Nat.card f.ker * p = Nat.card f.ker * f.ker.index := by rw [hidx]
    _ = Nat.card (Fin τ.rank → ZMod p) := AddSubgroup.card_mul_index f.ker
    _ = p ^ τ.rank := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem conj_mul_conj_inv {L' : Type} [Group L'] (w : L') (a : MulAut L') :
    MulAut.conj w * a * (MulAut.conj w)⁻¹ = MulAut.conj (w * (a w)⁻¹) * a := by
  refine MulEquiv.ext fun x => ?_
  change w * a (w⁻¹ * x * w) * w⁻¹ = w * (a w)⁻¹ * a x * (w * (a w)⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem conj_mem_normalizer_of_torusWeylElt {p : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A) {w : L'}
    (hw : GGTorusWeylElt p A w) : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  rw [conj_mul_conj_inv]
  obtain ⟨hcp, hcfix⟩ := hw a ha
  exact A.mul_mem (hsc _ hcfix hcp) ha

theorem ggTorusReflGenW_of_excPlusModel {τ : Tag} {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] {I : Set (MulAut R)} (h : GGExcPlusWeylModelSCr τ p r R I) :
    GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hsc : GGTorusSelfCent p A := hA.2.2.2.2.2.2.2
  obtain ⟨Φ, w, hw, hact, hnorm⟩ := h L' ψ A hA
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) :=
    fun i a => hact i a (ρ i a) (ggConjAut_apply A (hN i) a)
  have hρsq : ∀ i, ρ i ^ 2 = 1 := fun i => by
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [pow_two, MulAut.mul_apply, hρ, hρ, torusAct_simple_involutive, MulAut.one_apply]
  have hρfix : ∀ i, Nat.card {a : A // ρ i a = a} * p = Nat.card A := fun i => by
    have hcardA : Nat.card A = p ^ τ.rank := by
      rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hcardFix : Nat.card {a : A // ρ i a = a} = Nat.card
        {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Φ.toEquiv.trans Multiplicative.toAdd) ?_)
      intro a
      change ρ i a = a ↔ TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) =
        Multiplicative.toAdd (Φ a)
      rw [← hρ]
      constructor
      · intro hh
        rw [hh]
      · intro hh
        exact Φ.injective (Multiplicative.toAdd.injective hh)
    rw [hcardFix, card_fix_torusAct_simple τ hp2 i, hcardA]
  have hρmem : ∀ i, ρ i ∈ ggTorusReflSet p A := fun i =>
    ⟨w i, hN i, hw i, rfl, hρsq i, hρfix i⟩
  have hreal : ∀ u : WeylGroup τ, ∃ φ ∈ Subgroup.closure (ggTorusReflSet p A),
      ∀ a : A, Multiplicative.toAdd (Φ (φ a)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a)) := by
    intro u
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil =>
      refine ⟨1, Subgroup.one_mem _, fun a => ?_⟩
      rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
      rfl
    | cons i ω ih =>
      obtain ⟨φ, hφ, hφact⟩ := ih
      refine ⟨ρ i * φ, Subgroup.mul_mem _ (Subgroup.subset_closure (hρmem i)) hφ, fun a => ?_⟩
      rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, MulAut.mul_apply, hρ, hφact]
  refine (Subgroup.closure_le _).mpr ?_
  rintro φ ⟨g, hgH, hgN, hφ⟩
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hgH
  obtain ⟨u, hu⟩ := hnorm m hgN
  obtain ⟨φu, hφu, hact'⟩ := hreal u
  have hφeq : φ = φu := by
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [hact' a]
    exact hu a (φ a) (hφ a)
  rw [hφeq]
  exact hφu


end CFSG.StandardType

end
