module

public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateMinimalOrbit

public section

namespace CFSG

namespace FiveTransitive.FourFixerClosure

open MulAction

theorem card_data
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    {k:ℕ} (hk:IsMultiplyPretransitive G X k) (s t:Set X)
    (hs:s.ncard=k) (ht:t.ncard=k) :
    Nat.card (fixingSubgroup G s)=Nat.card (fixingSubgroup G t) ∧
    Nat.card (fixedPoints (fixingSubgroup G s) X)=Nat.card (fixedPoints (fixingSubgroup G t) X) := by
  obtain ⟨e,he⟩ := BaseSylowConjugacy.exists_embedding_range X k s hs
  obtain ⟨f,hf⟩ := BaseSylowConjugacy.exists_embedding_range X k t ht
  rw [←he,←hf,BaseSylowConjugacy.fixing_range_eq_stabilizer,
    BaseSylowConjugacy.fixing_range_eq_stabilizer]
  obtain ⟨g,hg⟩ := hk.exists_smul_eq e f
  let E:stabilizer G e ≃* stabilizer G f := stabilizerEquivStabilizer hg.symm
  refine ⟨Nat.card_congr E.toEquiv,?_⟩
  have hE:∀(a:stabilizer G e)(x:X),(MulAction.toPerm g) (a • x)=E a • (MulAction.toPerm g x) := by
    intro a x
    change g • (a.val • x)=(g*a.val*g⁻¹) • (g • x)
    simp only [mul_smul,inv_smul_smul]
  exact Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g)
    (ConjugateMinimalOrbit.fixedPoints_equivariant E (MulAction.toPerm g) hE))

theorem fixed_card_sub_three_dvd
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4:IsMultiplyPretransitive G X 4) (f:ℕ)
    (hf:∀s:Set X,s.ncard=4 → Nat.card (fixedPoints (fixingSubgroup G s) X)=f)
    (t:Set X) (ht:t.ncard=3) : f-3∣Nat.card X-3 := by
  classical
  let Y := ↥(tᶜ : Set X)
  let φ:Y→Subgroup G := fun x => fixingSubgroup G (insert x.val t)
  have h4set (x:Y):(insert x.val t).ncard=4 := by
    rw [Set.ncard_insert_of_notMem x.property,ht]
  have hbase (x:Y):t⊆fixedPoints (φ x) X := by
    intro z hz
    exact mem_fixedPoints.mpr fun a => (mem_fixingSubgroup_iff G).mp a.property z (Set.mem_insert_of_mem x.val hz)
  have hfiber (x y:Y):φ y=φ x ↔ y.val∈fixedPoints (φ x) X := by
    constructor
    · intro h
      rw [←h]
      exact mem_fixedPoints.mpr fun a => (mem_fixingSubgroup_iff G).mp a.property y.val (Set.mem_insert y.val t)
    · intro hy
      have hle:φ x≤φ y := by
        intro a ha
        rw [mem_fixingSubgroup_iff]
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl|hz
        · exact mem_fixedPoints.mp hy ⟨a,ha⟩
        · exact (mem_fixingSubgroup_iff G).mp ha z (Set.mem_insert_of_mem x.val hz)
      apply Eq.symm
      apply Subgroup.eq_of_le_of_card_ge hle
      exact (card_data h4 _ _ (h4set x) (h4set y)).1.symm.le
  have hcardFiber (x:Y):Nat.card {y:Y // φ y=φ x}=f-3 := by
    let E:{y:Y // φ y=φ x} ≃ ↥(fixedPoints (φ x) X \ t) := {
      toFun := fun y => ⟨y.val.val,⟨(hfiber x y.val).mp y.property,y.val.property⟩⟩
      invFun := fun z => ⟨⟨z.val,z.property.2⟩,(hfiber x ⟨z.val,z.property.2⟩).mpr z.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr E,Nat.card_coe_set_eq,Set.ncard_sdiff (hbase x),←Nat.card_coe_set_eq,hf _ (h4set x),ht]
  let R := Set.range φ
  let ψ:Y→R := fun y => ⟨φ y,⟨y,rfl⟩⟩
  have hψcard (a:R):Nat.card {y:Y // ψ y=a}=f-3 := by
    obtain ⟨x,hx⟩ := a.property
    let E:{y:Y // ψ y=a} ≃ {y:Y // φ y=φ x} := {
      toFun := fun y => ⟨y.val,(congrArg Subtype.val y.property).trans hx.symm⟩
      invFun := fun y => ⟨y.val,Subtype.ext (y.property.trans hx)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr E).trans (hcardFiber x)
  let _ := Fintype.ofFinite R
  have hsum:Fintype.card Y=∑a:R,Fintype.card {y:Y // ψ y=a} := by
    rw [←Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv ψ)).symm
  have hdiv:f-3∣Nat.card Y := by
    rw [Nat.card_eq_fintype_card,hsum]
    apply Finset.dvd_sum
    intro a _ha
    rw [←Nat.card_eq_fintype_card,hψcard]
  have hY:Nat.card Y=Nat.card X-3 := by
    change Nat.card (tᶜ : Set X)=Nat.card X-3
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht]
  rwa [hY] at hdiv

end FiveTransitive.FourFixerClosure

end CFSG
