module

public import CFSG.Permutation.FiveTransitive.OyamaSixNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.SemiregularFixedDegree
public import CFSG.Permutation.FiveTransitive.SixteenOddOrbits

public section

namespace CFSG

namespace FiveTransitive.OyamaSixOddOrbits

open MulAction Equiv FreeComplementOrbitCount

theorem degree_and_odd_orbits
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    22 ≤ Nat.card X ∧ 32 ∣ (Nat.card X - 22) ∧
      Odd (Nat.card (orbitRel.Quotient S
        (fixedComplement (X := X) (S : Subgroup (fixingSubgroup G s))))) := by
  classical
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  let _ : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hn : 22 ≤ Nat.card X := by
    have ht := SemiregularFixedDegree.card_add_fixed_le H X (S : Subgroup H) hfree
    rw [hS,hcard] at ht
    exact ht
  have hfixed : fixedPoints Q X = fixedPoints S X := OyamaSixElementary.fixedPoints_image G X H S
  have hcardQ : (fixedPoints Q X).ncard = 6 := by rw [hfixed,hcard]
  obtain ⟨hsq,hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage
  let e : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨hQsq,hQcomm⟩ := EquivariantSemiregular.square_and_commute_of_equiv S Q e hsq hcomm
  have hQcard : Nat.card Q = 16 := (Nat.card_congr e.toEquiv).symm.trans hS
  have hfreeQ := EquivariantSemiregular.free_of_equivariant S Q X X e (Equiv.refl X)
    (fun _ _ => rfl) hfree
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hcardQ heven
  have hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6 := by
    intro u hu
    have ht := OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree hcard himage u hu
    have heq : Nat.card (Function.fixedPoints (toPerm u : Perm X)) = (fixedBy X u).ncard := by
      rw [Nat.card_coe_set_eq]
      rfl
    rw [heq]
    omega
  obtain ⟨a,ha⟩ := exists_ne (1 : S)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by simpa only [pow_two] using hsq a) ha
  let aG : G := ((a : H) : G)
  have haG : orderOf aG = 2 := (Subgroup.orderOf_coe (a : H)).trans ((Subgroup.orderOf_coe a).trans ha2)
  have hafix : (fixedBy X aG).ncard = 6 := by
    change (fixedBy X a).ncard = 6
    rw [SemiregularSylowFixedSet.fixedBy_eq_fixedPoints S X hfree a ha,hcard]
  have hamoved : 4 ≤ (fixedBy X aG)ᶜ.ncard := by
    rw [Set.ncard_compl,hafix]
    omega
  obtain ⟨b,hb,hb2,hbne,hbfix,hbtwo⟩ := OyamaSixNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hcardQ heven aG haG hamoved
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hbne
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change b • x.val = x.val
    rw [hb1,one_smul]
  have hbOrder : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hsix : (fixedBy X b).ncard = 6 := hbfix.trans hafix
  have hd := (SixteenOddOrbits.degree_and_odd_orbits hlocal hinv Q hQcomm hQsq hQcard hcardQ
    b hb hbOrder hfreeQ hsix hbtwo).1
  have hSfree : ∀ (q : S) (y : fixedComplement (X := X) (S : Subgroup H)), q • y = y → q = 1 := by
    intro q y hy
    exact hfree q y.val y.property (congrArg Subtype.val hy)
  have hc := card_eq_mul_orbits hSfree
  rw [card_fixedComplement,hcard] at hc
  change Nat.card X - 6 = Nat.card (S : Subgroup H) *
    Nat.card (orbitRel.Quotient (S : Subgroup H) (fixedComplement (X := X) (S : Subgroup H))) at hc
  rw [hS] at hc
  refine ⟨hn,hd,?_⟩
  obtain ⟨m,hm⟩ := hd
  exact ⟨m,by omega⟩

end FiveTransitive.OyamaSixOddOrbits

end CFSG
