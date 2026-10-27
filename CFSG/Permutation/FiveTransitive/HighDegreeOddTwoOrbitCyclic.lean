module

public import CFSG.Permutation.FiveTransitive.HighDegreeOddEvenSocleMaxSeven
public import CFSG.Permutation.FiveTransitive.NormalizerTwoOrbitExclusion
public import CFSG.Permutation.FiveTransitive.NormalizerOneOrbitExclusion
public import CFSG.Permutation.FiveTransitive.NormalizerZeroOrbitFullCentralizer
public import CFSG.Permutation.FiveTransitive.GlobalMaximalPointFixer
public import CFSG.Permutation.FiveTransitive.CyclicFullCentralizerCardBound
public import CFSG.Permutation.FiveTransitive.FixedNormalizerSwapLift
public import CFSG.Permutation.FiveTransitive.CyclicFourActualExclusion
public import CFSG.Permutation.FiveTransitive.TwoGroupSmallCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.HighDegreeOddTwoOrbitCyclic

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X))
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ G ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ FaithfulSMul H X ∧
      IsMultiplyPretransitive H X 5 ∧ ¬ alternatingGroup X ≤ H ∧
      (∀ h : H, Equiv.Perm.sign h.val = 1) ∧
      ∀ (a : Fin 5 ↪ X) (P : Sylow 2 (stabilizer H a)),
    ∃ (x : X) (Q : Subgroup H),
      x ∉ Set.range a ∧
      Q = (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype ∧
      (∀ y : X, y ∉ Set.range a →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
      Q < ambientSylow a P ∧ IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      Nat.card (fixedPoints Q X) = 7 ∧ Nat.card (Fixed (X := X) Q) = 7 ∧
      Nat.card (Fixed (X := X) Q) < Nat.card X ∧
      Nat.card (Fixed (X := X) Q) ≤ Fintype.card X / 2 ∧
      Image (X := X) Q = ⊤ ∧ Nat.card (Image (X := X) Q) = 5040 ∧
      (∃ T : Sylow 2 (fixingSubgroup H (insert x (Set.range a))),
        (T : Subgroup (fixingSubgroup H (insert x (Set.range a)))).map
          (fixingSubgroup H (insert x (Set.range a))).subtype = Q) ∧
      (∃ S : Sylow 2 (fixingSubgroup H (fixedPoints Q X)),
        (S : Subgroup (fixingSubgroup H (fixedPoints Q X))).map
          (fixingSubgroup H (fixedPoints Q X)).subtype = Q) ∧
      (∀ t : H, t ∈ Q → orderOf t = 2 → fixedBy X t = fixedPoints Q X) ∧
      (∃ t : H, t ∈ Q ∧ orderOf t = 2 ∧ fixedBy X t = fixedPoints Q X ∧
        (fixedBy X t).ncard = 7 ∧
        ∀ u : H, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) ∧
      Fintype.card X % 4 = 3 ∧ 4 ∣ (Fintype.card X - 7) ∧
      (∀ q : H, q ∈ Q → q ≠ 1 → ∀ z : X, z ∉ fixedPoints Q X → q • z ≠ z) ∧
      (∀ U : Subgroup H, IsPGroup 2 U → 6 ≤ Nat.card (fixedPoints U X) →
        Nat.card U ≤ Nat.card Q) ∧
      IsCyclic Q ∧ Nat.card Q = 2 ∧
      ((Subgroup.centralizer (Q : Set H)).subgroupOf (Normalizer Q)).map
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤ ∧
      ∀ (A : Subgroup H), Q ≤ A → IsPGroup 2 A →
      ∀ (u : Normalizer Q), u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0 ∧
      IsCyclic Q ∧ (∀ q : Q, Commute u.val q.val) ∧
      ((Subgroup.centralizer (Q : Set H)).subgroupOf (Normalizer Q)).map
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤ ∧ Nat.card Q ≤ 4 := by
  classical
  obtain ⟨H, hHG, hsimple, hnoncomm, hfaithful, hH5, hHnotAlt, heven, hentrance⟩ :=
    HighDegreeOddEvenSocleMaxSeven.exists_entrance X G hcard h5 hnotAlt hodd hmax
  have hmaxH : ∀ t : H, orderOf t = 2 → (fixedBy X t).ncard ≤ 7 := by
    intro t ht
    exact hmax (Subgroup.inclusion hHG t)
      ((orderOf_injective (Subgroup.inclusion hHG) (Subgroup.inclusion_injective hHG) t).trans ht)
  refine ⟨H, hHG, hsimple, hnoncomm, hfaithful, hH5, hHnotAlt, heven, ?_⟩
  intro a P
  obtain ⟨x, Q, hx, hQ, hmin, hQA, hQp, hne, h7, h7', hlt, hhalf,
    htop, horder, hT, hS, hall, ht, hnmod, hdiv, hsemi⟩ := hentrance a P
  have hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1 := by
    intro q z hz hqz
    apply Subtype.ext
    by_contra hq
    exact hsemi q.val q.property hq z hz hqz
  obtain ⟨S, hS'⟩ := hS
  have htrans :
    ∀ (A : Subgroup H), Q ≤ A → IsPGroup 2 A →
    ∀ (u : Normalizer Q), u.val ∈ A → u.val ∉ Q →
    (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
    Nat.card (Function.fixedPoints
    (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0 ∧
    IsCyclic Q ∧ (∀ q : Q, Commute u.val q.val) ∧
    ((Subgroup.centralizer (Q : Set H)).subgroupOf (Normalizer Q)).map
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤ ∧ Nat.card Q ≤ 4 := by
    intro A hQleA hA u huA huQ hlocal
    have hle := NormalizerSevenOrbitCount.fixed_orbits_le_two hmaxH Q A hQleA hA
      hfree u huA huQ hlocal
    have hneTwo := NormalizerTwoOrbitExclusion.not_two_fixed_orbits
      hcard hH5 heven hnmod hmaxH Q A hQleA hA hQp hne h7 hfree
      S hS' htop u huA huQ hlocal
    have hneOne := NormalizerOneOrbitExclusion.not_one_fixed_orbit hcard hH5
      (fun g => by
        convert heven g using 1
        congr 2
        exact Subsingleton.elim _ _) hnmod hmaxH Q A hQleA hA hQp hne h7 hfree
        S hS' htop u huA huQ hlocal
    have hzero : Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0 := by omega
    let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
    obtain ⟨hcyclic, hcentral⟩ := NormalizerZeroOrbitCyclic.cyclic_and_commute
      Q S hS' A hQleA hA h7 hfree u huA hlocal (heven u.val) hzero
    have hfull := NormalizerZeroOrbitFullCentralizer.image_eq_top
      Q S hS' A hQleA hA h7 htop hfree u huA hlocal (heven u.val) hzero
    refine ⟨hzero, hcyclic, hcentral, hfull, ?_⟩
    exact CyclicFullCentralizerCardBound.card_le_four Q hcyclic S hS' h7' hfull
      (fun g => by
        convert heven g using 1
        congr 2
        exact Subsingleton.elim _ _) hmaxH hfree
  obtain ⟨A, u, hQleA, hA, huA, huQ, hlocal⟩ :=
    FixedNormalizerSwapLift.exists_lift Q h7' S hS' htop
  have hsmall := htrans A hQleA hA u huA huQ hlocal
  let _ : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hQtwo : Nat.card Q = 2 := by
    rcases TwoGroupSmallCard.two_or_four hQp hsmall.2.2.2.2 with htwo | hfour
    · exact htwo
    · exact False.elim (CyclicFourActualExclusion.false_of_card_four hcard hH5 hmaxH
        (fun g => by
          convert heven g using 1
          congr 2
          exact Subsingleton.elim _ _) Q hsmall.2.1 hfour h7 hfree S hS'
        hsmall.2.2.2.1 (fun A hQA hA u huA huQ hu => (htrans A hQA hA u huA huQ hu).1))
  refine ⟨x, Q, hx, hQ, hmin, hQA, hQp, hne, h7, h7', hlt, hhalf,
    htop, horder, hT, ⟨S, hS'⟩, hall, ht, hnmod, hdiv, hsemi, ?_,
    hsmall.2.1, hQtwo, hsmall.2.2.2.1, htrans⟩
  intro U hU hfixU
  have hfixed := (OddOriginalTupleEntrance.entrance X H hcard hH5 hHnotAlt hodd a P).2
  rw [hQ]
  exact GlobalMaximalPointFixer.order_bound hH5 a P hfixed x hx hmin U hU hfixU

end FiveTransitive.HighDegreeOddTwoOrbitCyclic

end CFSG
