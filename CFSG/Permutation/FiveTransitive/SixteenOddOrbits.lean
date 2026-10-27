module

public import CFSG.Permutation.FiveTransitive.SixteenExtensionLocalization
public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount

public section

namespace CFSG

namespace FiveTransitive.SixteenOddOrbits

open MulAction Equiv FreeComplementOrbitCount

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]

variable (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
  (hinv : ∀ u : G, orderOf u = 2 →
    Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
  (S : Subgroup G) (hcomm : ∀ s t : S, s * t = t * s) (h2 : ∀ s : S, s * s = 1)
  (hcard : Nat.card S = 16) (hF : (fixedPoints S X).ncard = 6)
  (b : G) (hb : b ∈ Subgroup.normalizer (S : Set G)) (hbOrder : orderOf b = 2)
  (hfree : ∀ (s : S) (x : X), x ∉ fixedPoints S X → s • x = x → s = 1)
  (hsix : (fixedBy X b).ncard = 6)
  (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2)

include hlocal hinv hcomm h2 hcard hF hb hbOrder hfree hsix htwo

private theorem exists_free_complement_and_odd_orbits :
    ∃ x : X, b • x = x ∧ x ∉ fixedPoints S X ∧
      Nat.card (S ⊔ Subgroup.zpowers b : Subgroup G) = 32 ∧
      (orbit S x).ncard = 16 ∧
      (∀ (q : G), q ∈ S ⊔ Subgroup.zpowers b → ∀ y : X,
        y ∉ fixedPoints S X ∪ orbit S x → q • y = y → q = 1) ∧
      32 ∣ (Nat.card X - 22) ∧
      Odd (Nat.card (orbitRel.Quotient S (fixedComplement (X := X) S))) := by
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X b) (fixedPoints S X)
  obtain ⟨x,hbx,hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0 < (fixedBy X b \ fixedPoints S X).ncard by omega)
  let Q : Subgroup G := S ⊔ Subgroup.zpowers b
  have hQcard : Nat.card Q = 32 := by
    rw [InvolutiveNormalizerExtension.card_sup S b hb hbOrder
      (SixteenExtensionLocalization.not_mem_common_fixer S hF b htwo), hcard]
  have horbit : (orbit S x).ncard = 16 := by
    rw [SixteenOrbitLocalization.orbit_card_of_free S x (fun s => hfree s x hx), hcard]
  have hfreeQ : ∀ (q : G), q ∈ Q → ∀ y : X,
      y ∉ fixedPoints S X ∪ orbit S x → q • y = y → q = 1 := by
    intro q hq y hy hqy
    by_contra hq1
    exact hy (SixteenExtensionLocalization.fixed_subset_union hlocal hinv S hcomm h2 hcard hF
      b hb hbOrder hfree hsix htwo x hbx hx q hq hq1 hqy)
  have heorbit : orbit Q x = orbit S x :=
    SixteenExtensionLocalization.extension_orbit_eq S b hb hbOrder x hbx
  have hQN : Q ≤ Subgroup.normalizer (S : Set G) :=
    sup_le S.le_normalizer (Subgroup.zpowers_le_of_mem hb)
  let D := fixedPoints S X ∪ orbit Q x
  have hDstable : ∀ (q : Q) (y : X), y ∈ D → q • y ∈ D := by
    intro q y hy
    rcases hy with hy | hy
    · exact Or.inl (FixedSetNormalizerPerm.smul_mem_fixedPoints G X S q.val
        (hQN q.property) hy)
    · exact Or.inr (mem_orbit_of_mem_orbit q hy)
  have hdis : Disjoint (fixedPoints S X) (orbit S x) := by
    rw [Set.disjoint_left]
    intro y hyF hyO
    exact SemiregularNormalizerBound.orbit_not_fixed S X x hx hyO hyF
  have hDcard : D.ncard = 22 := by
    change (fixedPoints S X ∪ orbit Q x).ncard = 22
    rw [heorbit,Set.ncard_union_eq hdis,hF,horbit]
  have hn : 22 ≤ Nat.card X := by
    have h := Set.ncard_le_ncard (Set.subset_univ D)
    rw [hDcard,Set.ncard_univ] at h
    exact h
  let R := complement Q D hDstable
  have hRfree : ∀ (q : Q) (y : R), q • y = y → q = 1 := by
    intro q y hqy
    apply Subtype.ext
    apply hfreeQ q.val q.property y.val
    · have hyD : y.val ∉ D := y.property
      simpa only [D,heorbit] using hyD
    · exact congrArg (fun z : R => z.val) hqy
  have hR := card_eq_mul_orbits hRfree
  have hRcard : Nat.card R = Nat.card X - 22 := by
    rw [card_complement,hDcard]
  have hd : 32 ∣ (Nat.card X - 22) := by
    rw [← hRcard,hR,hQcard]
    exact dvd_mul_right 32 _
  have hSfree : ∀ (s : S) (y : fixedComplement (X := X) S), s • y = y → s = 1 := by
    intro s y hy
    exact hfree s y.val y.property (congrArg (fun z : fixedComplement (X := X) S => z.val) hy)
  have hS := card_eq_mul_orbits hSfree
  rw [card_fixedComplement,hF,hcard] at hS
  have hodd : Odd (Nat.card (orbitRel.Quotient S (fixedComplement (X := X) S))) := by
    obtain ⟨m,hm⟩ := hd
    exact ⟨m,by omega⟩
  exact ⟨x,hbx,hx,hQcard,horbit,hfreeQ,hd,hodd⟩

theorem degree_and_odd_orbits :
    32 ∣ (Nat.card X - 22) ∧
      Odd (Nat.card (orbitRel.Quotient S (fixedComplement (X := X) S))) := by
  obtain ⟨x,hbx,hx,hQ,ho,hfreeQ,hd,hodd⟩ := exists_free_complement_and_odd_orbits
    hlocal hinv S hcomm h2 hcard hF b hb hbOrder hfree hsix htwo
  exact ⟨hd,hodd⟩

end FiveTransitive.SixteenOddOrbits

end CFSG
