module

public import CFSG.Permutation.FiveTransitive.PairSwapEightSubgroup
public import CFSG.Permutation.FiveTransitive.CentralFreeFixedBound
public import CFSG.Permutation.FiveTransitive.KernelImageGeneration
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.OneOrbitOrderFourSemiregular

open MulAction FixedNormalizerAction

private theorem exists_central_eight
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (B K : Subgroup (Normalizer Q)) (hKB : K ≤ B)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (himage : K.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)))
    (hK2 : ∀ k : K, k ^ 2 = 1) (hKcomm : IsMulCommutative K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (ha : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5))
    (hbc : ∀ q : Q, Commute (q : G) ((b.val : G) * (c.val : G)))
    (hbd : ∀ q : Q, Commute (q : G) ((b.val : G) * (d.val : G))) :
    ∃ L : Subgroup (Normalizer Q),
      L = Subgroup.closure ({a.val, b.val * c.val, b.val * d.val} : Set (Normalizer Q)) ∧
      L ≤ K ∧ Nat.card L = 8 ∧ ∀ l : L, ∀ u : B, Commute l.val u.val := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := isMulCommutative_iff.mp hKcomm }
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let fK := f.comp K.subtype
  let L0 := Subgroup.closure ({a, b * c, b * d} : Set K)
  let L := L0.map K.subtype
  have hfa : fK a = 1 := (hker.ge haQ).2
  change fK b = Equiv.swap (e 0) (e 1) at hb
  change fK c = Equiv.swap (e 2) (e 3) at hc
  change fK d = Equiv.swap (e 4) (e 5) at hd
  have hcard0 : Nat.card L0 = 8 := le_antisymm
    (PairSwapEightSubgroup.card_closure_le_eight a (b * c) (b * d) (hK2 a) (hK2 _) (hK2 _))
    (PairSwapEightSubgroup.eight_le_card_closure fK e a (b * c) (b * d) ha hfa
      (by rw [map_mul, hb, hc]) (by rw [map_mul, hb, hd]))
  have hcard : Nat.card L = 8 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hcard0
  have hLeq : L = Subgroup.closure ({a.val, b.val * c.val, b.val * d.val} : Set (Normalizer Q)) := by
    dsimp only [L, L0]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.subtype_apply,
      Subgroup.coe_mul]
  have hLK : L ≤ K := by
    rintro u ⟨k, hk, rfl⟩
    exact k.property
  have hQcomm : ∀ q r : Q, q * r = r * q :=
    isMulCommutative_iff.mp (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hQ))
  have hLI : L ≤ Subgroup.centralizer (Inside Q : Set (Normalizer Q)) := by
    rw [hLeq]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      apply Subtype.ext
      exact congrArg (fun r : Q => (r : G)) (hQcomm ⟨q.val, hq⟩ ⟨a.val.val, haQ⟩)
    · rw [hg]
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      exact Subtype.ext (hbc ⟨q.val, hq⟩).eq
    · rw [hg]
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      exact Subtype.ext (hbd ⟨q.val, hq⟩).eq
  have hBgen : B = Inside Q ⊔ K := by
    apply KernelImageGeneration.eq_of_kernel_image f B (Inside Q ⊔ K)
      (sup_le (hker.ge.trans inf_le_left) hKB)
    · rw [hker]
      exact le_sup_left
    · rw [← himage]
      exact Subgroup.map_mono le_sup_right
  have hcentral (l : L) (u : B) : Commute l.val u.val := by
    have hBcent : B ≤ Subgroup.centralizer ({l.val} : Set (Normalizer Q)) := by
      rw [hBgen]
      apply sup_le
      · intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hLI l.property) q hq)
      · intro k hk
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val
          ((isMulCommutative_iff.mp hKcomm) (⟨k, hk⟩ : K) ⟨l.val, hLK l.property⟩)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hBcent u.property)).symm
  exact ⟨L, hLeq, hLK, hcard, hcentral⟩

theorem semiregular_of_pair_central
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (B K : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B) (hKB : K ≤ B)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (himage : K.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)))
    (hK2 : ∀ k : K, k ^ 2 = 1) (hKcomm : IsMulCommutative K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (ha : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5))
    (hbc : ∀ q : Q, Commute (q : G) ((b.val : G) * (c.val : G)))
    (hbd : ∀ q : Q, Commute (q : G) ((b.val : G) * (d.val : G)))
    (O : Set X)
    (hsemi : ∀ (k : K) (z : X), z ∉ O → (k.val : G) • z = z → k = 1) :
    ∀ (u : B) (z : X), z ∉ O → (u.val : G) • z = z → u = 1 := by
  obtain ⟨L, _, hLK, hLcard, hcentral⟩ := exists_central_eight
    Q hQ B K hKB hker himage hK2 hKcomm a b c d haQ ha e hb hc hd hbc hbd
  have hbound (u : B) (hu : u ≠ 1) : (fixedBy X u.val).ncard ≤ 7 := by
    apply TwoGroupCosetFixedBound.fixed_le 7 ?_ B hB u hu
    intro t ht
    exact hmax t.val ((orderOf_injective (Normalizer Q).subtype Subtype.val_injective t).trans ht)
  apply CentralFreeFixedBound.semiregular B L O 7 (by omega) hbound hcentral
  intro l z hz hfix
  have hk := hsemi ⟨l.val, hLK l.property⟩ z hz hfix
  exact Subtype.ext (congrArg (fun k : K => k.val) hk)

end FiveTransitive.OneOrbitOrderFourSemiregular

end CFSG
