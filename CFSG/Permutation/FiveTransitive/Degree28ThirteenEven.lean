module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree28ThirteenEven

open MulAction GenericSylowFixedAction

theorem normalizer_even
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    [IsPretransitive G X] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hfixed : Nat.card (fixedPoints S X) = 2) :
    2 ∣ Nat.card (Subgroup.normalizer (S : Set G)) := by
  classical
  have hnonempty : Nonempty (fixedPoints S X) := (Nat.card_pos_iff.mp (show 0 < Nat.card (fixedPoints S X) by omega)).1
  obtain ⟨x⟩ := hnonempty
  let s : Set X := {x.val}
  have hs : s.ncard = 1 := Set.ncard_singleton _
  have hle : (S : Subgroup G) ≤ fixingSubgroup G s := by
    intro z hz
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hyx : y = x.val := hy
    rw [hyx]
    exact mem_fixedPoints.mp x.property ⟨z,hz⟩
  let T : Sylow p (fixingSubgroup G s) := S.subtype hle
  have himage : sylowImage G X s T = (S : Subgroup G) := by
    ext z
    change z ∈ ((S : Subgroup G).subgroupOf (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype ↔ z ∈ S
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z,hle hz⟩,hz,rfl⟩
  let N := sylowNormalizer G X s T
  let F := sylowFixedPoints G X s T
  have hF : F = fixedPoints S X := by
    apply Set.ext
    intro y
    constructor
    · intro hy
      rw [mem_fixedPoints] at hy ⊢
      intro z
      let zN : N := ⟨z.val, by
        change z.val ∈ Subgroup.normalizer (sylowImage G X s T : Set G)
        apply (sylowImage G X s T).le_normalizer
        rw [himage]
        exact z.property⟩
      exact hy ⟨zN, by change z.val ∈ sylowImage G X s T; rw [himage]; exact z.property⟩
    · intro hy
      rw [mem_fixedPoints] at hy ⊢
      intro z
      exact hy ⟨z.val.val, by
        have hz := z.property
        change z.val.val ∈ sylowImage G X s T at hz
        rwa [himage] at hz⟩
  have hFcard : Nat.card F = 2 := by rw [hF]; exact hfixed
  have htrans := sylowNormalizer_transitive_on_fixedPoints G X 1
    (fun a b _ _ => by
      obtain ⟨g,hg⟩ := exists_smul_eq G (a 0) (b 0)
      exact ⟨g,fun i => by have hi : i = 0 := Subsingleton.elim _ _; simpa [hi] using hg⟩)
    s hs T
  let _ : IsPretransitive N F := ⟨fun a b => by
    obtain ⟨g,hg⟩ := htrans (fun _ => a) (fun _ => b)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
    exact ⟨g,hg 0⟩⟩
  have hxF : x.val ∈ F := by rw [hF]; exact x.property
  have hd := (stabilizer N (⟨x.val,hxF⟩ : F)).index_dvd_card
  rw [index_stabilizer_of_transitive, hFcard] at hd
  change 2 ∣ Nat.card (Subgroup.normalizer (sylowImage G X s T : Set G)) at hd
  rwa [himage] at hd

end FiveTransitive.Degree28ThirteenEven

end CFSG
