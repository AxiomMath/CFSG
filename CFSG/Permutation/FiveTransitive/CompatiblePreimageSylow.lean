module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.CompatiblePreimageSylow

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

theorem kernel_eq
    (f : G →* H) (Q B : Subgroup G) (hQker : Q ≤ f.ker)
    (hmax : ∀ L : Subgroup G, L ≤ f.ker → IsPGroup p L → L ≤ Q)
    (hQB : Q ≤ B) (hB : IsPGroup p B) :
    B ⊓ f.ker = Q ∧ (f.comp B.subtype).ker = Q.subgroupOf B := by
  have he : B ⊓ f.ker = Q := le_antisymm
    (hmax (B ⊓ f.ker) inf_le_right hB.to_inf_left) (le_inf hQB hQker)
  refine ⟨he, ?_⟩
  ext b
  change f b.val = 1 ↔ b.val ∈ Q
  constructor
  · intro hb
    exact he.le ⟨b.property, hb⟩
  · intro hb
    exact hQker hb

private theorem exists_containing [Finite G] [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hQker : Q ≤ f.ker)
    (hmax : ∀ L : Subgroup G, L ≤ f.ker → IsPGroup p L → L ≤ Q)
    (V : Subgroup H) (hV : IsPGroup p V)
    (J : Subgroup G) (hJ : IsPGroup p J) (hQJ : Q ≤ J) (hJV : J ≤ V.comap f) :
    ∃ P : Sylow p (V.comap f),
      let B := SylowPreimageNormalizer.ambient f V P
      J ≤ B ∧ B.map f = V ∧ B ⊓ f.ker = Q ∧
      (f.comp B.subtype).ker = Q.subgroupOf B ∧
      (Subgroup.normalizer (B : Set G)).map f = Subgroup.normalizer (V : Set H) := by
  have hJp : IsPGroup p (J.subgroupOf (V.comap f)) := hJ.of_injective
    (Subgroup.subgroupOfEquivOfLe hJV).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hJV).injective
  obtain ⟨P, hJP⟩ := hJp.exists_le_sylow
  let B := SylowPreimageNormalizer.ambient f V P
  have hJB : J ≤ B := by
    intro j hj
    exact ⟨⟨j, hJV hj⟩, hJP hj, rfl⟩
  have hBp : IsPGroup p B := P.isPGroup'.map (V.comap f).subtype
  have hk := kernel_eq f Q B hQker hmax (hQJ.trans hJB) hBp
  exact ⟨P, hJB, SylowPreimageNormalizer.ambient_map f hf V hV P,
    hk.1, hk.2, SylowPreimageNormalizer.normalizer_map f hf V hV P⟩

theorem exists_with_element [Finite G] [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hQker : Q ≤ f.ker)
    (hmax : ∀ L : Subgroup G, L ≤ f.ker → IsPGroup p L → L ≤ Q)
    (V : Subgroup H) (hV : IsPGroup p V)
    (A : Subgroup G) (hA : IsPGroup p A) (hQA : Q ≤ A)
    (x : G) (hxA : x ∈ A) (hxV : f x ∈ V) :
    ∃ P : Sylow p (V.comap f),
      let B := SylowPreimageNormalizer.ambient f V P
      Q ≤ B ∧ x ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Q ∧
      (f.comp B.subtype).ker = Q.subgroupOf B ∧
      (Subgroup.normalizer (B : Set G)).map f = Subgroup.normalizer (V : Set H) := by
  let J := (Q ⊔ Subgroup.zpowers x : Subgroup G)
  have hJA : J ≤ A := sup_le hQA (Subgroup.zpowers_le.mpr hxA)
  have hJV : J ≤ V.comap f := by
    apply sup_le
    · intro q hq
      change f q ∈ V
      rw [MonoidHom.mem_ker.mp (hQker hq)]
      exact V.one_mem
    · exact Subgroup.zpowers_le.mpr hxV
  obtain ⟨P, hJP, hm, hk, hkr, hn⟩ := exists_containing f hf Q hQker hmax V hV
    J (hA.to_le hJA) le_sup_left hJV
  exact ⟨P, (show Q ≤ J from le_sup_left).trans hJP,
    hJP ((show Subgroup.zpowers x ≤ J from le_sup_right) (Subgroup.mem_zpowers x)),
    hm, hk, hkr, hn⟩

end FiveTransitive.CompatiblePreimageSylow

end CFSG
