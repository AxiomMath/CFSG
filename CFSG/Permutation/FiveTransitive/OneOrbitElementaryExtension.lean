module

public import CFSG.Permutation.FiveTransitive.OneOrbitThreeSwapLifts
public import CFSG.Permutation.FiveTransitive.CardTwoFixedCentralizer
public import CFSG.Permutation.FiveTransitive.ElementaryStabilizerExtension

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.OneOrbitElementaryExtension

open MulAction FixedNormalizerAction

theorem exists_extension
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (e : Fin 6 ↪ Fixed (X := X) Q)
    (B : Subgroup (Normalizer Q))
    (hmap : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : B)
    (hxf : toPermHom (Normalizer Q) (Fixed (X := X) Q) x.val = Equiv.swap (e 0) (e 1))
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) ≤ 1)
    (z : NormalizerFixedComplement.Domain (X := X) Q) (hz : x.val • z = z)
    (hC : Nat.card ((Subgroup.centralizer ({x.val.val} : Set G)).subgroupOf Q) = 2) :
    ∃ (a : Inside Q) (K : Subgroup (Normalizer Q)),
      orderOf a.val.val = 2 ∧ Commute a.val.val x.val.val ∧
      K = Subgroup.closure (insert a.val ((stabilizer B z).map B.subtype : Set (Normalizer Q))) ∧
      K ≤ B ∧ a.val ∈ K ∧ x.val ∈ K ∧ (stabilizer B z).map B.subtype ≤ K ∧
      IsPGroup 2 K ∧ (∀ k : K, k ^ 2 = 1) ∧ IsMulCommutative K ∧ 8 ∣ Nat.card K ∧
      K.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e ∧
      (∀ (k : K) (t : X), t ∈ orbit Q z.val → (k.val : G) • t ∈ orbit Q z.val) ∧
      ∃ y w : K,
        toPermHom (Normalizer Q) (Fixed (X := X) Q) y.val = Equiv.swap (e 2) (e 3) ∧
        toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val = Equiv.swap (e 4) (e 5) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let D := stabilizer B z
  let C := (Subgroup.centralizer ({x.val.val} : Set G)).subgroupOf Q
  obtain ⟨y, w, hyf, hwf, hD2, hDcomm, hDdiv⟩ :=
    OneOrbitThreeSwapLifts.exists_lifts Q e B hmap hker hfree x hone z hz
  obtain ⟨aC, haCorder⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hC])
  let a : Inside Q := ⟨⟨aC.val.val, Q.le_normalizer aC.val.property⟩, aC.val.property⟩
  have haorder : orderOf a.val.val = 2 :=
    (orderOf_injective Q.subtype Subtype.val_injective aC.val).trans
      ((orderOf_injective C.subtype Subtype.val_injective aC).trans haCorder)
  have hax : Commute a.val.val x.val.val := Subgroup.mem_centralizer_singleton_iff.mp aC.property
  have haB : a.val ∈ B := (hker.ge a.property).1
  have ha2 : a.val ^ 2 = 1 := Subtype.ext (haorder ▸ pow_orderOf_eq_one a.val.val)
  have hxD : x ∈ D := hz
  let xD : D := ⟨x, hxD⟩
  have hac (d : D) : Commute a.val d.val.val := by
    have hdx : Commute d.val.val.val x.val.val :=
      congrArg (fun t : D => t.val.val.val) ((isMulCommutative_iff.mp hDcomm) d xD)
    exact Subtype.ext (CardTwoFixedCentralizer.commute Q x.val.val hC aC d.val.val hdx).eq
  obtain ⟨K, hKdef, hKB, haK, hDK, hKp, hK2, hKcomm, hKdiv⟩ :=
    ElementaryStabilizerExtension.exists_extension B D a.val haB ha2 hac hD2 hDcomm hDdiv
  have hxK : x.val ∈ K := hDK ⟨x, hxD, rfl⟩
  let yK : K := ⟨y.val.val, hDK ⟨y.val, y.property, rfl⟩⟩
  let wK : K := ⟨w.val.val, hDK ⟨w.val, w.property, rfl⟩⟩
  have hKmap : K.map f = V := by
    apply le_antisymm ((Subgroup.map_mono hKB).trans hmap.le)
    apply (Subgroup.closure_le (K.map f)).mpr
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨x.val, hxK, hxf⟩
    · exact ⟨yK.val, yK.property, hyf⟩
    · exact ⟨wK.val, wK.property, hwf⟩
  have hVsq := (ThreeSwapTwoGroup.isTwoGroup e).2
  have hVinv (v : V) : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using hVsq v)
  have hVcomm (v w : V) : Commute v w := by
    calc
      v * w = (v * w)⁻¹ := (hVinv (v * w)).symm
      _ = w⁻¹ * v⁻¹ := mul_inv_rev _ _
      _ = w * v := by rw [hVinv, hVinv]
  have hcomm (b c : B) : Commute (f b.val) (f c.val) :=
    congrArg Subtype.val (hVcomm
      ⟨f b.val, hmap.le ⟨b.val, b.property, rfl⟩⟩
      ⟨f c.val, hmap.le ⟨c.val, c.property, rfl⟩⟩).eq
  have hBz (b : B) : (b.val : G) • z.val ∈ orbit Q z.val := by
    obtain ⟨q, hq⟩ := mem_orbit_iff.mp
      (UniqueOrbitStabilizer.preserves_unique_orbit Q f B hker hcomm x hone z hz b)
    exact mem_orbit_iff.mpr ⟨⟨q.val.val.val, q.property⟩, congrArg Subtype.val hq⟩
  have hOrbit (k : K) (t : X) (ht : t ∈ orbit Q z.val) :
      (k.val : G) • t ∈ orbit Q z.val := by
    obtain ⟨q, rfl⟩ := mem_orbit_iff.mp ht
    obtain ⟨r, hr⟩ := mem_orbit_iff.mp (hBz ⟨k.val, hKB k.property⟩)
    let q' : Q := Q.normalizerMonoidHom k.val q
    refine mem_orbit_iff.mpr ⟨q' * r, ?_⟩
    change ((k.val : G) * (q : G) * (k.val : G)⁻¹ * (r : G)) • z.val =
      (k.val : G) • ((q : G) • z.val)
    change (r : G) • z.val = (k.val : G) • z.val at hr
    rw [mul_smul, hr]
    simp only [mul_smul, inv_smul_smul]
  exact ⟨a, K, haorder, hax, hKdef, hKB, haK, hxK, hDK, hKp, hK2, hKcomm,
    hKdiv, hKmap, hOrbit, yK, wK, hyf, hwf⟩

end FiveTransitive.OneOrbitElementaryExtension

end CFSG
