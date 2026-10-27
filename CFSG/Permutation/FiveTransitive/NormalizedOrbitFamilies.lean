module

public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer
public import CFSG.Permutation.FiveTransitive.EvenSixTupleLocal

public section

namespace CFSG

namespace FiveTransitive.NormalizedOrbitFamilies

open MulAction Equiv

variable {G X : Type*} [Group G] [MulAction G X]

theorem normalizes_base {k : ℕ} (b : Fin k ↪ X) (a : G) (p : Perm (Fin k))
    (hp : ∀ i, a • b i = b (p i)) : a ∈ Subgroup.normalizer (stabilizer G b : Set G) := by
  rw [← EvenSixTupleLocal.fixing_range]
  apply SetwiseSylowNormalizer.normalizes_fixer
  intro x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p i,(hp i).symm⟩
  · rintro ⟨i,hi⟩
    refine ⟨p.symm i,(toPerm a).injective ?_⟩
    change a • b (p.symm i) = a • x
    rw [hp,p.apply_symm_apply]
    exact hi

private theorem smul_mem_orbit_iff (H : Subgroup G) (a : G)
    (ha : a ∈ Subgroup.normalizer (H : Set G)) (u : X) (hau : a • u = u) (x : X) :
    a • x ∈ orbit H u ↔ x ∈ orbit H u := by
  let e : MulAut H := H.normalizerMonoidHom ⟨a,ha⟩
  have he (h : H) : a • (h • u) = e h • u := by
    calc
      a • (h • u) = e h • (a • u) := by
        change a • ((h : G) • u) = (a * (h : G) * a⁻¹) • (a • u)
        simp only [mul_smul,inv_smul_smul]
      _ = e h • u := by rw [hau]
  constructor
  · rintro ⟨h,hh⟩
    refine ⟨e.symm h,(toPerm a).injective ?_⟩
    change a • (e.symm h • u) = a • x
    rw [he,e.apply_symm_apply]
    exact hh
  · rintro ⟨h,rfl⟩
    exact ⟨e h,(he h).symm⟩

private theorem orbit_disjoint_base (H : Subgroup G) (s : Set X)
    (hbase : ∀ (h : H) (x : X), x ∈ s → h • x = x) (u : X) (hu : u ∉ s) :
    Disjoint (orbit H u) s := by
  rw [Set.disjoint_left]
  intro x hx hs
  obtain ⟨h,rfl⟩ := mem_orbit_iff.mp hx
  have he : u = h • u := by
    have ht := hbase h⁻¹ (h • u) hs
    simpa only [inv_smul_smul] using ht
  exact hu (he ▸ hs)

private theorem mem_orbit_trans (H : Subgroup G) {x y u : X}
    (hxy : x ∈ orbit H y) (hyu : y ∈ orbit H u) : x ∈ orbit H u := by
  exact orbitRel_apply.mp ((orbitRel H X).trans (orbitRel_apply.mpr hxy) (orbitRel_apply.mpr hyu))

private theorem orbits_disjoint (H : Subgroup G) (u v : X) (hvu : v ∉ orbit H u) :
    Disjoint (orbit H u) (orbit H v) := by
  rw [Set.disjoint_left]
  intro x hxu hxv
  exact hvu (mem_orbit_trans H (orbitRel_apply.mp ((orbitRel H X).symm (orbitRel_apply.mpr hxv))) hxu)

private theorem not_rel_of_mem_not_mem (H : Subgroup G) (u x y : X)
    (hx : x ∈ orbit H u) (hy : y ∉ orbit H u) : ¬ orbitRel H X x y := by
  intro hr
  exact hy (mem_orbit_trans H (orbitRel_apply.mp ((orbitRel H X).symm hr)) hx)

private theorem exists_ne_in_orbit [Finite X] (H : Subgroup G) (u : X)
    (hu : 1 < Nat.card (orbit H u)) : ∃ x : X, x ∈ orbit H u ∧ x ≠ u := by
  classical
  have hn : ¬ orbit H u ⊆ {u} := by
    intro ht
    have hc := Set.ncard_le_ncard ht
    rw [Set.ncard_singleton,← Nat.card_coe_set_eq] at hc
    omega
  obtain ⟨x,hx,hn⟩ := Set.not_subset.mp hn
  exact ⟨x,hx,by simpa only [Set.mem_singleton_iff] using hn⟩

theorem exists_family [Finite X]
    (H : Subgroup G) (s F : Set X) (u v w : X)
    (hbase : ∀ (h : H) (x : X), x ∈ s → h • x = x)
    (hF : F = s ∪ {u,v}) (hu : u ∉ s) (hv : v ∉ s)
    (hvu : v ∉ orbit H u)
    (huCard : 1 < Nat.card (orbit H u)) (hvCard : 1 < Nat.card (orbit H v))
    (hw : w ∉ s ∪ orbit H u ∪ orbit H v)
    (a : G) (ha : a ∈ Subgroup.normalizer (H : Set G))
    (hau : a • u = u) (hav : a • v = v) :
    ∃ z : Fin 3 → X, (∀ i, z i ∉ F) ∧
      ∀ i j : Fin 3, i ≠ j → ∀ c d : Bool,
        ¬ orbitRel H X (if c then a • z i else z i) (if d then a • z j else z j) := by
  classical
  obtain ⟨x,hx,hxu⟩ := exists_ne_in_orbit H u huCard
  obtain ⟨y,hy,hyv⟩ := exists_ne_in_orbit H v hvCard
  have hdu := orbit_disjoint_base H s hbase u hu
  have hdv := orbit_disjoint_base H s hbase v hv
  have hduv := orbits_disjoint H u v hvu
  have hxF : x ∉ F := by
    rw [hF]
    rintro (hxs | hxuv)
    · exact Set.disjoint_left.mp hdu hx hxs
    · rcases Set.mem_insert_iff.mp hxuv with hxu' | hxv
      · exact hxu hxu'
      · exact hvu ((Set.mem_singleton_iff.mp hxv) ▸ hx)
  have hyF : y ∉ F := by
    rw [hF]
    rintro (hys | hyuv)
    · exact Set.disjoint_left.mp hdv hy hys
    · rcases Set.mem_insert_iff.mp hyuv with hyu | hyv'
      · exact Set.disjoint_left.mp hduv (by rw [hyu]; exact mem_orbit_self u) hy
      · exact hyv (Set.mem_singleton_iff.mp hyv')
  have hwF : w ∉ F := by
    rw [hF]
    rintro (hws | hwuv)
    · exact hw (Or.inl (Or.inl hws))
    · rcases Set.mem_insert_iff.mp hwuv with hwu | hwv
      · exact hw (Or.inl (Or.inr (by rw [hwu]; exact mem_orbit_self u)))
      · exact hw (Or.inr (by rw [Set.mem_singleton_iff.mp hwv]; exact mem_orbit_self v))
  have hxc (c : Bool) : (if c then a • x else x) ∈ orbit H u := by
    cases c
    · exact hx
    · exact (smul_mem_orbit_iff H a ha u hau x).mpr hx
  have hyc (c : Bool) : (if c then a • y else y) ∈ orbit H v := by
    cases c
    · exact hy
    · exact (smul_mem_orbit_iff H a ha v hav y).mpr hy
  have hwcu (c : Bool) : (if c then a • w else w) ∉ orbit H u := by
    have hn : w ∉ orbit H u := fun ht => hw (Or.inl (Or.inr ht))
    cases c
    · exact hn
    · exact fun ht => hn ((smul_mem_orbit_iff H a ha u hau w).mp ht)
  have hwcv (c : Bool) : (if c then a • w else w) ∉ orbit H v := by
    have hn : w ∉ orbit H v := fun ht => hw (Or.inr ht)
    cases c
    · exact hn
    · exact fun ht => hn ((smul_mem_orbit_iff H a ha v hav w).mp ht)
  refine ⟨![x,y,w],?_,?_⟩
  · intro i
    fin_cases i
    · exact hxF
    · exact hyF
    · exact hwF
  · intro i j hij c d
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact not_rel_of_mem_not_mem H u _ _ (hxc c) (fun ht => Set.disjoint_left.mp hduv ht (hyc d))
    · exact not_rel_of_mem_not_mem H u _ _ (hxc c) (hwcu d)
    · exact fun hr => not_rel_of_mem_not_mem H u _ _ (hxc d)
        (fun ht => Set.disjoint_left.mp hduv ht (hyc c)) ((orbitRel H X).symm hr)
    · exact (hij rfl).elim
    · exact not_rel_of_mem_not_mem H v _ _ (hyc c) (hwcv d)
    · exact fun hr => not_rel_of_mem_not_mem H u _ _ (hxc d) (hwcu c) ((orbitRel H X).symm hr)
    · exact fun hr => not_rel_of_mem_not_mem H v _ _ (hyc d) (hwcv c) ((orbitRel H X).symm hr)
    · exact (hij rfl).elim

end FiveTransitive.NormalizedOrbitFamilies

end CFSG
