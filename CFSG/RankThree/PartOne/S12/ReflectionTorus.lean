module

public import CFSG.RankThree.PartOne.S12.ReflectionFacts
public import CFSG.RankThree.PartOne.S12.InputsCT

public section

namespace CFSG.RankThree.PartOne

namespace RefFacts

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G}

omit [Finite G] in
theorem inf_autFixedInG_eq {B : Subgroup G} (hBE : B ≤ E) (t : MulAut E) :
    B ⊓ autFixedInG E t = (B.subgroupOf E ⊓ autFixed E t).map E.subtype := by
  rw [Subgroup.map_inf _ _ _ E.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hBE]
  rfl

omit [Finite G] in
theorem autMoved_le_subgroupOf_iff {B : Subgroup G} (t : MulAut E) :
    autMoved E t ≤ B.subgroupOf E ↔ autMovedInG E t ≤ B := by
  rw [autMovedInG, Subgroup.map_le_iff_le_comap]
  rfl

omit [Finite G] in
theorem relIndex_inf_autFixedInG_eq {B : Subgroup G} (hBE : B ≤ E) (t : MulAut E) :
    (B ⊓ autFixedInG E t).relIndex B =
      (B.subgroupOf E ⊓ autFixed E t).relIndex (B.subgroupOf E) := by
  have h := Subgroup.relIndex_map_map_of_injective (B.subgroupOf E ⊓ autFixed E t)
    (B.subgroupOf E) E.subtype_injective
  rwa [← inf_autFixedInG_eq hBE t, Subgroup.map_subgroupOf_eq_of_le hBE] at h

omit [Finite G] in
theorem centralizer_sup (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · intro x hx
    have hle : H ⊔ K ≤ Subgroup.centralizer {x} :=
      sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 hx.1) h hh))
        (fun k hk => Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 hx.2) k hk))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem autMovedInG_le_of_nontrivial (hd : ElemData p E) {t : MulAut E}
    (ht : IsAutReflection p E t) {B : Subgroup G} (hBE : B ≤ E)
    (hBinv : ∀ b : E, (b : G) ∈ B → ((t b : E) : G) ∈ B)
    (hnt : ∃ b : E, (b : G) ∈ B ∧ t b ≠ b) : autMovedInG E t ≤ B := by
  obtain ⟨b, hbB, hne⟩ := hnt
  have h := autMoved_le_of_move hd ht (B := B.subgroupOf E) (Subgroup.mem_subgroupOf.2 hbB)
    (Subgroup.mem_subgroupOf.2 (hBinv b hbB)) hne
  have h2 := Subgroup.map_mono (f := E.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hBE] at h2

theorem relIndex_inf_autFixedInG (hd : ElemData p E) {t : MulAut E}
    (ht : IsAutReflection p E t) {B : Subgroup G} (hBE : B ≤ E) (hmoved : autMovedInG E t ≤ B) :
    (B ⊓ autFixedInG E t).relIndex B = p := by
  rw [relIndex_inf_autFixedInG_eq hBE t]
  exact relIndex_inf_fixed hd ht ((autMoved_le_subgroupOf_iff t).2 hmoved)

theorem inf_autFixedInG_ne (hd : ElemData p E) {t s : MulAut E} (ht : IsAutReflection p E t)
    (hs : IsAutReflection p E s) (htW : t ∈ torusWeyl E) (hsW : s ∈ torusWeyl E) (hts : t ≠ s)
    {B : Subgroup G} (hBE : B ≤ E) (hmt : autMovedInG E t ≤ B) (hms : autMovedInG E s ≤ B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    (hord : Nat.Coprime (orderOf (t * s)) p) :
    B ⊓ autFixedInG E t ≠ B ⊓ autFixedInG E s := by
  intro heq
  have hmt' : autMoved E t ≤ B.subgroupOf E := (autMoved_le_subgroupOf_iff t).2 hmt
  have hms' : autMoved E s ≤ B.subgroupOf E := (autMoved_le_subgroupOf_iff s).2 hms
  have hH : B.subgroupOf E ⊓ autFixed E t = B.subgroupOf E ⊓ autFixed E s := by
    apply Subgroup.map_injective E.subtype_injective
    rw [← inf_autFixedInG_eq hBE t, ← inf_autFixedInG_eq hBE s]
    exact heq
  have hpow := pow_prime_fixes_of_same_fixed hd ht hs hmt' hms' hH
  have hg : (t * s) ^ p = 1 :=
    hfaith _ (pow_mem (mul_mem htW hsW) p) fun b hb => hpow b (Subgroup.mem_subgroupOf.2 hb)
  have hts1 : t * s = 1 := orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd hord (orderOf_dvd_of_pow_eq_one hg))
  apply hts
  rw [mul_eq_one_iff_eq_inv.1 hts1]
  exact inv_eq_of_mul_eq_one_right (mul_self_eq_one hs)

theorem inf_autFixedInG_sup_autMovedInG (hd : ElemData p E) {t : MulAut E}
    (ht : IsAutReflection p E t) {B : Subgroup G} (hBE : B ≤ E) (hmoved : autMovedInG E t ≤ B) :
    (B ⊓ autFixedInG E t) ⊔ autMovedInG E t = B := by
  have h := inf_fixed_sup_autMoved hd ht (B := B.subgroupOf E)
    ((autMoved_le_subgroupOf_iff t).2 hmoved)
  have h2 := congrArg (Subgroup.map E.subtype) h
  rwa [Subgroup.map_sup, ← inf_autFixedInG_eq hBE t, Subgroup.map_subgroupOf_eq_of_le hBE] at h2

theorem relIndex_inf_autFixedInG_inf (hd : ElemData p E) {t s : MulAut E}
    (ht : IsAutReflection p E t) (hs : IsAutReflection p E s) {B : Subgroup G} (hBE : B ≤ E)
    (hmt : autMovedInG E t ≤ B) (hms : autMovedInG E s ≤ B)
    (hne : B ⊓ autFixedInG E t ≠ B ⊓ autFixedInG E s) :
    ((B ⊓ autFixedInG E t) ⊓ (B ⊓ autFixedInG E s)).relIndex B = p ^ 2 := by
  have hne' : B.subgroupOf E ⊓ autFixed E t ≠ B.subgroupOf E ⊓ autFixed E s := by
    intro h
    apply hne
    rw [inf_autFixedInG_eq hBE t, inf_autFixedInG_eq hBE s, h]
  have h := relIndex_inf_inf_of_ne hd (B := B.subgroupOf E) inf_le_left inf_le_left
    (relIndex_inf_fixed hd ht ((autMoved_le_subgroupOf_iff t).2 hmt))
    (relIndex_inf_fixed hd hs ((autMoved_le_subgroupOf_iff s).2 hms)) hne'
  have h2 := Subgroup.relIndex_map_map_of_injective
    ((B.subgroupOf E ⊓ autFixed E t) ⊓ (B.subgroupOf E ⊓ autFixed E s)) (B.subgroupOf E)
    E.subtype_injective
  rw [h, Subgroup.map_inf _ _ _ E.subtype_injective, ← inf_autFixedInG_eq hBE t,
    ← inf_autFixedInG_eq hBE s, Subgroup.map_subgroupOf_eq_of_le hBE] at h2
  exact h2

theorem ctTorusCondition_of_reflections {n : ℕ} (hd : ElemData p E) {B : Subgroup G}
    (hBE : B ≤ E) (t : Fin n → MulAut E) (K : Fin n → Subgroup G)
    (ht : ∀ i, IsAutReflection p E (t i)) (hmovedB : ∀ i, autMovedInG E (t i) ≤ B)
    (hcent : ∀ i, E ⊓ Subgroup.centralizer (K i : Set G) = autFixedInG E (t i))
    (hmovedK : ∀ i, autMovedInG E (t i) ≤ K i)
    (hne : ∀ i j, i ≠ j → B ⊓ autFixedInG E (t i) ≠ B ⊓ autFixedInG E (t j)) :
    CTTorusCondition p B K := by
  have hBC : ∀ i, B ⊓ Subgroup.centralizer (K i : Set G) = B ⊓ autFixedInG E (t i) := by
    intro i
    rw [← hcent i, ← inf_assoc, inf_eq_left.2 hBE]
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · rw [hBC i]
    apply le_antisymm
    · calc B = (B ⊓ autFixedInG E (t i)) ⊔ autMovedInG E (t i) :=
            (inf_autFixedInG_sup_autMovedInG hd (ht i) hBE (hmovedB i)).symm
        _ ≤ (B ⊓ autFixedInG E (t i)) ⊔ (B ⊓ K i) :=
            sup_le_sup_left (le_inf (hmovedB i) (hmovedK i)) _
    · exact sup_le inf_le_left inf_le_left
  · rw [hBC i]
    exact relIndex_inf_autFixedInG hd (ht i) hBE (hmovedB i)
  · have h1 : B ⊓ Subgroup.centralizer ((K i ⊔ K j : Subgroup G) : Set G) =
        (B ⊓ autFixedInG E (t i)) ⊓ (B ⊓ autFixedInG E (t j)) := by
      rw [centralizer_sup, ← hBC i, ← hBC j]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [h1]
    exact relIndex_inf_autFixedInG_inf hd (ht i) (ht j) hBE (hmovedB i) (hmovedB j) (hne i j hij)

end RefFacts

end CFSG.RankThree.PartOne
