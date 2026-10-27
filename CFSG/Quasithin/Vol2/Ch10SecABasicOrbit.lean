module

public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjugate_conjugate (X : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate X a) b = CFSG.conjugate X (a * b) := by
  simp only [CFSG.conjugate, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjugate_one (X : Subgroup G) : CFSG.conjugate X 1 = X := by
  ext x
  simp [CFSG.conjugate]

theorem conjugate_eq_self_iff {X : Subgroup G} {s : G} :
    CFSG.conjugate X s = X ↔ s ∈ Subgroup.normalizer (X : Set G) := by
  rw [CFSG.conjugate, MulEquiv.toMonoidHom_eq_coe, ← Subgroup.mem_normalizer_iff_map_conj_eq,
    inv_mem_iff]

theorem mul_inv_mem_normalizer_of_conjugate_eq {X : Subgroup G} {s t : G}
    (h : CFSG.conjugate X s = CFSG.conjugate X t) :
    s * t⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
  have h' := congrArg (fun Y => CFSG.conjugate Y s⁻¹) h
  simp only [conjugate_conjugate, mul_inv_cancel, conjugate_one] at h'
  rw [← inv_mem_iff, mul_inv_rev, inv_inv, ← conjugate_eq_self_iff]
  exact h'.symm

theorem conjugate_eq_map (X : Subgroup G) (g : G) :
    CFSG.conjugate X g = X.map (MulAut.conj g⁻¹).toMonoidHom :=
  rfl

theorem mem_conjugate_iff {X : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  rw [CFSG.conjugate, Subgroup.mem_map_equiv]
  simp

theorem conj_mem_conjugate {X : Subgroup G} {x : G} (g : G) (hx : x ∈ X) :
    g⁻¹ * x * g ∈ CFSG.conjugate X g := by
  rw [mem_conjugate_iff]
  simpa [mul_assoc] using hx

theorem conjugate_mem_conjSubgroupsBy {T L : Subgroup G} {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s ∈ conjSubgroupsBy (fsuM T L) L :=
  ⟨s⁻¹, (fsuM T L).inv_mem hs, rfl⟩

theorem ne_conjugate {L : Subgroup G} {t : G} (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    L ≠ CFSG.conjugate L t :=
  fun h => htn (conjugate_eq_self_iff.mp h.symm)

variable [Finite G]

section Orbit

variable {T L I : Subgroup G}

theorem conjSubgroupsBy_fsuM_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    conjSubgroupsBy (fsuM T L) L = {L, CFSG.conjugate L t} := by
  have hcard := ncard_conjSubgroupsBy_fsuM h37 h38 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · rintro K (rfl | rfl)
    · simpa [conjugate_one] using conjugate_mem_conjSubgroupsBy (T := T) (L := K)
        (fsuM T K).one_mem
    · exact conjugate_mem_conjSubgroupsBy (le_fsuM T L ht)
  · rw [hcard, Set.ncard_pair (ne_conjugate htn)]

theorem conjugate_eq_or (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s = L ∨ CFSG.conjugate L s = CFSG.conjugate L t := by
  have h := conjugate_mem_conjSubgroupsBy hs
  rw [conjSubgroupsBy_fsuM_eq h37 h38 hyp ht htn] at h
  exact h

theorem conjugate_eq_of_not_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L s = CFSG.conjugate L t :=
  (conjugate_eq_or h37 h38 hyp ht htn (le_fsuM T L hs)).resolve_left
    fun h => hsn (conjugate_eq_self_iff.mp h)

theorem mul_inv_mem_normalizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    s * t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
  mul_inv_mem_normalizer_of_conjugate_eq (conjugate_eq_of_not_mem h37 h38 hyp ht htn hs hsn)

theorem mul_self_mem_normalizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    t * t ∈ Subgroup.normalizer (L : Set G) := by
  rcases conjugate_eq_or h37 h38 hyp ht htn (le_fsuM T L (T.mul_mem ht ht)) with h | h
  · exact conjugate_eq_self_iff.mp h
  · have := mul_inv_mem_normalizer_of_conjugate_eq h
    rw [mul_inv_cancel_right] at this
    exact absurd this htn

theorem mul_mem_normalizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    s * t ∈ Subgroup.normalizer (L : Set G) := by
  have h := (Subgroup.normalizer (L : Set G)).mul_mem
    (mul_inv_mem_normalizer h37 h38 hyp ht htn hs hsn) (mul_self_mem_normalizer h37 h38 hyp ht htn)
  simpa [mul_assoc] using h

theorem index_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : ((T1 T L).subgroupOf T).index = 2 := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, ht⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  by_cases hb : (b : G) ∈ Subgroup.normalizer (L : Set G)
  · refine Or.inr ⟨⟨b.2, hb⟩, fun h => htn ?_⟩
    have := (Subgroup.normalizer (L : Set G)).mul_mem ((Subgroup.normalizer _).inv_mem hb) h.2
    simpa using this
  · exact Or.inl ⟨⟨T.mul_mem b.2 ht, mul_mem_normalizer h37 h38 hyp ht htn b.2 hb⟩,
      fun h => hb h.2⟩

theorem conjugate_mem_cComp_fsuM (hloc : quasithinIsLocal T L) {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s ∈ cComp (fsuM T L) :=
  map_conj_mem_cComp (mem_cComp_fsuM hloc) ((fsuM T L).inv_mem hs)

end Orbit

end CFSG.Quasithin.Vol2.Ch10.SecA
