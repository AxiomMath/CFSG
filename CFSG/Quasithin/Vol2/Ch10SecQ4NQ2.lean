module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS16

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_normalizer_of_odd (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {m : G} (hm : m ∈ fsuM T L) (hodd : Odd (orderOf m)) :
    m ∈ Subgroup.normalizer (L : Set G) ∧
      m ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  have key := fun s (hs : s ∈ fsuM T L) => SecA.conjugate_eq_or h37 h38 hyp ht htn hs
  have htM := SecA.le_fsuM T L ht
  have htm : t * m ∈ fsuM T L := (fsuM T L).mul_mem htM hm
  have hm2 : m * m ∈ Subgroup.normalizer (L : Set G) := by
    rcases key m hm with h | h
    · have h1 := SecA.conjugate_eq_self_iff.mp h
      exact Subgroup.mul_mem _ h1 h1
    · rcases key (t * m) htm with h' | h'
      · rw [← SecA.conjugate_eq_self_iff, ← SecA.conjugate_conjugate, h,
          SecA.conjugate_conjugate]
        exact h'
      · exfalso
        apply htn
        have h1 := SecA.mul_inv_mem_normalizer_of_conjugate_eq (h'.trans h.symm)
        have h2 := SecA.mul_inv_mem_normalizer_of_conjugate_eq (h.trans h'.symm)
        have e : t = t * m * m⁻¹ := by group
        rw [e]
        exact h1
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := by
    obtain ⟨k, hk⟩ := hodd
    have e : m = (m * m) ^ (k + 1) := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf m + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hm2 _
  refine ⟨hmL, ?_⟩
  rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate]
  rcases key (t * m) htm with h | h
  · exfalso
    apply htn
    have h1 := SecA.conjugate_eq_self_iff.mp h
    have e : t = t * m * m⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hmL)
  · exact h

theorem mem_normalizer_of_odd_of_isLi (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {K : Subgroup G}
    (hK : Ch10.IsLi T L K) {m : G} (hm : m ∈ fsuM T L) (hodd : Odd (orderOf m)) :
    m ∈ Subgroup.normalizer (K : Set G) := by
  rcases hK with rfl | ⟨t, ht, htn, rfl⟩
  · obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
    exact (mem_normalizer_of_odd h37 h38 hyp ht htn hm hodd).1
  · exact (mem_normalizer_of_odd h37 h38 hyp ht htn hm hodd).2

theorem not_le_normalizer_V (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ¬ T ≤ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      ¬ T ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I) t : Set G) := by
  have hV1 : fsuUL T L I ≠ ⊥ := fun h => by
    have := card_fsuUL_case2 h2
    rw [h, Subgroup.card_bot] at this
    omega
  have h1 : t ∉ Subgroup.normalizer (fsuUL T L I : Set G) := fun h => by
    have he := SecA.conjugate_eq_self_iff.mpr h
    have hb := fsuUL_inf_conjugate_eq_bot h37 h38 hyp h2 ht htn
    rw [he, inf_idem] at hb
    exact hV1 hb
  refine ⟨fun hT => h1 (hT ht), fun hT => h1 ?_⟩
  have he := SecA.conjugate_eq_self_iff.mpr (hT ht)
  rw [SecA.conjugate_conjugate] at he
  have := SecA.mul_inv_mem_normalizer_of_conjugate_eq he
  simpa using this

omit [Finite G] in
theorem VK_le_fsuVM {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I := by
  have hKL0 : K ≤ fsuL0 T L := by
    rcases hK with rfl | ⟨t, ht, -, rfl⟩
    · exact SecA.le_fsuL0 T K
    · exact SecA.conjugate_le_fsuL0 ht
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hKL0.trans (SecA.fsuL0_le_normalizer_fsuVM T L I))

theorem VK_eq (hyp : Hyp10 G T L I) {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
      (⁅fsuVM T L I, K⁆ = fsuUL T L I ∧ K = L ∨
        ⁅fsuVM T L I, K⁆ = CFSG.conjugate (fsuUL T L I) t ∧ K = CFSG.conjugate L t) := by
  rcases hK with rfl | ⟨t, ht, htn, rfl⟩
  · obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
    exact ⟨t, ht, htn, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨t, ht, htn, Or.inr ⟨(SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)).symm,
      rfl⟩⟩

theorem VK_ne_bot (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) {K : Subgroup G}
    (hK : Ch10.IsLi T L K) : ⁅fsuVM T L I, K⁆ ≠ ⊥ := by
  have hV1 : fsuUL T L I ≠ ⊥ := fun h => by
    have := card_fsuUL_case2 h2
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨t, -, -, ⟨h, -⟩ | ⟨h, -⟩⟩ := VK_eq hyp hK
  · rw [h]; exact hV1
  · rw [h]; exact conjugate_ne_bot hV1 t

theorem le_normalizer_VK (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    fsuL0 T L ⊔ Ch10.T1 T L ≤ Subgroup.normalizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G) := by
  obtain ⟨t, ht, htn, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ := VK_eq hyp hK
  · obtain ⟨_, -, -, ha, -⟩ := hyp.three
    have hLt : CFSG.conjugate K t ≤ Subgroup.centralizer (fsuUL T K I : Set G) :=
      Subgroup.le_centralizer_iff.mp (ha t ht htn).2.2
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact sup_le (sup_le (SecC.le_normalizer_fsuUL T K I)
      (hLt.trans (Subgroup.centralizer_le_normalizer _))) (T1_le_normalizer_fsuUL T K I)
  · have hVt : L ≤ Subgroup.centralizer (CFSG.conjugate (fsuUL T L I) t : Set G) :=
      Subgroup.le_centralizer_iff.mp (SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn)
    have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    refine sup_le (sup_le ?_ (SecA.le_normalizer_commutator hLtV Subgroup.le_normalizer))
      (SecA.le_normalizer_commutator (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I))
        (SecB.T1_le_normalizer_conjugate h37 h38 hyp ht))
    rw [h]
    exact hVt.trans (Subgroup.centralizer_le_normalizer _)

theorem not_le_centralizer_VK (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    ¬ K ≤ Subgroup.centralizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G) := by
  have hV1 : fsuUL T L I ≠ ⊥ := fun h => by
    have := card_fsuUL_case2 h2
    rw [h, Subgroup.card_bot] at this
    omega
  have hbot := SecF.fsuUL_inf_centralizer_eq_bot h2
  have hfalse : fsuUL T L I ≤ Subgroup.centralizer (L : Set G) → False := fun hc => by
    apply hV1
    rw [eq_bot_iff, ← hbot]
    exact le_inf le_rfl hc
  obtain ⟨t, -, -, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ := VK_eq hyp hK
  · intro hc
    exact hfalse (Subgroup.le_centralizer_iff.mp (h ▸ hc))
  · intro hc
    rw [h] at hc
    refine hfalse fun v hv => Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hv' := SecA.conj_mem_conjugate t hv
    have hl' : t⁻¹ * l * t ∈ CFSG.conjugate L t := SecA.conj_mem_conjugate t hl
    have hc' := Subgroup.mem_centralizer_iff.mp (hc hl') _ hv'
    calc l * v = t * ((t⁻¹ * l * t) * (t⁻¹ * v * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * v * t) * (t⁻¹ * l * t)) * t⁻¹ := by rw [hc']
      _ = v * l := by group

theorem not_le_normalizer_conjugate_VK (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {K : Subgroup G} (hK : Ch10.IsLi T L K) {m : G} (hm : m ∈ fsuM T L) :
    ¬ T ≤ Subgroup.normalizer (CFSG.conjugate ⁅fsuVM T L I, K⁆ m : Set G) := by
  obtain ⟨t, ht, htn, ⟨h, -⟩ | ⟨h, -⟩⟩ := VK_eq hyp hK
  · rw [h]
    rcases conjugate_fsuUL_eq_or h37 h38 hyp ht htn hm with h' | h'
    · rw [h']; exact (not_le_normalizer_V h37 h38 hyp h2 ht htn).1
    · rw [h']; exact (not_le_normalizer_V h37 h38 hyp h2 ht htn).2
  · rw [h, SecA.conjugate_conjugate]
    rcases conjugate_fsuUL_eq_or h37 h38 hyp ht htn
        ((fsuM T L).mul_mem (SecA.le_fsuM T L ht) hm) with h' | h'
    · rw [h']; exact (not_le_normalizer_V h37 h38 hyp h2 ht htn).1
    · rw [h']; exact (not_le_normalizer_V h37 h38 hyp h2 ht htn).2

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
