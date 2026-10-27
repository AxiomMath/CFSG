module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5T0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem comm_of_mem_fsuVM (hyp : Ch10.Hyp10 G T L I) {a b : G} (ha : a ∈ fsuVM T L I)
    (hb : b ∈ fsuVM T L I) : a * b = b * a := by
  have h := (isElemAbelian_fsuVM hyp).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

omit [Finite G] in
theorem fsuUL_le_fsuVM (T L I : Subgroup G) : fsuUL T L I ≤ fsuVM T L I :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))

omit [Finite G] in
theorem conjugate_fsuUL_le {t : G} (ht : t ∈ fsuM T L) :
    CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have := (Subgroup.mem_normalizer_iff.mp (fsuM_le_normalizer_fsuVM T L I
    ((fsuM T L).inv_mem ht)) _).mp (fsuUL_le_fsuVM T L I hx)
  simpa [mul_assoc] using this

theorem conjugate_fsuUL_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate (fsuUL T L I) t ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have htt := mul_self_mem_normalizer h37 h38 hyp ht htn
  intro u hu
  rw [mem_conjugate_iff] at hu
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : t * l * t⁻¹ ∈ CFSG.conjugate L t := by
    rw [mem_conjugate_iff]
    have := (Subgroup.mem_normalizer_iff.mp htt l).mp hl
    simpa [mul_assoc] using this
  have h1 := Subgroup.mem_centralizer_iff.mp (hUt hu) _ hl'
  have h2 : t * (l * u) * t⁻¹ = t * (u * l) * t⁻¹ := by
    calc t * (l * u) * t⁻¹ = t * l * t⁻¹ * (t * u * t⁻¹) := by group
      _ = t * u * t⁻¹ * (t * l * t⁻¹) := h1
      _ = t * (u * l) * t⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem inf_conjugate_le_fsuCVM (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ CFSG.conjugate (fsuUL T L I) t ≤ fsuCVM T L I := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  rw [← (ha t ht htn).2.1]
  exact inf_le_inf le_sup_left le_sup_left

theorem exists_mul_of_mem_fsuVM (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G} (hv : v ∈ fsuVM T L I) :
    ∃ a ∈ fsuUL T L I, ∃ b ∈ CFSG.conjugate (fsuUL T L I) t, a * b = v := by
  have hV : fsuVM T L I = fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t := by
    rw [conjugate_commutator_fsuVM (le_fsuM T L ht)]
    exact fsuVM_eq_sup h37 h38 hyp ht htn
  have hN : CFSG.conjugate (fsuUL T L I) t ≤
      Subgroup.normalizer (fsuUL T L I : Set G) := by
    intro x hx
    have hxV := conjugate_fsuUL_le (I := I) (le_fsuM T L ht) hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [comm_of_mem_fsuVM hyp hxV (fsuUL_le_fsuVM T L I hu), mul_inv_cancel_right]
      exact hu
    · intro hu
      have hu' : x * u * x⁻¹ ∈ fsuVM T L I := fsuUL_le_fsuVM T L I hu
      have h1 : u = x⁻¹ * (x * u * x⁻¹) * x := by group
      rw [h1, mul_assoc, ← comm_of_mem_fsuVM hyp hxV hu', ← mul_assoc, inv_mul_cancel,
        one_mul]
      exact hu
  have hv' : v ∈ ((fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t : Subgroup G) : Set G) := by
    rw [← hV]
    exact hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hv'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hv'
  exact ⟨a, ha, b, hb, hab⟩

theorem mem_centralizer_T0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G} (hvV : v ∈ fsuVM T L I)
    (hv₁ : v ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G))
    (hv₂ : v ∈ Subgroup.centralizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G)) :
    v ∈ Subgroup.centralizer (T0 T L : Set G) := by
  have hle : T0 T L ≤ Subgroup.centralizer ({v} : Set G) := by
    refine (T0_le_sup h37 h38 hyp ht htn).trans (sup_le (sup_le ?_ ?_) ?_)
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hv₁ s hs).symm
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hv₂ s hs).symm
    · intro o ho
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact Subgroup.mem_centralizer_iff.mp (pCoreOf_fsuL0_le_centralizer h322 hyp ho) v hvV
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (Subgroup.mem_centralizer_iff.mp (hle hs) v rfl).symm

omit [Finite G] in
theorem le_normalizer_T0 (T L : Subgroup G) : T ≤ Subgroup.normalizer (T0 T L : Set G) :=
  fun _ hr => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr, le_fsuM T L hr⟩

omit [Finite G] in
theorem le_normalizer_W (T L I : Subgroup G) : T ≤ Subgroup.normalizer
    ((fsuVM T L I ⊓ Subgroup.centralizer (T0 T L : Set G) : Subgroup G) : Set G) :=
  fun _ hr => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨fsuM_le_normalizer_fsuVM T L I (le_fsuM T L hr),
      le_normalizer_centralizer le_rfl (le_normalizer_T0 T L hr)⟩

omit [Finite G] in
theorem B0_le_normalizer_W (T L I : Subgroup G) : B0 T L ≤ Subgroup.normalizer
    ((fsuVM T L I ⊓ Subgroup.centralizer (T0 T L : Set G) : Subgroup G) : Set G) := by
  intro b hb
  have hb' := oTwoUpper_le _ hb
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨fsuL0_le_normalizer_fsuVM T L I hb'.1, le_normalizer_centralizer le_rfl hb'.2⟩

omit [Finite G] in
theorem le_normalizer_B0 (T L : Subgroup G) : T ≤ Subgroup.normalizer (B0 T L : Set G) := by
  intro r hr
  apply normalizer_le_normalizer_oTwoUpper
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_fsuM T L hr, Subgroup.le_normalizer (le_normalizer_T0 T L hr)⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
