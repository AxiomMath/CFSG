module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] {T L I : Subgroup G}

theorem le_normalizer_fsuCVM (T L I : Subgroup G) :
    fsuM T L ≤ Subgroup.normalizer (fsuCVM T L I : Set G) := fun _ hm =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨fsuM_le_normalizer_fsuVM T L I hm, le_normalizer_centralizer le_rfl hm⟩

theorem eq_one_of_isPGroup_of_odd {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x = 1 :=
    ((Nat.coprime_two_right.mpr hodd).pow_right k).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk')
  exact orderOf_eq_one_iff.mp h1

theorem mem_normalizer_inf_of_mem {K : Subgroup G} (hK : K ≤ fsuL0 T L)
    (hKn : fsuL0 T L ≤ Subgroup.normalizer (K : Set G)) {x : G} (hxL0 : x ∈ fsuL0 T L)
    (hxN : x ∈ Subgroup.normalizer (T0 T L : Set G)) :
    x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have h : T0 T L ⊓ K = T ⊓ K := by rw [inf_assoc, inf_eq_right.mpr hK]
  rw [← h]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxN, hKn hxL0⟩

variable [Finite G]

omit [Finite G] in
theorem mem_inf_iff_conj {t : G} (ht : t ∈ T) (s : G) :
    s ∈ T ⊓ L ↔ t⁻¹ * s * t ∈ T ⊓ CFSG.conjugate L t := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_conjugate_iff]
  have h1 : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
  rw [h1]
  constructor
  · rintro ⟨hs, hsL⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hs) ht, hsL⟩
  · rintro ⟨hs, hsL⟩
    refine ⟨?_, hsL⟩
    have := T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
    simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mem_normalizer_inf {t : G} (ht : t ∈ T) {x : G}
    (hx : x ∈ Subgroup.normalizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [mem_inf_iff_conj ht s, mem_inf_iff_conj ht (t * x * t⁻¹ * s * (t * x * t⁻¹)⁻¹)]
  have h1 : t⁻¹ * (t * x * t⁻¹ * s * (t * x * t⁻¹)⁻¹) * t = x * (t⁻¹ * s * t) * x⁻¹ := by
    group
  rw [h1]
  exact Subgroup.mem_normalizer_iff.mp hx _

omit [Finite G] in
theorem forall_conj_eq_of_conj {t x : G}
    (h : ∀ u ∈ fsuUL T L I, t * x * t⁻¹ * u * (t * x * t⁻¹)⁻¹ = u) :
    ∀ u ∈ CFSG.conjugate (fsuUL T L I) t, x * u * x⁻¹ = u := by
  intro u hu
  have h1 := h _ (mem_conjugate_iff.mp hu)
  have h2 : t * x * t⁻¹ * (t * u * t⁻¹) * (t * x * t⁻¹)⁻¹ = t * (x * u * x⁻¹) * t⁻¹ := by
    group
  rw [h2] at h1
  have h3 := congrArg (fun z => t⁻¹ * z * t) h1
  simpa [mul_assoc] using h3

theorem eq_one_of_forall_conj_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G} (hxL0 : x ∈ fsuL0 T L)
    (hxodd : Odd (orderOf x)) (hU : ∀ u ∈ fsuUL T L I, x * u * x⁻¹ = u)
    (hUt : ∀ u ∈ CFSG.conjugate (fsuUL T L I) t, x * u * x⁻¹ = u) : x = 1 := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hV := (ha t ht htn).1
  have hcomm : ∀ u, x * u * x⁻¹ = u → u ∈ Subgroup.centralizer ({x} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (mul_inv_eq_iff_eq_mul.mp hu)
  have hle : fsuVM T L I ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hV]
    refine sup_le (sup_le (fun u hu => hcomm u (hU u hu)) (fun u hu => hcomm u (hUt u hu)))
      fun c hc => hcomm c ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 x hxL0
    rw [h1, mul_inv_cancel_right]
  have hxC : x ∈ fsuL0 T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine ⟨hxL0, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) x rfl).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_one_of_isPGroup_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
    (fsuL0_inf_centralizer_le h37 h38 hyp hxC) hxodd

theorem eq_one_of_centralizes
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I)
    (hcen : ∀ y ∈ fsuL0 T L, Odd (orderOf y) →
      y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) → ∀ w ∈ fsuUL T L I,
        w ∉ fsuCVM T L I → (∀ s ∈ T ⊓ L, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I) →
          y * w * y⁻¹ * w⁻¹ ∈ fsuCVM T L I → ∀ u ∈ fsuUL T L I, y * u * y⁻¹ = u)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {x : G} (hxL0 : x ∈ fsuL0 T L) (hxN : x ∈ Subgroup.normalizer (T0 T L : Set G))
    (hxodd : Odd (orderOf x)) {w₁ w₂ : G} (hw₁U : w₁ ∈ fsuUL T L I) (hw₁C : w₁ ∉ fsuCVM T L I)
    (hw₁S : ∀ s ∈ T ⊓ L, s * w₁ * s⁻¹ * w₁⁻¹ ∈ fsuCVM T L I)
    (hw₁x : x * w₁ * x⁻¹ * w₁⁻¹ ∈ fsuCVM T L I)
    (hw₂U : w₂ ∈ CFSG.conjugate (fsuUL T L I) t) (hw₂C : w₂ ∉ fsuCVM T L I)
    (hw₂S : ∀ s ∈ T ⊓ CFSG.conjugate L t, s * w₂ * s⁻¹ * w₂⁻¹ ∈ fsuCVM T L I)
    (hw₂x : x * w₂ * x⁻¹ * w₂⁻¹ ∈ fsuCVM T L I) : x = 1 := by
  have hloc := hyp.fsu.maximal.1
  have htM : t ∈ fsuM T L := le_fsuM T L ht
  have hCt := le_normalizer_fsuCVM T L I htM
  have hCt' := le_normalizer_fsuCVM T L I ((fsuM T L).inv_mem htM)
  have hxL := mem_normalizer_inf_of_mem (le_fsuL0 T L) (fsuL0_le_normalizer hloc) hxL0 hxN
  have hU := hcen x hxL0 hxodd hxL w₁ hw₁U hw₁C hw₁S hw₁x
  have hxLt := mem_normalizer_inf_of_mem (conjugate_le_fsuL0 ht)
    (fsuL0_le_normalizer_conjugate hloc htM) hxL0 hxN
  have hyL0 : t * x * t⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp htM x).mp hxL0
  have hyodd : Odd (orderOf (t * x * t⁻¹)) := by
    rw [show t * x * t⁻¹ = (MulAut.conj t).toMonoidHom x from rfl,
      orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective]
    exact hxodd
  have hwU : t * w₂ * t⁻¹ ∈ fsuUL T L I := mem_conjugate_iff.mp hw₂U
  have hwC : t * w₂ * t⁻¹ ∉ fsuCVM T L I := by
    intro h
    apply hw₂C
    have := (Subgroup.mem_normalizer_iff.mp hCt' _).mp h
    simpa [mul_assoc] using this
  have hwS : ∀ s ∈ T ⊓ L, s * (t * w₂ * t⁻¹) * s⁻¹ * (t * w₂ * t⁻¹)⁻¹ ∈ fsuCVM T L I := by
    intro s hs
    have h1 := (Subgroup.mem_normalizer_iff.mp hCt _).mp
      (hw₂S _ ((mem_inf_iff_conj ht s).mp hs))
    have h2 : t * (t⁻¹ * s * t * w₂ * (t⁻¹ * s * t)⁻¹ * w₂⁻¹) * t⁻¹ =
        s * (t * w₂ * t⁻¹) * s⁻¹ * (t * w₂ * t⁻¹)⁻¹ := by group
    rwa [h2] at h1
  have hwy : t * x * t⁻¹ * (t * w₂ * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * w₂ * t⁻¹)⁻¹ ∈
      fsuCVM T L I := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hCt _).mp hw₂x
    have h2 : t * (x * w₂ * x⁻¹ * w₂⁻¹) * t⁻¹ =
        t * x * t⁻¹ * (t * w₂ * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * w₂ * t⁻¹)⁻¹ := by group
    rwa [h2] at h1
  have hU' := hcen _ hyL0 hyodd (conj_mem_normalizer_inf ht hxLt) _ hwU hwC hwS hwy
  exact eq_one_of_forall_conj_eq h37 h38 hyp ht htn hxL0 hxodd hU
    (forall_conj_eq_of_conj hU')

end CFSG.Quasithin.Vol2.Ch10.SecA
