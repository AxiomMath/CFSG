module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.Sylow155KA6P
import CFSG.RankThree.PartTwo.Sec15.Sylow155NODeg
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

open CFSG.RankThree.PartTwo
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

private theorem exists_commuting_involution {a : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) :
    ∃ r ∈ A6Models.psl29, r * r = 1 ∧ r ≠ 1 ∧ r * (a * r * a⁻¹) = (a * r * a⁻¹) * r := by
  obtain ⟨g, hg, hga⟩ := Push153B.A6.exists_conj_tAdd ha ha3 ha1
  have hne : Sylow155KA6P.klL ≠ [] := fun h => by
    have := Sylow155KA6P.klL_length
    rw [h] at this
    exact absurd this (by decide)
  obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ hne
  have hrc' : rc ∈ Core.pslLit := by
    unfold Sylow155KA6P.klL at hrc
    exact (List.mem_filter.mp hrc).1
  obtain ⟨r₀, -, rfl⟩ := exists_psl29_of_code hrc'
  obtain ⟨hr₀, hr₀2, hr₀1, hr₀c⟩ := (Sylow155KA6P.mem_klL_iff r₀).mp hrc
  have ha' : a = g⁻¹ * A6Models.tAdd * g := by rw [← hga]; group
  refine ⟨g⁻¹ * r₀ * g, ?_, ?_, ?_, ?_⟩
  · have := psl29_normal g⁻¹ (A6Models.autA6.inv_mem hg) r₀ hr₀
    simpa using this
  · calc g⁻¹ * r₀ * g * (g⁻¹ * r₀ * g) = g⁻¹ * (r₀ * r₀) * g := by group
      _ = 1 := by rw [hr₀2]; group
  · intro h
    apply hr₀1
    have := congrArg (fun w => g * w * g⁻¹) h
    simpa [mul_assoc] using this
  · rw [ha']
    calc g⁻¹ * r₀ * g * (g⁻¹ * A6Models.tAdd * g * (g⁻¹ * r₀ * g) * (g⁻¹ * A6Models.tAdd * g)⁻¹)
        = g⁻¹ * (r₀ * (A6Models.tAdd * r₀ * A6Models.tAdd⁻¹)) * g := by group
      _ = g⁻¹ * ((A6Models.tAdd * r₀ * A6Models.tAdd⁻¹) * r₀) * g := by rw [hr₀c]
      _ = g⁻¹ * A6Models.tAdd * g * (g⁻¹ * r₀ * g) * (g⁻¹ * A6Models.tAdd * g)⁻¹ *
          (g⁻¹ * r₀ * g) := by group

private theorem exists_commuting_involution' (a : ↥A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) :
    ∃ ρ : ↥A6Models.psl29, ρ * ρ = 1 ∧ ρ ≠ 1 ∧ ρ * (a * ρ * a⁻¹) = (a * ρ * a⁻¹) * ρ := by
  obtain ⟨r, hr, hr2, hr1, hrc⟩ := exists_commuting_involution a.2
    (by simpa using congrArg Subtype.val ha3) (fun h => ha1 (Subtype.ext h))
  exact ⟨⟨r, hr⟩, Subtype.ext hr2, fun h => hr1 (congrArg Subtype.val h), Subtype.ext hrc⟩

private theorem commute_of_commutator_mem_center {X : Type*} [Group X]
    (hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1) {r s : X} (hr : r * r = 1)
    (h : r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center X) : r * s = s * r := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  rw [hri] at h
  have hzr : r * (r * s * r * s⁻¹) = (r * s * r * s⁻¹) * r := Subgroup.mem_center_iff.mp h r
  have h1 : r * s * r = (r * s * r * s⁻¹) * s := by group
  have h2 : s = (r * s * r * s⁻¹) * ((r * s * r * s⁻¹) * s) := by
    generalize r * s * r * s⁻¹ = z at h1 hzr
    calc s = (r * r) * s * (r * r) := by rw [hr]; group
      _ = r * (r * s * r) * r := by group
      _ = r * (z * s) * r := by rw [h1]
      _ = (r * z) * (s * r) := by group
      _ = (z * r) * (s * r) := by rw [hzr]
      _ = z * (r * s * r) := by group
      _ = z * (z * s) := by rw [h1]
  have h3 : (r * s * r * s⁻¹) * (r * s * r * s⁻¹) = 1 := by
    generalize r * s * r * s⁻¹ = z at h2
    have : z * z * s = 1 * s := by rw [one_mul, mul_assoc]; exact h2.symm
    exact mul_right_cancel this
  have h4 : r * s * r * s⁻¹ = 1 := by
    have h5 := hZ3 _ h
    generalize r * s * r * s⁻¹ = z at h3 h5
    calc z = z * (z * z) := by rw [h3, mul_one]
      _ = 1 := by rw [← pow_three]; exact h5
  have h6 : r * s * r = s := mul_inv_eq_one.mp h4
  calc r * s = r * s * (r * r) := by rw [hr, mul_one]
    _ = (r * s * r) * r := by group
    _ = s * r := by rw [h6]

private theorem isPGroup_closure_of_comm_sq {X : Type*} [Group X] {S : Set X}
    (h2 : ∀ x ∈ S, x * x = 1) (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    IsPGroup 2 (Subgroup.closure S) := by
  have h1 : ∀ x ∈ S, ∀ w ∈ Subgroup.closure S, x * w = w * x := by
    intro x hx w hw
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact hc x hx y hy)
    exact (Subgroup.mem_centralizer_iff.mp (hle hw)) x rfl
  have hcomm : ∀ v ∈ Subgroup.closure S, ∀ w ∈ Subgroup.closure S, v * w = w * v := by
    intro v hv w hw
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({v} : Set X) := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (h1 y hy v hv).symm)
    exact (Subgroup.mem_centralizer_iff.mp (hle hw)) v rfl
  have hsq : ∀ v ∈ Subgroup.closure S, v * v = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx => exact h2 x hx
    | one => exact mul_one 1
    | mul x y hx hy hx2 hy2 =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x _ hx2 =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx2, inv_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := hsq g.1 g.2
  simpa [pow_two] using this

private theorem conj_mem_closure_of {X : Type*} [Group X] {S : Set X} {g : X}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) {v : X} (hv : v ∈ Subgroup.closure S) :
    g * v * g⁻¹ ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun x hx => by simpa [MulAut.conj_apply] using h x hx
  simpa [MulAut.conj_apply] using hle hv

private theorem mem_normalizer_closure {X : Type*} [Group X] {S : Set X} {y : X}
    (h : ∀ x ∈ S, y * x * y⁻¹ ∈ Subgroup.closure S)
    (h' : ∀ x ∈ S, y⁻¹ * x * y ∈ Subgroup.closure S) :
    y ∈ Subgroup.normalizer (Subgroup.closure S : Set X) := by
  refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨conj_mem_closure_of h, fun hv => ?_⟩
  have := conj_mem_closure_of (g := y⁻¹) (by simpa using h') hv
  simpa [mul_assoc] using this

private theorem exists_involution_lift {X : Type*} [Group X]
    (hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1) {ρ : X ⧸ Subgroup.center X} (hρ : ρ * ρ = 1) :
    ∃ r : X, r * r = 1 ∧ (QuotientGroup.mk r : X ⧸ Subgroup.center X) = ρ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ρ
  have hx2 : x * x ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hρ
  have h6 : (x * x) ^ 3 = 1 := hZ3 _ hx2
  refine ⟨x ^ 3, ?_, ?_⟩
  · calc x ^ 3 * x ^ 3 = (x * x) ^ 3 := ((Commute.refl x).mul_pow 3).symm
      _ = 1 := h6
  · rw [QuotientGroup.mk_pow, pow_three, hρ, mul_one]

private theorem exists_isPGroup_normalized {X : Type*} [Group X]
    (hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1) {y r : X} (hy3 : y ^ 3 = 1) (hr2 : r * r = 1)
    (hr1 : r ≠ 1) (hrc : r * (y * r * y⁻¹) * r⁻¹ * (y * r * y⁻¹)⁻¹ ∈ Subgroup.center X) :
    ∃ V : Subgroup X, IsPGroup 2 V ∧ V ≠ ⊥ ∧ y ∈ Subgroup.normalizer (V : Set X) := by
  have hyy : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hy3)
  have hyy2 : y⁻¹ * y⁻¹ = y := by rw [← mul_inv_rev, ← hyy, inv_inv]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = y * r * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = y⁻¹ * r * y := ⟨_, rfl⟩
  rw [← hc₁] at hrc
  have hconj : ∀ g u v : X, u * v = v * u →
      (g * u * g⁻¹) * (g * v * g⁻¹) = (g * v * g⁻¹) * (g * u * g⁻¹) := by
    intro g u v huv
    calc (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * (v * u) * g⁻¹ := by rw [huv]
      _ = (g * v * g⁻¹) * (g * u * g⁻¹) := by group
  have hrc₁ : r * c₁ = c₁ * r := commute_of_commutator_mem_center hZ3 hr2 hrc
  have hyr : y * r * y⁻¹ = c₁ := hc₁.symm
  have hyc₁ : y * c₁ * y⁻¹ = c₂ := by
    rw [hc₁, hc₂]
    calc y * (y * r * y⁻¹) * y⁻¹ = y * y * r * (y⁻¹ * y⁻¹) := by group
      _ = y⁻¹ * r * y := by rw [← hyy, hyy2]
  have hyc₂ : y * c₂ * y⁻¹ = r := by rw [hc₂]; group
  have hyr' : y⁻¹ * r * y = c₂ := hc₂.symm
  have hyc₁' : y⁻¹ * c₁ * y = r := by rw [hc₁]; group
  have hyc₂' : y⁻¹ * c₂ * y = c₁ := by
    rw [hc₂, hc₁]
    calc y⁻¹ * (y⁻¹ * r * y) * y = (y⁻¹ * y⁻¹) * r * (y * y) := by group
      _ = y * r * y⁻¹ := by rw [hyy2, ← hyy]
  have hc₁c₂ : c₁ * c₂ = c₂ * c₁ := by
    have := hconj y r c₁ hrc₁
    rwa [hyr, hyc₁] at this
  have hc₂r : c₂ * r = r * c₂ := by
    have := hconj y⁻¹ r c₁ hrc₁
    rwa [inv_inv, hyr', hyc₁'] at this
  have hc₁sq : c₁ * c₁ = 1 := by
    rw [hc₁]
    calc y * r * y⁻¹ * (y * r * y⁻¹) = y * (r * r) * y⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hc₂sq : c₂ * c₂ = 1 := by
    rw [hc₂]
    calc y⁻¹ * r * y * (y⁻¹ * r * y) = y⁻¹ * (r * r) * y := by group
      _ = 1 := by rw [hr2]; group
  have hrV : r ∈ Subgroup.closure ({r, c₁, c₂} : Set X) :=
    Subgroup.subset_closure (by simp)
  have hc₁V : c₁ ∈ Subgroup.closure ({r, c₁, c₂} : Set X) :=
    Subgroup.subset_closure (by simp)
  have hc₂V : c₂ ∈ Subgroup.closure ({r, c₁, c₂} : Set X) :=
    Subgroup.subset_closure (by simp)
  refine ⟨Subgroup.closure {r, c₁, c₂}, isPGroup_closure_of_comm_sq ?_ ?_, ?_,
    mem_normalizer_closure ?_ ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    · exact hr2
    · exact hc₁sq
    · exact hc₂sq
  · intro x hx x' hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with h | h | h <;> rcases hx' with h' | h' | h' <;> rw [h, h'] <;>
      first | rfl | exact hrc₁ | exact hrc₁.symm | exact hc₂r | exact hc₂r.symm |
        exact hc₁c₂ | exact hc₁c₂.symm
  · intro h
    apply hr1
    rw [h] at hrV
    exact Subgroup.mem_bot.mp hrV
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    · rwa [hyr]
    · rwa [hyc₁]
    · rwa [hyc₂]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    · rwa [hyr']
    · rwa [hyc₁']
    · rwa [hyc₂']

theorem exists_two_subgroup_normalized_of_pow_three {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) {y : X} (hy3 : y ^ 3 = 1)
    (hyZ : y ∉ Subgroup.center X) :
    ∃ V : Subgroup X, IsPGroup 2 V ∧ V ≠ ⊥ ∧ y ∈ Subgroup.normalizer (V : Set X) := by
  obtain ⟨hZ, ⟨e⟩⟩ := hX
  obtain ⟨ψ⟩ := QuasithinUnique.Out21.A6.exists_psl29_equiv
  have hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz
    rw [hZ] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  let φ : X ⧸ Subgroup.center X ≃* ↥A6Models.psl29 := e.trans ψ.symm
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπ1 : ∀ z : X, π z = 1 ↔ z ∈ Subgroup.center X := fun z => QuotientGroup.eq_one_iff z
  obtain ⟨a, hφy⟩ : ∃ a : ↥A6Models.psl29, φ (π y) = a := ⟨_, rfl⟩
  have ha3 : a ^ 3 = 1 := by rw [← hφy, ← map_pow, ← map_pow, hy3, map_one, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hyZ
    rw [← hπ1]
    apply φ.injective
    rw [hφy, h, map_one]
  obtain ⟨ρ, hρ2, hρ1, hρc⟩ := exists_commuting_involution' a ha3 ha1
  obtain ⟨r, hr2, hrπ⟩ := exists_involution_lift hZ3 (ρ := φ.symm ρ)
    (by rw [← map_mul, hρ2, map_one])
  have hφr : φ (π r) = ρ := by
    rw [show π r = φ.symm ρ from hrπ]
    exact φ.apply_symm_apply ρ
  have hr1 : r ≠ 1 := by
    intro h
    apply hρ1
    rw [← hφr, h, map_one, map_one]
  have hcomm : r * (y * r * y⁻¹) * r⁻¹ * (y * r * y⁻¹)⁻¹ ∈ Subgroup.center X := by
    rw [← hπ1]
    apply φ.injective
    simp only [map_mul, map_inv, map_one, hφr, hφy]
    have := commutatorElement_eq_one_iff_mul_comm.mpr hρc
    rwa [commutatorElement_def] at this
  exact exists_isPGroup_normalized hZ3 hy3 hr2 hr1 hcomm

theorem exists_pow_three_le_normalizer_two {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    ∃ y : X, y ^ 3 = 1 ∧ y ∉ Subgroup.center X ∧ ∃ V : Subgroup X, IsPGroup 2 V ∧ V ≠ ⊥ ∧
      y ∈ Subgroup.normalizer (V : Set X) := by
  obtain ⟨y, hy3, hyZ⟩ := Sylow155NO.exists_pow_three_not_mem_center hX
  exact ⟨y, hy3, hyZ, exists_two_subgroup_normalized_of_pow_three hX hy3 hyZ⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
