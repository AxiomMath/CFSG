module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

structure C23Core {U : Type*} [CommGroup U] (Y₁ Y₂ : Subgroup U)
    (A₁ A₂ Mb : Subgroup (MulAut U)) : Prop where
  card₁ : Nat.card Y₁ = 8
  card₂ : Nat.card Y₂ = 8
  inf_eq : Y₁ ⊓ Y₂ = ⊥
  sup_eq : Y₁ ⊔ Y₂ = ⊤
  card_A₁ : Nat.card A₁ = 168
  card_A₂ : Nat.card A₂ = 168
  triv₁ : ∀ a ∈ A₁, ∀ y ∈ Y₂, (a : MulAut U) y = y
  triv₂ : ∀ a ∈ A₂, ∀ y ∈ Y₁, (a : MulAut U) y = y
  trans₁ : ∀ y ∈ Y₁, y ≠ 1 → ∀ y' ∈ Y₁, y' ≠ 1 → ∃ a ∈ A₁, (a : MulAut U) y = y'
  trans₂ : ∀ y ∈ Y₂, y ≠ 1 → ∀ y' ∈ Y₂, y' ≠ 1 → ∃ a ∈ A₂, (a : MulAut U) y = y'
  le₁ : A₁ ≤ Mb
  le₂ : A₂ ≤ Mb
  perm : ∀ φ ∈ Mb, (Y₁.map φ.toMonoidHom = Y₁ ∧ Y₂.map φ.toMonoidHom = Y₂) ∨
    (Y₁.map φ.toMonoidHom = Y₂ ∧ Y₂.map φ.toMonoidHom = Y₁)

@[expose] def c23Omega {U : Type*} [CommGroup U] (Y₁ Y₂ : Subgroup U) : Set U :=
  {u | u ∉ Y₁ ∧ u ∉ Y₂}

variable {U : Type*} [CommGroup U] [Finite U] {Y₁ Y₂ : Subgroup U}
  {A₁ A₂ Mb : Subgroup (MulAut U)}

theorem c23_core_map_eq₁ (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {a : MulAut U} (ha : a ∈ A₁) :
    Y₁.map a.toMonoidHom = Y₁ := by
  rcases h.perm a (h.le₁ ha) with ⟨h1, _⟩ | ⟨_, h12⟩
  · exact h1
  · exfalso
    have hfix2 : Y₂.map a.toMonoidHom = Y₂ := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        show (a : MulAut U) x ∈ Y₂
        rw [h.triv₁ a ha x hx]
        exact hx
      · intro y hy
        exact Subgroup.mem_map.mpr ⟨y, hy, by simpa using h.triv₁ a ha y hy⟩
    have heq : Y₁ = Y₂ := by rw [← h12, hfix2]
    have hbot : Y₁ = ⊥ := by
      have hY : Y₁ = Y₁ ⊓ Y₂ := by rw [heq, inf_idem]
      rw [hY, h.inf_eq]
    have hc : Nat.card Y₁ = 1 := by rw [hbot, Subgroup.card_bot]
    have hc8 : Nat.card Y₁ = 8 := h.card₁
    rw [hc] at hc8
    norm_num at hc8

theorem c23_core_map_eq₂ (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {a : MulAut U} (ha : a ∈ A₂) :
    Y₂.map a.toMonoidHom = Y₂ := by
  rcases h.perm a (h.le₂ ha) with ⟨_, h2⟩ | ⟨h12, _⟩
  · exact h2
  · exfalso
    have hfix1 : Y₁.map a.toMonoidHom = Y₁ := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        show (a : MulAut U) x ∈ Y₁
        rw [h.triv₂ a ha x hx]
        exact hx
      · intro y hy
        exact Subgroup.mem_map.mpr ⟨y, hy, by simpa using h.triv₂ a ha y hy⟩
    have heq : Y₁ = Y₂ := by rw [← h12, hfix1]
    have hbot : Y₁ = ⊥ := by
      have hY : Y₁ = Y₁ ⊓ Y₂ := by rw [heq, inf_idem]
      rw [hY, h.inf_eq]
    have hc : Nat.card Y₁ = 1 := by rw [hbot, Subgroup.card_bot]
    have hc8 : Nat.card Y₁ = 8 := h.card₁
    rw [hc] at hc8
    norm_num at hc8

theorem c23_core_commute (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {a b : MulAut U} (ha : a ∈ A₁)
    (hb : b ∈ A₂) : a * b = b * a := by
  refine MulEquiv.ext fun u => ?_
  have hu : u ∈ Y₁ ⊔ Y₂ := by rw [h.sup_eq]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
  simp only [MulAut.mul_apply]
  have hbz : (b : MulAut U) z ∈ Y₂ := by
    have hmem : (b : MulAut U) z ∈ Y₂.map b.toMonoidHom :=
      Subgroup.mem_map_of_mem b.toMonoidHom hz
    rwa [c23_core_map_eq₂ h hb] at hmem
  have hay : (a : MulAut U) y ∈ Y₁ := by
    have hmem : (a : MulAut U) y ∈ Y₁.map a.toMonoidHom :=
      Subgroup.mem_map_of_mem a.toMonoidHom hy
    rwa [c23_core_map_eq₁ h ha] at hmem
  simp only [map_mul, h.triv₂ b hb y hy, h.triv₁ a ha ((b : MulAut U) z) hbz,
    h.triv₁ a ha z hz, h.triv₂ b hb ((a : MulAut U) y) hay]

theorem c23_core_inf_A_eq_bot (h : C23Core Y₁ Y₂ A₁ A₂ Mb) : A₁ ⊓ A₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro φ hφ
  rw [Subgroup.mem_inf] at hφ
  refine MulEquiv.ext fun u => ?_
  have hu : u ∈ Y₁ ⊔ Y₂ := by rw [h.sup_eq]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
  change (φ : MulAut U) (y * z) = y * z
  rw [map_mul, h.triv₂ φ hφ.2 y hy, h.triv₁ φ hφ.1 z hz]

theorem c23_core_card_sup (h : C23Core Y₁ Y₂ A₁ A₂ Mb) : Nat.card ↥(A₁ ⊔ A₂) = 168 * 168 := by
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x :=
    fun x hx y hy => c23_core_commute h hx hy
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcomm).1
  rw [c23_core_inf_A_eq_bot h, Subgroup.card_bot, h.card_A₁, h.card_A₂] at hprod
  omega

theorem c23_core_card_top (h : C23Core Y₁ Y₂ A₁ A₂ Mb) : Nat.card U = 64 := by
  have hcomm : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y = y * x := fun x _ y _ => mul_comm x y
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Y₁ Y₂ hcomm).1
  rw [h.sup_eq, h.inf_eq, Subgroup.card_top, Subgroup.card_bot, h.card₁, h.card₂] at hprod
  omega

theorem c23_ncard_omega (h : C23Core Y₁ Y₂ A₁ A₂ Mb) : (c23Omega Y₁ Y₂).ncard = 49 := by
  have hcompl : c23Omega Y₁ Y₂ = ((Y₁ : Set U) ∪ (Y₂ : Set U))ᶜ := by
    ext u
    simp [c23Omega]
  have h1 : (Y₁ : Set U).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact h.card₁
  have h2 : (Y₂ : Set U).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact h.card₂
  have hinter : ((Y₁ : Set U) ∩ (Y₂ : Set U)).ncard = 1 := by
    have hcoe : (Y₁ : Set U) ∩ (Y₂ : Set U) = ((Y₁ ⊓ Y₂ : Subgroup U) : Set U) :=
      (Subgroup.coe_inf Y₁ Y₂).symm
    rw [hcoe, h.inf_eq, Subgroup.coe_bot, Set.ncard_singleton]
  have hunion : ((Y₁ : Set U) ∪ (Y₂ : Set U)).ncard = 15 := by
    have hsum := Set.ncard_union_add_ncard_inter (Y₁ : Set U) (Y₂ : Set U)
    rw [hinter, h1, h2] at hsum
    omega
  rw [hcompl, Set.ncard_compl, c23_core_card_top h, hunion]

theorem c23_omega_stable (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {φ : MulAut U} (hφ : φ ∈ Mb) {u : U}
    (hu : u ∈ c23Omega Y₁ Y₂) : φ u ∈ c23Omega Y₁ Y₂ := by
  simp only [c23Omega, Set.mem_setOf_eq] at hu ⊢
  rcases h.perm φ hφ with ⟨h1, h2⟩ | ⟨h12, h21⟩
  · refine ⟨?_, ?_⟩
    · intro hmem
      apply hu.1
      have hmem' : φ u ∈ Y₁.map φ.toMonoidHom := by rwa [h1]
      rw [Subgroup.mem_map_equiv] at hmem'
      simpa using hmem'
    · intro hmem
      apply hu.2
      have hmem' : φ u ∈ Y₂.map φ.toMonoidHom := by rwa [h2]
      rw [Subgroup.mem_map_equiv] at hmem'
      simpa using hmem'
  · refine ⟨?_, ?_⟩
    · intro hmem
      apply hu.2
      have hmem' : φ u ∈ Y₂.map φ.toMonoidHom := by rwa [h21]
      rw [Subgroup.mem_map_equiv] at hmem'
      simpa using hmem'
    · intro hmem
      apply hu.1
      have hmem' : φ u ∈ Y₁.map φ.toMonoidHom := by rwa [h12]
      rw [Subgroup.mem_map_equiv] at hmem'
      simpa using hmem'

theorem c23_omega_trans (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {u u' : U} (hu : u ∈ c23Omega Y₁ Y₂)
    (hu' : u' ∈ c23Omega Y₁ Y₂) : ∃ a ∈ A₁, ∃ b ∈ A₂, (a : MulAut U) ((b : MulAut U) u) = u' := by
  simp only [c23Omega, Set.mem_setOf_eq] at hu hu'
  obtain ⟨y₁, hy₁, y₂, hy₂, hy_eq⟩ :=
    Subgroup.mem_sup.mp (by rw [h.sup_eq]; trivial : u ∈ Y₁ ⊔ Y₂)
  obtain ⟨y₁', hy₁', y₂', hy₂', hy'_eq⟩ :=
    Subgroup.mem_sup.mp (by rw [h.sup_eq]; trivial : u' ∈ Y₁ ⊔ Y₂)
  have hy₂ne : y₂ ≠ 1 := by
    intro h2
    apply hu.1
    rw [← hy_eq, h2, mul_one]
    exact hy₁
  have hy₁ne : y₁ ≠ 1 := by
    intro h1
    apply hu.2
    rw [← hy_eq, h1, one_mul]
    exact hy₂
  have hy₂'ne : y₂' ≠ 1 := by
    intro h2
    apply hu'.1
    rw [← hy'_eq, h2, mul_one]
    exact hy₁'
  have hy₁'ne : y₁' ≠ 1 := by
    intro h1
    apply hu'.2
    rw [← hy'_eq, h1, one_mul]
    exact hy₂'
  obtain ⟨a, ha, ha_eq⟩ := h.trans₁ y₁ hy₁ hy₁ne y₁' hy₁' hy₁'ne
  obtain ⟨b, hb, hb_eq⟩ := h.trans₂ y₂ hy₂ hy₂ne y₂' hy₂' hy₂'ne
  refine ⟨a, ha, b, hb, ?_⟩
  have hbz : (b : MulAut U) y₂ ∈ Y₂ := by
    have hmem : (b : MulAut U) y₂ ∈ Y₂.map b.toMonoidHom :=
      Subgroup.mem_map_of_mem b.toMonoidHom hy₂
    rwa [c23_core_map_eq₂ h hb] at hmem
  calc (a : MulAut U) ((b : MulAut U) u)
      = (a : MulAut U) ((b : MulAut U) (y₁ * y₂)) := by rw [← hy_eq]
    _ = (a : MulAut U) ((b : MulAut U) y₁ * (b : MulAut U) y₂) := by rw [map_mul]
    _ = (a : MulAut U) (y₁ * (b : MulAut U) y₂) := by rw [h.triv₂ b hb y₁ hy₁]
    _ = (a : MulAut U) y₁ * (a : MulAut U) ((b : MulAut U) y₂) := by rw [map_mul]
    _ = y₁' * (b : MulAut U) y₂ := by rw [ha_eq, h.triv₁ a ha ((b : MulAut U) y₂) hbz]
    _ = y₁' * y₂' := by rw [hb_eq]
    _ = u' := by rw [hy'_eq]

theorem c23_exists_fixed_omega (h : C23Core Y₁ Y₂ A₁ A₂ Mb)
    {Tb : Subgroup (MulAut U)} (hTb : Tb ≤ Mb) (hT : IsPGroup 2 Tb) :
    ∃ u ∈ c23Omega Y₁ Y₂, ∀ t ∈ Tb, (t : MulAut U) u = u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ : ∀ g : ↥Tb, ∀ y ∈ c23Omega Y₁ Y₂,
      ((MulAut.toPerm U).comp Tb.subtype) g y ∈ c23Omega Y₁ Y₂ := by
    intro g y hy
    show (g : MulAut U) y ∈ c23Omega Y₁ Y₂
    exact c23_omega_stable h (hTb g.2) hy
  have hcard : ¬ 2 ∣ Nat.card (c23Omega Y₁ Y₂) := by
    rw [Nat.card_coe_set_eq, c23_ncard_omega h]
    norm_num
  obtain ⟨u, hu, hfix⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof.exists_fixed_of_invariant
      (P := ↥Tb) (Y := U) (p := 2) hT ((MulAut.toPerm U).comp Tb.subtype)
      (c23Omega Y₁ Y₂) hΩ hcard
  exact ⟨u, hu, fun t ht => by
    show (t : MulAut U) u = u
    exact hfix ⟨t, ht⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
