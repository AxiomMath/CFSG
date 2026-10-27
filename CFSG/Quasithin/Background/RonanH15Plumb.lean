module

public import CFSG.Quasithin.Background.RonanH15Trans

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem nonempty_equiv_of_mem_iff {Γ : Subgroup (Equiv.Perm (Fin 24))} {C : Subgroup ↥Γ}
    {T : Subgroup (Equiv.Perm (Fin 24))} (hT : T ≤ Γ)
    (h : ∀ g : ↥Γ, g ∈ C ↔ (g : Equiv.Perm (Fin 24)) ∈ T) : Nonempty (↥C ≃* ↥T) := by
  have hC : C = T.subgroupOf Γ := by
    ext g
    rw [h g, Subgroup.mem_subgroupOf]
  exact ⟨(MulEquiv.subgroupCongr hC).trans (Subgroup.subgroupOfEquivOfLe hT)⟩

theorem exists_index_two_equiv {Γ : Subgroup (Equiv.Perm (Fin 24))} {C : Subgroup ↥Γ}
    {T T' : Subgroup (Equiv.Perm (Fin 24))} (hT : T ≤ Γ)
    (h : ∀ g : ↥Γ, g ∈ C ↔ (g : Equiv.Perm (Fin 24)) ∈ T) (hT' : T' ≤ T)
    (hidx : T'.relIndex T = 2) : ∃ N : Subgroup ↥C, N.index = 2 ∧ Nonempty (↥N ≃* ↥T') := by
  have hC : C = T.subgroupOf Γ := by
    ext g
    rw [h g, Subgroup.mem_subgroupOf]
  have hT'Γ : T' ≤ Γ := hT'.trans hT
  have hQC : T'.subgroupOf Γ ≤ C := by
    rw [hC]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hT' hx
  refine ⟨(T'.subgroupOf Γ).subgroupOf C, ?_, ?_⟩
  · show (T'.subgroupOf Γ).relIndex C = 2
    rw [hC, Subgroup.relIndex_subgroupOf hT, hidx]
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hQC).trans (Subgroup.subgroupOfEquivOfLe hT'Γ)⟩

theorem relIndex_stab_eq_two {a b j : Fin 24} (hab : a ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hKΓ : AutPerm ⊓ stab a ⊓ stab b ≤ Γ)
    (hΓP : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) ({a, b} : Finset (Fin 24)))
    (hne : Γ ≠ AutPerm ⊓ stab a ⊓ stab b) :
    (AutPerm ⊓ stab a ⊓ stab b ⊓ stab j).relIndex (Γ ⊓ stab j) = 2 := by
  have hKmem : ∀ y : Equiv.Perm (Fin 24),
      y ∈ AutPerm ⊓ stab a ⊓ stab b ↔ y ∈ AutPerm ∧ y a = a ∧ y b = b := by
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stab_iff, mem_stab_iff, and_assoc]
  have hAP : ∀ y : Equiv.Perm (Fin 24), y ∈ Γ → y ∈ AutPerm := fun y hy =>
    (Subgroup.mem_inf.1 (hΓP hy)).1
  have hswap : ∀ y : Equiv.Perm (Fin 24), y ∈ Γ →
      (y a = a ∧ y b = b) ∨ (y a = b ∧ y b = a) := by
    intro y hy
    have hstab := (Subgroup.mem_inf.1 (hΓP hy)).2
    have key : ∀ x : Fin 24, x ∈ ({a, b} : Finset (Fin 24)) →
        y x ∈ ({a, b} : Finset (Fin 24)) := by
      intro x hx
      have hm : y x ∈ y • ({a, b} : Finset (Fin 24)) := Finset.mem_smul_finset.2 ⟨x, hx, rfl⟩
      rwa [MulAction.mem_stabilizer_iff.1 hstab] at hm
    have ha := key a (by simp)
    have hb := key b (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (y.injective (ha.trans hb.symm)) hab
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (y.injective (ha.trans hb.symm)) hab
  obtain ⟨s, hsΓ, hsK⟩ : ∃ s : Equiv.Perm (Fin 24),
      s ∈ Γ ∧ s ∉ AutPerm ⊓ stab a ⊓ stab b := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm (fun s hs => hc s hs) hKΓ)
  have hsab : s a = b ∧ s b = a := by
    rcases hswap s hsΓ with h | h
    · exact absurd ((hKmem s).2 ⟨hAP s hsΓ, h.1, h.2⟩) hsK
    · exact h
  have hsja : s j ≠ a := fun h => hjb (s.injective (h.trans hsab.2.symm))
  have hsjb : s j ≠ b := fun h => hja (s.injective (h.trans hsab.1.symm))
  obtain ⟨m, hmK, hmj⟩ := exists_mem_stab_stab_maps hab hsja hsjb hja hjb
  obtain ⟨hmAP, hma, hmb⟩ := (hKmem m).1 hmK
  have hmsΓ : m * s ∈ Γ := Γ.mul_mem (hKΓ hmK) hsΓ
  have hmsj : (m * s) j = j := by rw [Equiv.Perm.mul_apply, hmj]
  have hmsAP : m * s ∈ AutPerm := AutPerm.mul_mem hmAP (hAP s hsΓ)
  have hfix : ∀ z : Equiv.Perm (Fin 24), z ∈ AutPerm ⊓ stab a ⊓ stab b ⊓ stab j → z a = a :=
    fun z hz => ((hKmem z).1 (Subgroup.mem_inf.1 hz).1).2.1
  have hPmem : ∀ z : Equiv.Perm (Fin 24), z ∈ AutPerm → z a = a → z b = b → z j = j →
      z ∈ AutPerm ⊓ stab a ⊓ stab b ⊓ stab j := fun z hz hza hzb hzj =>
    Subgroup.mem_inf.2 ⟨(hKmem z).2 ⟨hz, hza, hzb⟩, (mem_stab_iff j z).2 hzj⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨m * s, Subgroup.mem_inf.2 ⟨hmsΓ, (mem_stab_iff j _).2 hmsj⟩⟩, fun y => ?_⟩
  obtain ⟨yΓ, yj⟩ := Subgroup.mem_inf.1 y.2
  have yj' : (y : Equiv.Perm (Fin 24)) j = j := (mem_stab_iff j _).1 yj
  rcases hswap _ yΓ with ⟨hya, hyb⟩ | ⟨hya, hyb⟩
  ·
    have hP := hPmem _ (hAP _ yΓ) hya hyb yj'
    refine Or.inr ⟨hP, fun hQ => ?_⟩
    have h := hfix ((y : Equiv.Perm (Fin 24)) * (m * s)) hQ
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsab.1, hmb, hyb] at h
    exact hab h.symm
  ·
    have hQa : ((y : Equiv.Perm (Fin 24)) * (m * s)) a = a := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsab.1, hmb, hyb]
    have hQb : ((y : Equiv.Perm (Fin 24)) * (m * s)) b = b := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsab.2, hma, hya]
    have hQj : ((y : Equiv.Perm (Fin 24)) * (m * s)) j = j := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hmj, yj']
    have hQ := hPmem _ (AutPerm.mul_mem (hAP _ yΓ) hmsAP) hQa hQb hQj
    refine Or.inl ⟨hQ, fun hP => ?_⟩
    have h := hfix (y : Equiv.Perm (Fin 24)) hP
    rw [hya] at h
    exact hab h.symm

end CFSG.Quasithin.RonanH15
