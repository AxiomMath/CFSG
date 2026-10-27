module

public import CFSG.Quasithin.Vol2.Ch10SecG31C

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

structure IsMaxFull (Δ : Set W) (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W))
    (P : Submodule (ZMod 2) W) : Prop where
  full : IsFull Δ F P
  exists_ne : ∃ x ∈ P, x ≠ 0
  faithful : ∀ x ∈ P, x ≠ 0 → ∀ φ ∈ F x, (∀ u ∈ P, φ u = 0) → φ = 0

theorem not_mem_C_of_isFull {Δ : Set W} {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}
    {P : Submodule (ZMod 2) W} (hP : IsFull Δ F P) {u v : W} (hu : u ∈ P) (hv : v ∈ P)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) : v ∉ C F u := by
  intro h
  have hmem : v ∈ Submodule.span (ZMod 2) {u} := (hP u hu hu0).2 ▸ ⟨h, hv⟩
  rcases mem_span_singleton_iff_two.1 hmem with h1 | h1
  · exact hv0 h1
  · exact huv h1.symm

namespace Hyp

variable {G : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)} [Finite W]

theorem inf_C_add_eq (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hP : IsFull Δ F P) {x x' : W}
    (hx : x ∈ P) (hx' : x' ∈ P) (h0 : x ≠ 0) (h0' : x' ≠ 0) (hxx' : x ≠ x') :
    C F x ⊓ C F x' = C F x ⊓ C F (x + x') := by
  have hxΔ := (hP x hx h0).1
  have hx'Δ := (hP x' hx' h0').1
  have he := not_mem_C_of_isFull hP hx hx' h0 h0' hxx'
  have hs : x + x' ∈ P := P.add_mem hx hx'
  have hs0 : x + x' ≠ 0 := fun h => hxx' (by rwa [two_add_eq_iff, zero_add] at h)
  have hxs : x ≠ x + x' := fun h => h0' (by simpa using h.symm)
  refine le_antisymm (le_inf inf_le_left (hH.inf_le_C_add hxΔ hx'Δ he)) ?_
  have he' := not_mem_C_of_isFull hP hx hs h0 hs0 hxs
  refine le_inf inf_le_left ?_
  have := hH.inf_le_C_add hxΔ (hP _ hs hs0).1 he'
  rwa [← add_assoc, two_add_self, zero_add] at this

theorem inf_C_le_C (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hP : IsFull Δ F P)
    {x x' x'' : W} (hx : x ∈ P) (hx' : x' ∈ P) (hx'' : x'' ∈ P) (h0 : x ≠ 0) (h0' : x' ≠ 0)
    (h0'' : x'' ≠ 0) (hxx' : x ≠ x') (hxx'' : x ≠ x'') (hx'x'' : x' ≠ x'')
    (hsum : x'' ≠ x + x') : C F x ⊓ C F x' ≤ C F x'' := by
  have hxΔ := (hP x hx h0).1
  have hx''Δ := (hP x'' hx'' h0'').1
  rintro d ⟨hdx, hdx'⟩
  obtain ⟨e₁, he₁, e, ⟨-, he⟩, hde⟩ := Submodule.mem_sup.1
    (hH.C_le_sup hxΔ hx''Δ (not_mem_C_of_isFull hP hx hx'' h0 h0'' hxx'') hdx)
  rcases mem_span_singleton_iff_two.1 he₁ with h1 | h1
  · rw [← hde, h1, zero_add]
    exact he
  rw [h1] at hde
  obtain ⟨f₁, hf₁, f, ⟨-, hf⟩, hef⟩ := Submodule.mem_sup.1
    (hH.C_le_sup hx''Δ (hP x' hx' h0').1
      (not_mem_C_of_isFull hP hx'' hx' h0'' h0' (Ne.symm hx'x'')) he)
  exfalso
  rcases mem_span_singleton_iff_two.1 hf₁ with h2 | h2
  ·
    rw [h2, zero_add] at hef
    refine not_mem_C_of_isFull hP hx' hx h0' h0 (Ne.symm hxx') ?_
    have := (C F x').sub_mem hdx' (hef ▸ hf)
    rwa [← hde, add_sub_cancel_right] at this
  ·
    rw [h2] at hef
    have hmem : x + x'' ∈ C F x' := by
      have := (C F x').sub_mem hdx' hf
      rwa [← hde, ← hef, ← add_assoc, add_sub_cancel_right] at this
    have hs : x + x'' ∈ Submodule.span (ZMod 2) {x'} :=
      (hP x' hx' h0').2 ▸ ⟨hmem, P.add_mem hx hx''⟩
    rcases mem_span_singleton_iff_two.1 hs with h3 | h3
    · exact hxx'' (by rwa [two_add_eq_iff, zero_add] at h3)
    · exact hsum (by rw [← h3, ← add_assoc, two_add_self, zero_add])

theorem inf_C_eq (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hP : IsFull Δ F P)
    {x x' x'' : W} (hx : x ∈ P) (hx' : x' ∈ P) (hx'' : x'' ∈ P) (h0 : x ≠ 0) (h0' : x' ≠ 0)
    (h0'' : x'' ≠ 0) (hxx' : x ≠ x') (hxx'' : x ≠ x'') :
    C F x ⊓ C F x' = C F x ⊓ C F x'' := by
  by_cases h1 : x'' = x'
  · rw [h1]
  by_cases h2 : x'' = x + x'
  · rw [h2]
    exact hH.inf_C_add_eq hP hx hx' h0 h0' hxx'
  have h3 : x' ≠ x + x'' := fun h => h2 (by rw [h, ← add_assoc, two_add_self, zero_add])
  exact le_antisymm
    (le_inf inf_le_left (hH.inf_C_le_C hP hx hx' hx'' h0 h0' h0'' hxx' hxx'' (Ne.symm h1) h2))
    (le_inf inf_le_left (hH.inf_C_le_C hP hx hx'' hx' h0 h0'' h0' hxx'' hxx' h1 h3))

theorem sup_C_eq_top (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hM : IsMaxFull Δ F P)
    {x : W} (hxP : x ∈ P) (hx0 : x ≠ 0) : P ⊔ C F x = ⊤ := by
  have _ := hH
  rw [← Submodule.dualAnnihilator_eq_bot_iff, Submodule.dualAnnihilator_sup_eq,
    Subspace.dualCoannihilator_dualAnnihilator_eq]
  refine (Submodule.eq_bot_iff _).2 fun φ hφ => hM.faithful x hxP hx0 φ hφ.2 fun u hu =>
    (Submodule.mem_dualAnnihilator φ).1 hφ.1 u hu

theorem finrank_F_add_one (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hM : IsMaxFull Δ F P)
    {x : W} (hxP : x ∈ P) (hx0 : x ≠ 0) :
    finrank (ZMod 2) (F x) + 1 = finrank (ZMod 2) P := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P (C F x)
  rw [hH.sup_C_eq_top hM hxP hx0, finrank_top, inf_comm, (hM.full x hxP hx0).2,
    finrank_span_singleton hx0] at h1
  have h2 : finrank (ZMod 2) (F x) + finrank (ZMod 2) (C F x) = finrank (ZMod 2) W :=
    Subspace.finrank_add_finrank_dualCoannihilator_eq (F x)
  omega

section D

variable (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hM : IsMaxFull Δ F P) {x₁ x₂ : W}
  (hx₁ : x₁ ∈ P) (hx₂ : x₂ ∈ P) (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h₁₂ : x₁ ≠ x₂)
include hH hM hx₁ hx₂ h₁ h₂ h₁₂

theorem D_le_C {x : W} (hx : x ∈ P) (h0 : x ≠ 0) : C F x₁ ⊓ C F x₂ ≤ C F x := by
  by_cases hx1 : x = x₁
  · rw [hx1]
    exact inf_le_left
  rw [hH.inf_C_eq hM.full hx₁ hx₂ hx h₁ h₂ h0 h₁₂ (Ne.symm hx1)]
  exact inf_le_right

theorem C_le_sup_D {x : W} (hx : x ∈ P) (h0 : x ≠ 0) :
    C F x ≤ Submodule.span (ZMod 2) {x} ⊔ (C F x₁ ⊓ C F x₂) := by
  by_cases hx1 : x = x₁
  · rw [hx1]
    exact hH.C_le_sup (hM.full x₁ hx₁ h₁).1 (hM.full x₂ hx₂ h₂).1
      (not_mem_C_of_isFull hM.full hx₁ hx₂ h₁ h₂ h₁₂)
  have := hH.C_le_sup (hM.full x hx h0).1 (hM.full x₁ hx₁ h₁).1
    (not_mem_C_of_isFull hM.full hx hx₁ h0 h₁ hx1)
  rwa [inf_comm (C F x), hH.inf_C_eq hM.full hx₁ hx hx₂ h₁ h0 h₂ (Ne.symm hx1) h₁₂] at this

omit [Finite W] hH in
theorem inf_D_eq_bot : P ⊓ (C F x₁ ⊓ C F x₂) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
  have hmem : w ∈ Submodule.span (ZMod 2) {x₁} := (hM.full x₁ hx₁ h₁).2 ▸ ⟨hw.2.1, hw.1⟩
  rcases mem_span_singleton_iff_two.1 hmem with h | h
  · exact h
  · exact absurd (h ▸ hw.2.2) (not_mem_C_of_isFull hM.full hx₂ hx₁ h₂ h₁ (Ne.symm h₁₂))

theorem sup_D_eq_top : P ⊔ (C F x₁ ⊓ C F x₂) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← hH.sup_C_eq_top hM hx₁ h₁]
  refine sup_le le_sup_left
    ((hH.C_le_sup_D hM hx₁ hx₂ h₁ h₂ h₁₂ hx₁ h₁).trans (sup_le ?_ le_sup_right))
  exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_sup_left hx₁)

theorem outer (h3 : 3 ≤ finrank (ZMod 2) P) {z : W} (hz : z ∈ Δ) (hzP : z ∉ P) {x : W}
    (hx : x ∈ P) (hx0 : x ≠ 0) (hzx : z ∉ C F x) :
    ∃ p₀ ∈ P, ∃ d₀ ∈ C F x₁ ⊓ C F x₂, z = p₀ + d₀ ∧ p₀ ≠ 0 ∧ d₀ ≠ 0 ∧
      C F x₁ ⊓ C F x₂ ≤ C F z ∧ F z = F p₀ := by
  have hPD := inf_D_eq_bot hM hx₁ hx₂ h₁ h₂ h₁₂
  have hz' : z ∈ P ⊔ (C F x₁ ⊓ C F x₂) := by
    rw [hH.sup_D_eq_top hM hx₁ hx₂ h₁ h₂ h₁₂]
    exact Submodule.mem_top
  obtain ⟨p₀, hp₀, d₀, hd₀, hzpd⟩ := Submodule.mem_sup.1 hz'
  have hcrit : ∀ x' ∈ P, x' ≠ 0 → (z ∈ C F x' ↔ p₀ ∈ Submodule.span (ZMod 2) {x'}) := by
    intro x' hx' hx'0
    constructor
    · intro hzC
      obtain ⟨a', ha', d, hd, had⟩ :=
        Submodule.mem_sup.1 (hH.C_le_sup_D hM hx₁ hx₂ h₁ h₂ h₁₂ hx' hx'0 hzC)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha'
      have hmem : p₀ - a • x' ∈ P ⊓ (C F x₁ ⊓ C F x₂) := by
        refine ⟨P.sub_mem hp₀ (P.smul_mem a hx'), ?_⟩
        have he : p₀ - a • x' = d - d₀ := by
          rw [sub_eq_sub_iff_add_eq_add, hzpd, add_comm d, had]
        rw [he]
        exact Submodule.sub_mem _ hd hd₀
      rw [hPD, Submodule.mem_bot, sub_eq_zero] at hmem
      rw [hmem]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x')
    · intro hp
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hp
      rw [← hzpd]
      exact (C F x').add_mem ((C F x').smul_mem a (hH.self_mem_C (hM.full x' hx' hx'0).1))
        (hH.D_le_C hM hx₁ hx₂ h₁ h₂ h₁₂ hx' hx'0 hd₀)
  have hp0 : p₀ ≠ 0 := fun h => hzx ((hcrit x hx hx0).2 (h ▸ Submodule.zero_mem _))
  have hd0 : d₀ ≠ 0 := fun h => hzP (by rw [← hzpd, h, add_zero]; exact hp₀)
  have hp₀Δ : p₀ ∈ Δ := (hM.full p₀ hp₀ hp0).1
  have hp₀z : p₀ ∈ C F z :=
    hH.mem_C_comm hz hp₀Δ ((hcrit p₀ hp₀ hp0).2 (Submodule.mem_span_singleton_self _))
  obtain ⟨x', hx'P, hx'S⟩ := exists_mem_notMem_of_finrank_lt (U := P)
    (S := Submodule.span (ZMod 2) {p₀, x}) ((finrank_span_pair_le p₀ x).trans_lt (by omega))
  have hx'0 : x' ≠ 0 := fun h => hx'S (h ▸ Submodule.zero_mem _)
  have hzx' : z ∉ C F x' := by
    intro h
    rcases mem_span_singleton_iff_two.1 ((hcrit x' hx'P hx'0).1 h) with h' | h'
    · exact hp0 h'
    · exact hx'S (h' ▸ Submodule.subset_span (Set.mem_insert _ _))
  have hCzP : ∀ u ∈ P, u ≠ 0 → z ∉ C F u → ∀ w ∈ C F z, w ∈ P →
      w ∈ Submodule.span (ZMod 2) {p₀, u} := by
    intro u hu hu0 hzu w hw hwP
    have huz : u ∉ C F z := hH.not_mem_C_comm (hM.full u hu hu0).1 hz hzu
    obtain ⟨a', ha', e, he, hwe⟩ := Submodule.mem_sup.1 (hH.C_le_sup hz (hM.full u hu hu0).1 huz hw)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha'
    obtain ⟨b', hb', d, hd, hed⟩ :=
      Submodule.mem_sup.1 (hH.C_le_sup_D hM hx₁ hx₂ h₁ h₂ h₁₂ hu hu0 he.2)
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hb'
    have hwexp : w = a • p₀ + b • u + (a • d₀ + d) := by
      rw [← hwe, ← hed, ← hzpd, smul_add]
      abel
    have hmem : a • d₀ + d ∈ P ⊓ (C F x₁ ⊓ C F x₂) := by
      refine ⟨?_, Submodule.add_mem _ (Submodule.smul_mem _ a hd₀) hd⟩
      have he' : a • d₀ + d = w - (a • p₀ + b • u) := by
        rw [hwexp]
        abel
      rw [he']
      exact P.sub_mem hwP (P.add_mem (P.smul_mem a hp₀) (P.smul_mem b hu))
    rw [hPD, Submodule.mem_bot] at hmem
    rw [hwexp, hmem, add_zero]
    exact Submodule.mem_span_pair.2 ⟨a, b, rfl⟩
  have hDz : C F x₁ ⊓ C F x₂ ≤ C F z := by
    intro d hd
    by_contra hdz
    have hdC : ∀ u ∈ P, u ≠ 0 → z ∉ C F u → d + u ∈ C F z := by
      intro u hu hu0 hzu
      obtain ⟨a', ha', e, he, hde⟩ := Submodule.mem_sup.1 (hH.C_le_sup (hM.full u hu hu0).1 hz hzu
        (hH.D_le_C hM hx₁ hx₂ h₁ h₂ h₁₂ hu hu0 hd))
      rcases mem_span_singleton_iff_two.1 ha' with h0 | h0
      · exact absurd (by rw [← hde, h0, zero_add]; exact he.2) hdz
      · rw [← hde, h0, add_comm u e, add_assoc, two_add_self, add_zero]
        exact he.2
    have hsum := (C F z).add_mem (hdC x hx hx0 hzx) (hdC x' hx'P hx'0 hzx')
    rw [show d + x + (d + x') = x + x' by rw [add_add_add_comm, two_add_self, zero_add]] at hsum
    have h1 := hCzP x hx hx0 hzx _ hsum (P.add_mem hx hx'P)
    refine hx'S ?_
    have h2 := Submodule.sub_mem _ h1 (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    rwa [add_sub_cancel_left] at h2
  have hCeq : C F z = C F p₀ := by
    have hle : C F p₀ ≤ C F z := (hH.C_le_sup_D hM hx₁ hx₂ h₁ h₂ h₁₂ hp₀ hp0).trans
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hp₀z) hDz)
    exact (Submodule.eq_of_le_of_finrank_eq hle (hH.finrank_C hp₀Δ hz)).symm
  refine ⟨p₀, hp₀, d₀, hd₀, hzpd.symm, hp0, hd0, hDz, ?_⟩
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := F z),
    ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := F p₀)]
  exact congrArg Submodule.dualAnnihilator hCeq

end D

end Hyp

end CFSG.Quasithin.G31
