module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.L3Lat

open Matrix

abbrev Γ := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

abbrev ent (g : Γ) (i j : Fin 3) : ZMod 2 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

@[expose] def inD0 (g : Γ) : Prop :=
  ent g 0 0 = 1 ∧ ent g 1 1 = 1 ∧ ent g 2 2 = 1 ∧ ent g 1 0 = 0 ∧ ent g 2 0 = 0 ∧ ent g 2 1 = 0
@[expose] def inSpt (g : Γ) : Prop := ent g 0 0 = 1 ∧ ent g 1 0 = 0 ∧ ent g 2 0 = 0
@[expose] def inSln (g : Γ) : Prop := ent g 2 0 = 0 ∧ ent g 2 1 = 0 ∧ ent g 2 2 = 1

instance : DecidablePred inD0 := fun g => by unfold inD0; infer_instance
instance : DecidablePred inSpt := fun g => by unfold inSpt; infer_instance
instance : DecidablePred inSln := fun g => by unfold inSln; infer_instance

theorem inD0_mul : ∀ g h : Γ, inD0 g → inD0 h → inD0 (g * h) := by decide +kernel
theorem inD0_inv : ∀ g : Γ, inD0 g → inD0 g⁻¹ := by decide +kernel
theorem inSpt_mul : ∀ g h : Γ, inSpt g → inSpt h → inSpt (g * h) := by decide +kernel
theorem inSpt_inv : ∀ g : Γ, inSpt g → inSpt g⁻¹ := by decide +kernel
theorem inSln_mul : ∀ g h : Γ, inSln g → inSln h → inSln (g * h) := by decide +kernel
theorem inSln_inv : ∀ g : Γ, inSln g → inSln g⁻¹ := by decide +kernel

@[expose] def D0 : Subgroup Γ where
  carrier := {g | inD0 g}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => inD0_mul a b ha hb
  inv_mem' := fun {a} ha => inD0_inv a ha

@[expose] def Spt : Subgroup Γ where
  carrier := {g | inSpt g}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => inSpt_mul a b ha hb
  inv_mem' := fun {a} ha => inSpt_inv a ha

@[expose] def Sln : Subgroup Γ where
  carrier := {g | inSln g}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => inSln_mul a b ha hb
  inv_mem' := fun {a} ha => inSln_inv a ha

theorem mem_D0 {g : Γ} : g ∈ D0 ↔ inD0 g := Iff.rfl
theorem mem_Spt {g : Γ} : g ∈ Spt ↔ inSpt g := Iff.rfl
theorem mem_Sln {g : Γ} : g ∈ Sln ↔ inSln g := Iff.rfl

theorem card_Γ : Nat.card Γ = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_succ]

theorem card_D0 : Nat.card D0 = 8 := by
  have h : Nat.card D0 = Nat.card {g : Γ // inD0 g} := rfl
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_Spt : Nat.card Spt = 24 := by
  have h : Nat.card Spt = Nat.card {g : Γ // inSpt g} := rfl
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_Sln : Nat.card Sln = 24 := by
  have h : Nat.card Sln = Nat.card {g : Γ // inSln g} := rfl
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem D0_le_Spt : D0 ≤ Spt := by
  intro g hg
  have : ∀ g : Γ, inD0 g → inSpt g := by decide +kernel
  exact this g hg

theorem D0_le_Sln : D0 ≤ Sln := by
  intro g hg
  have : ∀ g : Γ, inD0 g → inSln g := by decide +kernel
  exact this g hg

theorem dc_pt : ∀ g : Γ, inSpt g → ¬ inD0 g → ∀ h : Γ, inSpt h →
    inD0 h ∨ ∃ d : Γ, inD0 d ∧ inD0 (g⁻¹ * (d⁻¹ * h)) := by decide +kernel

theorem dc_ln : ∀ g : Γ, inSln g → ¬ inD0 g → ∀ h : Γ, inSln h →
    inD0 h ∨ ∃ d : Γ, inD0 d ∧ inD0 (g⁻¹ * (d⁻¹ * h)) := by decide +kernel

theorem word3 : ∀ g : Γ, ¬ inSpt g → ¬ inSln g →
    ∃ d : Γ, inD0 d ∧ (inSpt (g * d * g⁻¹) ∨ inSln (g * d * g⁻¹)) ∧ ¬ inD0 (g * d * g⁻¹) := by
  decide +kernel

theorem Spt_le_of_mem {P : Subgroup Γ} (hD : D0 ≤ P) {g : Γ} (hg : g ∈ Spt) (hgD : g ∉ D0)
    (hgP : g ∈ P) : Spt ≤ P := by
  intro h hh
  rcases dc_pt g hg hgD h hh with h1 | ⟨d, hd, hd'⟩
  · exact hD h1
  ·
    have : h = d * (g * (g⁻¹ * (d⁻¹ * h))) := by group
    rw [this]
    exact P.mul_mem (hD hd) (P.mul_mem hgP (hD hd'))

theorem Sln_le_of_mem {P : Subgroup Γ} (hD : D0 ≤ P) {g : Γ} (hg : g ∈ Sln) (hgD : g ∉ D0)
    (hgP : g ∈ P) : Sln ≤ P := by
  intro h hh
  rcases dc_ln g hg hgD h hh with h1 | ⟨d, hd, hd'⟩
  · exact hD h1
  · have : h = d * (g * (g⁻¹ * (d⁻¹ * h))) := by group
    rw [this]
    exact P.mul_mem (hD hd) (P.mul_mem hgP (hD hd'))

theorem overgroup_cases {P : Subgroup Γ} (hD : D0 ≤ P) : P = D0 ∨ Spt ≤ P ∨ Sln ≤ P := by
  by_cases h : P ≤ D0
  · exact Or.inl (le_antisymm h hD)
  · right
    obtain ⟨g, hgP, hgD⟩ : ∃ g, g ∈ P ∧ g ∉ D0 := by
      by_contra hcon
      push Not at hcon
      exact h fun g hg => hcon g hg
    by_cases hgs : inSpt g
    · exact Or.inl (Spt_le_of_mem hD hgs hgD hgP)
    by_cases hgl : inSln g
    · exact Or.inr (Sln_le_of_mem hD hgl hgD hgP)
    obtain ⟨d, hd, hw, hwD⟩ := word3 g hgs hgl
    have hwP : g * d * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hgP (hD hd)) (P.inv_mem hgP)
    rcases hw with hw | hw
    · exact Or.inl (Spt_le_of_mem hD hw hwD hwP)
    · exact Or.inr (Sln_le_of_mem hD hw hwD hwP)

theorem eq_top_of_Spt_lt {P : Subgroup Γ} (hP : Spt ≤ P) {y : Γ} (hy : y ∈ P) (hyS : y ∉ Spt) :
    P = ⊤ := by
  have h1 : Spt.index * 24 = 168 := by
    have := Subgroup.card_mul_index Spt
    rw [card_Spt, card_Γ] at this
    omega
  have h7 : Spt.index = 7 := by omega
  have hdvd : P.index ∣ 7 := h7 ▸ Subgroup.index_dvd_of_le hP
  have hcases : P.index = 1 ∨ P.index = 7 := (Nat.dvd_prime (by norm_num)).mp hdvd
  rcases hcases with h | h
  · exact Subgroup.index_eq_one.mp h
  · exfalso
    have hcard : Nat.card P = 24 := by
      have := Subgroup.card_mul_index P
      rw [card_Γ, h] at this
      omega
    have : Spt = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hcard, card_Spt])
    exact hyS (this ▸ hy)

theorem eq_top_of_Sln_lt {P : Subgroup Γ} (hP : Sln ≤ P) {y : Γ} (hy : y ∈ P) (hyS : y ∉ Sln) :
    P = ⊤ := by
  have h1 : Sln.index * 24 = 168 := by
    have := Subgroup.card_mul_index Sln
    rw [card_Sln, card_Γ] at this
    omega
  have h7 : Sln.index = 7 := by omega
  have hdvd : P.index ∣ 7 := h7 ▸ Subgroup.index_dvd_of_le hP
  have hcases : P.index = 1 ∨ P.index = 7 := (Nat.dvd_prime (by norm_num)).mp hdvd
  rcases hcases with h | h
  · exact Subgroup.index_eq_one.mp h
  · exfalso
    have hcard : Nat.card P = 24 := by
      have := Subgroup.card_mul_index P
      rw [card_Γ, h] at this
      omega
    have : Sln = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hcard, card_Sln])
    exact hyS (this ▸ hy)

theorem eq_D0_or_top {P : Subgroup Γ} (hD : D0 ≤ P) (α : MulAut Γ) (hα : ∀ x ∈ P, α x ∈ P)
    (h1 : ∃ x ∈ Spt, α x ∉ Spt) (h2 : ∃ x ∈ Sln, α x ∉ Sln) : P = D0 ∨ P = ⊤ := by
  rcases overgroup_cases hD with h | h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hαx⟩ := h1
    exact Or.inr (eq_top_of_Spt_lt h (hα x (h hx)) hαx)
  · obtain ⟨x, hx, hαx⟩ := h2
    exact Or.inr (eq_top_of_Sln_lt h (hα x (h hx)) hαx)

theorem inD0_of_normalizes : ∀ x : Γ, (∀ d : Γ, inD0 d → inD0 (x * d * x⁻¹)) → inD0 x := by
  decide +kernel


theorem exists_sylow_eq {D : Subgroup Γ} (hD : Nat.card D = 8) : ∃ S : Sylow 2 Γ, (S : Subgroup Γ) = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  obtain ⟨S, hS⟩ := hDp.exists_le_sylow
  refine ⟨S, ?_⟩
  have hSp : IsPGroup 2 (S : Subgroup Γ) := S.isPGroup'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hSp
  have hdvd : Nat.card (S : Subgroup Γ) ∣ 168 := card_Γ ▸ Subgroup.card_subgroup_dvd_card _
  have hle : Nat.card D ∣ Nat.card (S : Subgroup Γ) := Subgroup.card_dvd_of_le hS
  have h8 : Nat.card (S : Subgroup Γ) = 8 := by
    rw [hD, hk] at hle
    rw [hk] at hdvd
    have hk3 : k = 3 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · interval_cases k <;> simp at hle
      · have h16 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 h
        have := h16.trans hdvd
        norm_num at this
    rw [hk, hk3]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [h8, hD])).symm

theorem exists_conj_D0 (D : Subgroup Γ) (hD : Nat.card D = 8) :
    ∃ g : Γ, ∀ x : Γ, x ∈ D ↔ g⁻¹ * x * g ∈ D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq hD
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq card_D0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S₀ S
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • S₀ : Sylow 2 Γ) : Subgroup Γ) = D := by rw [hg, hS]
  rw [Sylow.coe_subgroup_smul, hS₀] at h1
  rw [← h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

abbrev tau : MulAut Γ := CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 (ZMod 2)

theorem tau_moves : ∀ A : Γ, (∀ x : Γ, inD0 x → inD0 (A * tau x * A⁻¹)) →
    (∃ x : Γ, inSpt x ∧ ¬ inSpt (A * tau x * A⁻¹)) ∧
      (∃ x : Γ, inSln x ∧ ¬ inSln (A * tau x * A⁻¹)) := by
  decide +kernel

theorem eq_D0_or_top_of_tau {P : Subgroup Γ} (hD : D0 ≤ P) (A : Γ)
    (hf : ∀ x ∈ D0, A * tau x * A⁻¹ ∈ D0) (hP : ∀ x ∈ P, A * tau x * A⁻¹ ∈ P) :
    P = D0 ∨ P = ⊤ := by
  obtain ⟨⟨x, hx, hnx⟩, ⟨y, hy, hny⟩⟩ := tau_moves A fun x hx => hf x hx
  rcases overgroup_cases hD with h | h | h
  · exact Or.inl h
  · exact Or.inr (eq_top_of_Spt_lt h (hP x (h hx)) hnx)
  · exact Or.inr (eq_top_of_Sln_lt h (hP y (h hy)) hny)

theorem exists_form_of_not_inner (α : MulAut Γ) (hout : ¬ ∃ k : Γ, α = MulAut.conj k) :
    ∃ A : Γ, ∀ x : Γ, α x = A * tau x * A⁻¹ := by
  rcases CFSG.QuasithinUnique.Setup.Family.aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
  · exfalso
    apply hout
    refine ⟨(CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm A, ?_⟩
    refine MulEquiv.ext fun x => ?_
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hA, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      MulAut.conj_apply, map_mul, map_mul, map_inv]
    have : Matrix.SpecialLinearGroup.toGL ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm A) = A :=
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).apply_symm_apply A
    rw [this]
  · refine ⟨(CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm A, fun x => ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hA, MulAut.mul_apply, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
    have : Matrix.SpecialLinearGroup.toGL ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm A) = A :=
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).apply_symm_apply A
    rw [this]

theorem eq_or_top_of_outer (D P : Subgroup Γ) (hD : Nat.card D = 8) (hDP : D ≤ P) (α : MulAut Γ)
    (hαD : ∀ x ∈ D, α x ∈ D) (hαP : ∀ x ∈ P, α x ∈ P) (hout : ¬ ∃ k : Γ, α = MulAut.conj k) :
    P = D ∨ P = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_D0 D hD
  obtain ⟨A, hA⟩ := exists_form_of_not_inner α hout
  set A' : Γ := g⁻¹ * A * tau g with hA'
  have hf : ∀ y : Γ, g⁻¹ * α (g * y * g⁻¹) * g = A' * tau y * A'⁻¹ := by
    intro y
    rw [hA, hA']
    simp only [map_mul, map_inv]
    group
  let P' : Subgroup Γ := P.comap (MulAut.conj g).toMonoidHom
  have hP'mem : ∀ y : Γ, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by simp [P', MulAut.conj_apply]
  have hD0P' : D0 ≤ P' := by
    intro y hy
    rw [hP'mem]
    apply hDP
    rw [hg]
    simpa [mul_assoc] using hy
  have hf0 : ∀ x ∈ D0, A' * tau x * A'⁻¹ ∈ D0 := by
    intro x hx
    rw [← hf]
    have h1 : g * x * g⁻¹ ∈ D := by rw [hg]; simpa [mul_assoc] using hx
    have h2 := hαD _ h1
    rw [hg] at h2
    simpa [mul_assoc] using h2
  have hfP : ∀ x ∈ P', A' * tau x * A'⁻¹ ∈ P' := by
    intro x hx
    rw [← hf, hP'mem]
    have h1 := hαP _ ((hP'mem x).mp hx)
    simpa [mul_assoc] using h1
  rcases eq_D0_or_top_of_tau hD0P' A' hf0 hfP with h | h
  · left
    apply le_antisymm
    · intro x hx
      have : g⁻¹ * x * g ∈ P' := by
        rw [hP'mem]; simpa [mul_assoc] using hx
      rw [h] at this
      rw [hg]; exact this
    · exact hDP
  · right
    rw [eq_top_iff]
    intro x _
    have : g⁻¹ * x * g ∈ P' := by rw [h]; exact Subgroup.mem_top _
    rw [hP'mem] at this
    simpa [mul_assoc] using this

theorem mem_of_normalizes (D : Subgroup Γ) (hD : Nat.card D = 8) (x : Γ)
    (hx : ∀ d ∈ D, x * d * x⁻¹ ∈ D) : x ∈ D := by
  obtain ⟨g, hg⟩ := exists_conj_D0 D hD
  have h1 : inD0 (g⁻¹ * x * g) := by
    apply inD0_of_normalizes
    intro d hd
    have h2 : g * d * g⁻¹ ∈ D := by rw [hg]; simpa [mul_assoc] using mem_D0.mpr hd
    have h3 := hx _ h2
    rw [hg] at h3
    have : g⁻¹ * (x * (g * d * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ := by group
    rw [this] at h3
    exact h3
  rw [hg]
  exact h1

end CFSG.Quasithin.L3Lat
