module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Claim
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab5Norm

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem false_of_twoNat (h : TwoNat A B z V c V₂) : False := by
  classical
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have hex : ∃ n : ℕ, ∃ x y : CosetGeom (A ⊔ B) A B,
      CosetGeom.dist x y = n ∧ ¬ Nm A B V V₂ x ≤ ballStab 1 y := by
    obtain ⟨x, y, hxy⟩ := exists_crit h
    exact ⟨_, x, y, rfl, hxy⟩
  obtain ⟨α, α', hdist, hnot⟩ := Nat.find_spec hex
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.find hex := ⟨_, rfl⟩
  rw [← hb] at hdist
  have hmin : ∀ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y < b →
      Nm A B V V₂ x ≤ ballStab 1 y := by
    intro x y hxy
    by_contra hc
    rw [hb] at hxy
    exact Nat.find_min hex hxy ⟨x, y, rfl, hc⟩
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    rcases (by omega : b = 0 ∨ b = 1) with h0 | h1
    · rw [h0] at hdist
      have : α = α' := (dist_eq_zero_iff (G₁ := A) (G₂ := B) rfl).mp hdist
      subst this
      exact hnot (goodV_all h α).nm_le
    · rw [h1] at hdist
      exact hnot (goodE_all h (dist_eq_one_iff_adj.mp hdist)).nm_le
  obtain ⟨β, hαβ, hβdist⟩ : ∃ β, (graph (A ⊔ B) A B).Adj α β ∧ CosetGeom.dist α' β = b - 1 :=
    exists_adj_dist_eq (G₁ := A) (G₂ := B) rfl (α := α') (δ := α) (d := b - 1)
      (by rw [CosetGeom.dist_comm, hdist]; omega)
  obtain ⟨ε, hα'ε, hβε⟩ : ∃ ε, (graph (A ⊔ B) A B).Adj α' ε ∧ CosetGeom.dist β ε = b - 2 :=
    exists_adj_dist_eq (G₁ := A) (G₂ := B) rfl (α := β) (δ := α') (d := b - 2)
      (by rw [CosetGeom.dist_comm, hβdist]; omega)
  have hαβ1 : CosetGeom.dist α β = 1 := dist_eq_one_iff_adj.mpr hαβ
  have hαε_lt : CosetGeom.dist α ε < b := by
    have := dist_triangle (G₁ := A) (G₂ := B) rfl α β ε
    omega
  have hαε : Nm A B V V₂ α ≤ ballStab 1 ε := hmin α ε hαε_lt
  have hα'β : Nm A B V V₂ α' ≤ ballStab 1 β := hmin α' β (by omega)
  have hββα' : CosetGeom.dist β α' = b - 1 := by rw [CosetGeom.dist_comm]; exact hβdist
  obtain ⟨μ₁, hμ₁adj, hμ₁ne, hμ₁not⟩ := exists_nbr_not_le h hαβ hα'ε hnot hαε hα'β
  have hα'μ₁ : CosetGeom.dist α' μ₁ = 1 := dist_eq_one_iff_adj.mpr hμ₁adj
  have hμβ : CosetGeom.dist μ₁ β = b := by
    have h1 := dist_triangle (G₁ := A) (G₂ := B) rfl β α' μ₁
    have h3 : b ≤ CosetGeom.dist μ₁ β := by
      by_contra hlt
      push Not at hlt
      exact hμ₁not (hmin μ₁ β hlt)
    have h4 := CosetGeom.dist_comm μ₁ β
    omega
  obtain ⟨p, hβp, hpdist⟩ : ∃ p, (graph (A ⊔ B) A B).Adj β p ∧ CosetGeom.dist μ₁ p = b - 1 :=
    exists_adj_dist_eq (G₁ := A) (G₂ := B) rfl (α := μ₁) (δ := β) (d := b - 1)
      (by rw [hμβ]; omega)
  have hμ₁p : Nm A B V V₂ μ₁ ≤ ballStab 1 p := hmin μ₁ p (by omega)
  have hββ : Nm A B V V₂ β ≤ ballStab 1 α' := hmin β α' (by omega)
  have hμ₁β : Nm A B V V₂ μ₁ ≤ stab β := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := p) (δ := β)
      (dist_eq_one_iff_adj.mpr hβp.symm).le (hμ₁p ha)
  have hnotβ : ¬ Nm A B V V₂ β ≤ ballStab 1 μ₁ :=
    not_nm_le_symm (goodV_all h μ₁) (goodV_all h β) hμ₁β hμ₁not
  obtain ⟨t, htβ, -, ht1, htF⟩ := exists_commutator h (x := β) (y := μ₁) (p := p) (q := α')
    hμ₁adj.symm hβp.symm hββ hμ₁p hnotβ
  obtain ⟨f, hfα, hfn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfε : f ∈ ballStab 1 ε := hαε hfα
  have hf_st : f ∈ stab α' := ballStab_le_stab_of_dist_le (n := 1) (γ := ε) (δ := α')
    (dist_eq_one_iff_adj.mpr hα'ε.symm).le hfε
  have hfstε : f ∈ stab ε := ballStab_le_stab 1 ε hfε
  have hfβ : f ∈ ballStab 1 β := (goodE_all h hαβ).nm_le hfα
  have hft : t * f = f * t := (goodV_all h β).qv_cent f hfβ t htβ
  have hEα'ε := goodE_all h hα'ε
  obtain ⟨hμ₂adj, hμ₂ne1, -⟩ :=
    smul_nbr_facts hEα'ε hα'ε hα'ε hμ₁adj hμ₁ne.symm hf_st hfstε hfn
  have hgα' : (⟨f, stab_le α' hf_st⟩ : ↥(A ⊔ B)) • α' = α' :=
    smul_eq_of_mem_stab (g := ⟨f, stab_le α' hf_st⟩) hf_st
  have hteq : f * t * f⁻¹ = t := by
    calc f * t * f⁻¹ = (t * f) * f⁻¹ := by rw [hft]
      _ = t := by group
  have hmem : t ∈ Fx V V₂ ((⟨f, stab_le α' hf_st⟩ : ↥(A ⊔ B)) • μ₁) α' := by
    have h1 : f * t * f⁻¹ ∈ Fx V V₂ ((⟨f, stab_le α' hf_st⟩ : ↥(A ⊔ B)) • μ₁)
        ((⟨f, stab_le α' hf_st⟩ : ↥(A ⊔ B)) • α') := by
      rw [mem_Fx_smul hA hB]
      change f⁻¹ * (f * t * f⁻¹) * f ∈ Fx V V₂ μ₁ α'
      rw [show f⁻¹ * (f * t * f⁻¹) * f = t by group]
      exact htF
    rw [hgα', hteq] at h1
    exact h1
  exact ht1 (eq_one_of_mem_Fx_of_mem_Fx hA hB hEα'ε hα'ε hμ₁adj hμ₂adj hμ₂ne1.symm htF hmem)

end GoldAmLab6

namespace GoldAmLab5

theorem doublyMovedEmpty : DoublyMovedEmpty.{u} := by
  intro D _ _ A B z V x c V₂ h h2 h32 hxB hx3 hxz hc hAc
  exact GoldAmLab6.false_of_twoNat
    (GoldAmLab6.TwoNat.of_oneSide h h2 h32 ⟨x, hxB, hxz⟩ hAc)

end GoldAmLab5

namespace GoldAmLab4

theorem b3DoublyMovedNoFiveInput : B3DoublyMovedNoFiveInput.{u} :=
  GoldAmLab5.b3DoublyMovedNoFiveInput_iff.mpr GoldAmLab5.doublyMovedEmpty

end GoldAmLab4

end F6

end CFSG.Quasithin
