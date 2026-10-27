module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootDef

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Subgroups

variable (K : Type) [Field K]

@[expose] def Xe (γ : Fin Tag.G2.rank → ℤ) : Subgroup (C K) where
  carrier := Set.range (xe γ)
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, xe_add γ s t⟩
  one_mem' := ⟨0, xe_zero γ⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, (xe_inv_neg γ s).symm⟩

variable {K}

theorem mem_Xe_iff {γ : Fin Tag.G2.rank → ℤ} {g : C K} : g ∈ Xe K γ ↔ ∃ s : K, xe γ s = g :=
  Iff.rfl

variable (K)

abbrev Xa : Subgroup (C K) := Xe K rA

abbrev Xr : Subgroup (C K) := Xe K rR

abbrev Xu : Subgroup (C K) := Xe K rU

abbrev Xv : Subgroup (C K) := Xe K rV

abbrev Xb : Subgroup (C K) := Xe K rB

abbrev Xc : Subgroup (C K) := Xe K rC

variable {K}

theorem mem_Xa_iff {g : C K} : g ∈ Xa K ↔ ∃ s : K, xa s = g := Iff.rfl

theorem xa_mem_Xa (s : K) : xa s ∈ Xa K := ⟨s, rfl⟩

theorem xu_mem_Xu (s : K) : xu s ∈ Xu K := ⟨s, rfl⟩

theorem mem_Xv_iff {g : C K} : g ∈ Xv K ↔ ∃ s : K, xv s = g := Iff.rfl

theorem xv_mem_Xv (s : K) : xv s ∈ Xv K := ⟨s, rfl⟩

theorem mem_Xb_iff {g : C K} : g ∈ Xb K ↔ ∃ s : K, xb s = g := Iff.rfl

theorem xb_mem_Xb (s : K) : xb s ∈ Xb K := ⟨s, rfl⟩

theorem mem_Xc_iff {g : C K} : g ∈ Xc K ↔ ∃ s : K, xc s = g := Iff.rfl

theorem xc_mem_Xc (s : K) : xc s ∈ Xc K := ⟨s, rfl⟩

variable (K)

@[expose] def U : Subgroup (C K) := (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)

variable {K}

theorem mem_U_iff {g : C K} : g ∈ U K ↔ (g : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K := Iff.rfl

theorem xe_mem_U {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = rA ∨ γ = rR ∨ γ = rU ∨ γ = rV ∨ γ = rB ∨ γ = rC) (s : K) : xe γ s ∈ U K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot Tag.G2 α ∧ 0 < height α}) (isRoot_pos_iff.2 hγ) s

theorem xa_mem_U (s : K) : xa s ∈ U K := xe_mem_U (Or.inl rfl) s

theorem Xa_le_U : Xa K ≤ U K := by
  rintro _ ⟨s, rfl⟩
  exact xa_mem_U s

theorem xr_mem_U (s : K) : xr s ∈ U K := xe_mem_U (Or.inr (Or.inl rfl)) s

theorem xu_mem_U (s : K) : xu s ∈ U K := xe_mem_U (Or.inr (Or.inr (Or.inl rfl))) s

theorem Xu_le_U : Xu K ≤ U K := by
  rintro _ ⟨s, rfl⟩
  exact xu_mem_U s

theorem xv_mem_U (s : K) : xv s ∈ U K := xe_mem_U (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) s

theorem Xv_le_U : Xv K ≤ U K := by
  rintro _ ⟨s, rfl⟩
  exact xv_mem_U s

theorem xb_mem_U (s : K) : xb s ∈ U K := xe_mem_U (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) s

theorem Xb_le_U : Xb K ≤ U K := by
  rintro _ ⟨s, rfl⟩
  exact xb_mem_U s

theorem xc_mem_U (s : K) : xc s ∈ U K :=
  xe_mem_U (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) s

theorem Xc_le_U : Xc K ≤ U K := by
  rintro _ ⟨s, rfl⟩
  exact xc_mem_U s

variable (K)

@[expose] def Q1 : Subgroup (C K) := Xa K ⊔ Xu K ⊔ Xv K ⊔ Xb K ⊔ Xc K

@[expose] def Q2 : Subgroup (C K) := Xr K ⊔ Xu K ⊔ Xv K ⊔ Xb K ⊔ Xc K

@[expose] def V : Subgroup (C K) := Xb K ⊔ Xc K

variable {K}

theorem Xa_le_Q1 : Xa K ≤ Q1 K :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))

theorem Xu_le_Q1 : Xu K ≤ Q1 K :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))

theorem Xv_le_Q1 : Xv K ≤ Q1 K := le_sup_of_le_left (le_sup_of_le_left le_sup_right)

theorem Xb_le_Q1 : Xb K ≤ Q1 K := le_sup_of_le_left le_sup_right

theorem Xc_le_Q1 : Xc K ≤ Q1 K := le_sup_right

theorem Xr_le_Q2 : Xr K ≤ Q2 K :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))

theorem Xu_le_Q2 : Xu K ≤ Q2 K :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))

theorem Xv_le_Q2 : Xv K ≤ Q2 K := le_sup_of_le_left (le_sup_of_le_left le_sup_right)

theorem Xb_le_Q2 : Xb K ≤ Q2 K := le_sup_of_le_left le_sup_right

theorem Xc_le_Q2 : Xc K ≤ Q2 K := le_sup_right

theorem Xb_le_V : Xb K ≤ V K := le_sup_left

theorem Xc_le_V : Xc K ≤ V K := le_sup_right

theorem V_le_Q1 : V K ≤ Q1 K := sup_le Xb_le_Q1 Xc_le_Q1

theorem Q1_le_U : Q1 K ≤ U K :=
  sup_le (sup_le (sup_le (sup_le Xa_le_U Xu_le_U) Xv_le_U) Xb_le_U) Xc_le_U

theorem xa_mem_Q1 (s : K) : xa s ∈ Q1 K := Xa_le_Q1 (xa_mem_Xa s)
theorem xu_mem_Q1 (s : K) : xu s ∈ Q1 K := Xu_le_Q1 (xu_mem_Xu s)
theorem xv_mem_Q1 (s : K) : xv s ∈ Q1 K := Xv_le_Q1 (xv_mem_Xv s)
theorem xb_mem_Q1 (s : K) : xb s ∈ Q1 K := Xb_le_Q1 (xb_mem_Xb s)
theorem xc_mem_Q1 (s : K) : xc s ∈ Q1 K := Xc_le_Q1 (xc_mem_Xc s)
theorem xv_mem_Q2 (s : K) : xv s ∈ Q2 K := Xv_le_Q2 (xv_mem_Xv s)
theorem xb_mem_V (s : K) : xb s ∈ V K := Xb_le_V (xb_mem_Xb s)
theorem xc_mem_V (s : K) : xc s ∈ V K := Xc_le_V (xc_mem_Xc s)

end Subgroups

end CFSG.Quasithin.H13.F431.G2
