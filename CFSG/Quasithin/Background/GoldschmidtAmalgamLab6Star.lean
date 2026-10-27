module

public import CFSG.Quasithin.Recognition.F112WValency
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Vert

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D}

theorem mem_ballStab_one_of_fix_two {γ γ' ε μ : CosetGeom (A ⊔ B) A B}
    (hE : GoodE V V₂ γ γ') (hγγ' : (graph (A ⊔ B) A B).Adj γ γ')
    (hε : (graph (A ⊔ B) A B).Adj γ ε) (hμ : (graph (A ⊔ B) A B).Adj γ μ) (hne : ε ≠ μ)
    {u : D} (hu : u ∈ stab γ) (hu1 : u ∈ stab ε) (hu2 : u ∈ stab μ) :
    u ∈ ballStab 1 γ := by
  obtain ⟨a, ha1, ha2⟩ := exists_stab_smul_eq hγγ' hε
  obtain ⟨a', ha1', ha2'⟩ := exists_stab_smul_eq hγγ' hμ
  have haγ : (a : D) ∈ stab γ := mem_stab_of_smul_eq ha1
  have ha'γ : (a' : D) ∈ stab γ := mem_stab_of_smul_eq ha1'
  have hsε : stab ε = conjSub (a : D) (stab γ') := by rw [← ha2, stab_smul]
  have hsμ : stab μ = conjSub (a' : D) (stab γ') := by rw [← ha2', stab_smul]
  have hu0 : (a : D)⁻¹ * u * a ∈ stab γ ⊓ stab γ' := by
    refine ⟨(stab γ).mul_mem ((stab γ).mul_mem ((stab γ).inv_mem haγ) hu) haγ, ?_⟩
    have := hu1
    rw [hsε, mem_conjSub] at this
    exact this
  have hu0' : (a' : D)⁻¹ * u * a' ∈ stab γ ⊓ stab γ' := by
    refine ⟨(stab γ).mul_mem ((stab γ).mul_mem ((stab γ).inv_mem ha'γ) hu) ha'γ, ?_⟩
    have := hu2
    rw [hsμ, mem_conjSub] at this
    exact this
  have hxγ : (a : D)⁻¹ * a' ∈ stab γ := (stab γ).mul_mem ((stab γ).inv_mem haγ) ha'γ
  have hxE : (a : D)⁻¹ * a' ∉ stab γ ⊓ stab γ' := by
    intro hxE
    apply hne
    have hxG : (a⁻¹ * a' : ↥(A ⊔ B)) • γ' = γ' :=
      smul_eq_of_mem_stab (g := a⁻¹ * a') (by simpa using hxE.2)
    calc ε = a • γ' := ha2.symm
      _ = a • ((a⁻¹ * a') • γ') := by rw [hxG]
      _ = a' • γ' := by rw [← mul_smul]; simp
      _ = μ := ha2'
  have hcore := F112W.coreIn_eq_inf_conjSub_of_relIndex_three
    (inf_le_left : stab γ ⊓ stab γ' ≤ stab γ) hE.rel3 hxγ hxE
  have hmem : (a : D)⁻¹ * u * a ∈ coreIn (stab γ ⊓ stab γ') (stab γ) := by
    rw [hcore]
    refine ⟨hu0, mem_conjSub.mpr ?_⟩
    have e : ((a : D)⁻¹ * a')⁻¹ * ((a : D)⁻¹ * u * a) * ((a : D)⁻¹ * a') = (a' : D)⁻¹ * u * a' := by
      group
    rw [e]
    exact hu0'
  rw [← ballStab_one_eq_coreIn (G₁ := A) (G₂ := B) rfl hγγ'] at hmem
  have hn := le_normalizer_ballStab 1 γ haγ
  have := (Subgroup.mem_normalizer_iff.mp hn _).mp hmem
  have e2 : (a : D) * ((a : D)⁻¹ * u * a) * (a : D)⁻¹ = u := by group
  rwa [e2] at this

omit [Finite D] in
theorem exists_adj_ne {γ ε : CosetGeom (A ⊔ B) A B} (hE : GoodE V V₂ γ ε)
    (hε : (graph (A ⊔ B) A B).Adj γ ε) :
    ∃ μ, (graph (A ⊔ B) A B).Adj γ μ ∧ μ ≠ ε := by
  by_contra hcon
  push Not at hcon
  have hle : stab γ ≤ stab γ ⊓ stab ε := by
    intro u hu
    refine ⟨hu, ?_⟩
    have hadj : (graph (A ⊔ B) A B).Adj γ ((⟨u, stab_le γ hu⟩ : ↥(A ⊔ B)) • ε) := by
      have := (smul_adj (⟨u, stab_le γ hu⟩ : ↥(A ⊔ B))).mpr hε
      rwa [smul_eq_of_mem_stab (g := ⟨u, stab_le γ hu⟩) hu] at this
    have := hcon _ hadj
    exact mem_stab_of_smul_eq (g := ⟨u, stab_le γ hu⟩) this
  have h1 := Subgroup.relIndex_eq_one.mpr hle
  rw [hE.rel3] at h1
  omega

omit [Finite D] in
theorem eq_one_of_mem_Fx_of_mem_Fx (hA : A ≤ Subgroup.normalizer (V : Set D))
    (hB : B ≤ Subgroup.normalizer (V₂ : Set D)) {γ γ' μ₁ μ₂ : CosetGeom (A ⊔ B) A B}
    (hE : GoodE V V₂ γ γ') (hγγ' : (graph (A ⊔ B) A B).Adj γ γ')
    (h₁ : (graph (A ⊔ B) A B).Adj γ μ₁) (h₂ : (graph (A ⊔ B) A B).Adj γ μ₂) (hne : μ₁ ≠ μ₂)
    {x : D} (hx₁ : x ∈ Fx V V₂ μ₁ γ) (hx₂ : x ∈ Fx V V₂ μ₂ γ) : x = 1 := by
  obtain ⟨w, hw1, hw2⟩ := hE.lab
  obtain ⟨a₁, ha₁, ha₁'⟩ := exists_stab_smul_eq hγγ' h₁
  obtain ⟨a₂, ha₂, ha₂'⟩ := exists_stab_smul_eq hγγ' h₂
  have e1 : x ∈ Fx V V₂ (a₁ • γ') (a₁ • γ) := by rw [ha₁, ha₁']; exact hx₁
  have e2 : x ∈ Fx V V₂ (a₂ • γ') (a₂ • γ) := by rw [ha₂, ha₂']; exact hx₂
  rw [mem_Fx_smul hA hB] at e1 e2
  by_contra hx1
  have conj_ne : ∀ a : D, a⁻¹ * x * a ≠ 1 := fun a h => hx1 (by
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hy1 : (a₁ : D)⁻¹ * x * a₁ = w := (hw1 _ e1).resolve_left (conj_ne _)
  have hy2 : (a₂ : D)⁻¹ * x * a₂ = w := (hw1 _ e2).resolve_left (conj_ne _)
  have hg : (a₁ : D)⁻¹ * a₂ ∈ stab γ :=
    (stab γ).mul_mem ((stab γ).inv_mem (mem_stab_of_smul_eq ha₁)) (mem_stab_of_smul_eq ha₂)
  have hcomm : ((a₁ : D)⁻¹ * a₂) * w * ((a₁ : D)⁻¹ * a₂)⁻¹ = w := by
    calc ((a₁ : D)⁻¹ * a₂) * w * ((a₁ : D)⁻¹ * a₂)⁻¹
        = ((a₁ : D)⁻¹ * a₂) * ((a₂ : D)⁻¹ * x * a₂) * ((a₁ : D)⁻¹ * a₂)⁻¹ := by rw [hy2]
      _ = (a₁ : D)⁻¹ * x * a₁ := by group
      _ = w := hy1
  have hfix : (a₁⁻¹ * a₂ : ↥(A ⊔ B)) • γ' = γ' :=
    smul_eq_of_mem_stab (g := a₁⁻¹ * a₂) (by simpa using hw2 _ hg hcomm)
  apply hne
  calc μ₁ = a₁ • γ' := ha₁'.symm
    _ = a₁ • ((a₁⁻¹ * a₂) • γ') := by rw [hfix]
    _ = a₂ • γ' := by rw [← mul_smul]; simp
    _ = μ₂ := ha₂'

end GoldAmLab6

end F6

end CFSG.Quasithin
