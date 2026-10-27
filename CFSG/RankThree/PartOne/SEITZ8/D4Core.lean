module

public import CFSG.RankThree.PartOne.SEITZ8.D4Rat
public import CFSG.RankThree.PartOne.SEITZ8.D4Pair
public import CFSG.RankThree.PartOne.SEITZ8.D4Faith

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7

variable {K : Type} [Field K]

structure D4Setup (σ δ : K →+* K) (k : Subfield K) (F0 : Subfield (fixedField σ))
    (d q : ℕ) : Prop where
  hσ3 : ∀ c, σ (σ (σ c)) = c
  hcomm : ∀ c, δ (σ c) = σ (δ c)
  hfix : ∀ c ∈ k, δ c = c
  rat : Rat3 σ k
  hF0 : ∀ c : fixedField σ, c ∈ F0 ↔ (c : K) ∈ k
  prime : d.Prime
  ne2 : d ≠ 2
  card : Nat.card (fixedField σ) = Nat.card F0 ^ d
  four : 4 ∣ Nat.card F0
  span : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}
  q2 : 2 ≤ q
  hKq : Nat.card K = q ^ 3
  hσq : ∀ c, σ c = c ^ q
  stab : ∀ g : twistedGroup σ, ∃ g' : twistedGroup σ,
    ((g' : adjointGroup d4 K) : ModGL d4 K) =
      Units.map (entrywiseHom δ) ((g : adjointGroup d4 K) : ModGL d4 K)

@[expose] noncomputable def Rg (σ δ : K →+* K) : Subgroup (twistedGroup σ) :=
  (Rδ σ δ).comap (twistedGroup σ).subtype

theorem mem_Rg {σ δ : K →+* K} {g : twistedGroup σ} :
    g ∈ Rg σ δ ↔ Units.map (entrywiseHom δ) ((g : adjointGroup d4 K) : ModGL d4 K) =
      ((g : adjointGroup d4 K) : ModGL d4 K) :=
  ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

section Wt


theorem entrywise_Wt (δ : K →+* K) :
    Units.map (entrywiseHom δ) ((Wt : adjointGroup d4 K) : ModGL d4 K) =
      ((Wt : adjointGroup d4 K) : ModGL d4 K) := by
  unfold Wt
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, map_mul,
    entrywise_weylElement, entrywise_weylElement, entrywise_weylElement, entrywise_weylElement]

theorem entrywise_xH [CharP K 2] (δ : K →+* K) (c : K) :
    Units.map (entrywiseHom δ) ((xe 22 c : adjointGroup d4 K) : ModGL d4 K) =
      ((xe 22 (δ c) : adjointGroup d4 K) : ModGL d4 K) := by
  have h1 : (xe 22 c : adjointGroup d4 K) = Wt * xe 2 c * Wt⁻¹ := (Wt_xB c).symm
  have h2 : (xe 22 (δ c) : adjointGroup d4 K) = Wt * xe 2 (δ c) * Wt⁻¹ := (Wt_xB (δ c)).symm
  rw [h1, h2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, entrywise_Wt,
    entrywise_xe_simple δ (nd 2) d4Root_simple_2]

end Wt

section Core

variable [CharP K 2] [Finite K]
  {σ δ : K →+* K} {k : Subfield K} {F0 : Subfield (fixedField σ)} {d q : ℕ}

omit [Finite K]
  in
theorem psiB_upper_mem_Rg (S : D4Setup σ δ k F0 d q) {c : fixedField σ} (hc : c ∈ F0) :
    psiB σ S.hσ3 (sl2Upper c) ∈ Rg σ δ := by
  rw [mem_Rg, psiB_upper σ S.hσ3 c]
  show Units.map (entrywiseHom δ) ((xe 22 (c : K) : adjointGroup d4 K) : ModGL d4 K) =
    ((xe 22 (c : K) : adjointGroup d4 K) : ModGL d4 K)
  rw [entrywise_xH, S.hfix _ ((S.hF0 c).1 hc)]

theorem exists_bad_entry (S : D4Setup σ δ k F0 d q) (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    ∃ r ∈ Rδ σ δ, ∃ r' ∈ Rδ σ δ,
      coordAt (d4Root 23) ((r * (g : adjointGroup d4 K) * r') • (rv 22 : RootModule d4 K)) ∉ k := by
  have hSpan := spanHyp_Rδ S.hσ3 S.hcomm S.hfix S.rat
  by_contra hcon
  push Not at hcon
  have hrat := ratMod_of_hcon hSpan (g : adjointGroup d4 K) hcon
  have hbasis := fun b => ratMod_basis hSpan hrat b
  obtain ⟨g', hg'⟩ := S.stab g
  have hcols : ∀ b : Label d4, (g' : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K) =
        Finsupp.mapRange δ δ.map_zero ((g : adjointGroup d4 K) •
          (Finsupp.single b (1 : K) : RootModule d4 K)) := by
    intro b
    rw [smul_eq_end, hg']
    show entrywise δ _ (Finsupp.single b 1) = _
    rw [entrywise_single]
    rfl
  have heq := eq_of_ratMod S.q2 S.hKq S.hσq δ S.hfix g g' hcols hbasis
  apply hg
  rw [mem_Rg, ← hg', heq]

theorem long_full (S : D4Setup σ δ k F0 d q) (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    ∀ c : fixedField σ, psiB σ S.hσ3 (sl2Upper c) ∈
      Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
        (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
          Set (twistedGroup σ))) := by
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry S g hg
  set H : Subgroup (twistedGroup σ) := Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
    (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ))) with hH
  have hRH : Rg σ δ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : (Rg σ δ).map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  set ρ : twistedGroup σ := ⟨r, hr.1⟩ with hρdef
  set ρ' : twistedGroup σ := ⟨r', hr'.1⟩ with hρ'def
  have hρ : ρ ∈ Rg σ δ := hr
  have hρ' : ρ' ∈ Rg σ δ := hr'
  have hcoe : ((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) =
      r * (g : adjointGroup d4 K) * r' := rfl
  have hne0 : coordAt (d4Root 23) (((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) •
      (rv 22 : RootModule d4 K)) ≠ 0 := by
    rw [hcoe]
    intro h
    exact hbad (h ▸ k.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, hmu, hu, hl⟩ := bigCell_tw S.hσ3 (ρ * g * ρ') hne0
  have hlam_eq : ((μ₁ * μ₂ : fixedField σ) : K) = coordAt (d4Root 23)
      (((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) := hmu
  have hlam : μ₁ * μ₂ ∉ F0 := by
    intro hmem
    have h3 := (S.hF0 _).1 hmem
    rw [hlam_eq, hcoe] at h3
    exact hbad h3
  have hψ : ∀ c ∈ F0, psiB σ S.hσ3 (sl2Upper c) ∈ H := fun c hc =>
    hRH (psiB_upper_mem_Rg S hc)
  have hψ2 : ∀ c ∈ F0, (ρ * g * ρ') * psiB σ S.hσ3 (sl2Upper c) * (ρ * g * ρ')⁻¹ ∈ H := by
    intro c hc
    have h5 : ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹ ∈ Rg σ δ :=
      (Rg σ δ).mul_mem ((Rg σ δ).mul_mem hρ' (psiB_upper_mem_Rg S hc)) ((Rg σ δ).inv_mem hρ')
    have h6 : g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹ ∈
        (Rg σ δ).map (MulAut.conj g).toMonoidHom := ⟨_, h5, by simp [MulAut.conj_apply]⟩
    have h7 : ρ * (g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹) * ρ⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hρ) (hRgH h6)) (H.inv_mem (hRH hρ))
    have e : (ρ * g * ρ') * psiB σ S.hσ3 (sl2Upper c) * (ρ * g * ρ')⁻¹ =
        ρ * (g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹) * ρ⁻¹ := by group
    rw [e]
    exact h7
  exact full_h_of_pair S.hσ3 F0 S.prime S.ne2 S.card S.four (ρ * g * ρ') hψ hψ2 (μ₁ * μ₂)
    hlam_eq hlam

end Core

end CFSG.RankThree.PartOne.SEITZ8
