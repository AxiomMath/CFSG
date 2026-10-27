module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62B

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

variable {L : ZLab Γ G} (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem prod_fix_delta {α κ δ μ₁ μ₂ l₁ l₂ : V} {s : G} (hα : valence Γ α = 5)
    (h₁ : Br Γ α μ₁ l₁) (h₂ : Br Γ α μ₂ l₂) (hs : s ∈ MulAction.stabilizer G α)
    (hsμ₁ : s • μ₁ = μ₂) (hsκ : s • κ = κ) (hb : Br Γ α κ δ) :
    (L.z l₁ * L.z l₂) • δ = δ := by
  have hsα : s • α = α := MulAction.mem_stabilizer_iff.1 hs
  have hbs : Br Γ α κ (s • δ) := by
    have := Br.smul F s hb
    rwa [hsα, hsκ] at this
  have hb₁s : Br Γ α μ₂ (s • l₁) := by
    have := Br.smul F s h₁
    rwa [hsα, hsμ₁] at this
  have hvδ := (Br.valence F hα hb).2
  have e1 : NC L δ l₁ ↔ NC L (s • δ) (s • l₁) :=
    (NC.smul hvδ (Br.valence F hα h₁).2 s).symm
  have e2 : NC L (s • δ) (s • l₁) ↔ NC L δ (s • l₁) :=
    nc_br F H hα hbs hb (Br.dist_two F hb₁s)
  have e4 : NC L (s • l₁) δ ↔ NC L l₂ δ := nc_br F H hα hb₁s h₂ (Br.dist_two F hb)
  have e3 : NC L δ (s • l₁) ↔ NC L (s • l₁) δ := ⟨NC.symm, NC.symm⟩
  have e5 : NC L l₂ δ ↔ NC L δ l₂ := ⟨NC.symm, NC.symm⟩
  have key : NC L δ l₁ ↔ NC L δ l₂ := e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 := nc_iff F H hα hb (Br.dist_two F h₁)
  have c2 := nc_iff F H hα hb (Br.dist_two F h₂)
  by_cases hn : NC L δ l₁
  · exact prod_fix F H hα hb (Br.dist_two F h₁) (Br.dist_two F h₂) (c1.1 hn) (c2.1 (key.1 hn))
  · have f1 : L.z l₁ • δ = δ := by_contra fun h => hn (c1.2 h)
    have f2 : L.z l₂ • δ = δ := by_contra fun h => hn (key.2 (c2.2 h))
    rw [mul_smul, f2, f1]

theorem step_end {α κ δ ν η : V} {y : G} (hα : valence Γ α = 5) (hvδ : valence Γ δ = 5)
    (hbα : Br Γ δ κ α) (hbη : Br Γ δ ν η) (hνκ : ν ≠ κ) (hyδ : y • δ = δ) (hyκ : y • κ = κ)
    (hyK : y ∉ nbrStab Γ G δ)
    (hmem : y⁻¹ * L.z η * y * L.z η = 1 ∨ y⁻¹ * L.z η * y * L.z η = L.z α) : False := by
  have hvη := (Br.valence F hvδ hbη).2
  have hyd : y⁻¹ • δ = δ := by rw [inv_smul_eq_iff, hyδ]
  have hbη' : Br Γ δ (y⁻¹ • ν) (y⁻¹ • η) := by
    have := Br.smul F y⁻¹ hbη
    rwa [hyd] at this
  have hne : y⁻¹ • ν ≠ ν := by
    intro e
    exact hyK (F.fix_two_nbrs hbα.1 hbη.1 hνκ.symm hyκ (by rw [← inv_smul_eq_iff.1 e]))
  have hdist4 : Γ.dist η (y⁻¹ • η) = 4 := dist_four F hbη hbη' hne.symm
  have hηne : η ≠ y⁻¹ • η := fun e => by rw [← e, dist_self] at hdist4; omega
  have hvη' := (Br.valence F hvδ hbη').2
  have hlab := H.dist η (y⁻¹ • η) hηne hvη hvη' (Or.inr hdist4)
  have hz' : L.z (y⁻¹ • η) = y⁻¹ * L.z η * y := by rw [z_smul hvη, inv_inv]
  have hsq := z_sq (L := L) hvη
  rcases hmem with h | h
  · apply hlab
    have h1 : L.z (y⁻¹ • η) * L.z η = 1 := by rw [hz']; exact h
    rw [eq_inv_of_mul_eq_one_left h1, z_inv hvη]
  · have hsα := z_sq (L := L) hα
    apply H.triple δ (y⁻¹ • η) η α hvδ (Br.dist_two F hbη') (Br.dist_two F hbη)
      (Br.dist_two F hbα) (by rw [hz', h, hsα]; exact one_mem _)

end P62

end CFSG.Quasithin.Fan86
