module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem StarBound.conjSub {E Q H : Subgroup G} (hs : StarBound E Q H) (g : G) :
    StarBound (CFSG.Quasithin.conjSub g E) (CFSG.Quasithin.conjSub g Q)
      (CFSG.Quasithin.conjSub g H) := by
  intro P hPH hP hcomm hsq hPQ
  let P' : Subgroup G := CFSG.Quasithin.conjSub g⁻¹ P
  have hconjRelIndex : ∀ A B : Subgroup G,
      (CFSG.Quasithin.conjSub g A).relIndex (CFSG.Quasithin.conjSub g B) = A.relIndex B := by
    intro A B
    exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective
  have hP'H : P' ≤ H := by
    show CFSG.Quasithin.conjSub g⁻¹ P ≤ H
    rw [conjSub_le_iff]
    simpa using hPH
  have hP'grp : IsPGroup 2 P' := by
    show IsPGroup 2 (CFSG.Quasithin.conjSub g⁻¹ P)
    exact (isPGroup_conjSub_iff (g := g⁻¹)).mpr hP
  have hcomm' : ∀ x ∈ P', ∀ y ∈ P', x * y * x⁻¹ * y⁻¹ ∈ Q := by
    intro x hx y hy
    have hxP : g * x * g⁻¹ ∈ P := by simpa using (mem_conjSub.mp hx)
    have hyP : g * y * g⁻¹ ∈ P := by simpa using (mem_conjSub.mp hy)
    have hc := hcomm (g * x * g⁻¹) hxP (g * y * g⁻¹) hyP
    have e : x * y * x⁻¹ * y⁻¹ =
        g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) * g := by
      group
    rw [e]
    exact mem_conjSub.mp hc
  have hsq' : ∀ x ∈ P', x ^ 2 ∈ Q := by
    intro x hx
    have hxP : g * x * g⁻¹ ∈ P := by simpa using (mem_conjSub.mp hx)
    have hc := hsq (g * x * g⁻¹) hxP
    have e : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [e]
    exact mem_conjSub.mp hc
  have hP'Q : ¬ P' ≤ Q := by
    intro h
    exact hPQ (by
      show P ≤ CFSG.Quasithin.conjSub g Q
      rw [← conjSub_inv_conjSub g P]
      exact CFSG.Quasithin.conjSub_mono g h)
  have hkey := hs P' hP'H hP'grp hcomm' hsq' hP'Q
  have hAeq : P = CFSG.Quasithin.conjSub g P' := (conjSub_inv_conjSub g P).symm
  have hB : P ⊓ CFSG.Quasithin.conjSub g Q = CFSG.Quasithin.conjSub g (P' ⊓ Q) := by
    rw [conjSub_inf, ← hAeq]
  have hcent : Subgroup.centralizer (P : Set G) =
      CFSG.Quasithin.conjSub g (Subgroup.centralizer (P' : Set G)) := by
    rw [hAeq, conjSub_centralizer]
  have hC : CFSG.Quasithin.conjSub g E ⊓ Subgroup.centralizer (P : Set G) =
      CFSG.Quasithin.conjSub g (E ⊓ Subgroup.centralizer (P' : Set G)) := by
    rw [hcent, ← conjSub_inf]
  have hR1 : (P ⊓ CFSG.Quasithin.conjSub g Q).relIndex P = (P' ⊓ Q).relIndex P' := by
    rw [hB, hAeq]
    exact hconjRelIndex _ _
  have hR2 : (CFSG.Quasithin.conjSub g E ⊓ Subgroup.centralizer (P : Set G)).relIndex
        (CFSG.Quasithin.conjSub g E) = (E ⊓ Subgroup.centralizer (P' : Set G)).relIndex E := by
    rw [hC]
    exact hconjRelIndex _ _
  rw [hR1, hR2]
  exact hkey

theorem ConfigA.localA (hA : ConfigA G₀ G₁ G₂ T L E) (hS : LocalS3 G₀ G₁ G₂)
    (h1 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2)
    (h2 : ¬ G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    LocalA G₀ G₁ G₂ E where
  toLocalS3 := hS
  star := by
    intro γ hγ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg, Vv_smul_γ₀ hA.hypV.normalizes, stab_smul, pCoreOf_conjSub,
      stab_γ₀ hA.hyp.le₁]
    exact StarBound.conjSub hA.star (g : G)
  elemAbelian := by
    intro γ hγ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg, Vv_smul_γ₀ hA.hypV.normalizes]
    exact isElemAbelian_conjSub hA.hypV.elemAbelian
  ne_bot := by
    intro γ hγ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg, Vv_smul_γ₀ hA.hypV.normalizes]
    exact fun h => hA.ne_bot ((conjSub_eq_bot_iff (g : G)).mp h)
  le_pCoreOf := by
    intro γ hγ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg, Vv_smul_γ₀ hA.hypV.normalizes, stab_smul, pCoreOf_conjSub,
      stab_γ₀ hA.hyp.le₁]
    exact conjSub_mono (g : G) (V_le_pCoreOf hA.hypV)
  pCoreOf_le_centralizer := by
    intro γ hγ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg, Vv_smul_γ₀ hA.hypV.normalizes, stab_smul, pCoreOf_conjSub,
      conjSub_centralizer, stab_γ₀ hA.hyp.le₁]
    exact conjSub_mono (g : G) (pCoreOf_le_centralizer hA.hypV)
  le_stab := by
    intro γ hγ ε hε
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg] at hε ⊢
    rw [Vv_smul_γ₀ hA.hypV.normalizes]
    have hd : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • ε) ≤ critDist G₀ G₁ G₂ E := by
      have h1 := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • ε)
      rw [smul_inv_smul] at h1
      rw [← h1]
      exact hε
    have hVle := V_le_stab_of_dist_le hA.hypV hA.ne_bot hd
    have hstab : CFSG.Quasithin.conjSub (g : G) (stab (g⁻¹ • ε)) = stab ε := by
      rw [← stab_smul (g := g) (γ := g⁻¹ • ε), smul_inv_smul]
    rw [← hstab]
    exact conjSub_mono (g : G) hVle
  le_pCoreOf_of_dist_lt := by
    intro γ hγ ε hε
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hγ
    rw [hg] at hε ⊢
    rw [Vv_smul_γ₀ hA.hypV.normalizes]
    obtain ⟨δ, hδ⟩ := exists_adj ε
    exact (conjSub_V_le_pCoreOf hA.hypV hA.ne_bot g hε hδ).1.trans
      (pCoreOf_mono_of_le_normalizer (ballStab_le_stab 1 ε) (le_normalizer_ballStab 1 ε))
  elemAbelian_δ := by
    intro hb δ hδ
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hδ
    rw [hg, Vv_smul hA.hypV.normalizes]
    exact isElemAbelian_conjSub (isElemAbelian_Vv_γ₁ hA.hypV hA.ne_bot hb)
  relIndex_inf := by
    intro γ δ hγ hδ
    have hδt : vtype δ = true := vtype_eq_true_of_mem_nbrs hγ hδ
    obtain ⟨g, hg | hg⟩ := exists_smul_edge (show (graph G₀ G₁ G₂).Adj γ δ from hδ)
    · rw [← hg.1, ← hg.2, stab_smul, stab_smul, pCoreOf_conjSub, pCoreOf_conjSub,
        stab_γ₀ hA.hyp.le₁, stab_γ₁ hA.hyp.le₂, ← conjSub_inf]
      exact (Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (g : G)).injective).trans h1
    · exfalso
      have h1 : vtype (g • γ₀ G₀ G₁ G₂) = true := by rw [hg.1]; exact hδt
      rw [vtype_smul, vtype_γ₀] at h1
      exact Bool.false_ne_true h1
  not_le_normalizer := by
    intro γ δ hγ hδ hle
    have hδt : vtype δ = true := vtype_eq_true_of_mem_nbrs hγ hδ
    obtain ⟨g, hg | hg⟩ := exists_smul_edge (show (graph G₀ G₁ G₂).Adj γ δ from hδ)
    · have hstabγ : stab γ = CFSG.Quasithin.conjSub (g : G) G₁ := by
        rw [← hg.1, stab_smul, stab_γ₀ hA.hyp.le₁]
      have hstabδ : stab δ = CFSG.Quasithin.conjSub (g : G) G₂ := by
        rw [← hg.2, stab_smul, stab_γ₁ hA.hyp.le₂]
      have hQ : pCoreOf 2 (stab γ) ⊓ pCoreOf 2 (stab δ) =
          CFSG.Quasithin.conjSub (g : G) (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) := by
        rw [hstabγ, hstabδ, pCoreOf_conjSub, pCoreOf_conjSub, ← conjSub_inf]
      have hN : CFSG.Quasithin.conjSub (g : G)⁻¹
          (Subgroup.normalizer ((pCoreOf 2 (stab γ) ⊓ pCoreOf 2 (stab δ) : Subgroup G) : Set G)) =
          Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G) := by
        rw [← conjSub_normalizer, hQ, conjSub_conjSub_inv]
      have hL : CFSG.Quasithin.conjSub (g : G)⁻¹ (stab δ) = G₂ := by
        rw [hstabδ, CFSG.Quasithin.conjSub_conjSub_inv]
      have hle' := CFSG.Quasithin.conjSub_mono (g : G)⁻¹ hle
      rw [hL, hN] at hle'
      exact h2 hle'
    · exfalso
      have h1 : vtype (g • γ₀ G₀ G₁ G₂) = true := by rw [hg.1]; exact hδt
      rw [vtype_smul, vtype_γ₀] at h1
      exact Bool.false_ne_true h1

end CFSG.Quasithin.F112Crit.APrime

end
