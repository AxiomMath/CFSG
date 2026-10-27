module

public import CFSG.Quasithin.Vol2.Ch11G2Q8CartanW
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Quasithin.Vol2.Ch11.SecS (gammaW centW)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (map_inf_sectionCentralizer pCoreOf_map_of_injective)

namespace KC1

variable {K : Type} [Field K] [CharP K 2]
variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem fix_of_trivial (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g t : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K))
    (htriv : ∀ u ∈ hf.pre (gmapG g S).toAddSubgroup, psiG hc0 hc1 π g t u * u⁻¹ ∈ Z)
    {y : Ix3 → K} (hy : y ∈ S) : g2Act t y = y := by
  obtain ⟨w, hw⟩ := hf.surj (g2Act g y)
  have hw1 : w ∈ hf.pre (gmapG g S).toAddSubgroup := by
    change f w ∈ gmapG g S
    rw [mem_gmapG, hw, g2Act_inv_apply]
    exact hy
  have h1 := htriv w hw1
  rw [← hf.ker, hf.map_mul_inv, psiG_apply, IsCoord.actG hf hc0 hc1, hw, sub_eq_zero,
    g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply] at h1
  have h2 := congrArg (g2Act g⁻¹) h1
  rwa [g2Act_inv_apply, g2Act_inv_apply] at h2

omit [CharP K 2] in
theorem single_mem_stdF {j : Ix3} {h : ℕ} (hj : ht j < h) (t : K) :
    (Pi.single j t : Ix3 → K) ∈ stdF K h := by
  intro k hk
  have hkj : k ≠ j := by
    rintro rfl
    omega
  simp [hkj]

omit [CharP K 2] in
theorem eu_injective {a b : K} (h : (eu 0 a : Ix3 → K) = eu 0 b) : a = b := by
  have := congrFun h (.inl 0)
  simpa [eu] using this

end KC1

open KC1 in
theorem factCartanPointG2_holds : FactCartanPointG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [eq_map_psiG_of_sylow hg, inf_normalizer_eqG hf hc0 hc1 g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torusG hf hc0 hc1 hK (by omega) g hD
  have hg' := sylow_conj_mulG hg hx
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg' (by rw [hK]; exact hU₁)
  subst hU1 hDx
  have hψ := psiG_injective hf hc0 hc1 (g * x)
  have hC₁ : centW ((torusG K).map (psiG hc0 hc1 π (g * x)))
      (gammaW H (hf.pre (gmapG (g * x) (stdF K 1)).toAddSubgroup)) =
      ((g2T (F := K)).comp (torHomC1 K)).range.map (psiG hc0 hc1 π (g * x)) := by
    rw [centW, gammaW_one_eqG h4 hf hc0 hc1 (g * x), pCoreOf_map_of_injective _ hψ,
      map_inf_sectionCentralizer _ hψ, torusG_inf_sc1]
  intro d hd htriv
  rw [hC₁] at hd
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hd
  have h1 := fix_of_trivial hf hc0 hc1 (g * x) _ (stdF K 1) htriv
    (show eu 0 (1 : K) ∈ stdF K 1 from mem_stdF_one_iff.mpr ⟨1, by rw [one_smul]⟩)
  rw [MonoidHom.comp_apply, g2Act_g2T_eu, torHomC1_apply] at h1
  have h2 := eu_injective h1
  rw [mul_one, Units.val_mul] at h2
  have hc : c = 1 := by
    have h3 : ((c⁻¹ : Kˣ) : K) = 1 := by
      rcases sq_eq_one_iff.mp (show ((c⁻¹ : Kˣ) : K) ^ 2 = 1 by rw [sq]; exact h2) with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    exact inv_eq_one.mp (Units.ext h3)
  rw [hc, map_one, map_one]

open KC1 in
theorem factCartanLineG2_holds : FactCartanLineG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₂ hU₂ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [eq_map_psiG_of_sylow hg, inf_normalizer_eqG hf hc0 hc1 g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torusG hf hc0 hc1 hK (by omega) g hD
  have hg' := sylow_conj_mulG hg hx
  have hU2 := eq_U2_of_isFlagWG hW hf hc0 hc1 hg' (by rw [hK]; exact hU₂)
  subst hU2 hDx
  intro d hd htriv
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hd
  have h0 := fix_of_trivial hf hc0 hc1 (g * x) _ (stdF K 2) htriv
    (single_mem_stdF (j := .inl 0) (by decide) (1 : K))
  have h2 := fix_of_trivial hf hc0 hc1 (g * x) _ (stdF K 2) htriv
    (single_mem_stdF (j := .inr 2) (by decide) (1 : K))
  have e0 := congrFun h0 (.inl 0)
  have e2 := congrFun h2 (.inr 2)
  rw [g2Act_g2T] at e0 e2
  simp [q6] at e0 e2
  have hs1 : s.1 = 1 := e0
  have hs2 : s.2 = 1 := by
    rw [hs1] at e2
    exact Units.ext (by simpa using e2)
  rw [show s = 1 from Prod.ext hs1 hs2, map_one, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecA
