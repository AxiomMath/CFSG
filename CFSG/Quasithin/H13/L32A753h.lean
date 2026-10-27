module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8NoOff
public import CFSG.Quasithin.Background.SmithB45U33Mid

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin Orbit
open scoped Pointwise

@[expose] def genS (j : ℕ) : ↥(quasithinG2 (ZMod 2)) := ⟨sGenE j, sGenE_mem j⟩

theorem coe_foldl_genS (w : List ℕ) (h : ↥(quasithinG2 (ZMod 2))) :
    ((w.foldl (fun g j => g * genS j) h : ↥(quasithinG2 (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) =
        w.foldl (fun g j => g * sGenE j) (h : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) := by
  induction w generalizing h with
  | nil => rfl
  | cons j w ih => exact ih (h * genS j)

theorem sEltG_eq_foldl (i : ℕ) :
    sEltG i = (sWords.getD i []).foldl (fun g j => g * genS j) 1 :=
  Subtype.ext (by rw [coe_foldl_genS]; rfl)

theorem genS_mem_iff
    {j : ℕ} (hj : j < 3) :
    genS j ∈ g2Derived (ZMod 2) ↔ j = 0 := by
  have h1 : (zT01 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) ∈
      ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := G2NoOff.zT01_mem
  have h2 : (zT10 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) ∈
      ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := G2NoOff.zT10_mem
  have h3 := G2NoOff.zX_not_mem
  rw [g2Derived, Subgroup.mem_subgroupOf]
  interval_cases j
  · exact iff_of_true h1 rfl
  · exact iff_of_false h3 one_ne_zero
  · refine iff_of_false (fun h => h3 ?_) (by norm_num)
    change (zT10 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) * zT01 * zX * zT01 *
      zT10 ∈ _ at h
    have e : (zX : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) =
        (zT10 * zT01)⁻¹ * (zT10 * zT01 * zX * zT01 * zT10) * (zT01 * zT10)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (mul_mem h2 h1)) h) (inv_mem (mul_mem h1 h2))

theorem foldl_genS_mem_iff
    (w : List ℕ)
    (hw : ∀ j ∈ w, j < 3) (h : ↥(quasithinG2 (ZMod 2))) :
    w.foldl (fun g j => g * genS j) h ∈ g2Derived (ZMod 2) ↔
      (h ∈ g2Derived (ZMod 2) ↔ Even (w.countP fun j => j ≠ 0)) := by
  induction w generalizing h with
  | nil => simp
  | cons j w ih =>
    rw [List.foldl_cons, ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)),
      Subgroup.mul_mem_iff_of_index_two B45U33.index_g2Derived,
      genS_mem_iff (hw j List.mem_cons_self), List.countP_cons]
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, iff_false, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        Nat.even_add_one]
      tauto

theorem sInner_words_even : ∀ i ∈ sInner, (sWords.getD i []).countP (fun j => j ≠ 0) % 2 = 0 := by
  decide

theorem sEltG_mem_of_inner
    {i : ℕ} (hi : i ∈ sInner) :
    sEltG i ∈ g2Derived (ZMod 2) := by
  have hi64 : i < 64 := by
    simp only [sInner, List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  rw [sEltG_eq_foldl, foldl_genS_mem_iff _ (sWords_spec i hi64).2]
  exact iff_of_true (one_mem _) (Nat.even_iff.2 (sInner_words_even i hi))

theorem card_fixV_le_eight
    {g : ↥(quasithinG2 (ZMod 2))} (hg : g ∉ g2Derived (ZMod 2)) (hg2 : g ^ 2 = 1) :
    Nat.card (fixV ((Subgroup.zpowers g).map (g2QAct (ZMod 2)))) ≤ 8 := by
  classical
  set ρ := g2QAct (ZMod 2) with hρ
  have hDn : (g2Derived (ZMod 2)).Normal :=
    Subgroup.normal_of_index_eq_two B45U33.index_g2Derived
  have hsq : ∀ {x : ↥(quasithinG2 (ZMod 2))}, x ^ 2 = 1 →
      ∀ b ∈ Subgroup.zpowers x, b ^ 2 = 1 := by
    intro x hx b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hp : IsPGroup 2 ↥(Subgroup.zpowers g) := fun b =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hsq hg2 b.1 b.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set g' := c * g * c⁻¹ with hg'
  have hg'S : g' ∈ sSubG := by
    have h1 : MulAut.conj c • g ∈ MulAut.conj c • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP (Subgroup.mem_zpowers g))
    rw [← Sylow.coe_subgroup_smul, hc] at h1
    exact h1
  have hg'D : g' ∉ g2Derived (ZMod 2) := by
    intro h
    apply hg
    have h1 := hDn.conj_mem _ h c⁻¹
    have e : c⁻¹ * g' * c⁻¹⁻¹ = g := by rw [hg']; group
    rwa [e] at h1
  have hg'2 : g' ^ 2 = 1 := by
    rw [hg', pow_two, show c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ by group, ← pow_two,
      hg2, mul_one, mul_inv_cancel]
  obtain ⟨i, hi64, hi⟩ := mem_sSubG.1 hg'S
  set B := Subgroup.zpowers g' with hB
  have hBS : B ≤ sSubG := Subgroup.zpowers_le.2 hg'S
  have hiB : i ∈ idx B := mem_idx.2 ⟨hi64, hi ▸ Subgroup.mem_zpowers g'⟩
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [sEltG_zero] at hi
    exact hg'D (hi ▸ (g2Derived (ZMod 2)).one_mem)
  rcases List.mem_append.1 (idx_inv (hsq hg'2) hiB hi0) with hin | hout
  · exact absurd (hi ▸ sEltG_mem_of_inner hin) hg'D
  · let P' : ℕ → Bool := fun c => decide (∀ k ∈ idx B, fixQB (sM k) c = true)
    have hP' : ∀ c : O0C, P' c.1 = true ↔ ∀ k ∈ idx B, fixQB (sM k) c.1 = true := fun c => by
      simp [P']
    have hC := card_fixV_Q hBS P' hP'
    have hCi : Nat.card (fixV (B.map ρ)) ≤
        (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length := by
      rw [hC]
      refine length_filter_le fun c hc => ?_
      simp only [P', Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [Bool.and_eq_true]
      exact ⟨hc.1, hc.2 i hiB⟩
    rw [(sOuter_fix i hout).2] at hCi
    have hmap : B.map ρ = ((Subgroup.zpowers g).map ρ).map (MulAut.congr (ρ c)).toMonoidHom := by
      rw [hB, MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      congr 1
      change ρ (c * g * c⁻¹) = MulAut.congr (ρ c) (ρ g)
      rw [congr_eq_conj, map_mul, map_mul, map_inv]
    have hfix : Nat.card (fixV (B.map ρ)) = Nat.card (fixV ((Subgroup.zpowers g).map ρ)) := by
      rw [hmap, B1Red.fixV_map_congr',
        Subgroup.card_map_of_injective (f := (ρ c).toMonoidHom) (ρ c).injective]
    rw [← hfix]
    exact hCi

end CFSG.Quasithin.H13.L32A.M753
