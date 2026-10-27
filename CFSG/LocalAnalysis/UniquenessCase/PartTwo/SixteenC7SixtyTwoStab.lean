module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c7_card_of_bar2 {K : Subgroup G} (h : IsL3 (Bar2 K) 1) :
    ∃ a : ℕ, Nat.card K = 2 ^ a * 168 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  refine ⟨a, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have h2 : Nat.card (Bar2 K) = 168 := card_eq_of_isL3 h
  rw [h1]
  show Nat.card (Bar2 K) * Nat.card ↥(CFSG.pCore 2 ↥K) = 2 ^ a * 168
  rw [h2, ha]
  ring

theorem s16c7_exists_tensor_lift (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil ⊥ V) {K₁ K₂ : Subgroup G} (hK₁M : K₁ ≤ D.M) (hK₂M : K₂ ≤ D.M)
    (hn₁₂ : K₁ ≤ normalizer (K₂ : Set G))
    (hMN : D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    (hA : Nat.card (barSub ⊥ V hV (K₁ ⊔ K₂)) = 168 * 168) {a b : ℕ}
    (h₁ : Nat.card K₁ = 2 ^ a * 168) (h₂ : Nat.card K₂ = 2 ^ b * 168)
    (hreal : (tensorPairModel SL32 SL32).RealizesMod (barSub ⊥ V hV (K₁ ⊔ K₂)))
    (hMA : Mbar D.M ⊥ V hV ≤
      normalizer (barSub ⊥ V hV (K₁ ⊔ K₂) : Set (MulAut (Vtil ⊥ V hV)))) :
    ∃ (z : G) (X : Subgroup G), z ∈ V ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧
      V ⊓ centralizer (D.T : Set G) = Subgroup.zpowers z ∧
      V ⊓ centralizer (X : Set G) = Subgroup.zpowers z ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧
      ∀ j ∈ K₁ ⊔ K₂, j * z = z * j → ∃ x ∈ X, ∃ t ∈ D.T, j = x * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h𝓛M : K₁ ⊔ K₂ ≤ D.M := sup_le hK₁M hK₂M
  have h𝓛s : K₁ ⊔ K₂ ≤ stabTil ⊥ V := h𝓛M.trans hMs
  have hTs : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMs
  have hN2 : IsPGroup 2 ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) :=
    s16c7_isPGroup_two_inf_centralizer V hV hn₁₂ h𝓛s hA h₁ h₂
  have hNT : (K₁ ⊔ K₂) ⊓ centralizer (V : Set G) ≤ D.T :=
    s16c7_inf_centralizer_le h𝓛M hMN (hMs.trans (stabTil_le_normalizer ⊥ V)) D.sylowM hN2
  have h4 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    D.sylowM.inf_of_le_normalizer h𝓛M hMN
  have h5 := s16c7_isSylowOf_barSub ⊥ V hV h4 h𝓛s
  have hTbar : IsPGroup 2 (barSub ⊥ V hV D.T) := by
    have h0 : IsPGroup 2 (D.T.subgroupOf (stabTil ⊥ V)) := D.sylowM.isPGroup.comap_subtype
    exact h0.map (actTil ⊥ V hV)
  have hTbA : barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂)) =
      barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (K₁ ⊔ K₂) := by
    have hle : barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂)) ≤
        barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (K₁ ⊔ K₂) :=
      le_inf (barSub_mono ⊥ V hV inf_le_left) (barSub_mono ⊥ V hV inf_le_right)
    exact (h5.eq_of_le hle inf_le_right hTbar.to_inf_left).symm
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (K₁ ⊔ K₂))
      (barSub ⊥ V hV (K₁ ⊔ K₂)) := by
    rw [← hTbA]
    exact h5
  have hTn : barSub ⊥ V hV D.T ≤
      normalizer (barSub ⊥ V hV (K₁ ⊔ K₂) : Set (MulAut (Vtil ⊥ V hV))) :=
    (barSub_mono ⊥ V hV D.sylowM.le).trans hMA
  obtain ⟨zt, Xb, hz1, hz2, hfixT, hXbA, hXbp, hXb9, hfixX, -, hstab⟩ :=
    s16c7_tensor_data hreal hTn hsyl
  obtain ⟨z, rfl⟩ := mkTil_surjective ⊥ V hV zt
  have hSyl3 : CFSG.ABGLocalTools.IsSylowOf 3 Xb (barSub ⊥ V hV (K₁ ⊔ K₂)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hXbA, hXbp, ?_⟩
    have e := Subgroup.relIndex_mul_card (H := Xb) (K := barSub ⊥ V hV (K₁ ⊔ K₂))
    rw [inf_eq_left.2 hXbA, hXb9, hA] at e
    omega
  obtain ⟨X, hXsyl, hXb⟩ := s16c7_exists_lift_sylow (p := 3) ⊥ V hV h𝓛s hSyl3
  have hXs : X ≤ stabTil ⊥ V := hXsyl.le.trans h𝓛s
  have hfixX' : fixV (barSub ⊥ V hV X) = Subgroup.zpowers (mkTil ⊥ V hV z) := by
    rw [hXb]
    exact hfixX
  have hCX := s16c7_inf_centralizer_eq_zpowers V hV hXs hfixX'
  have hCT := s16c7_inf_centralizer_eq_zpowers V hV hTs hfixT
  have hz1' : z.val ≠ 1 := by
    intro h
    apply hz1
    have : z = 1 := IntMod.val_injective (by rw [h]; rfl)
    rw [this, map_one]
  refine ⟨z.val, X, z.val_mem, hz1', hV.2 z.val z.val_mem, hCT, hCX, hXsyl, ?_⟩
  intro j hj hjz
  have hjs : j ∈ stabTil ⊥ V := h𝓛s hj
  have hjb : actTil ⊥ V hV ⟨j, hjs⟩ ∈ barSub ⊥ V hV (K₁ ⊔ K₂) :=
    actTil_mem_barSub ⊥ V hV hj hjs
  have hjfix : actTil ⊥ V hV ⟨j, hjs⟩ (mkTil ⊥ V hV z) = mkTil ⊥ V hV z := by
    rw [s16c7_act_mkTil_eq_iff]
    calc j * z.val * j⁻¹ = (z.val * j) * j⁻¹ := by rw [hjz]
      _ = z.val := by group
  obtain ⟨xb, hxb, tb, htb, hxt⟩ := hstab _ hjb hjfix
  rw [← hXb] at hxb
  obtain ⟨x, hxX, rfl⟩ := (mem_barSub ⊥ V hV X xb).1 hxb
  rw [← hTbA] at htb
  obtain ⟨s, hsTL, rfl⟩ := (mem_barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂)) tb).1 htb
  have hxL : (x : G) ∈ K₁ ⊔ K₂ := hXsyl.le hxX
  have hsL : (s : G) ∈ K₁ ⊔ K₂ := (Subgroup.mem_inf.1 hsTL).2
  have hsT : (s : G) ∈ D.T := (Subgroup.mem_inf.1 hsTL).1
  have hker : actTil ⊥ V hV ((x * s)⁻¹ * ⟨j, hjs⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hxt]
    simp
  have hn : (((x * s)⁻¹ * ⟨j, hjs⟩ : ↥(stabTil ⊥ V)) : G) ∈
      (K₁ ⊔ K₂) ⊓ centralizer (V : Set G) := by
    refine Subgroup.mem_inf.2 ⟨?_, (s16c7_actTil_eq_one_iff_mem_centralizer V hV _).1 hker⟩
    show ((x : G) * (s : G))⁻¹ * j ∈ K₁ ⊔ K₂
    exact (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).inv_mem ((K₁ ⊔ K₂).mul_mem hxL hsL)) hj
  refine ⟨x, hxX, (s : G) * (((x * s)⁻¹ * ⟨j, hjs⟩ : ↥(stabTil ⊥ V)) : G),
    D.T.mul_mem hsT (hNT hn), ?_⟩
  show j = (x : G) * ((s : G) * (((x : G) * (s : G))⁻¹ * j))
  group

theorem s16c7_exists_X_z (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil ⊥ V) {K₁ K₂ : Subgroup G} (hK₁M : K₁ ≤ D.M) (hK₂M : K₂ ≤ D.M)
    (hn₁₂ : K₁ ≤ normalizer (K₂ : Set G))
    (hMN : D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    (hA : Nat.card (barSub ⊥ V hV (K₁ ⊔ K₂)) = 168 * 168) {a b : ℕ}
    (h₁ : Nat.card K₁ = 2 ^ a * 168) (h₂ : Nat.card K₂ = 2 ^ b * 168)
    (hreal : (tensorPairModel SL32 SL32).RealizesMod (barSub ⊥ V hV (K₁ ⊔ K₂)))
    (hMA : Mbar D.M ⊥ V hV ≤
      normalizer (barSub ⊥ V hV (K₁ ⊔ K₂) : Set (MulAut (Vtil ⊥ V hV)))) :
    ∃ (z : G) (X : Subgroup G), z ∈ V ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧
      V ⊓ centralizer (D.T : Set G) = Subgroup.zpowers z ∧
      V ⊓ centralizer (X : Set G) = Subgroup.zpowers z ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧ Permutes X D.T := by
  obtain ⟨z, X, hzV, hz1, hz2, hCT, hCX, hXsyl, hcov⟩ :=
    s16c7_exists_tensor_lift D V hV hMs hK₁M hK₂M hn₁₂ hMN hA h₁ h₂ hreal hMA
  refine ⟨z, X, hzV, hz1, hz2, hCT, hCX, hXsyl, ?_⟩
  have hzT : z ∈ centralizer (D.T : Set G) :=
    (Subgroup.mem_inf.1 (hCT ▸ Subgroup.mem_zpowers z : z ∈ V ⊓ centralizer (D.T : Set G))).2
  have hzX : z ∈ centralizer (X : Set G) :=
    (Subgroup.mem_inf.1 (hCX ▸ Subgroup.mem_zpowers z : z ∈ V ⊓ centralizer (X : Set G))).2
  exact s16c7_permutes_of_cover hXsyl.le (D.sylowM.le.trans hMN)
    (fun t ht => Subgroup.mem_centralizer_iff.1 hzT t ht)
    (fun x hx => Subgroup.mem_centralizer_iff.1 hzX x hx) hcov

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
