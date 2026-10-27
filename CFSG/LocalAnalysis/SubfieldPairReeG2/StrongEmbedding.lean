module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final

public section

open Subgroup CFSG CFSG.BenderSuzuki CFSG.BenderSuzuki.PFchapter1section1

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

def StronglyEmbeddedIn {Γ : Type*} [Group Γ] (J M : Subgroup Γ) : Prop :=
  M ≤ J ∧ M ≠ J ∧ (∃ x ∈ M, orderOf x = 2) ∧
    ∀ g ∈ J, g ∉ M → ∀ x ∈ M, orderOf x = 2 → g * x * g⁻¹ ∉ M

theorem stronglyEmbeddedIn_of_centralizer {Γ : Type*} [Group Γ] (J M : Subgroup Γ)
    (hMJ : M ≤ J) (hne : M ≠ J) {t : Γ} (htM : t ∈ M) (ht2 : orderOf t = 2)
    (hfus : ∀ u ∈ M, orderOf u = 2 → ∃ m ∈ M, m * t * m⁻¹ = u)
    (hcent : ∀ x ∈ J, x * t = t * x → x ∈ M) : StronglyEmbeddedIn J M := by
  refine ⟨hMJ, hne, ⟨t, htM, ht2⟩, ?_⟩
  intro g hgJ hgM x hxM hx2 hgx
  obtain ⟨a, haM, ha⟩ := hfus x hxM hx2
  have hy2 : orderOf (g * x * g⁻¹) = 2 := by
    rw [← hx2]
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    rwa [MulAut.conj_apply] at this
  obtain ⟨b, hbM, hb⟩ := hfus _ hgx hy2
  have hz : (b⁻¹ * g * a) * t = t * (b⁻¹ * g * a) := by
    have h1 : (b⁻¹ * g * a) * t * (b⁻¹ * g * a)⁻¹ = t := by
      calc (b⁻¹ * g * a) * t * (b⁻¹ * g * a)⁻¹
          = b⁻¹ * (g * (a * t * a⁻¹) * g⁻¹) * b := by group
        _ = b⁻¹ * (b * t * b⁻¹) * b := by rw [ha, hb]
        _ = t := by group
    exact (mul_inv_eq_iff_eq_mul.1 h1)
  have hzJ : b⁻¹ * g * a ∈ J :=
    J.mul_mem (J.mul_mem (J.inv_mem (hMJ hbM)) hgJ) (hMJ haM)
  have hzM := hcent _ hzJ hz
  apply hgM
  have : g = b * (b⁻¹ * g * a) * a⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hbM hzM) (M.inv_mem haM)

theorem isStronglyEmbedded_subgroupOf {Γ : Type*} [Group Γ] [Finite Γ] {J M : Subgroup Γ}
    (h : StronglyEmbeddedIn J M) : BenderSuzuki.IsStronglyEmbedded (M.subgroupOf J) := by
  obtain ⟨hMJ, hMne, ⟨x₀, hx₀M, hx₀⟩, hse⟩ := h
  refine ⟨?_, ⟨⟨x₀, hMJ hx₀M⟩, Subgroup.mem_subgroupOf.2 hx₀M, ?_⟩, ?_⟩
  · intro htop
    exact hMne (le_antisymm hMJ (Subgroup.subgroupOf_eq_top.1 htop))
  · have h2 : x₀ ^ 2 = 1 := by rw [← hx₀]; exact pow_orderOf_eq_one x₀
    have h1 : x₀ ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hx₀; omega
    refine ⟨fun h => h1 (congrArg Subtype.val h), Subtype.ext ?_⟩
    simpa using h2
  · intro g hgM x hxM hxconj hx
    have hxmap : x ∈ (M.subgroupOf J).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa [rightConjugate, Subgroup.conjBy] using hxconj
    obtain ⟨y, hy, hyx⟩ := hxmap
    have hgxg : (g : Γ) * (x : Γ) * (g : Γ)⁻¹ ∈ M := by
      have h1 : (g : J) * x * (g : J)⁻¹ = y := by
        rw [← hyx]; simp [MulAut.conj_apply, mul_assoc]
      have h2 := congrArg Subtype.val h1
      have h3 : (y : Γ) ∈ M := Subgroup.mem_subgroupOf.1 hy
      have h4 : (g : Γ) * (x : Γ) * (g : Γ)⁻¹ = (y : Γ) := by simpa using h2
      rw [h4]; exact h3
    have hx2 : orderOf (x : Γ) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · have := congrArg Subtype.val hx.2; simpa using this
      · intro h1; exact hx.1 (Subtype.ext (by simpa using h1))
    exact hse g g.2 hgM x (Subgroup.mem_subgroupOf.1 hxM) hx2 hgxg


theorem false_of_stronglyEmbeddedIn {Γ : Type*} [Group Γ] [Finite Γ]
    {J M : Subgroup Γ} (h : StronglyEmbeddedIn J M) {E : Subgroup Γ} (hEJ : E ≤ J)
    (hE4 : Nat.card E = 4) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    {W : Subgroup Γ} (hWM : W ≤ M) (hWs : IsSimpleGroup W)
    (hWnc : ∃ x y : W, x * y ≠ y * x) (hWinv : ∃ s ∈ W, orderOf s = 2) : False := by
  classical
  have hMJ : M ≤ J := h.1
  have hM'se := isStronglyEmbedded_subgroupOf h
  have hSE := theorem_SE (M.subgroupOf J) hM'se
  set L : Subgroup J := involutionCore J with hL
  have hrank : TwoRankAtLeastTwo L := by
    set E₁ : Subgroup J := E.subgroupOf J with hE₁
    have hE₁L : E₁ ≤ L := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact L.one_mem
      · apply Subgroup.subset_closure
        refine ⟨hx1, Subtype.ext ?_⟩
        have := hE2 (x : Γ) (Subgroup.mem_subgroupOf.1 hx)
        simpa using this
    refine ⟨E₁.subgroupOf L, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁L).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hE4]
    · intro x
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      have := hE2 (x : Γ) (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 x.2))
      simpa using this
  rcases hSE with hlow | ⟨-, -, hBorel⟩
  · exact hlow hrank
  · set O : Subgroup L := twoPrimeCore L with hO
    set B : Subgroup (L ⧸ O) :=
      (((M.subgroupOf J ⊓ L).subgroupOf L).map (QuotientGroup.mk' O)) with hB
    have hBsolv : Group.IsSolvable B := hBorel.1
    have hWJ : W ≤ J := hWM.trans hMJ
    set φ : W →* J := Subgroup.inclusion hWJ with hφ
    obtain ⟨s, hsW, hs2⟩ := hWinv
    set s' : W := ⟨s, hsW⟩ with hs'
    have hs'2 : orderOf s' = 2 := by rw [← hs2]; exact Subgroup.orderOf_mk s hsW
    have hφinj : Function.Injective φ := Subgroup.inclusion_injective hWJ
    have hφs2 : orderOf (φ s') = 2 := by
      rw [← hs'2]; exact orderOf_injective φ hφinj s'
    have hWL : ∀ w : W, φ w ∈ L := by
      have hN : (L.comap φ) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.comap φ) with hbot | htop
        · exfalso
          have hmem : s' ∈ L.comap φ := by
            rw [Subgroup.mem_comap]
            apply Subgroup.subset_closure
            refine ⟨?_, ?_⟩
            · intro h1; rw [h1, orderOf_one] at hφs2; omega
            · rw [← hφs2]; exact pow_orderOf_eq_one _
          rw [hbot, Subgroup.mem_bot] at hmem
          rw [hmem, map_one, orderOf_one] at hφs2
          omega
        · exact htop
      intro w
      have : w ∈ L.comap φ := by rw [hN]; exact Subgroup.mem_top w
      exact this
    set ψ₁ : W →* L := φ.codRestrict L hWL with hψ₁
    have hψ₁inj : Function.Injective ψ₁ := by
      intro x y hxy
      apply hφinj
      have := congrArg Subtype.val hxy
      simpa [hψ₁] using this
    set f : W →* L ⧸ O := (QuotientGroup.mk' O).comp ψ₁ with hf
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
      · exact hbot
      · exfalso
        have hs'ker : s' ∈ f.ker := by rw [htop]; exact Subgroup.mem_top s'
        have hψmem : ψ₁ s' ∈ O := by
          have := (MonoidHom.mem_ker.1 hs'ker)
          simpa [hf] using this
        have hord : orderOf (⟨ψ₁ s', hψmem⟩ : O) = 2 := by
          rw [Subgroup.orderOf_mk, orderOf_injective ψ₁ hψ₁inj s']
          exact hs'2
        have hdvd : 2 ∣ Nat.card O := hord ▸ orderOf_dvd_natCard _
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := L)
        exact absurd (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd) (by norm_num)
    have hfB : ∀ w : W, f w ∈ B := by
      intro w
      refine ⟨ψ₁ w, ?_, rfl⟩
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (hWM w.2) |> fun h => h)
      · exact hWL w
    set f' : W →* B := f.codRestrict B hfB with hf'
    have hf'inj : Function.Injective f' := by
      intro x y hxy
      apply hfinj
      have := congrArg Subtype.val hxy
      simpa [hf'] using this
    haveI : Group.IsSolvable W := solvable_of_solvable_injective hf'inj
    obtain ⟨x, y, hxy⟩ := hWnc
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := W)).2 inferInstance x y)


end CFSG.LocalAnalysis.SubfieldPairReeG2
