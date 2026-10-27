module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NCore
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aXIrreducible

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne.B1Normal

private theorem normHom_sign_on_gens {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {g : G} (hgN : g ∈ nB b z) (hgb : g * b * g⁻¹ = b)
    (hgz : ∀ i : Fin 3, g * GGFF.zs z i * g⁻¹ = GGFF.zs z i ∨
      g * GGFF.zs z i * g⁻¹ = (GGFF.zs z i)⁻¹) :
    ∀ x ∈ ({bG, zsG 0, zsG 1, zsG 2} : Set ↥(GGFF.Bt b z)),
      (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ x = x ∨
      (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ x = x⁻¹ := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · left
    apply Subtype.ext
    rw [normHom_apply_coe]
    simpa [bG] using hgb
  · rcases hgz 0 with h | h
    · left; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h
    · right; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h
  · rcases hgz 1 with h | h
    · left; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h
    · right; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h
  · rcases hgz 2 with h | h
    · left; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h
    · right; apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using h

private theorem normHom_comm_of_fixes_inverts {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {g τ : G}
    (hgN : g ∈ nB b z) (hgb : g * b * g⁻¹ = b)
    (hτN : τ ∈ nB b z) (hτb : τ * b * τ⁻¹ = b)
    (hτinv : ∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹) :
    (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ * (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ =
      (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ *
        (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ := by
  have hzs : ∀ i : Fin 3,
      ((GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ *
        (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩) (zsG i) =
      ((GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ *
        (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩) (zsG i) := by
    intro i
    obtain ⟨j, e, -, hge⟩ :=
      h.facts.stab g hgN (by rw [hgb]; exact Subgroup.mem_zpowers b) i
    have hgz : (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ (zsG i) = (zsG j) ^ e := by
      apply Subtype.ext
      rw [normHom_apply_coe, Subgroup.coe_pow]
      simpa [zsG] using hge
    have hτi : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG i) = (zsG i)⁻¹ := by
      apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using hτinv i
    have hτj : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG j) = (zsG j)⁻¹ := by
      apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using hτinv j
    calc ((GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ *
            (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩) (zsG i)
        = (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩
            ((GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG i)) := rfl
      _ = (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ ((zsG i)⁻¹) := by rw [hτi]
      _ = ((GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ (zsG i))⁻¹ := by rw [map_inv]
      _ = ((zsG j) ^ e)⁻¹ := by rw [hgz]
      _ = ((zsG j)⁻¹) ^ e := (inv_pow (zsG j) e).symm
      _ = ((GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG j)) ^ e := by rw [hτj]
      _ = (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ ((zsG j) ^ e) := by rw [map_pow]
      _ = (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩
            ((GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ (zsG i)) := by rw [hgz]
      _ = ((GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ *
            (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩) (zsG i) := rfl
  apply mulAut_ext_on_gens closure_four_gens
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [MulAut.mul_apply, MulAut.mul_apply]
    have hg : (GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ bG = bG := by
      apply Subtype.ext; rw [normHom_apply_coe]; simpa [bG] using hgb
    have hτ : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ bG = bG := by
      apply Subtype.ext; rw [normHom_apply_coe]; simpa [bG] using hτb
    rw [hg, hτ]
    exact hg
  · exact hzs 0
  · exact hzs 1
  · exact hzs 2

theorem x_irreducible {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    {τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (hMono : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirrMono : ∀ H : Subgroup G, H ≤ bOne z → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = bOne z)
    (hB1not : ∃ m ∈ nB b z, ∃ y ∈ bOne z, m * y * m⁻¹ ∉ bOne z) :
    ∀ U : Subgroup ↥(GGFF.Bt b z),
      (∀ σ : MulAut ↥(GGFF.Bt b z), σ ∈ (GGFF.Bt b z).normalizerMonoidHom.range →
        Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hτN : τ ∈ nB b z := by
    have h := (hMono.mem τ (by simp)).1
    rwa [BB_eq_Bt] at h
  have hτb : τ * b * τ⁻¹ = b := (hMono.mem τ (by simp)).2
  have hτinv : ∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹ := by
    intro i; fin_cases i
    · exact hMono.inv.1
    · exact hMono.inv.2.1
    · exact hMono.inv.2.2
  have hτXb : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ bG = bG := by
    apply Subtype.ext; rw [normHom_apply_coe]; simpa [bG] using hτb
  have hτXz0 : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG 0) = (zsG 0)⁻¹ := by
    apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using hτinv 0
  have hτXz1 : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG 1) = (zsG 1)⁻¹ := by
    apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using hτinv 1
  have hτXz2 : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ (zsG 2) = (zsG 2)⁻¹ := by
    apply Subtype.ext; rw [normHom_apply_coe]; simpa [zsG] using hτinv 2
  have hτX2 : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ *
      (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ = 1 :=
    mulAut_mul_self_of_sign_on_gens closure_four_gens
      (normHom_sign_on_gens hτN hτb fun i => Or.inr (hτinv i))
  have hτXmem : (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ ∈
      (GGFF.Bt b z).normalizerMonoidHom.range := ⟨⟨τ, hτN⟩, rfl⟩
  have hB1irr : ∀ U₁ : Subgroup ↥(GGFF.Bt b z),
      U₁ ≤ (bOne z).subgroupOf (GGFF.Bt b z) →
      (∀ σ : MulAut ↥(GGFF.Bt b z), σ ∈ (GGFF.Bt b z).normalizerMonoidHom.range →
        σ * (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ =
          (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩ * σ → Subgroup.map σ U₁ = U₁) →
      U₁ = ⊥ ∨ U₁ = (bOne z).subgroupOf (GGFF.Bt b z) := by
    intro U₁ hU₁le hU₁inv
    have hHle : U₁.map (GGFF.Bt b z).subtype ≤ bOne z := by
      rintro x ⟨u, hu, rfl⟩
      exact hU₁le hu
    have hinv : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G),
        ∀ x ∈ U₁.map (GGFF.Bt b z).subtype, g * x * g⁻¹ ∈ U₁.map (GGFF.Bt b z).subtype := by
      intro g hg x hx
      have hg' : g ∈ ({τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
        tauto
      have hgN : g ∈ nB b z := by
        have h := (hMono.mem g hg').1
        rwa [BB_eq_Bt] at h
      have hgb : g * b * g⁻¹ = b := (hMono.mem g hg').2
      have hcomm := normHom_comm_of_fixes_inverts h hgN hgb hτN hτb hτinv
      have hmap := hU₁inv _ ⟨⟨g, hgN⟩, rfl⟩ hcomm
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr
        ⟨(GGFF.Bt b z).normalizerMonoidHom ⟨g, hgN⟩ u,
          by rw [← hmap]; exact Subgroup.mem_map_of_mem _ hu, ?_⟩
      exact normHom_apply_coe g hgN u
    by_cases hHbot : U₁.map (GGFF.Bt b z).subtype = ⊥
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective U₁ (GGFF.Bt b z).subtype_injective).mp hHbot
    · right
      have hHz : U₁.map (GGFF.Bt b z).subtype = bOne z :=
        hirrMono _ hHle hHbot hinv
      have hle : bOne z ≤ GGFF.Bt b z := GGFF.SettingCore.tor_le_Bt b z
      have hmaps : U₁.map (GGFF.Bt b z).subtype =
          ((bOne z).subgroupOf (GGFF.Bt b z)).map (GGFF.Bt b z).subtype := by
        rw [hHz, Subgroup.map_subgroupOf_eq_of_le hle]
      exact (Subgroup.map_subtype_inj (H := GGFF.Bt b z)).mp hmaps
  have hmove : ∃ σ : MulAut ↥(GGFF.Bt b z),
      σ ∈ (GGFF.Bt b z).normalizerMonoidHom.range ∧ σ bG ∉ Subgroup.zpowers bG :=
    exists_move h
  have hB1not' : ∃ σ : MulAut ↥(GGFF.Bt b z),
      σ ∈ (GGFF.Bt b z).normalizerMonoidHom.range ∧
      Subgroup.map σ ((bOne z).subgroupOf (GGFF.Bt b z)) ≠
        (bOne z).subgroupOf (GGFF.Bt b z) := by
    obtain ⟨m, hm, y, hy, hmy⟩ := hB1not
    refine ⟨(GGFF.Bt b z).normalizerMonoidHom ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, ?_⟩
    intro heq
    apply hmy
    have hyB : y ∈ GGFF.Bt b z := GGFF.SettingCore.tor_le_Bt b z hy
    have hmem : (⟨y, hyB⟩ : ↥(GGFF.Bt b z)) ∈
        (bOne z).subgroupOf (GGFF.Bt b z) := hy
    have h2 : (GGFF.Bt b z).normalizerMonoidHom ⟨m, hm⟩ ⟨y, hyB⟩ ∈
        (bOne z).subgroupOf (GGFF.Bt b z) := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ hmem
    change (((GGFF.Bt b z).normalizerMonoidHom ⟨m, hm⟩) ⟨y, hyB⟩ : G) ∈ bOne z at h2
    rw [normHom_apply_coe] at h2
    exact h2
  exact CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.X_irreducible_of_move
    (B := GGFF.Bt b z) (B₁ := bOne z) (b := b)
    (b₁ := GGFF.zs z 0) (b₂ := GGFF.zs z 1) (b₃ := GGFF.zs z 2)
    (X := (GGFF.Bt b z).normalizerMonoidHom.range)
    (τX := (GGFF.Bt b z).normalizerMonoidHom ⟨τ, hτN⟩)
    rfl (GGFF.SettingCore.tor_eq_closure z) (isElemAb_Bt h)
    (GGFF.SettingCore.b_mem_Bt b z) (GGFF.SettingCore.zs_mem_Bt b z 0)
    (GGFF.SettingCore.zs_mem_Bt b z 1) (GGFF.SettingCore.zs_mem_Bt b z 2)
    hτXmem hτX2 hτXb hτXz0 hτXz1 hτXz2 hB1irr hmove hB1not' hU

end CFSG.StandardType.FF81.PropOne.B1Normal

end
