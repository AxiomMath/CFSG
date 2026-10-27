module

public import CFSG.LocalAnalysis.SubfieldPairReeG2.StrongEmbedding

public section

open Subgroup

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

theorem exists_conj_involution_sylow {Γ : Type*} [Group Γ] [Finite Γ] (H : Subgroup Γ)
    (S : Sylow 2 Γ) (hSH : (S : Subgroup Γ) ≤ H) {u : Γ} (huH : u ∈ H) (hu2 : orderOf u = 2) :
    ∃ h ∈ H, ∃ s ∈ (S : Subgroup Γ), h * s * h⁻¹ = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SH : Sylow 2 H := S.subtype hSH
  let u' : H := ⟨u, huH⟩
  have hu'2 : orderOf u' = 2 := by rw [← hu2]; exact Subgroup.orderOf_mk u huH
  have hP : IsPGroup 2 (Subgroup.zpowers u') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu'2]; simp
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H SH Q
  have hu'Q : u' ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers u')
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu'Q
  obtain ⟨s, hs, hsu⟩ := hu'Q
  refine ⟨h, h.2, (s : Γ), ?_, ?_⟩
  · have : s ∈ (SH : Subgroup H) := hs
    have h2 : s ∈ (S : Subgroup Γ).subgroupOf H := this
    exact (Subgroup.mem_subgroupOf.1 h2)
  · have := congrArg Subtype.val hsu
    simpa [u', MulAut.conj_apply] using this



theorem pair_closure_eq_top {Γ : Type*} [Group Γ] [Finite Γ]
    {A : Type*} [Group A]
    (R : Subgroup Γ) (g : Γ) (hne : R.map (MulAut.conj g).toMonoidHom ≠ R)
    {t : Γ} (htR : t ∈ R) (ht2 : orderOf t = 2)
    (hfus : ∀ u ∈ R, orderOf u = 2 → ∃ r ∈ R, r * t * r⁻¹ = u)
    (S : Sylow 2 Γ) (hSR : (S : Subgroup Γ) ≤ R)
    {E : Subgroup Γ} (hER : E ≤ R) (hE4 : Nat.card E = 4) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    {W : Subgroup Γ} (hWR : W ≤ R) (hWs : IsSimpleGroup W) (hWnc : ∃ x y : W, x * y ≠ y * x)
    (hWinv : ∃ s ∈ W, orderOf s = 2)
    (ψ : A →* Γ) (A₀ : Subgroup A) (hdich : ∀ M : Subgroup A, A₀ ≤ M → M = A₀ ∨ M = ⊤)
    (hψR : ∀ x, ψ x ∈ R ↔ x ∈ A₀)
    (hcent : ∀ x : Γ, x * t = t * x → ∃ y : A, x = ψ y ∨ x = t * ψ y)
    (hψs : IsSimpleGroup ψ.range) (hψnc : ∃ x y : ψ.range, x * y ≠ y * x)
    (hψinv : ∃ s ∈ ψ.range, orderOf s = 2) :
    Subgroup.closure ((R : Set Γ) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ)) = ⊤ := by
  classical
  set H := Subgroup.closure ((R : Set Γ) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ)) with hH
  by_contra hHtop
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have htH : t ∈ H := hRH htR
  have hRneH : R ≠ H := by
    intro h
    apply hne
    have hle : R.map (MulAut.conj g).toMonoidHom ≤ R := by
      calc R.map (MulAut.conj g).toMonoidHom ≤ H := hRgH
        _ = R := h.symm
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  set M₀ : Subgroup A := H.comap ψ with hM₀
  have hA₀M : A₀ ≤ M₀ := fun x hx => hRH ((hψR x).2 hx)
  rcases hdich M₀ hA₀M with hM | hM
  ·
    have hcentH : ∀ x ∈ H, x * t = t * x → x ∈ R := by
      intro x hxH hxt
      obtain ⟨y, hy | hy⟩ := hcent x hxt
      · have hy' : y ∈ M₀ := by
          rw [hM₀, Subgroup.mem_comap, ← hy]; exact hxH
        rw [hM] at hy'
        rw [hy]; exact (hψR y).2 hy'
      · have hψy : ψ y ∈ H := by
          have := H.mul_mem (H.inv_mem htH) hxH
          rwa [hy, inv_mul_cancel_left] at this
        have hy' : y ∈ M₀ := hψy
        rw [hM] at hy'
        rw [hy]; exact R.mul_mem htR ((hψR y).2 hy')
    have hSE := stronglyEmbeddedIn_of_centralizer H R hRH hRneH htR ht2 hfus hcentH
    exact false_of_stronglyEmbeddedIn hSE (hER.trans hRH) hE4 hE2 hWR hWs hWnc hWinv
  ·
    have hψH : ∀ y : A, ψ y ∈ H := by
      intro y
      have : y ∈ M₀ := by rw [hM]; exact Subgroup.mem_top y
      exact this
    have hcentΓ : ∀ x ∈ (⊤ : Subgroup Γ), x * t = t * x → x ∈ H := by
      intro x _ hxt
      obtain ⟨y, hy | hy⟩ := hcent x hxt
      · rw [hy]; exact hψH y
      · rw [hy]; exact H.mul_mem htH (hψH y)
    have hSH : (S : Subgroup Γ) ≤ H := hSR.trans hRH
    have hfusH : ∀ u ∈ H, orderOf u = 2 → ∃ h ∈ H, h * t * h⁻¹ = u := by
      intro u huH hu2
      obtain ⟨h, hhH, s, hsS, hsu⟩ := exists_conj_involution_sylow H S hSH huH hu2
      have hs2 : orderOf s = 2 := by
        have h1 : orderOf (MulAut.conj h s) = orderOf s := MulEquiv.orderOf_eq (MulAut.conj h) s
        rw [MulAut.conj_apply, hsu] at h1
        rw [← h1, hu2]
      obtain ⟨r, hrR, hrts⟩ := hfus s (hSR hsS) hs2
      exact ⟨h * r, H.mul_mem hhH (hRH hrR), by rw [← hsu, ← hrts]; group⟩
    have hSE := stronglyEmbeddedIn_of_centralizer ⊤ H le_top hHtop htH ht2 hfusH hcentΓ
    have hψle : ψ.range ≤ H := by
      rintro _ ⟨y, rfl⟩
      exact hψH y
    exact false_of_stronglyEmbeddedIn hSE (E := E) le_top hE4 hE2 hψle hψs hψnc hψinv

end CFSG.LocalAnalysis.SubfieldPairReeG2
