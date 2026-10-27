module

public import CFSG.Quasithin.Background.A3Structure314Cases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace A314

theorem isSL2_quotient_oddCore {Λ : Type} [Group Λ] [Finite Λ] {B : Subgroup Λ} {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hM : IsSL2 r ↥(A313.imgOdd B)) :
    IsSL2 r (↥B ⧸ CFSG.oddCore ↥B) := by
  have hker : (A313.rho B).ker = CFSG.oddCore ↥B := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, A313.odd_card_ker_rho B⟩
    · intro x hx
      have h1 : (x : Λ) ∈ (CFSG.oddCore ↥B).map B.subtype := ⟨x, hx, rfl⟩
      rw [A313.oddCore_map_eq hr hr5 hM] at h1
      exact A313.mem_ker_rho.mpr h1.2
  let e1 : (↥B ⧸ (A313.rho B).ker) ≃* ↥(A313.imgOdd B) :=
    QuotientGroup.quotientKerEquivOfSurjective (A313.rho B) (A313.rho_surjective B)
  let e2 : (↥B ⧸ CFSG.oddCore ↥B) ≃* (↥B ⧸ (A313.rho B).ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact IsSL2.of_mulEquiv (e2.trans e1).symm hM

theorem nonquasi_case {G : Type} [Group G] [Finite G] {B L : Subgroup G} (h36 : A36Strong L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) (hBL : B < L)
    (hA : IsAlt 5 (↥B ⧸ CFSG.solvableRadical ↥B)) (h : A312Nonquasi B L) :
    (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)) := by
  obtain ⟨p₀, hp₀, hp₀3, hΛ⟩ := A312.exists_isSL2_oddCore h36 hnq
  have hr5₀ : 5 ≤ p₀ := A313.five_le_of_prime hp₀ hp₀3
  set B' : Subgroup ↥L := B.subgroupOf L with hB'
  let eB : ↥B' ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL.le
  have hOLnorm := A312.normal_subgroupOf_sup_oddCoreSub hBL.le
  have hQ : ∀ {r : ℕ}, r.Prime → 5 ≤ r → IsSL2 r ↥(A313.imgOdd B') →
      IsSL2 r (↥B ⧸ CFSG.oddCore ↥B) := fun {r} hr hr5 hM => by
    let e : (↥B' ⧸ CFSG.oddCore ↥B') ≃* (↥B ⧸ CFSG.oddCore ↥B) :=
      QuotientGroup.congr _ _ eB (A313.oddCore_map_mulEquiv eB)
    exact IsSL2.of_mulEquiv e (isSL2_quotient_oddCore hr hr5 hM)
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, -⟩ | ⟨-, ⟨p₂, hp₂, hp₂5, hp₂8, hpSL₂⟩, N, hNn, hNeq, hN5⟩
  · have htop : A313.imgOdd B' = ⊤ := (A313.imgOdd_eq_top_iff hBL.le).mpr hLB
    have hM : IsSL2 p₀ ↥(A313.imgOdd B') :=
      IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
    have hQ' := hQ hp₀ hr5₀ hM
    have hp5 : p₀ = 5 :=
      p_eq_five_of_sl2 (V := CFSG.oddCore ↥B) (A312.oddCore_isSolvable _) hp₀ hp₀3 hQ' hA
    subst hp5
    exact Or.inl ⟨hQ', hLB⟩
  · subst hNeq
    have hM : IsSL2 5 ↥(A313.imgOdd B') := IsSL2.of_mulEquiv (A312.quotEquivImage hBL.le) hN5
    exact Or.inr ⟨hQ Nat.prime_five le_rfl hM, p₂, hp₂, hp₂5, hp₂8, hpSL₂⟩

end A314

theorem a314 (hF : A314Facts) {G : Type} [Group G] (hG : SQTKHyp G) (h36 : A36Statement G)
    (h312 : A312Statement G) {T B L : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T)
    (hA : IsAlt 5 (↥B ⧸ CFSG.solvableRadical ↥B)) (hL : L ∈ cComp (⊤ : Subgroup G))
    (hBL : B < L) : A314Statement T B L := by
  have : Finite G := hG.finite
  obtain ⟨L₀, hL₀, hBL₀, huniq, hcases⟩ := h312 T hT B hB
  have hLL₀ : L = L₀ := huniq L hL hBL.le
  subst hLL₀
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL) hT
  have hB1 : B ∈ lFamily (T ⊓ L) :=
    cComp_mem_of_le hB le_sup_left (sup_le_sup_left inf_le_left B)
  rcases hcases with h | h | h
  · exact absurd h hBL.ne
  · exact A314.of_case hF ⟨hB, hBL, hTL, hB1, hA⟩ h
  · unfold A314Statement
    rcases A314.nonquasi_case (h36 L hL) (A312.not_quasisimple_of_nonquasi h) hBL hA h
      with h13 | h14
    · iterate 12 right
      left
      exact h13
    · iterate 13 right
      exact h14

end CFSG.Quasithin
