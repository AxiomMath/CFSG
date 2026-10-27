module

public import CFSG.Quasithin.Vol2.Ch9Sec3Red
public import CFSG.Quasithin.Vol2.Ch9Sec2Swap

public section

namespace CFSG.Quasithin.H.Om4

open Matrix

theorem ns_mul_swap {K : Type} [Field K] (A B A' B' : GL (Fin 2) K) (τ τ' : K ≃+* K) :
    ∃ A'' B'' : GL (Fin 2) K, (Om4.lr A B * Om4.frM τ) * (Om4.lr A' B' * Om4.frM τ' * Om4.trM) =
      Om4.lr A'' B'' * Om4.frM (τ * τ') * Om4.trM := by
  refine ⟨A * GeneralLinearGroup.map τ.toRingHom A', B * GeneralLinearGroup.map τ.toRingHom B', ?_⟩
  rw [← Om4.frM_mul, ← Om4.lr_mul]
  calc Om4.lr A B * Om4.frM τ * (Om4.lr A' B' * Om4.frM τ' * Om4.trM)
      = Om4.lr A B * (Om4.frM τ * Om4.lr A' B') * Om4.frM τ' * Om4.trM := by group
    _ = _ := by rw [Om4.frM_lr]; group

end CFSG.Quasithin.H.Om4

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

include S in
theorem exists_mul_mem_normalizer_hall {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    {t₀ : G} (ht₀ : t₀ ∈ T) :
    ∃ m ∈ T ⊓ fsuL0 T L, m * t₀ ∈ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hP₀S := S.isSylowTwoOf_T_inf_L0_normalizer
  have hP₀N₀ : P₀ ≤ N₀ := hP₀S.1
  have hP₀2 : IsPGroup 2 P₀ := hP₀S.2.1
  have hTP : ∀ s ∈ T, s ∈ Subgroup.normalizer (P₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
      Setup.T_le_normalizer_L0 hs⟩
  have hTN : ∀ s ∈ T, s ∈ Subgroup.normalizer (N₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Setup.T_le_normalizer_L0 hs,
      Subgroup.le_normalizer (hTP s hs)⟩
  set D' := D.map (MulAut.conj t₀).toMonoidHom with hD'def
  have hD' : Lin2.IsHallTwoPrimeOf D' N₀ :=
    Vol2.Ch10.SecB.C11AmS.isHallTwoPrimeOf_map_conj (hTN t₀ ht₀) hD
  have hsup : P₀ ⊔ D = P₀ ⊔ D' :=
    (le_antisymm (sup_le hP₀N₀ hD.1) (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall hP₀S hD)).trans
      (le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall hP₀S hD') (sup_le hP₀N₀ hD'.1))
  obtain ⟨m, hm, hmD⟩ := Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement hP₀2 hD.2.1
    (hD.1.trans inf_le_right) (hD'.1.trans inf_le_right)
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP₀2 hD.2.1)
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP₀2 hD'.2.1) hsup
  refine ⟨m, hm, ?_⟩
  have hDn : ∀ d ∈ D, (m * t₀) * d * (m * t₀)⁻¹ ∈ D := by
    intro d hd
    have h1 : t₀ * d * t₀⁻¹ ∈ D' := ⟨d, hd, by simp [MulAut.conj_apply]⟩
    rw [hmD] at h1
    obtain ⟨d₂, hd₂, hd₂e⟩ := h1
    have h2 : m⁻¹ * d₂ * m = t₀ * d * t₀⁻¹ := by simpa [MulAut.conj_apply] using hd₂e
    have h3 : (m * t₀) * d * (m * t₀)⁻¹ = d₂ := by
      calc (m * t₀) * d * (m * t₀)⁻¹ = m * (t₀ * d * t₀⁻¹) * m⁻¹ := by group
        _ = m * (m⁻¹ * d₂ * m) * m⁻¹ := by rw [h2]
        _ = d₂ := by group
    rw [h3]
    exact hd₂
  have hle : D.map (MulAut.conj (m * t₀)).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    show (MulAut.conj (m * t₀)) d ∈ D
    rw [MulAut.conj_apply]
    exact hDn d hd
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj (m * t₀)).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem not_mem_normalizer_L_of_swap
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) {x : G}
    (hx : x ∈ fsuM T L) {A B : GL (Fin 2) K} {τ : K ≃+* K}
    (hform : bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ * Om4.trM) :
    x ∉ Subgroup.normalizer (L : Set G) := by
  intro hxN
  set PL := (L.subgroupOf (fsuL0 T L)).map ψ with hPL
  have hconj : ∀ l (hl : l ∈ L), ψ ⟨x * l * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx l).mp (S.L_le_L0 hl)⟩ = 1 := by
    intro l hl
    have hρ := hc.bar_conj hx ⟨l, S.L_le_L0 hl⟩
    rw [hform, Om4.rho_apply (ψ ⟨l, S.L_le_L0 hl⟩), Om4.conj_swap] at hρ
    have hmem : ψ ⟨l, S.L_le_L0 hl⟩ ∈ PL :=
      ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hmem' : ψ ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx l).mp (S.L_le_L0 hl)⟩ ∈ PL :=
      ⟨_, Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl), rfl⟩
    rcases hc.map_L h37c h38c with h | h <;> rw [← hPL] at h <;> rw [h] at hmem hmem'
    · have h2 : (ψ ⟨l, S.L_le_L0 hl⟩).2 = 1 := hmem
      rw [h2, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨h3, -⟩ := Om4.eq_of_rho_eq_lr (by rw [Units.val_one, Matrix.det_one]) hρ
      have h4 : (ψ ⟨x * l * x⁻¹, _⟩).1 = 1 := Subtype.ext h3.symm
      exact Prod.ext h4 hmem'
    · have h2 : (ψ ⟨l, S.L_le_L0 hl⟩).1 = 1 := hmem
      rw [h2, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨-, h3⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
      have h4 : (ψ ⟨x * l * x⁻¹, _⟩).2 = 1 := Subtype.ext h3.symm
      exact Prod.ext hmem' h4
  have hu : u1 K ≠ 1 := fun h1 => by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp [u1] at this
  have hne : PL ≠ ⊥ := by
    rcases hc.map_L h37c h38c with h | h <;> rw [← hPL] at h <;> rw [h] <;> intro hbot
    · have : ((u1 K, 1) : SpecialLinearGroup (Fin 2) K × _) ∈
          (MonoidHom.snd (SpecialLinearGroup (Fin 2) K) (SpecialLinearGroup (Fin 2) K)).ker :=
        MonoidHom.mem_ker.mpr rfl
      rw [hbot, Subgroup.mem_bot] at this
      exact hu (congrArg Prod.fst this)
    · have : ((1, u1 K) : SpecialLinearGroup (Fin 2) K × _) ∈
          (MonoidHom.fst (SpecialLinearGroup (Fin 2) K) (SpecialLinearGroup (Fin 2) K)).ker :=
        MonoidHom.mem_ker.mpr rfl
      rw [hbot, Subgroup.mem_bot] at this
      exact hu (congrArg Prod.snd this)
  apply hne
  rw [eq_bot_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hkL : (k : G) ∈ L := Subgroup.mem_subgroupOf.mp hk
  have hl' : x⁻¹ * k * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) k).mp hkL
    simpa using this
  have hk2 : k = ⟨x * (x⁻¹ * k * x) * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx _).mp (S.L_le_L0 hl')⟩ :=
    Subtype.ext (by simp [mul_assoc])
  rw [Subgroup.mem_bot, hk2]
  exact hconj _ hl'

theorem exists_swap_field (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hT : ¬ T ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    ∃ t, ∃ ht : t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
      t ∈ Subgroup.normalizer (D : Set G) ∧
      ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), τ ≠ 1 ∧
        bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM := by
  obtain ⟨t₁, ht₁, ht₁V⟩ := IsConcreteLE.not_le_iff_exists.mp hT
  obtain ⟨A₁, B₁, τ₁, h₁⟩ := hc.exists_form (Setup.T_le_fsuM ht₁)
  have hτ₁ : τ₁ ≠ 1 := by
    rintro rfl
    exact ht₁V (hc.mem_centralizer_V1_of_one ht₁ h₁)
  obtain ⟨t₀, ht₀, ht₀n⟩ := S.exists_not_mem_normalizer
  obtain ⟨A₀, B₀, τ₀, -, -, h₀⟩ := hc.swap_of_not_mem h37 h38 h37c h38c ht₀ ht₀n
  have key : ∃ t₂, ∃ ht₂ : t₂ ∈ T, ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), τ ≠ 1 ∧
      bar e ⟨t₂, S.hMN (Setup.T_le_fsuM ht₂)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM := by
    by_cases hτ₀ : τ₀ = 1
    · subst hτ₀
      rcases h₁ with h₁ | h₁
      · obtain ⟨A'', B'', hAB⟩ := Om4.ns_mul_swap A₁ B₁ A₀ B₀ τ₁ 1
        refine ⟨t₁ * t₀, T.mul_mem ht₁ ht₀, A'', B'', τ₁ * 1, by rwa [mul_one], ?_⟩
        have hm : bar e ⟨t₁ * t₀, S.hMN (Setup.T_le_fsuM (T.mul_mem ht₁ ht₀))⟩ =
            bar e ⟨t₁, S.hMN (Setup.T_le_fsuM ht₁)⟩ * bar e ⟨t₀, S.hMN (Setup.T_le_fsuM ht₀)⟩ := by
          rw [← map_mul]
          rfl
        rw [hm, h₁, h₀, hAB]
      · exact ⟨t₁, ht₁, A₁, B₁, τ₁, hτ₁, h₁⟩
    · exact ⟨t₀, ht₀, A₀, B₀, τ₀, hτ₀, h₀⟩
  obtain ⟨t₂, ht₂, A₂, B₂, τ₂, hτ₂, h₂⟩ := key
  obtain ⟨m, hm, hmN⟩ := S.exists_mul_mem_normalizer_hall hD ht₂
  have hmt : m * t₂ ∈ T := T.mul_mem hm.1 ht₂
  have hform : bar e ⟨m * t₂, S.hMN (Setup.T_le_fsuM hmt)⟩ =
      Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ ⟨m, hm.2⟩).1 * A₂)
        (Matrix.SpecialLinearGroup.toGL (ψ ⟨m, hm.2⟩).2 * B₂) * Om4.frM τ₂ * Om4.trM := by
    have h3 : bar e ⟨m * t₂, S.hMN (Setup.T_le_fsuM hmt)⟩ =
        bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨m, hm.2⟩) *
          bar e ⟨t₂, S.hMN (Setup.T_le_fsuM ht₂)⟩ := by
      rw [← map_mul]
      rfl
    rw [h3, hc.bar_L0, Om4.rho_apply, h₂, ← mul_assoc, ← mul_assoc, Om4.lr_mul]
  exact ⟨m * t₂, hmt, hc.not_mem_normalizer_L_of_swap h37c h38c (Setup.T_le_fsuM hmt) hform, hmN,
    _, _, τ₂, hτ₂, hform⟩

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
