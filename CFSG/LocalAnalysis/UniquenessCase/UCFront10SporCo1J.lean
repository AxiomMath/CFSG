module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1T24
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique
  CFSG.EvenSporadicStandard.TwoCo1

theorem card_epsHom_range :
    Nat.card epsHom.range = 2 ^ 11 := by
  rw [Nat.card_congr (MonoidHom.ofInjective epsHom_injective).toEquiv.symm,
    Nat.card_congr (Multiplicative.ofAdd :
      (Fin 11 → ZMod 2) ≃ Multiplicative (Fin 11 → ZMod 2)).symm]
  simp [Nat.card_eq_fintype_card]

theorem isElemAbelian_epsHom_range :
    IsElemAbelian 2 epsHom.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    simp only [Subgroup.coe_mul, ← map_mul, mul_comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    convert map_one epsHom
    exact Multiplicative.toAdd.injective (by
      rw [toAdd_pow, toAdd_one, two_nsmul]
      funext i
      exact CharTwo.add_self_eq_zero (Multiplicative.toAdd x i))


theorem isSylowTwoOf_t24 : IsSylowTwoOf t24 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card card_t24, ?_⟩
  change ¬ 2 ∣ t24.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index t24
  rw [card_t24, natCard_PM24] at h
  omega


theorem theta_mul_epsMask_eMaskA {s : SM24} (hs : s.right ∈ t24) :
    theta s * epsMask eMaskA = epsMask eMaskA * theta s := by
  have hc : iota s.right * epsMask eMaskA * (iota s.right)⁻¹ = epsMask eMaskA := by
    rw [epsMask, iota_conj, toAdd_ofAdd, eMaskA, rho_t24_xA hs]
  have he : epsHom s.left * epsMask eMaskA = epsMask eMaskA * epsHom s.left := by
    rw [epsMask, ← map_mul, ← map_mul, mul_comm s.left]
  rw [theta_apply, mul_assoc, mul_inv_eq_iff_eq_mul.1 hc, ← mul_assoc, he, mul_assoc]


theorem card_co1Sylow : Nat.card co1Sylow = 2 ^ 21 := by
  rw [co1Sylow, Subgroup.card_map_of_injective theta_injective]
  have h1 := Subgroup.card_mul_index (t24.comap (SemidirectProduct.rightHom : SM24 →* PM24))
  rw [Subgroup.index_comap_of_surjective _ SemidirectProduct.rightHom_surjective,
    natCard_SM24] at h1
  have h2 := Subgroup.card_mul_index t24
  rw [card_t24, natCard_PM24] at h2
  have hi : t24.index = 239085 := by omega
  rw [hi] at h1
  have h3 : Nat.card (t24.comap (SemidirectProduct.rightHom : SM24 →* PM24)) * 239085 =
      2 ^ 21 * 239085 := by
    rw [h1]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem isSylowTwoOf_co1Sylow : IsSylowTwoOf co1Sylow ⊤ := by
  refine ⟨le_top, IsPGroup.of_card card_co1Sylow, ?_⟩
  change ¬ 2 ∣ co1Sylow.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index co1Sylow
  rw [card_co1Sylow, CFSG.Sporadic.Co1.card_Co1] at h
  omega

theorem le_epsHom_range_or_card_le {B : Subgroup NativeSporadic.Co1} (hB : B ≤ co1Sylow)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    B ≤ epsHom.range ∨ Nat.card B ≤ 2 ^ 10 := by
  classical
  set B' := B.comap theta
  have hmap : B'.map theta = B :=
    Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
  have hB'T : ∀ s ∈ B', s.right ∈ t24 := fun s hs => (theta_mem_co1Sylow_iff s).1 (hB hs)
  have hc' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    theta_injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy)
  set Bbar := B'.map (SemidirectProduct.rightHom : SM24 →* PM24)
  by_cases hbar : Bbar = ⊥
  · left
    rw [← hmap]
    rintro _ ⟨s, hs, rfl⟩
    have hr : s.right = 1 := by
      have : s.right ∈ Bbar := ⟨s, hs, rfl⟩
      rwa [hbar, Subgroup.mem_bot] at this
    exact ⟨s.left, by rw [theta_apply, hr, map_one, mul_one]⟩
  right
  let φ : B' →* PM24 := SemidirectProduct.rightHom.comp B'.subtype
  have hrange : φ.range = Bbar := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker ≤ Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ Bbar, rho p v = v} := by
    refine Nat.card_le_card_of_injective
      (fun s => ⟨Multiplicative.toAdd ((s : B') : SM24).left, ?_⟩) ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨⟨x, hx⟩, hxk⟩ := s
      have hx1 : x.right = 1 := hxk
      have hl := congrArg SemidirectProduct.left (hc' x hx y hy)
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hx1, map_one,
        MulAut.one_apply, mul_comm x.left y.left] at hl
      have h := congrArg Multiplicative.toAdd (mul_left_cancel hl)
      rw [phiOf_apply, toAdd_ofAdd] at h
      exact h.symm
    · rintro ⟨⟨x, hx⟩, hxk⟩ ⟨⟨y, hy⟩, hyk⟩ h
      have hx1 : x.right = 1 := hxk
      have hy1 : y.right = 1 := hyk
      have hl : x.left = y.left := Multiplicative.toAdd.injective (congrArg Subtype.val h)
      exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hl (hx1.trans hy1.symm)))
  have hbound := card_mul_card_fixed_le (K := Bbar) (by rintro _ ⟨y, hy, rfl⟩; exact hB'T y hy)
    hbar (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc' a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, show a * a = 1 from theta_injective (by rw [map_mul, map_one]; exact hsq _ ha),
        map_one])
  have hcard : Nat.card B = Nat.card B' := by
    rw [← hmap, Subgroup.card_map_of_injective theta_injective]
  rw [hcard, ← Subgroup.card_ker_mul_card_range φ, hrange]
  calc Nat.card φ.ker * Nat.card Bbar
      ≤ Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ Bbar, rho p v = v} * Nat.card Bbar :=
        Nat.mul_le_mul_right _ hker
    _ = Nat.card Bbar * Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ Bbar, rho p v = v} := mul_comm _ _
    _ ≤ 2 ^ 10 := hbound

theorem thompsonJ_co1Sylow : CFSG.Quasithin.thompsonJ co1Sylow = epsHom.range := by
  have hab : ∀ B : Subgroup NativeSporadic.Co1, IsElemAbelian 2 B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x * x = 1 := by
    intro B hB
    have := hB.1
    exact ⟨fun x hx y hy => Subgroup.mul_comm_of_mem_isMulCommutative B hx hy,
      fun x hx => (pow_two x).symm.trans (hB.2 x hx)⟩
  have : Finite epsHom.range := Nat.finite_of_card_ne_zero (by rw [card_epsHom_range]; norm_num)
  have hE : CFSG.Quasithin.IsMaxElemAbelian co1Sylow epsHom.range := by
    refine ⟨epsHom_range_le_co1Sylow, isElemAbelian_epsHom_range, fun B hB hBab => ?_⟩
    rcases le_epsHom_range_or_card_le hB (hab B hBab).1 (hab B hBab).2 with h | h
    · exact Subgroup.card_le_of_le h
    · rw [card_epsHom_range]
      omega
  have hiff : ∀ A, CFSG.Quasithin.IsMaxElemAbelian co1Sylow A → A = epsHom.range := by
    intro A hA
    have hge : Nat.card epsHom.range ≤ Nat.card A := hA.2.2 _ hE.1 hE.2.1
    rcases le_epsHom_range_or_card_le hA.1 (hab A hA.2.1).1 (hab A hA.2.1).2 with h | h
    · exact Subgroup.eq_of_le_of_card_ge h hge
    · rw [card_epsHom_range] at hge
      omega
  refine le_antisymm (iSup₂_le fun A hA => (hiff A hA).le) ?_
  exact le_iSup₂_of_le (f := fun A (_ : CFSG.Quasithin.IsMaxElemAbelian co1Sylow A) => A) _ hE
    le_rfl

theorem epsA_mem_quasithinOmegaOneCenter :
    epsMask eMaskA ∈ quasithinOmegaOneCenter co1Sylow := by
  have hE : epsMask eMaskA ∈ epsHom.range := by
    rw [epsMask]
    exact ⟨_, rfl⟩
  have hC : epsMask eMaskA ∈ Subgroup.centralizer (co1Sylow : Set NativeSporadic.Co1) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 (SetLike.mem_coe.1 hh)
    exact theta_mul_epsMask_eMaskA ((theta_mem_co1Sylow_iff s).1 (SetLike.mem_coe.1 hh))
  exact Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨epsHom_range_le_co1Sylow hE, hC⟩,
    isElemAbelian_epsHom_range.2 _ hE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
